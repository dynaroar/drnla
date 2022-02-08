open Cil
open Eutils
open Printf
open Int64
open String
module E = Errormsg
module L = List

let mkAtomic (vi: varinfo) : exp =
   BinOp (Eq, Lval (Var vi, NoOffset), kinteger64 IInt (of_int 0), TInt (IInt, []))

  (* create tmperate variable to be assigned atomic proposition to *)


let mkVis (fd: fundec) (exprs: exp list): (varinfo * exp) list =
  L.mapi (fun i expr ->
      ((makeLocalVar fd ("atomic"^(string_of_int i)) (TInt (IInt, []))), expr)
(* not adding to funciton's slocals. *)
      (* ((makeLocalVar fd ~insert:false ("atomic"^(string_of_int i)) (TInt (IInt, []))), expr) *)
    ) exprs


let mkCall ?(ftype=TVoid []) ?(av=None) (fname:string) args : instr =
  let mkVi ?(ftype=TVoid []) fname: varinfo = makeVarinfo true fname ftype in
  let f = var(mkVi ~ftype:ftype fname) in
  Call(av, Lval f, args, !currentLoc)

let rec hasVar (expr : exp) : bool =
  match expr with
  | BinOp (_, opr1, opr2, _) -> (hasVar opr1) || (hasVar opr2)
  | AlignOfE opr -> hasVar opr
  | UnOp (_, opr, _) -> hasVar opr
  | CastE (_, opr) -> hasVar opr
  | AddrOf lval -> true
  | StartOf lval -> true
  | Lval _ -> true
  | _ -> false
  
let rec isnonlinear (expr : exp) : bool =
  match expr with
  | BinOp (opc, opr1, opr2, _) ->
     (match opc with
      | Mult | Div | Mod | Shiftlt | Shiftrt | BAnd | BXor | BOr
        | PlusPI | IndexPI | MinusPI | MinusPP ->
         ( match opr1 with
           | Lval _ ->
              (match opr2 with
               | Lval _ -> true
               | _ -> isnonlinear opr2
              )
           | Const _ -> isnonlinear opr2
           | _ ->
              (match opr2 with
               | Const _ -> isnonlinear opr1
               | _ ->
                  if (hasVar opr1 && hasVar opr2 )
                  then true
                  else (isnonlinear opr1) || (isnonlinear opr2) 
              )
         ) 
      | _ -> (isnonlinear opr1) || (isnonlinear opr2)
     )
  | UnOp (opc, opr, _) ->
     (match opc with
      | BNot -> true
      | _ -> isnonlinear opr
     )
  | Const _ | Lval _ -> false
  | _ -> true


(* class assignAddVisitor (vinfos : varinfo list) = object(self) *)
class assignAtomicVisitor (vexprs : (varinfo * exp) list) (flocals: varinfo list)= object(self)
  inherit nopCilVisitor

  method vinst (i : instr) =
    match i with
    | Set(_, _, loc) | Call(_, _, _, loc) ->
       let inject = L.map (fun (vi, exp) -> Set((Var vi, NoOffset), exp, loc)) vexprs in
       (* let atomFormals = L.map (fun (vi, _) -> Lval (Var vi, NoOffset)) vexprs in *)
       let localFormals = L.map (fun x -> Lval (Var x, NoOffset)) flocals in
       let traceName = "vtrace"^(string_of_int (!currentLoc).line) in
       let vtraceCall = mkCall traceName localFormals in
       (* let injectVis = i::inject@[vtraceCall] in *)
       (* without injecting a auxiliary variables *)
       let injectVis = [i; vtraceCall] in
       ChangeTo injectVis
    | _ -> SkipChildren
end


let nonlinearInstr nonhash i =
  match i with
  | Set (lv, expr, loc) ->
     if isnonlinear expr
     then (Hashtbl.add nonhash loc expr; nonhash)
     else nonhash
  | _ -> nonhash

 
class nonlinearVisitor nonhash = object(self)
  inherit nopCilVisitor
  method vexpr (e: exp) =
    if isnonlinear e 
    then (Hashtbl.add nonhash !currentLoc e;          
          SkipChildren)
    else SkipChildren
end


(* let inserTmp bkstmt:stmt list = *)

let headList l =
  match l with
   | [h] -> h
   | h :: t -> h
   | [] -> failwith "empty statement list!"
let tailList l =
  match l with
  | h :: t -> t
  | [h] -> []
  | [] -> failwith "empty list!"
let stringOfExp e =
  Pretty.sprint (Int64.to_int max_int) (printExp defaultCilPrinter () e)  
  
let negExp e =
  match e with
  | UnOp (LNot, opr, _) -> opr
  | _ -> failwith "expecting a negate of loop condition expression!"


class loopVisitor tmpVarHash = object(self)
  inherit nopCilVisitor
  val mutable nonlinearExpr = mkString "nonliear"
  method vstmt (s: stmt) =
    let action s =
      match s.skind with
      | Loop (bk, loc, stmt1, stmt2) ->
         
        let stmtsBk = bk.bstmts in
        let loopIf = headList stmtsBk in
        (match loopIf.skind with
         | If (expr, bk1, bk2, loc) ->
            if isnonlinear expr
            then
              let tmpVarInfo = Hashtbl.find tmpVarHash loc in
              printf "while loop nonlinear condition, %s.\n" (stringOfExp expr);
              nonlinearExpr <- expr;            
              let tail = tailList stmtsBk in
              let ifTransKind = If (v2e tmpVarInfo, bk1, bk2, loc) in
              loopIf.skind <- ifTransKind;
              bk.bstmts <- (loopIf :: tail);
              let nonStmt = i2s (Set(var tmpVarInfo, nonlinearExpr, loc)) in
              let nb = mkBlock [nonStmt; mkStmt s.skind] in
              s.skind <- Block nb;
              s
            else s
         | _ -> s
        )
      | If (expr, bk1, bk2, loc) ->
         if isnonlinear expr
         then
           let tmpVarInfo = Hashtbl.find tmpVarHash loc in
           nonlinearExpr <- expr;
           printf "for nonlinear condition, %s.\n" (stringOfExp expr);
           let nonStmt = i2s (Set(var tmpVarInfo, nonlinearExpr, loc)) in
           let ifTransKind = If (v2e tmpVarInfo, bk1, bk2, loc) in
           s.skind <- ifTransKind;
           let nb = mkBlock [nonStmt; mkStmt s.skind] in
           s.skind <- Block nb;
           s    
         else s
  
      | _ -> s
    in
    ChangeDoChildrenPost(s, action)

    (* ChangeTo s *)
       
end



let processFunction ((tf, exprs) : string * exp list) (fd : fundec) (loc : location) : unit =
  if fd.svar.vname <> tf then () else begin
      (* let varInfos = L.map (fun s -> makeLocalVar fd s (TInt (IInt, []))) tvs in  (\* empty attribute for locals injected *\)
       * let vis = new assignAddVisitor varInfos in
       *     ignore(visitCilFunction vis fd) *)
      let varInfos = mkVis fd exprs in
      let nonlinear = Hashtbl.create 10 in
      let nonVis = new nonlinearVisitor nonlinear in
      ignore(visitCilFunction nonVis fd);
      (* let expPinter = new defaultCILPrinter in *)

      let nonTmpVars = Hashtbl.fold (fun key _ tmpVars ->
                           (Hashtbl.add tmpVars key (makeLocalVar fd ("tmpVar"^(string_of_int key.line)) (TInt (IInt, []))));
                           tmpVars
                         ) nonlinear (Hashtbl.create 10) in
      let vStmts = new loopVisitor nonTmpVars in
      ignore(visitCilFunction vStmts fd);

      let vis = new assignAtomicVisitor varInfos fd.slocals in
      ignore(visitCilFunction vis fd);
      
      Hashtbl.iter (fun x y ->
          let sExpr = stringOfExp y in
          Printf.printf "nonlinear location at line : %s, %s \n" (string_of_int x.line) sExpr;
        ) nonlinear;
        Hashtbl.iter (fun _ y -> Printf.printf "tmp var name: %s\n" y.vname) nonTmpVars
      
    end

let varInject (funvars : string * exp list) (f : file) : unit =
(* let varInject (funvars : string * string list) (f : file) : unit = *)
  funvars |> processFunction |> onlyFunctions |> iterGlobals f
