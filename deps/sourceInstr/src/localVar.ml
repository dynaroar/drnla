open Cil
open Eutils

open Int64
open String
module E = Errormsg
module L = List

let mkAtomic (vi: varinfo) : exp =
   BinOp (Eq, Lval (Var vi, NoOffset), kinteger64 IInt (of_int 0), TInt (IInt, []))

  (* create tmperate variable to be assigned atomic proposition to *)
let mkVis (fd: fundec) (exprs: exp list): (varinfo * exp) list =
  L.mapi (fun i expr ->
      (* ((makeLocalVar fd ("atomic"^(string_of_int i)) (TInt (IInt, []))), expr) *)
(* not adding to funciton's slocals. *)
      ((makeLocalVar fd ~insert:false ("atomic"^(string_of_int i)) (TInt (IInt, []))), expr)
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


(* class nonlinearVisitor nonhash = object(self)
 *   inherit nopcilVisitor
 *   method vinst (i : instr) =
 *     match i with
 *     | Set (lv, expr, loc) ->
 *        if isnonlinear expr false
 *        then (Hashtbl.add nonhash loc expr; SkipChildren)
 *        else SkipChildren
 *     | _ -> SkipChildren
 * end *)

(* class nonlinearVisitor nonhash = object(self)
 *   inherit nopCilVisitor
 *   method vstmt (s: stmt) =
 *     let skind = s.skind in
 *     (match skind with
 *      | Instr instr_list -> (List.fold_left nonlinearInstr nonhash instr_list; DoChildren)
 *      | _ -> DoChildren
 *     )    
 * end *)


class nonlinearVisitor nonhash = object(self)
  inherit nopCilVisitor
  method vexpr (e: exp) =
    if isnonlinear e 
    then (Hashtbl.add nonhash !currentLoc e; SkipChildren)
    else SkipChildren
end


let processFunction ((tf, exprs) : string * exp list) (fd : fundec) (loc : location) : unit =
  if fd.svar.vname <> tf then () else begin
      (* let varInfos = L.map (fun s -> makeLocalVar fd s (TInt (IInt, []))) tvs in  (\* empty attribute for locals injected *\)
       * let vis = new assignAddVisitor varInfos in
       *     ignore(visitCilFunction vis fd) *)
      let varInfos = mkVis fd exprs in
      let nonlinear = Hashtbl.create 10 in
      let vis = new assignAtomicVisitor varInfos fd.slocals in
      let nonVis = new nonlinearVisitor nonlinear in
      ignore(visitCilFunction vis fd);
      ignore(visitCilFunction nonVis fd);
      (* let expPinter = new defaultCILPrinter in *)
      Hashtbl.iter (fun x y ->
          let string_expr = Pretty.sprint (Int64.to_int max_int) (printExp defaultCilPrinter () y) in
          Printf.printf "nonlinear location at line : %s, %s \n" (string_of_int x.line) string_expr;
          ) nonlinear
      
    end

let varInject (funvars : string * exp list) (f : file) : unit =
(* let varInject (funvars : string * string list) (f : file) : unit = *)
  funvars |> processFunction |> onlyFunctions |> iterGlobals f
