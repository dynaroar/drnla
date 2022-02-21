open Cil
open Eutils
open Printf
open Int64
open String
module E = Errormsg
module L = List

 
class nonlinearVisitor nonhash = object(self)
  inherit nopCilVisitor
  method vexpr (e: exp) =
    if isnonlinear e 
    then (Hashtbl.add nonhash !currentLoc e;          
          SkipChildren)
    else SkipChildren
end


let notCompExp exp =
  match exp with
  | BinOp (opc, _, _, _) ->
     (match opc with
      | Lt | Gt | Le | Ge | Eq | Ne -> false
      | _  -> true
     )
  | _ -> true

let rec subNonlinear fd binExp loc counter tmpList =
  match binExp with
  | BinOp (opc, opr1, opr2, typ) ->
     (match opc with
      | Lt | Gt | Le | Ge | Eq | Ne ->
         if isnonlinear opr1 && notCompExp opr1
         then
           let tmpVarInfo = makeLocalVar fd ("tmpVar"^(string_of_int loc.line)^"_"^(string_of_int !counter)) (TInt (IInt, [])) in
           let tmpInstr = Set(var tmpVarInfo, opr1, loc) in
           counter := !counter + 1;
           tmpList := tmpInstr :: !tmpList;
           let (tmpListOpr2, tmpOpr2) = subNonlinear fd opr2 loc counter tmpList in
             (!tmpList @ tmpListOpr2, BinOp (opc, v2e tmpVarInfo, tmpOpr2, typ))
         else if isnonlinear opr2 && notCompExp opr2
         then
           let tmpVarInfo = makeLocalVar fd ("tmpVar"^(string_of_int loc.line)^"_"^(string_of_int !counter)) (TInt (IInt, [])) in
           let tmpInstr = Set(var tmpVarInfo, opr2, loc) in
           counter := !counter + 1 ;
           tmpList := tmpInstr :: !tmpList;
           let (tmpListOpr1, tmpOpr1) = subNonlinear fd opr1 loc counter tmpList in
           (!tmpList @ tmpListOpr1, BinOp (opc, tmpOpr1, v2e tmpVarInfo, typ))
         else
           let (tmpListOpr1, tmpOpr1) = subNonlinear fd opr1 loc counter tmpList in
           let (tmpListOpr2, tmpOpr2) = subNonlinear fd opr2 loc counter tmpList in
           (tmpListOpr1 @ tmpListOpr2, BinOp (opc, tmpOpr1, tmpOpr2, typ))
      | _ -> ([], binExp)
     )
  | _ -> ([], binExp)
 
class stmtVisitor fd = object(self)
  inherit nopCilVisitor
  val mutable nonlinearExpr = mkString "nonliear"
  val mutable vassert = "assert"
    
  method vstmt (s: stmt) =
    let action s =
      match s.skind with
       | If (expr, bk1, bk2, loc) ->
         if isnonlinear expr
         then
           let (tempList, tmpExp) = subNonlinear fd expr loc (ref 0) (ref []) in
           nonlinearExpr <- expr;
           printf "if nonlinear condition, %s.\n" (stringOfExp expr);
           let ifTransKind = If (tmpExp, bk1, bk2, loc) in
           s.skind <- ifTransKind;
           let nonStmtList = L.map i2s tempList in
           let nb = mkBlock (nonStmtList @ [mkStmt s.skind]) in
           s.skind <- Block nb;
           s    
         else s
      | Instr instrList ->
         let changeIns =
           List.fold_left (fun insL i ->
               match i with
               | Call (lv, fvname, args, loc) ->
                  let fvi = e2v fvname in
                  if fvi.vname <> vassert then i :: insL else begin
                      match args with
                      | [prop] ->
                         if isnonlinear prop
                         then
                           let (tmpList, tmpExp) = subNonlinear fd prop loc (ref 0) (ref []) in
                           printf "set instruction nonlinear, %s.\n" (stringOfExp prop);
                           tmpList @ [Call (lv, fvname, [tmpExp], loc)] @ insL
                         else  i :: insL
                      | _ -> failwith "assume call expecting proposition argument!"
                    end
               | _ -> i :: insL
             ) [] instrList in
         s.skind <- (Instr changeIns);
         s
  
      | _ -> s
    in
    ChangeDoChildrenPost(s, action)
 end

class assertVisitor  = object(slef)
  inherit nopCilVisitor
  val mutable vassert = "assert"
  val mutable nonlinearExpr= mkString "nonlinear"
  method vinst (i:instr) =
    match i with
    | Call (_, fvname, args, loc) ->
       let fvi = e2v fvname in
       if fvi.vname <> vassert then SkipChildren else begin
           match args with
           | [pros] ->
              if isnonlinear pros
              then
                (* ignore (printf("ToDo, another visitor pass for assert call? ")); *)
                SkipChildren
              else  SkipChildren
           | _ -> failwith "assume call expecting proposition argument!"
         end
    | _ -> SkipChildren    
       
end

 (* class vtraceVisitor (vexprs : (varinfo * exp) list) (flocals: varinfo list)= object(self) *)

class vtraceVisitor (ast: file) (flocals: varinfo list)= object(self)
  inherit nopCilVisitor
  val mutable vassume = "assert"
  method vinst (i : instr) =
    match i with
    | Set(_, expr, loc) ->
       if isnonlinear expr
       then
         let traceName = "vtrace"^(string_of_int (!currentLoc).line) in
         let vtraceFunc = emptyFunction traceName in
         setFormals vtraceFunc flocals;
         ast.globals <- GFun(vtraceFunc, loc) :: ast.globals;
         let localFormals = L.map v2e flocals in
         let vtraceCall = mkCall traceName localFormals in
         let injectVis = [i; vtraceCall] in
         ChangeTo injectVis
       else SkipChildren
     | _ -> SkipChildren
end

 
let processFunction ((ast, mf, gvars): file * string * varinfo list) (fd : fundec) (loc : location) : unit =
  if fd.svar.vname <> mf then () else begin

      let nonlinear = Hashtbl.create 10 in
      let nonVis = new nonlinearVisitor nonlinear in
      ignore(visitCilFunction nonVis fd);
      Hashtbl.iter (fun x y ->
          let sExpr = stringOfExp y in
          Printf.printf "nonlinear location at line : %s, %s \n" (string_of_int x.line) sExpr;
        ) nonlinear;

      let vStmts = new stmtVisitor fd in
      ignore(visitCilFunction vStmts fd);

      let vis = new vtraceVisitor ast (gvars @ fd.slocals) in
      ignore(visitCilFunction vis fd);
        
    end

(* let varInject (funvars : string * exp list) (f : file) : unit =
 * (\* let varInject (funvars : string * string list) (f : file) : unit = *\)
 *   funvars |> processFunction |> onlyFunctions |> iterGlobals f *)

let nonlinearTrans (mf : file * string * varinfo list) (f : file) : unit =
  mf |> processFunction |> onlyFunctions |> iterGlobals f

