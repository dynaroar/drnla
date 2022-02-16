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


(* class loopVisitor tmpVarHash = object(self) *)
class loopVisitor fd = object(self)
  inherit nopCilVisitor
  val mutable nonlinearExpr = mkString "nonliear"
  method vstmt (s: stmt) =
    let action s =
      match s.skind with
      (* | Loop (bk, loc, stmt1, stmt2) ->
       *    
       *   let stmtsBk = bk.bstmts in
       *   let loopIf = headList stmtsBk in
       *   (match loopIf.skind with
       *    | If (expr, bk1, bk2, loc) ->
       *       if isnonlinear expr
       *       then
       *         let tmpVarInfo = Hashtbl.find tmpVarHash loc in
       *         printf "while loop nonlinear condition, %s.\n" (stringOfExp expr);
       *         nonlinearExpr <- expr;            
       *         let tail = tailList stmtsBk in
       *         let ifTransKind = If (v2e tmpVarInfo, bk1, bk2, loc) in
       *         loopIf.skind <- ifTransKind;
       *         bk.bstmts <- (loopIf :: tail);
       *         let nonStmt = i2s (Set(var tmpVarInfo, nonlinearExpr, loc)) in
       *         let nb = mkBlock [nonStmt; mkStmt s.skind] in
       *         s.skind <- Block nb;
       *         s
       *       else s
       *    | _ -> s
       *   ) *)
      | If (expr, bk1, bk2, loc) ->
         if isnonlinear expr
         then
           (* let tmpVarInfo = Hashtbl.find tmpVarHash loc in *)
           let tmpVarInfo = makeLocalVar fd ("tmpVar"^(string_of_int loc.line)) (TInt (IInt, [])) in
           nonlinearExpr <- expr;
           printf "if nonlinear condition, %s.\n" (stringOfExp expr);
           let nonStmt = i2s (Set(var tmpVarInfo, nonlinearExpr, loc)) in
           let ifTransKind = If (v2e tmpVarInfo, bk1, bk2, loc) in
           s.skind <- ifTransKind;
           let nb = mkBlock [nonStmt; mkStmt s.skind] in
           s.skind <- Block nb;
           s    
         else s
      (* | Instr instrList ->
       *    let changeIns =
       *      List.fold_left (fun insL i ->
       *          match i with
       *          | Set (lv, expr, loc) ->
       *             if isnonlinear expr
       *             then
       *               let tmpVarInfo = Hashtbl.find tmpVarHash loc in
       *               nonlinearExpr <- expr;
       *               printf "set instruction nonlinear, %s.\n" (stringOfExp expr);
       *               let nonInstr = Set(var tmpVarInfo, nonlinearExpr, loc) in
       *               [nonInstr; (Set (lv, v2e tmpVarInfo, loc))] @ insL
       *             else
       *               i :: insL
       *           | _ -> i :: insL
       *        ) [] instrList in
       *    s.skind <- (Instr changeIns);
       *    s *)
  
      | _ -> s
    in
    ChangeDoChildrenPost(s, action)
    (* s <- action s; *)

    (* DoChildren *)
    (* ChangeTo (action s) *)
       
end

 (* class vtraceVisitor (vexprs : (varinfo * exp) list) (flocals: varinfo list)= object(self) *)

class vtraceVisitor (flocals: varinfo list)= object(self)
  inherit nopCilVisitor
  method vinst (i : instr) =
    match i with
    | Set(_, expr, loc) ->
       if isnonlinear expr
       then
         let localFormals = L.map v2e flocals in
         let traceName = "vtrace"^(string_of_int (!currentLoc).line) in
         let vtraceCall = mkCall traceName localFormals in
         let injectVis = [i; vtraceCall] in
         ChangeTo injectVis
       else SkipChildren
    | _ -> SkipChildren
end


(* let processFunction ((tf, exprs) : string * exp list) (fd : fundec) (loc : location) : unit = *)

let processFunction ((mf, gvars): string * varinfo list) (fd : fundec) (loc : location) : unit =
  if fd.svar.vname <> mf then () else begin

      let nonlinear = Hashtbl.create 10 in
      let nonVis = new nonlinearVisitor nonlinear in
      ignore(visitCilFunction nonVis fd);
 
      (* let nonTmpVars = Hashtbl.fold (fun key _ tmpVars ->
       *                      (Hashtbl.add tmpVars key (makeLocalVar fd ("tmpVar"^(string_of_int key.line)) (TInt (IInt, []))));
       *                      tmpVars
       *                    ) nonlinear (Hashtbl.create 10) in *)
      (* let vStmts = new loopVisitor nonTmpVars in *)
      let vStmts = new loopVisitor fd in
      ignore(visitCilFunction vStmts fd);

      
      let vis = new vtraceVisitor (gvars @ fd.slocals) in
      ignore(visitCilFunction vis fd);
      
      Hashtbl.iter (fun x y ->
          let sExpr = stringOfExp y in
          Printf.printf "nonlinear location at line : %s, %s \n" (string_of_int x.line) sExpr;
        ) nonlinear;
        (* Hashtbl.iter (fun _ y -> Printf.printf "tmp var name: %s\n" y.vname) nonTmpVars *)
      
    end

(* let varInject (funvars : string * exp list) (f : file) : unit =
 * (\* let varInject (funvars : string * string list) (f : file) : unit = *\)
 *   funvars |> processFunction |> onlyFunctions |> iterGlobals f *)

let nonlinearTrans (mf : string * varinfo list) (f : file) : unit =
  mf |> processFunction |> onlyFunctions |> iterGlobals f
