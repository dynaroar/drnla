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

let rec isnonlinear (expr : exp) : bool =
  match expr with
  | BinOp (opc, opr1, opr2, _) ->
     (match opc with
      | Mult | Div | Mod | Shiftlt | Shiftrt | BAnd | BXor | BOr | LAnd
      | LOr | PlusPI | IndexPI | MinusPI | MinusPP -> true         
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


 

let processFunction ((tf, exprs) : string * exp list) (fd : fundec) (loc : location) : unit =
  if fd.svar.vname <> tf then () else begin
      (* let varInfos = L.map (fun s -> makeLocalVar fd s (TInt (IInt, []))) tvs in  (\* empty attribute for locals injected *\)
       * let vis = new assignAddVisitor varInfos in
       *     ignore(visitCilFunction vis fd) *)
      let varInfos = mkVis fd exprs in
      let vis = new assignAtomicVisitor varInfos fd.slocals in
      ignore(visitCilFunction vis fd)
    end

let varInject (funvars : string * exp list) (f : file) : unit =
(* let varInject (funvars : string * string list) (f : file) : unit = *)
  funvars |> processFunction |> onlyFunctions |> iterGlobals f
