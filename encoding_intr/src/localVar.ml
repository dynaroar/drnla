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
      ((makeLocalVar fd ("_atomic"^(string_of_int i)) (TInt (IInt, []))), expr)
    ) exprs
     
 
(* class assignAddVisitor (vinfos : varinfo list) = object(self) *)
class assignAtomicVisitor (vexprs : (varinfo * exp) list) = object(self)
  inherit nopCilVisitor 
  
  method vinst (i : instr) = 
    match i with
    | Set(_, _, loc) | Call(_, _, _, loc) ->
       let inject = L.map (fun (vi, exp) -> Set((Var vi, NoOffset), exp, loc)) vexprs in
       let injectVis = i::inject in
       ChangeTo injectVis
    | _ -> SkipChildren 

end
 
                                      

let processFunction ((tf, exprs) : string * exp list) (fd : fundec) (loc : location) : unit =
  if fd.svar.vname <> tf then () else begin
      (* let varInfos = L.map (fun s -> makeLocalVar fd s (TInt (IInt, []))) tvs in  (\* empty attribute for locals injected *\)
       * let vis = new assignAddVisitor varInfos in
       *     ignore(visitCilFunction vis fd) *)
      let varInfos = mkVis fd exprs in
      let vis = new assignAtomicVisitor varInfos in
      ignore(visitCilFunction vis fd)
    end

let varInject (funvars : string * exp list) (f : file) : unit =
(* let varInject (funvars : string * string list) (f : file) : unit = *)
  funvars |> processFunction |> onlyFunctions |> iterGlobals f


