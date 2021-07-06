open Cil
open Eutils
open Int64
module E = Errormsg
module L = List

let mkAssign (vi: varinfo) : exp =
   BinOp (PlusA, Lval (Var vi, NoOffset), kinteger64 IInt (of_int 2), TInt (IInt, []))
  
     
 
class assignAddVisitor (vinfos : varinfo list) = object(self)
  inherit nopCilVisitor 
  
  method vinst (i : instr) = 
    match i with
    | Set(_, _, loc) | Call(_, _, _, loc) ->
       let inject = L.map (fun vi -> Set((Var vi, NoOffset), mkAssign vi, loc) ) vinfos in
       let injectVis = i::inject in
       ChangeTo injectVis
    | _ -> SkipChildren 

end
 
                                      

let processFunction ((tf, tvs) : string * string list) (fd : fundec) (loc : location) : unit =
  if fd.svar.vname <> tf then () else begin
      let varInfos = L.map (fun s -> makeLocalVar fd s (TInt (IInt, []))) tvs in  (* empty attribute for locals injected *)
      let vis = new assignAddVisitor varInfos in
          ignore(visitCilFunction vis fd)
    end


let varInject (funvars : string * string list) (f : file) : unit =
  funvars |> processFunction |> onlyFunctions |> iterGlobals f


