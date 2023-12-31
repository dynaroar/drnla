open Cil
open Pretty
open Int64
module E = Errormsg
module S = Str
module L = List

module SM = Map.Make(struct
  type t = string
  let compare = Pervasives.compare
end)


let i2s (i : instr) : stmt = mkStmt(Instr [i])
let var (v: varinfo): lval = (Var v, NoOffset)
let v2e (v : varinfo) : exp = Lval(var v)
let e2v (e: exp) : varinfo =
  match e with
  | Lval (Var vi, _) -> vi
  | _ -> failwith "expecting a variable expression!"
 
let (|>) (a : 'a) (f : 'a -> 'b) : 'b = f a

(* fucntions for nonlinear expression process *)
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

let mkAtomic (vi: varinfo) : exp =
   BinOp (Eq, Lval (Var vi, NoOffset), kinteger64 IInt (of_int 0), TInt (IInt, []))
 
let mkVis (fd: fundec) (exprs: exp list): (varinfo * exp) list =
  L.mapi (fun i expr ->
      ((makeLocalVar fd ("atomic"^(string_of_int i)) (TInt (IInt, []))), expr)
(* not adding to funciton's slocals. *)
      (* ((makeLocalVar fd ~insert:false ("atomic"^(string_of_int i)) (TInt (IInt, []))), expr) *)
    ) exprs

let mkCall ?(ftype=TVoid []) ?(av=None) (fname:string) args : instr =
  let mkVi ?(ftype=TVoid []) fname: varinfo = makeVarinfo true fname ftype in
  (* let mkVi ?(ftype=TVoid []) fname: varinfo = findOrCreateFunc ast fname ftype in *)
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

let nonlinearInstr nonhash i =
  match i with
  | Set (lv, expr, loc) ->
     if isnonlinear expr
     then (Hashtbl.add nonhash loc expr; nonhash)
     else nonhash
  | _ -> nonhash
let isNonlinearIns i =
  match i with
  | Set (lv, expr, loc) ->
     if isnonlinear expr
     then true
     else false
  | _ -> false


  

let fst3 (a,_,_) = a
let snd3 (_,b,_) = b
let thd3 (_,_,c) = c

let fst23 (f,s,_) = (f,s)
let snd23 (_,s,t) = (s,t)

let fst24 (f,s,_,_) = (f,s)

let tuplemap (f : 'a -> 'b) ((a,b) : ('a * 'a)) : ('b * 'b) = (f a, f b)

let triplemap (f : 'a -> 'b) ((a,b,c) : ('a * 'a * 'a)) : ('b * 'b * 'b) =
  (f a, f b, f c)

let forceOption (ao : 'a option) : 'a =
  match ao with
  | Some a -> a
  | None -> raise(Failure "forceOption")

let list_of_hash (sih : ('a, 'b) Hashtbl.t) : ('a * 'b) list =
	Hashtbl.fold (fun a b l -> (a,b) :: l) sih []

let list_init (len : int) (f : int -> 'a) : 'a list =
	let rec helper l f r =
		if l < 0 then r
		else helper (l - 1) f ((f l) :: r)
	in
	helper (len - 1) f []

let split ?(re : string = "[ \t]+") (line : string) : string list =
  S.split (S.regexp re) line


let onlyFunctions (fn : fundec -> location -> unit) (g : global) : unit = 
  match g with
  | GFun(f, loc) -> fn f loc
  | _ -> ()

let function_elements (fe : exp) : typ * (string * typ * attributes) list =
  match typeOf fe with
  | TFun(rt, Some stal, _, _) -> rt, stal
  | TFun(rt, None,      _, _) -> rt, []
  | _ -> E.s(E.bug "Expected function expression")

let fieldinfo_of_name (t: typ) (fn: string) : fieldinfo =
	match unrollType t with
	| TComp(ci, _) -> begin
		try List.find (fun fi -> fi.fname = fn) ci.cfields
		with Not_found ->
			E.s (E.error "%a: Field %s not in comp %s"
				d_loc (!currentLoc) fn ci.cname)
	end
	| _ ->
		E.s (E.error "%a: Base type not a comp: %a"
			d_loc (!currentLoc) d_type t)

let force_block (s : stmt) : block =
  match s.skind with
  | Block b -> b
  | _ -> E.s(E.bug "Expected block")

let list_equal (eq : 'a -> 'a -> bool) (l1 : 'a list) (l2 : 'a list) : bool =
  let rec helper b l1 l2 =
    if not b then false else
    match l1, l2 with
    | e1 :: rst1, e2 :: rst2 ->
      helper (eq e1 e2) rst1 rst2
    | [], [] -> true
    | _, _ -> false
  in
  helper true l1 l2

let list_take (len : int) (l : 'a list) : 'a list =
  let rec helper n l res =
    match l with
    | [] -> List.rev res
    | _ :: _ when n = 0 -> List.rev res
    | x :: rst -> helper (n - 1) rst (x :: res)
  in
  helper len l []

let list_union (l1 : 'a list) (l2 : 'a list) : 'a list =
  List.fold_left (fun l a2 ->
    if not(List.mem a2 l) then a2 :: l else l
  ) l1 l2

let sm_find_all (sm : 'a SM.t) (sl : string list) : 'a list =
  List.map (fun s -> SM.find s sm) sl

let sargs (f : 'b -> 'a -> 'c) (x : 'a) (y : 'b) : 'c = f y x

let list_of_growarray (ga : 'a GrowArray.t) : 'a list =
  GrowArray.fold_right (fun x l -> x :: l) ga []

let array_of_growarray (ga : 'a GrowArray.t) : 'a array =
  Array.init (GrowArray.max_init_index ga + 1) (GrowArray.get ga)

let array_sort_result (c : 'a -> 'a -> int) (a : 'a array) : 'a array =
  Array.sort c a;
  a

let array_filter (f : 'a -> bool) (a : 'a array) : 'a array =
  a |> Array.to_list |> List.filter f |> Array.of_list

let array_bin_search (c : 'a -> 'a -> int) (x : 'a) (a : 'a array) : int list =
  if Array.length a = 0 then raise(Invalid_argument "array_bin_search") else
  let rec helper (lo : int) (hi : int) : int list =
    if lo >= hi then begin
      match c a.(hi) x with
      | 0            -> [hi]
      | n when n > 0 -> [max 0 hi-1; hi]
      | _            -> [hi        ; min (hi+1) (Array.length a - 1)]
    end else begin
      let mid = (lo + hi) / 2 in
      match c a.(mid) x with
      | 0            -> [mid]
      | n when n > 0 -> helper lo (mid - 1)
      | _            -> helper (mid + 1) hi
    end
  in
  helper 0 (Array.length a - 1)

type comment = Cabs.cabsloc * string * bool

let cabsloc_of_cilloc (l : location) : Cabs.cabsloc =
  {Cabs.lineno = l.line; Cabs.filename = l.file; Cabs.byteno = l.byte; Cabs.ident = 0;}

let cilloc_of_cabsloc (l :Cabs.cabsloc) : location =
  {line = l.Cabs.lineno; file = l.Cabs.filename; byte = l.Cabs.byteno;}

let comment_of_cilloc (l : location) : comment =
  (cabsloc_of_cilloc l, "", false)

let cabsloc_compare (l1 : Cabs.cabsloc) (l2 : Cabs.cabsloc) : int =
  compareLoc (cilloc_of_cabsloc l1) (cilloc_of_cabsloc l2)

let comment_compare (c1 : comment) (c2 : comment) : int =
  cabsloc_compare (fst3 c1) (fst3 c2)

let rec findType (gl : global list) (typname : string) : typ =
  match gl with
  | [] -> E.s (E.error "Type not found: %s" typname)
  | GType(ti,_) :: _        when ti.tname = typname -> TNamed(ti,[])
  | GCompTag(ci,_) :: _     when ci.cname = typname -> TComp(ci,[])
  | GCompTagDecl(ci,_) :: _ when ci.cname = typname -> TComp(ci,[])
  | GEnumTag(ei,_) :: _     when ei.ename = typname -> TEnum(ei,[])
  | GEnumTagDecl(ei,_) :: _ when ei.ename = typname -> TEnum(ei,[])
  | _ :: rst -> findType rst typname

let rec findFunction (gl : global list) (fname : string) : fundec =
    match gl with
    | [] -> raise(Failure "Function not found")
    | GFun(fd,_) :: _ when fd.svar.vname = fname -> fd
    | _ :: rst -> findFunction rst fname

let rec findCompinfo (gl : global list) (ciname : string) : compinfo =
	match gl with
	| [] -> raise(Failure "Compinfo not found")
	| GCompTag(ci, _) :: _ when ci.cname = ciname -> ci
	| GCompTagDecl(ci, _) :: _ when ci.cname = ciname -> ci
	| _ :: rst -> findCompinfo rst ciname

let rec findGlobalVar (gl : global list) (varname : string) : varinfo =
  match gl with
  | [] -> E.s (E.error "Global not found: %s" varname)
  | GVarDecl(vi, _) :: _ when vi.vname = varname -> vi
  | GVar(vi, _, _) :: _ when vi.vname = varname -> vi
  | _ :: rst -> findGlobalVar rst varname
let isGlobalVar (g : global) : bool =
  match g with
  | GVar(vi, _, _)  | GVarDecl(vi, _) ->  true
  | _ -> false
let rec getGlobalVars (gl : global list) (base: varinfo list): varinfo list =
  match gl with
  | [] -> base
  | GVarDecl(vi, _) :: rst -> getGlobalVars rst (vi :: base)
  | GVar(vi, _, _) :: rst -> getGlobalVars rst (vi :: base)
  | _ :: rst -> getGlobalVars rst base


let mallocType (f : file) : typ =
  let size_t = findType f.globals "size_t" in
  TFun(voidPtrType, Some ["s",size_t,[]], false, [])

let iterCompound ~(implicit : bool)
                 ~(doinit : offset -> init -> typ -> unit -> unit)
                 ~(ct : typ) ~(initl : (offset * init) list)
                 : unit
  =
  foldLeftCompound ~implicit ~doinit ~ct ~initl ~acc:()

 
