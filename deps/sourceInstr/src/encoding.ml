open Cil
open Printf
open Int64
open Ctl
open Eutils
module F = Frontc
module E = Errormsg
module CM = Common
module L = List
module S = String

let filename = ref ""
let encodeTrans = ref false
let invars = ref ""
let outFile = ref ""

let parseOneFile (fname: string) : file =
  let cabs, cil = F.parse_with_cabs fname () in
  Rmtmps.removeUnusedTemps cil;
  cil

let outputFile (f : file) : unit =
  if !outFile <> "" then
    try
      let c = open_out !outFile in

      print_CIL_Input := false;
      Stats.time "printCIL"
        (dumpFile defaultCilPrinter c !outFile) f;
      close_out c
    with _ ->
      E.s (E.error "Couldn't open file %s" !outFile)


let usage = "usage: " ^ Sys.argv.(0) ^ " [-i] filename"

let speclist = [
    ("-i", Arg.Set encodeTrans, ": encoding transform for LTL.");
    ("-inv", Arg.Set_string invars, ": invariants to assert.");
    
]

let parse_cmdline =
  begin
    Arg.parse speclist (fun x -> filename := x) usage;
    try
      if !filename = "" then
        raise (Arg.Bad ("missing argument: no input file name given"))
    with
    | Arg.Bad msg ->
       (eprintf "%s: %s\n" Sys.argv.(0) msg; eprintf "%s\n" usage; exit 1)
  end

let main () =
  initCIL();
  Cil.lineDirectiveStyle:= None; (*reduce code, remove all junk stuff*)
  Cprint.printLn := false; (*don't print line #*)
  (* for Cil to retain &&, ||, ?: instead of transforming them to If stmts *)
  Cil.useLogicalOperators := true;

  let () = parse_cmdline in
  let src = !filename in
  let invar_trans = !invars in
  outFile := (src ^ ".encode.c");
  let ast = parseOneFile src in

  let mainQ = "main" in
  let vtrace = "vtrace" in
  let vassume = "vassume" in

  (* let includes = ["stdio.h"; "stdlib.h"; "assert.h"; "math.h"] in
   * let includes = L.map(fun x -> "#include \"" ^ x ^ "\"") includes in
   * let adds = S.concat "\n" includes in
   * ast.globals <- (GText adds):: ast.globals; *)
  let gvs = getGlobalVars (ast.globals) [] in

  let () =
    (* (match ctlProperty with
     * | Atomic (aexp) ->
     *    let exprs = [aexp] in
     *    LocalVar.varInject(mainQ, exprs) ast
     * | _ -> ()
     * ) in *)
    (Dltl.nonlinearTrans (ast, mainQ, gvs) ast;
     ignore ()
    ) in
  outputFile ast
 ;;

begin
  try
    main ()
  with
  | F.CabsOnly -> ()
  | E.Error -> ()
end;
exit (if !E.hadErrors then 1 else 0)
