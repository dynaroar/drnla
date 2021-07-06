open Cil
open Printf
module F = Frontc
module C = Cil
module E = Errormsg
module CM = Common
         
let filename = ref ""
let encodeTrans = ref false

let outFile = ref ""
          
let parseOneFile (fname: string) : C.file =
  let cabs, cil = F.parse_with_cabs fname () in
  Rmtmps.removeUnusedTemps cil;
  cil

let outputFile (f : C.file) : unit =
  if !outFile <> "" then
    try
      let c = open_out !outFile in
      
      C.print_CIL_Input := false;
      Stats.time "printCIL" 
        (C.dumpFile (C.defaultCilPrinter) c !outFile) f;
      close_out c
    with _ ->
      E.s (E.error "Couldn't open file %s" !outFile)

          
let usage = "usage: " ^ Sys.argv.(0) ^ " [-i] filename"

let speclist = [
  ("-i", Arg.Set encodeTrans, ": encoding transform for CTL*");
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
  
  C.print_CIL_Input := true;
  C.insertImplicitCasts := false;
  C.lineLength := 100000;
  C.warnTruncate := false;
  E.colorFlag := true;
  Cabs2cil.doCollapseCallCast := true;

  let () = parse_cmdline in
  let src = !filename in
  outFile := (src ^ ".encode.c");
  let ast = parseOneFile src in

  (* TODO  we might want to parse CTL* property here, then extract the atomic proposition *)
  (* let () =  LocalVar.varInject("mainQ",["atomX"; "atomY"]) ast in *)
  let () =  LocalVar.varInject("mainQ",["atomX"; "atomY"]) ast in
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
