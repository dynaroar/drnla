open Cil

(*
   'A' stands for 'all paths'
   'E' stands for 'exists a path'
   Operators
   X: next
   F: future/eventually
   G: global/always
   U: until
   
*)

type ctl =
  | Atomic of exp (* atomic property *)
  | AX of ctl (* next *)
  | AF of ctl (* future/eventually *)
  | AG of ctl (* global *)
  | AU of (ctl * ctl) (* until *)
  | EX of ctl (* next *)
  | EF of ctl (* future/eventually *)
  | EG of ctl (* global *)
  | EU of (ctl * ctl) (* until *)
  | AND of (ctl * ctl) (* and *)
  | OR of (ctl * ctl) (* or *)
  | NOT of ctl (* not *)


             
