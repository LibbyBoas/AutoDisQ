
From Coq Require Import Extraction.
From Coq Require Import ExtrOcamlBasic ExtrOcamlString ExtrOcamlNatInt.

(* Import the whole executable pipeline *)
Require Import BasicUtility.
Require Import DisQSyntax.

Extraction Language OCaml.

(* Avoid re-extracting Coq stdlib *)
Extraction Blacklist String List Nat Bool.

Extraction Language OCaml.
Set Extraction Optimize.
Set Extraction AutoInline.

Require Import AUTO.
Check my_vars_of_exp.
Set Extraction AutoInline.
Extraction Inline
  my_vars_of_exp my_place_operation
  my_insert_teleport_sends my_insert_teleport_receives
  my_empty_config my_gen_seq my_gen_mem
  my_fit my_order_by_seq.


Extraction "AAautodisq_1.ml"
  AUTO.auto_disq
  AUTO.auto_disq_search
 AUTO.gen_prog
AUTO.gen_prog_core
AUTO.parallelize_in_membrane.




(*
(* SINGLE FILE extraction *)
Extraction "autodisq_4.ml"
  auto_disq
  auto_disq_search
  gen_prog
  gen_prog_core
  parallelize_in_membrane.




From Coq Require Import Extraction.
From Coq Require Import ExtrOcamlBasic ExtrOcamlString ExtrOcamlNatInt.

Extraction Language OCaml.
Extraction Blacklist String List Nat Bool.

Extraction Language OCaml.
Set Extraction Optimize.
Set Extraction AutoInline.

Require Import AUTO.
Cd "extracted".
Extraction "autodisq.ml"
  AUTO.auto_disq
  AUTO.auto_disq_search
 AUTO.gen_prog
AUTO.gen_prog_core
AUTO.parallelize_in_membrane.
*)
