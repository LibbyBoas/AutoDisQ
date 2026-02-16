From Coq Require Import Extraction.
From Coq Require Import ExtrOcamlBasic ExtrOcamlNatInt ExtrOcamlString.
From Coq Require Import List.
Extraction Language OCaml.
Require Import DisQ.BasicUtility.
Require Import DisQ.DisQSyntax.

Extraction Blacklist List String Bool.


Set Extraction AutoInline.
Set Extraction Optimize.
Unset Extraction KeepSingleton.

Require Import DisQ.AUTO.
Require Import DisQ.AUTO_Test.

Extraction
  "autodisq_extract.ml"
  auto_disq_alg1_paper
  gen_prog_alg2
  gen_prog_loop_alg2
  gen_prog_paper
  auto_parallelize_alg3
  gen_hp
  gen_mem_seed
  gen_seq_many
  fit
  order_by_seq
  insert_send_recv
  place_operation
  place_reloc
  diff_mem
  mem_up_smap
scc_partition_fuel
  scc_partition
  alg3_loop
 P_1 P_3 P_4 P_5 P_6.






















