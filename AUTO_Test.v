From Coq Require Import List Arith Bool Nat.
Import ListNotations.
Local Open Scope nat_scope.
Local Open Scope list_scope.

Require Import DisQ.BasicUtility.   (* var := nat *)
Require Import DisQ.DisQSyntax.     (* exp, process, memb, config, ... *)
Require Import DisQ.AUTO.



Definition cfg1 : config := [Memb 0 []; Memb 1 []].

Definition op1 : myOp := OpAP (CNew 0 1).
Definition op2 : myOp := OpAP (CMeas 0 ([] : locus)).
Definition R1  : op_list := [op1; op2].

Definition P1 : distributed_prog :=
  auto_disq_alg1_paper 2 2 R1 cfg1.

Compute P1.

Compute fit P1.

Definition cfg_test : config := [Memb 0 []; Memb 1 []].

Definition S_empty : Smap := [].

Definition T1 :=
  insert_send_recv cfg_test S_empty 1 0.

Compute T1.

Definition S_one : Smap := [(0, 0)].

Definition T2 :=
  insert_send_recv cfg_test S_one 1 0.

Compute T2.


Definition S_two : Smap := [(0,0); (1,0)].
Definition T3 := insert_send_recv cfg_test S_two 1 0.
Compute T3.
Definition memb_procs (m : memb) : list process :=
  match m with
  | Memb _ ps => ps
  | LockMemb _ _ ps => ps
  end.

Fixpoint flatten_config (cfg : config) : list process :=
  match cfg with
  | [] => []
  | m :: tl => memb_procs m ++ flatten_config tl
  end.

Compute flatten_config (fst T2).
Definition opAP1 : myOp := OpAP (CNew 0 1).

Definition moQ0 : var -> membrane_id := fun _ => 0.
Definition moO_to_1 : myOp -> membrane_id := fun _ => 1.

Definition TB :=
  gen_prog_loop_alg2 ([opAP1] : list myOp) moQ0 moO_to_1 empty_config 0.

Compute TB.
Compute flatten_config TB.

Definition cond0 : cbexp := CEq (BA 0) (Num 0).

Definition p_then : process := AP (CNew 0 1) PNil.
Definition p_else : process := PNil.

Definition opIF1 : myOp := OpIf cond0 p_then p_else.

Definition TC :=
  gen_prog_loop_alg2 ((opIF1 :: nil) : list myOp) moQ0 moO_to_1 empty_config 0.


Compute TC.
Compute flatten_config TC.

Definition opAP2 : myOp := OpAP (CMeas 0 ([] : locus)).
Definition seq2 : list myOp := [opAP1; opAP2].

Definition TD :=
  gen_prog_alg2 seq2 moQ0 moO_to_1.

Compute TD.
Compute flatten_config TD.
Compute diff_mem moQ0 (locus_myOp opAP1) 1.
Compute diff_mem (mem_up_smap moQ0 (diff_mem moQ0 (locus_myOp opAP1) 1) 1)
                (locus_myOp opAP2) 1.

(* ============================================================ *)
(* Tests for Algorithm 1                                         *)
(* ============================================================ *)

Definition cfgA : config := [Memb 0 []; Memb 1 []].

(* Simple: two ops share qubit 0 *)
Definition Aop1 : myOp := OpAP (CNew 0 1).
Definition Aop2 : myOp := OpAP (CMeas 0 ([] : locus)).
Definition AR1  : op_list := [Aop1; Aop2].

Definition AP1 : distributed_prog :=
  auto_disq_alg1_paper 2 2 AR1 cfgA.

Compute AP1.
Compute fit AP1.

Definition Aop3 : myOp := OpAP (CNew 1 1).
Definition Aop4 : myOp := OpDP (NewCh 7 1).
Definition AR2  : op_list := [Aop1; Aop3; Aop4; Aop2].

Definition AP2 : distributed_prog :=
  auto_disq_alg1_paper 3 3 AR2 cfgA.

Compute AP2.
Compute fit AP2.

(* ============================================================ *)
(* Tests for Algorithm 2                                         *)
(* ============================================================ *)

Definition seq0 : seq_relation := fun _ => 0.

Definition moO_all0 : op_mem_assign := fun _ => 0.
Definition moQ_all0 : qubit_mem_assign := fun _ => 0.

Definition P2A : distributed_prog :=
  gen_prog_paper seq0 moQ_all0 moO_all0 AR1.

Compute P2A.
Compute fit P2A.  

Definition moO_all1 : op_mem_assign := fun _ => 1.
Definition moQ_all0_again : qubit_mem_assign := fun _ => 0.

Definition P2B : distributed_prog :=
  gen_prog_paper seq0 moQ_all0_again moO_all1 AR1.

Compute P2B.
Compute fit P2B.  

Fixpoint flat_cfg (cfg : config) : list process :=
  match cfg with
  | [] => []
  | Memb _ ps :: tl => ps ++ flat_cfg tl
  | LockMemb _ _ ps :: tl => ps ++ flat_cfg tl
  end.

Compute flat_cfg P2A.
Compute flat_cfg P2B.




(* ============================================================ *)
(* Tests for Algorithm 3                                         *)
(* ============================================================ *)

Definition B1 : myOp := OpAP (CNew 0 1).
Definition B2 : myOp := OpAP (CMeas 0 ([] : locus)).
Definition B3 : myOp := OpAP (CNew 1 1).

Definition Bops : list myOp := [B1; B2; B3].

(* A custom hp that creates a cycle B1 <-> B2, and B2 -> B3 *)
Definition hpB : hb_relation :=
  fun a b =>
    orb
      (orb (andb (myOp_eqb a B1) (myOp_eqb b B2))
           (andb (myOp_eqb a B2) (myOp_eqb b B1)))
      (andb (myOp_eqb a B2) (myOp_eqb b B3)).

(* A seq that orders B1 then B2 then B3 *)
Definition seqB : seq_relation :=
  fun o =>
    if myOp_eqb o B1 then 0
    else if myOp_eqb o B2 then 1
    else 2.

Definition Rpar : list process :=
  auto_parallelize_alg3 myOp_eqb Bops hpB seqB.

Compute Rpar.


(* --------------------------------------------- *)
(* Example quantum program in your input format  *)
(* --------------------------------------------- *)

Definition q0 : var := 0.
Definition q1 : var := 1.

(* empty locus for “apply U on these qubits” — depends on your DisQSyntax meaning *)
Definition L : locus := ([] : locus).

(* exp programs (unitary-ish) *)
Definition eH_q0 : exp := H q0 (Num 0).
Definition eX_q1 : exp := X q1 (Num 0).

(* “Controlled-X on q1 controlled by q0”  *)
Definition eCX : exp := CU q0 (Num 0) eX_q1.

(* Wrap into cexp actions: CAppU locus exp *)
Definition appH_q0 : cexp := CAppU L eH_q0.
Definition appCX   : cexp := CAppU L eCX.

(* Allocate 1-qubit registers (your CNew takes x and n) *)
Definition new_q0 : cexp := CNew q0 1.
Definition new_q1 : cexp := CNew q1 1.

(* Measure q0 and q1 into classical x0 and x1 *)
Definition x0 : var := 10.
Definition x1 : var := 11.

Definition meas_q0 : cexp := CMeas x0 L.
Definition meas_q1 : cexp := CMeas x1 L.

(* Now the program as op_list *)
Definition Qprog : op_list :=
  [ OpAP new_q0;
    OpAP new_q1;
    OpAP appH_q0;
    OpAP appCX;
    OpAP meas_q0;
    OpAP meas_q1
  ].

Definition cfg2 : config := [Memb 0 []; Memb 1 []].
Definition Pbest : distributed_prog :=
  auto_disq_alg1_paper 3 3 Qprog cfg2.

Compute Pbest.
Compute fit Pbest.


Definition P_alg2 : distributed_prog :=
  gen_prog_paper seq0 moQ_all0 moO_all0 Qprog.

Compute P_alg2.
Compute fit P_alg2.

Definition moQ_start0 : qubit_mem_assign := fun _ => 0.


Definition P_reloc : distributed_prog :=
  gen_prog_paper seq0 moQ_start0 moO_all1 Qprog.

Compute P_reloc.
Compute fit P_reloc.


Definition P1_q : var := 0.
Definition P1_x : var := 10.

Definition P_1 : op_list :=
  [ OpAP (CNew P1_q 1);
    OpAP (CAppU L (H P1_q 0));
    OpAP (CMeas P1_x L)
  ].


(* Test harness *)


Definition moO0 : op_mem_assign := fun _ => 0.

Definition P_1_dist0 : distributed_prog :=
  gen_prog_paper seq0 moQ0 moO0 P_1.

Compute P_1_dist0.
Compute fit P_1_dist0.

Definition moO1 : op_mem_assign := fun _ => 1.

Definition P_1_dist1 : distributed_prog :=
  gen_prog_paper seq0 moQ0 moO1 P_1.

Compute P_1_dist1.
Compute fit P_1_dist1.

Definition P_2_q : var := 0.
Definition P_2_x : var := 10.

Definition P_2 : op_list :=
  [ OpAP (CNew P_2_q 1);
    OpAP (CAppU L (H P_2_q 0));
    OpAP (CAppU L (RZ 0 P_2_q 0));
    OpAP (CMeas P_2_x L)
  ].

Definition P_2_dist0 :=
  gen_prog_paper seq0 moQ0 moO0 P_2.

Compute P_2_dist0.
Compute fit P_2_dist0.

(* 6 membranes available *)
Definition cfg6 : config :=
  [ Memb 0 []; Memb 1 []; Memb 2 []; Memb 3 []; Memb 4 []; Memb 5 [] ].

(* initial location: all qubits start on membrane 0 *)


(* send all operations to a chosen membrane *)
Definition moO2 : op_mem_assign := fun _ => 2.
Definition moO3 : op_mem_assign := fun _ => 3.
Definition moO4 : op_mem_assign := fun _ => 4.
Definition moO5 : op_mem_assign := fun _ => 5.

(* Algorithm 2 placement tests for P_1 *)
Definition P_1_dist2 : distributed_prog :=
  gen_prog_paper seq0 moQ0 moO2 P_1.
Compute P_1_dist2.
Compute fit P_1_dist2.

Definition P_1_dist3 : distributed_prog :=
  gen_prog_paper seq0 moQ0 moO3 P_1.
Compute P_1_dist3.
Compute fit P_1_dist3.

Definition P_1_dist4 : distributed_prog :=
  gen_prog_paper seq0 moQ0 moO4 P_1.
Compute P_1_dist4.
Compute fit P_1_dist4.

Definition P_1_dist5 : distributed_prog :=
  gen_prog_paper seq0 moQ0 moO5 P_1.
Compute P_1_dist5.
Compute fit P_1_dist5.

Definition P_3_q0 : var := 0.
Definition P_3_q1 : var := 1.
Definition P_3_q2 : var := 2.

Definition P_3_x0 : var := 10.
Definition P_3_x1 : var := 11.
Definition P_3_x2 : var := 12.

(* CNOT-like: control P_3_q0, apply X on target *)
Definition CX_01 : exp := CU P_3_q0 0 (X P_3_q1 0).
Definition CX_02 : exp := CU P_3_q0 0 (X P_3_q2 0).

Definition P_3 : op_list :=
  [ OpAP (CNew P_3_q0 1);
    OpAP (CNew P_3_q1 1);
    OpAP (CNew P_3_q2 1);

    OpAP (CAppU L (H P_3_q0 0));
    OpAP (CAppU L CX_01);
    OpAP (CAppU L CX_02);

    OpAP (CMeas P_3_x0 L);
    OpAP (CMeas P_3_x1 L);
    OpAP (CMeas P_3_x2 L)
  ].


Definition P_3_dist0 : distributed_prog :=
  gen_prog_paper seq0 moQ0 moO0 P_3.

Compute P_3_dist0.
Compute fit P_3_dist0.


Definition P_3_dist1 : distributed_prog :=
  gen_prog_paper seq0 moQ0 moO1 P_3.

Compute P_3_dist1.
Compute fit P_3_dist1.

(* QFT *)

Definition P_4_q : var := 0.
Definition P_4_n : nat := 3.
Definition P_4_x : var := 10.

Definition P_4 : op_list :=
  [ OpAP (CNew P_4_q 1);
    OpAP (CAppU L (H P_4_q 0));
    OpAP (CAppU L (QFT P_4_q P_4_n));
    OpAP (CAppU L (RQFT P_4_q P_4_n));
    OpAP (CMeas P_4_x L)
  ].



Definition P_4_dist0 : distributed_prog :=
  gen_prog_paper seq0 moQ0 moO0 P_4.

Compute P_4_dist0.
Compute fit P_4_dist0.


Definition P_4_dist1 : distributed_prog :=
  gen_prog_paper seq0 moQ0 moO1 P_4.

Compute P_4_dist1.
Compute fit P_4_dist1.


Definition P_4_dist5 : distributed_prog :=
  gen_prog_paper seq0 moQ0 moO5 P_4.

Compute P_4_dist5.
Compute fit P_4_dist5.

(* ============================================================ *)
(* P_5 : 2-qubit Grover (one iteration)                          *)
(* ============================================================ *)

Definition P_5_q0 : var := 0.
Definition P_5_q1 : var := 1.
Definition P_5_x0 : var := 10.
Definition P_5_x1 : var := 11.

(* a symbolic “pi phase” parameter  *)
Definition theta_pi : nat := 1.

(* Controlled phase-like oracle: control q0, apply RZ on q1 *)
Definition ORACLE_01 : exp := CU P_5_q0 0 (RZ 0 P_5_q1 theta_pi).

(* Diffusion (in the usual circuit form): H,H; X,X; controlled-phase; X,X; H,H *)
Definition P_5 : op_list :=
  [ OpAP (CNew P_5_q0 1);
    OpAP (CNew P_5_q1 1);

    (* Prepare uniform superposition *)
    OpAP (CAppU L (H P_5_q0 0));
    OpAP (CAppU L (H P_5_q1 0));

    (* Oracle (phase flip on marked state, here approximated by ORACLE_01) *)
    OpAP (CAppU L ORACLE_01);

    (* Diffusion *)
    OpAP (CAppU L (H P_5_q0 0));
    OpAP (CAppU L (H P_5_q1 0));
    OpAP (CAppU L (X P_5_q0 0));
    OpAP (CAppU L (X P_5_q1 0));
    OpAP (CAppU L ORACLE_01);
    OpAP (CAppU L (X P_5_q0 0));
    OpAP (CAppU L (X P_5_q1 0));
    OpAP (CAppU L (H P_5_q0 0));
    OpAP (CAppU L (H P_5_q1 0));

    (* Measure *)
    OpAP (CMeas P_5_x0 L);
    OpAP (CMeas P_5_x1 L)
  ].


Definition P_5_dist0 := gen_prog_paper seq0 moQ0 moO0 P_5.
Compute P_5_dist0.
Compute fit P_5_dist0.

Definition P_5_dist5 := gen_prog_paper seq0 moQ0 moO5 P_5.
Compute P_5_dist5.
Compute fit P_5_dist5.


(* ============================================================ *)
(* P_6 : Quantum teleportation                                  *)
(* ============================================================ *)

Definition P_6_qs : var := 0.   (* source qubit to teleport *)
Definition P_6_qa : var := 1.   (* Alice half of EPR *)
Definition P_6_qb : var := 2.   (* Bob half of EPR (target) *)

Definition P_6_m1 : var := 10.  (* classical measurement bit from qs *)
Definition P_6_m2 : var := 11.  (* classical measurement bit from qa *)

(* Build the usual CNOTs  *)
Definition CNOT_a_b : exp := CU P_6_qa 0 (X P_6_qb 0).
Definition CNOT_s_a : exp := CU P_6_qs 0 (X P_6_qa 0).

(* “Z correction” approximated via RZ(pi) on qb *)
Definition Zcorr_qb : exp := RZ 0 P_6_qb theta_pi.
Definition Xcorr_qb : exp := X  P_6_qb 0.

(* Processes used in OpIf branches *)
Definition proc_Xcorr : process := AP (CAppU L Xcorr_qb) PNil.
Definition proc_Zcorr : process := AP (CAppU L Zcorr_qb) PNil.

Definition P_6 : op_list :=
  [ (* Allocate qubits *)
    OpAP (CNew P_6_qs 1);
    OpAP (CNew P_6_qa 1);
    OpAP (CNew P_6_qb 1);

    (* Prepare an example “unknown” state on qs *)
    OpAP (CAppU L (H P_6_qs 0));

    (* Create EPR pair between qa and qb *)
    OpAP (CAppU L (H P_6_qa 0));
    OpAP (CAppU L CNOT_a_b);

    (* Bell measurement on (qs, qa) *)
    OpAP (CAppU L CNOT_s_a);
    OpAP (CAppU L (H P_6_qs 0));

    OpAP (CMeas P_6_m1 L);
    OpAP (CMeas P_6_m2 L);

    OpIf (CEq (BA P_6_m2) (Num 1)) proc_Xcorr PNil;
    OpIf (CEq (BA P_6_m1) (Num 1)) proc_Zcorr PNil

  ].

Definition P_6_dist0 := gen_prog_paper seq0 moQ0 moO0 P_6.
Compute P_6_dist0.
Compute fit P_6_dist0.

Definition P_6_dist5 := gen_prog_paper seq0 moQ0 moO5 P_6.
Compute P_6_dist5.
Compute fit P_6_dist5.











