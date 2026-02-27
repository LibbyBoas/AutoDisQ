From Coq Require Import List Arith Bool Nat.
Import ListNotations.
Local Open Scope nat_scope.

Local Open Scope list_scope.
Require Import DisQ.BasicUtility.   (* var := nat *)
Require Import DisQ.DisQSyntax.     (* exp, process, memb, config, ... *)
Require Import DisQ.AUTO.

Definition cfg1 : config := [Memb 0 []; Memb 1 []].
Definition L : locus := ([] : locus).

Definition MAJ a b c : op_list := [OpAP (CAppU [b[0]] (CU c (Num 0) (X b (Num 0)))); OpAP (CAppU [a[0]] (CU c (Num 0) (X a (Num 0)))); OpAP (CAppU [c[0]](CU a (Num 0) (CU b (Num 0) (X c (Num 0)))))].
Definition UMA a b c : op_list := [OpAP (CAppU [c[0]] (CU a (Num 0) (CU b (Num 0)) (X c (Num 0)))); OpAP (CAppU [a[0]] (CU c (Num 0) (X a (Num 0)))); OpAP (CAppU [b[0]] (CU a (Num 0) (X b (Num 0))))].

Fixpoint MAJseq' n t y x : op_list :=
  match n with
  | 0 => MAJ (x (Num 0)) (y (Num 0)) (t (Num 0))
  | S m => (MAJseq' m t y x) ++ (MAJ (x (Num m)) (y (Num n)) (x (Num n)))
  end.
  Definition MAJseq n t y x := MAJseq' (n - 1) t y x.

Fixpoint UMAseq' n t y x : op_list :=
  match n with
  | 0 => UMA x (y (Num 0)) (t (Num 0))
  | S m => (UMA (t (Num m)) (y (Num n)) (t (Num n))) ++ (UMAseq' m t y x)
  end.
Definition UMAseq n t y x := UMAseq' (n - 1) t y x.


Definition n : var := 2.

Definition rippleCarrySeq : op_list := [OpAP (CNew t n); OpAP (CNew y n); OpAP (CNew x 2);] 
  ++ (MAJseq n t y x) ++ (UMAseq n t y x);.

Definition dist : distributed_prog :=
  auto_disq_alg1_paper 2 2 ops cfg1.
Compute dist.


