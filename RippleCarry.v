From Coq Require Import List Arith Bool Nat.
Import ListNotations.
Local Open Scope nat_scope.

Local Open Scope list_scope.
Require Import DisQ.BasicUtility.   (* var := nat *)
Require Import DisQ.DisQSyntax.     (* exp, process, memb, config, ... *)
Require Import DisQ.AUTO.

Definition cfg1 : config := [Memb 0 []; Memb 1 []].
Definition L : locus := ([] : locus).

Definition MAJ a b c : exp := (Seq ((CU c (Num 0) (X b (Num 0)))) (Seq (CU c (Num 0) (X a (Num 0))) (CU a (Num 0) (CU b (Num 0) (X b (Num 0)))))).
Definition UMA a b c : exp := (Seq (CU a (Num 0) (CU b (Num 0) (X c (Num 0)))) (Seq (CU c (Num 0) (X a (Num 0))) (CU a (Num 0) (X b (Num 0))))).

Fixpoint MAJseq' n t y x : exp :=
  match n with
  | 0 => MAJ (x (Num 0)) (y (Num 0)) (t (Num 0))
  | S m => Seq (MAJseq' m t y x) (MAJ (x (Num m)) (y (Num n)) (x (Num n)))
  end.
  Definition MAJseq n t y x := MAJseq' (n - 1) t y x.

Fixpoint UMAseq' n t y x : exp :=
  match n with
  | 0 => UMA x (y (Num 0)) (t (Num 0))
  | S m => Seq (UMA (t (Num m)) (y (Num n)) (t (Num n))) (UMAseq' m t y x)
  end.
Definition UMAseq n t y x := UMAseq' (n - 1) t y x.


Definition n : var := 0.
Definition t : var := 1.
Definition y : var := 2.
Definition x : var := 3.

Definition new v i : cexp := CNew v i.


Definition ops : op_list := [
  OpAP (CNew t n);


].

Definition dist : distributed_prog :=
  auto_disq_alg1_paper 2 2 ops cfg1.
Compute dist.


  OpAP (CNew y n);
  OpAP (CNew x 2);

  OpAP (MAJseq n t y x);
  OpAP (CAppU CU t (Num n-1) (X x (Num 1)));
  OpAP (UMAseq n t y x);