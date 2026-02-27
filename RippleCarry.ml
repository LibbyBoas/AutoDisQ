open Autodisq_extract

(* cfg1 : config := [Memb 0 []; Memb 1 []]. *)
let cfg1 : config =
  [Memb (0, []); Memb (1, [])]

(* L : locus := [] *)
let l : locus = []

(* MAJ definition *)
let maj a b c =
  Seq (
    CU (c, Num 0, X (b, Num 0)),
    Seq (
      CU (c, Num 0, X (a, Num 0)),
      CU (a, Num 0, CU (b, Num 0, X (b, Num 0)))
    )
  )

(* UMA definition *)
let uma a b c =
  Seq (
    CU (a, Num 0, CU (b, Num 0, X (c, Num 0))),
    Seq (
      CU (c, Num 0, X (a, Num 0)),
      CU (a, Num 0, X (b, Num 0))
    )
  )

(* MAJseq' *)
let rec majseq' n t y x =
  match n with
  | 0 ->
      maj (x (Num 0)) (y (Num 0)) (t (Num 0))
  | n ->
      let m = n - 1 in
      Seq (
        majseq' m t y x,
        maj (x (Num m)) (y (Num n)) (x (Num n))
      )

let majseq n t y x =
  majseq' (n - 1) t y x

(* UMAseq' *)
let rec umaseq' n t y x =
  match n with
  | 0 ->
      uma x (y (Num 0)) (t (Num 0))
  | n ->
      let m = n - 1 in
      Seq (
        uma (t (Num m)) (y (Num n)) (t (Num n)),
        umaseq' m t y x
      )

let umaseq n t y x =
  umaseq' (n - 1) t y x

(* Variables *)
let n : var = 0
let t : var = 1
let y : var = 2
let x : var = 3

(* ops *)
let ops : op_list =
  [
    OpAP (CNew (t, n));
    OpAP (CNew (y, n));
    OpAP (CNew (x, 2));

    OpAP (CAppU (L, (majseq n t y x)));
    OpAP (CAppU (L, (umaseq n t y x)));
  ]

(* distributed program *)
let dist : distributed_prog =
  auto_disq_alg1_paper 2 2 ops cfg1

(* Equivalent of Compute dist *)
let () =
  print_endline "Program generated.";
  (* If there's a printer function for distributed_prog,
     call it here *)