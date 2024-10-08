Require Import utils.VSTALib.

Require Import cprogs.list.program.
Require Import cprogs.list.definitions.
Require Import cprogs.list.annotation.
Require cprogs.list.reverse.path1.

Module SH_Proof <: STRAIGHTLINE_HOARE_TRIPLE_PROOF.

Include cprogs.list.reverse.path1.
  
Theorem proof: functional_correctness_statement.
Proof.
  cbv delta [functional_correctness_statement].
  intros.
  Intros l1 l2 w v.
  forward. list_intros a l2b t.
  do 4 forward. Exists (a :: l1) l2b v t.
  entailer!.
  - simpl. rewrite <- app_assoc.
    reflexivity.
  - unfold listrep at 2; fold listrep.
    Exists w. entailer!.
Qed.

End SH_Proof.
