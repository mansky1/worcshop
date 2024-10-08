Require Import utils.VSTALib.

Require Import cprogs.list.program.
Require Import cprogs.list.definitions.
Require Import cprogs.list.annotation.
Require cprogs.list.append.path0.

Module SH_Proof <: STRAIGHTLINE_HOARE_TRIPLE_PROOF.

Include cprogs.list.append.path0.

Theorem proof: functional_correctness_statement.
Proof.
  cbv delta [functional_correctness_statement].
  intros.
  forward; list_intros a s1b z.
  do 2 forward; list_intros b s1c w.
  do 2 forward.
  Exists (@nil Z) a (b :: s1c) x' x' y' z; entailer!.
  unfold lseg; unfold listrep at 2; fold listrep.
  Exists w; entailer!.
Qed.

End SH_Proof.

