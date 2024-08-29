Require Import utils.VSTALib.

Require Import cprogs.list.program.
Require Import cprogs.list.definitions.
Require Import cprogs.list.annotation.
Require cprogs.list.reverse1.path0.

Module SH_Proof <: STRAIGHTLINE_HOARE_TRIPLE_PROOF.

Include cprogs.list.reverse1.path0.
  
Theorem proof: functional_correctness_statement.
Proof.
  cbv delta [functional_correctness_statement].
  intros.
  forward.
  forward.
  Exists (@nil Z) l nullval p'.
  entailer!.
  unfold listrep.
  entailer!.
Qed.

End SH_Proof.
