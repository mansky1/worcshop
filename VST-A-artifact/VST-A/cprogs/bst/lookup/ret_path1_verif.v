Require Import utils.VSTALib.

Require Import cprogs.bst.program.
Require Import cprogs.bst.definitions.
Require Import cprogs.bst.annotation.
Require cprogs.bst.lookup.ret_path1.

Module SH_Proof <: STRAIGHTLINE_HOARE_TRIPLE_PROOF.

Include cprogs.bst.lookup.ret_path1.

Theorem proof: functional_correctness_statement.
Proof.
  cbv delta [functional_correctness_statement].
  intros. Intros t t1 x p.
  forward. forward. unfold map_rep.
  Exists nullval t.
  entailer!.
  - erewrite <- lookup_relate; eauto.
  - rewrite sepcon_comm. apply wand_frame_elim.
Qed.

End SH_Proof.