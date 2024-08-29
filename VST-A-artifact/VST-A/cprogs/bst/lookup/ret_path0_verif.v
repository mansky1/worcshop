Require Import utils.VSTALib.

Require Import cprogs.bst.program.
Require Import cprogs.bst.definitions.
Require Import cprogs.bst.annotation.
Require cprogs.bst.lookup.ret_path0.

Module SH_Proof <: STRAIGHTLINE_HOARE_TRIPLE_PROOF.

Include cprogs.bst.lookup.ret_path0.

Theorem proof: functional_correctness_statement.
Proof.
  cbv delta [functional_correctness_statement].
  intros. Intros t t1 x p.
  forward.
  tree_intros k v tl tr pl pr.
  forward. forward.
  forward. forward.
  forward. unfold map_rep. Exists v t.
  entailer!.
  - erewrite <- lookup_relate; eauto.
    rewrite <- H. simpl. simpl_if. auto.
  - sep_apply store_tree_rep; auto.
    apply wand_frame_elim.
Qed.

End SH_Proof.
