Require Import utils.VSTALib.

Require Import cprogs.bst.program.
Require Import cprogs.bst.definitions.
Require Import cprogs.bst.annotation.
Require cprogs.bst.delete.ret_path1.

Module SH_Proof <: STRAIGHTLINE_HOARE_TRIPLE_PROOF.

Include cprogs.bst.delete.ret_path1.

Theorem proof: functional_correctness_statement.
Proof.
  cbv delta [functional_correctness_statement].
  intros. Intros t t1 x b.
  unfold treebox_rep at 1. Intros p.
  forward. forward.
  tree_intros k v tl tr pl pr.
  subst t1. simpl delete.
  forward. forward. forward.
  assert_PROP (is_pointer_or_null p). entailer!.
  forward_call (v, tr, tl, p, k, b, b).
  { unfold_data_at (store_tree_cell p k v pl pr).
    sep_apply treerep_treebox_rep.
    sep_apply treerep_treebox_rep.
    cancel. }
  { tauto. }
  forward. assert (k = n) by lia. subst n.
  simpl_if. unfold mapbox_rep. Exists (delete k t). entailer!.
  - split. apply delete_relate; auto. apply delete_BST; auto.
  - apply wand_frame_elim.
Qed.

End SH_Proof.
