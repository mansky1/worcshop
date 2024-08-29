Require Import utils.VSTALib.

Require Import cprogs.dlist.program.
Require Import cprogs.dlist.definitions.
Require Import cprogs.dlist.annotation.
Require cprogs.dlist.append.ret_path1.

Module SH_Proof <: STRAIGHTLINE_HOARE_TRIPLE_PROOF.

Include cprogs.dlist.append.ret_path1.

Theorem proof: functional_correctness_statement.
Proof.
  cbv delta [functional_correctness_statement].
  intros.
  Intros z l3 l4 l5 a b t x y u.
  forward.
  subst u. list_intros.
  forward.
  forward.
  forward. Exists x. entailer!.
  rewrite <- H0.
  list_intros.
  subst l2.
  rewrite app_nil_r.
  entailer!.
  sep_apply singleton_lseg_pre.
  unfold listrep.
  sep_apply lseg_pre_listrep_pre.
  sep_apply lseg_pre_listrep_pre_app.
  entailer!.
Qed.

End SH_Proof.
