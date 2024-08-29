Require Import utils.VSTALib.

Require Import cprogs.list.program.
Require Import cprogs.list.definitions.
Require Import cprogs.list.annotation.
Require cprogs.list.append.ret_path2.

Module SH_Proof <: STRAIGHTLINE_HOARE_TRIPLE_PROOF.

Include cprogs.list.append.ret_path2.
  
Theorem proof: functional_correctness_statement.
Proof.
  cbv delta [functional_correctness_statement].
  intros.
  forward; list_intros a s1b z.
  do 4 forward; list_intros.
  Exists x'. Intros; subst.
  sep_apply store_listrep.
  simpl app; entailer!.
Qed.

End SH_Proof.
