Require Import utils.VSTALib.

Require Import cprogs.abs.program.
Require Import cprogs.abs.definitions.
Require Import cprogs.abs.annotation.
Require cprogs.abs.abs.ret_path1.

Module SH_Proof <: STRAIGHTLINE_HOARE_TRIPLE_PROOF.

Include cprogs.abs.abs.ret_path1.

Theorem proof: functional_correctness_statement.
Proof.
  cbv delta [functional_correctness_statement].
  intros. Intros.
  subst x'. forward. forward.
  Exists (Vint (Int.repr (x0))).
  rewrite Z.abs_eq by lia.
  entailer!.
Qed.

End SH_Proof.

