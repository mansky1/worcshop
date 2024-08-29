Require Import utils.VSTALib.

Require Import cprogs.interpreter.program.
Require Import cprogs.interpreter.definitions.
Require Import cprogs.interpreter.annotation.
Require cprogs.interpreter.eval.ret_path17.

Module SH_Proof <: STRAIGHTLINE_HOARE_TRIPLE_PROOF.

Include cprogs.interpreter.eval.ret_path17.

Theorem proof: functional_correctness_statement.
Proof.
  cbv delta [functional_correctness_statement].
  intros. Intros; subst.
  destruct_expr.
  forward.
  forward_call (st, m, arg, m, arg, st).
  Intros ret. forward.
  forward_call. Intros ret2. forward. 
  Exists (Vint ret2).
  sep_apply deref_expr_rep. entailer!.
Qed.

End SH_Proof.
