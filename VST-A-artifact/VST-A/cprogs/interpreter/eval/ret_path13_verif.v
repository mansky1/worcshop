Require Import utils.VSTALib.

Require Import cprogs.interpreter.program.
Require Import cprogs.interpreter.definitions.
Require Import cprogs.interpreter.annotation.
Require cprogs.interpreter.eval.ret_path13.

Module SH_Proof <: STRAIGHTLINE_HOARE_TRIPLE_PROOF.

Include cprogs.interpreter.eval.ret_path13.

Theorem proof: functional_correctness_statement.
Proof.
  cbv delta [functional_correctness_statement].
  intros. Intros; subst.
  destruct_expr.
  forward. forward. forward.
  forward_call (st, m, arg, m, arg, st).
  Intros ret. forward.
  do 8 forward.
  forward_call (st, m, arg0, m, arg0, st).
  Intros ret2.
  forward. forward. forward.
  Exists (Vint (Int.repr 1)).
  sep_apply binop_expr_rep. entailer!.
Qed.

End SH_Proof.
