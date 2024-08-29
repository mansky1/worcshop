Require Import utils.VSTALib.

Require Import cprogs.interpreter.program.
Require Import cprogs.interpreter.definitions.
Require Import cprogs.interpreter.annotation.
Require cprogs.interpreter.eval.ret_path3.

Module SH_Proof <: STRAIGHTLINE_HOARE_TRIPLE_PROOF.

Include cprogs.interpreter.eval.ret_path3.

Theorem proof: functional_correctness_statement.
Proof.
  cbv delta [functional_correctness_statement].
  intros. Intros; subst.
  destruct_expr.
  forward. forward. forward.
  forward_call (st, m, arg, m, arg, st).
  Intros ret. forward.
  forward. forward. forward.
  Exists (Vint (Int.repr 0)).
  sep_apply binop_expr_rep. entailer!.
Qed.

End SH_Proof.
