Require Import utils.VSTALib.

Require Import cprogs.interpreter.program.
Require Import cprogs.interpreter.definitions.
Require Import cprogs.interpreter.annotation.
Require cprogs.interpreter.step.ret_path3.

Module SH_Proof <: STRAIGHTLINE_HOARE_TRIPLE_PROOF.

Include cprogs.interpreter.step.ret_path3.

Theorem proof: functional_correctness_statement.
Proof.
  cbv delta [functional_correctness_statement].
  intros. Intros; subst.
  destruct_prog; [| discriminate].
  forward. destruct_cmd.
  forward. forward. gather_SEP 1.
  destruct_expr.
  forward.
  forward_call (st, m, arg0, m, arg0, st).
  Intros ret. forward.
  forward_call (st, st).
  forward_call arg.
  forward_call arg0. forward.
  forward_call foc.
  forward. change (Vint (IntRepr 0)) with nullval.
  sep_apply ectx_prog_rep_or_end.
  entailer!.
Qed.

End SH_Proof.
