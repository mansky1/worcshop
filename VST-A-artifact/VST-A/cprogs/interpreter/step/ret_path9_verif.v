Require Import utils.VSTALib.

Require Import cprogs.interpreter.program.
Require Import cprogs.interpreter.definitions.
Require Import cprogs.interpreter.annotation.
Require cprogs.interpreter.step.ret_path9.

Module SH_Proof <: STRAIGHTLINE_HOARE_TRIPLE_PROOF.

Include cprogs.interpreter.step.ret_path9.

Theorem proof: functional_correctness_statement.
Proof.
  cbv delta [functional_correctness_statement].
  intros. Intros; subst.
  destruct_prog; [| discriminate].
  forward.
  destruct_cmd.
  forward.
  forward_call (st, m, arg, m, arg, st).
  Intros ret. forward.
  forward. forward.
  forward. forward_call arg.
  forward_call sub.
  forward_call foc.
  forward. change (Vint (IntRepr 0)) with nullval.
  sep_apply ectx_prog_rep_or_end.
  cancel.
Qed.

End SH_Proof.
