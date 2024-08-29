Require Import utils.VSTALib.

Require Import cprogs.interpreter.program.
Require Import cprogs.interpreter.definitions.
Require Import cprogs.interpreter.annotation.
Require cprogs.interpreter.step.ret_path7.

Module SH_Proof <: STRAIGHTLINE_HOARE_TRIPLE_PROOF.

Include cprogs.interpreter.step.ret_path7.

Theorem proof: functional_correctness_statement.
Proof.
  cbv delta [functional_correctness_statement].
  intros. Intros; subst.
  destruct_prog; [| discriminate].
  forward.
  destruct_cmd.
  forward.
  forward_call (st, m, arg, m, arg, st).
  Intros ret. forward. forward. forward.
  forward. forward.
  forward_call sub0.
  forward_call arg.
  forward_call foc.
  forward. sep_apply foc_prog_rep_or_end.
  cancel.
Qed.

End SH_Proof.
