Require Import utils.VSTALib.

Require Import cprogs.interpreter.program.
Require Import cprogs.interpreter.definitions.
Require Import cprogs.interpreter.annotation.
Require cprogs.interpreter.step.ret_path1.

Module SH_Proof <: STRAIGHTLINE_HOARE_TRIPLE_PROOF.

Include cprogs.interpreter.step.ret_path1.

Theorem proof: functional_correctness_statement.
Proof.
  cbv delta [functional_correctness_statement].
  intros. Intros; subst.
  destruct_prog.
  - forward. subst foc.
    sep_apply cmd_rep_local_facts.
    Intros. destruct Pnullval.
  - forward. forward.
    forward. forward. forward.
    forward_call ectx.
    forward.
    sep_apply foc_prog_rep_or_end.
    cancel.
Qed.

End SH_Proof.
