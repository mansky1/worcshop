Require Import utils.VSTALib.

Require Import cprogs.interpreter.program.
Require Import cprogs.interpreter.definitions.
Require Import cprogs.interpreter.annotation.
Require cprogs.interpreter.step.ret_path0.

Module SH_Proof <: STRAIGHTLINE_HOARE_TRIPLE_PROOF.

Include cprogs.interpreter.step.ret_path0.

Theorem proof: functional_correctness_statement.
Proof.
  cbv delta [functional_correctness_statement].
  intros. Intros; subst.
  destruct_prog.
  - forward. destruct_cmd. forward.
    forward_call (st, m, arg, m, arg, st).
    Intros ret. forward.
    forward. forward.
    forward_call (sub, sub).
    Intros ret2. forward. forward. forward.
    sep_apply while_cmd_rep.
    forward_call.
    Intros ret3. forward. forward. forward.
    sep_apply foc_prog_rep_or_end.
    cancel.
  - forward.
    discriminate H.
Qed.

End SH_Proof.
