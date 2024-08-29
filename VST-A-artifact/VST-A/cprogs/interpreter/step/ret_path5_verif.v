Require Import utils.VSTALib.

Require Import cprogs.interpreter.program.
Require Import cprogs.interpreter.definitions.
Require Import cprogs.interpreter.annotation.
Require cprogs.interpreter.step.ret_path5.

Module SH_Proof <: STRAIGHTLINE_HOARE_TRIPLE_PROOF.

Include cprogs.interpreter.step.ret_path5.

Theorem proof: functional_correctness_statement.
Proof.
  cbv delta [functional_correctness_statement].
  intros. Intros; subst.
  destruct_prog; [| discriminate].
  forward.
  destruct_cmd.
  forward. forward. gather_SEP 1.
  destruct_expr;
    ( forward_call (Vint (Int.repr 1))
    ; [cancel | contradiction]).
Qed.

End SH_Proof.
