Require Import utils.VSTALib.

Require Import cprogs.list.program.
Require Import cprogs.list.definitions.
Require Import cprogs.list.annotation.
Require cprogs.list.enqueue.path0_verif.

Theorem f_enqueue_functionally_correct:
  semax_body Vprog Gprog f_enqueue enqueue_spec.
Proof.
  VST_A_start_function f_enqueue_hint.
  apply path0_verif.SH_Proof.proof.
Qed.
