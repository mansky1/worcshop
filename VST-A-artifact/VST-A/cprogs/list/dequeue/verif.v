Require Import utils.VSTALib.

Require Import cprogs.list.program.
Require Import cprogs.list.definitions.
Require Import cprogs.list.annotation.
Require cprogs.list.dequeue.ret_path0_verif.
Require cprogs.list.dequeue.ret_path1_verif.

Theorem f_dequeue_functionally_correct :
  semax_body Vprog Gprog f_dequeue dequeue_spec.
Proof.
  VST_A_start_function f_dequeue_hint.
  apply ret_path0_verif.SH_Proof.proof.
  apply ret_path1_verif.SH_Proof.proof.
Qed.
