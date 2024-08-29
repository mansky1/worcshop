     = "Require Import VST.floyd.proofauto.
Require Import TOP.input.

#[local] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition main_spec :=
 DECLARE _main
  WITH gv : globals
  PRE  [] main_pre prog tt gv
  POST [ tint ] main_post prog gv.

Definition Gprog : funspecs := ltac:(with_library prog [main_spec]).

Lemma body_main: semax_body Vprog Gprog f_main main_spec.
Proof.
  start_function.
  forward_call.
  forward.
  forward.
  try entailer!.
Qed.
"%string
     : string
