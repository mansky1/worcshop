Require Import VST.floyd.proofauto.
Require Import Lia.
Require Import cprogs.abs.program.
Require Import cprogs.abs.definitions.

Definition abs_spec :=
  DECLARE _abs
    WITH x0: Z
    PRE [ _x OF tint ]
      PROP (- INT_MAX <= x0 <= INT_MAX)
      LOCAL (temp _x (Vint (IntRepr x0)))
      SEP ()
    POST [ tint ]
        PROP ()
        LOCAL (temp ret_temp (Vint (IntRepr (Zabs x0))))
        SEP ().

Definition Gprog : funspecs :=
  ltac:(with_library prog [abs_spec]).

Theorem f_abs_functionally_correct :
  semax_body Vprog Gprog f_abs abs_spec.
Proof.
  start_function.
  forward_if.
  - forward. entailer!.
    change (Int.signed Int.zero) with 0; lia.
    entailer!. rewrite Z.abs_neq by lia.
    reflexivity.
  - forward. entailer!.
    rewrite Z.abs_eq by lia.
    reflexivity.
Qed.
