Require Import VST.floyd.proofauto.
Require Import Lia.
Require Import cprogs.add.program.
Require Import cprogs.add.definitions.

Definition add_spec :=
  DECLARE _add
    WITH x0: Z, y0: Z
    PRE [ _x OF tint, _y OF tint ]
      PROP (0 <= x0 <= 100; 0 <= y0 <= 100)
      LOCAL (temp _x (Vint (IntRepr x0)); temp _y (Vint (IntRepr y0)))
      SEP ()
    POST [ tint ]
      PROP ()
      LOCAL (temp ret_temp (Vint (IntRepr (x0 + y0))))
      SEP ().

Definition slow_add_spec :=
  DECLARE _slow_add
    WITH x0: Z, y0: Z
    PRE [ _x OF tint, _y OF tint ]
      PROP (0 <= x0 <= 100; 0 <= y0 <= 100)
      LOCAL (temp _x (Vint (IntRepr x0)); temp _y (Vint (IntRepr y0)))
      SEP ()
    POST [ tint ]
      PROP ()
      LOCAL (temp ret_temp (Vint (IntRepr (x0 + y0))))
      SEP ().

Definition Gprog : funspecs :=
  ltac:(with_library prog [add_spec; slow_add_spec]).

Theorem f_add_functionally_correct :
  semax_body Vprog Gprog f_add add_spec.
Proof.
  start_function.
  forward.
  forward.
Qed.

Theorem f_slow_add_functionally_correct:
  semax_body Vprog Gprog f_slow_add slow_add_spec.
Proof.
  start_function.
  forward_while (EX x1: Z, EX y1: Z,
    PROP (0 <= x1 <= 100; 0 <= x1 + y1 <= 200; Z.add x1 y1 = Z.add x0 y0)
    LOCAL (temp _x (Vint (IntRepr x1)); temp _y (Vint (IntRepr y1)))
    SEP ()).
  - Exists x0 y0. entailer!.
  - entailer!.
  - forward. forward.
    Exists (x1 - 1, y1 + 1). entailer!. 
    lia.
  - forward. entailer!.
    assert (x1 = 0) by lia. rewrite <- H3.
    subst. reflexivity.
Qed.
