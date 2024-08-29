Require Import VST.floyd.proofauto.
Require Import Lia.
Require Import cprogs.max3.program.
Require Import cprogs.max3.definitions.

Definition max3_spec :=
  DECLARE _max3
    WITH x0: Z, y0: Z, z0: Z
    PRE [ _x OF tint, _y OF tint, _z OF tint ]
      PROP (Int.min_signed <= x0 <= Int.max_signed;
            Int.min_signed <= y0 <= Int.max_signed;
            Int.min_signed <= z0 <= Int.max_signed)
      LOCAL (temp _x (Vint (IntRepr x0)); temp _y (Vint (IntRepr y0)); temp _z (Vint (IntRepr z0)))
      SEP ()
    POST [ tint ]
      EX r: Z,
        PROP (r >= x0; r >= y0; r >= z0)
        LOCAL (temp ret_temp (Vint (IntRepr r)))
        SEP ().

Definition Gprog : funspecs :=
  ltac:(with_library prog [max3_spec]).

Theorem f_max3_functionally_correct :
  semax_body Vprog Gprog f_max3 max3_spec.
Proof.
  start_function.
  forward_if.
  - forward_if.
    + forward.
      Exists z0.
      entailer!.
    + forward.
      Exists y0.
      entailer!.
  - forward_if.
    + forward.
      Exists z0.
      entailer!.
    + forward.
      Exists x0.
      entailer!.
Qed.
