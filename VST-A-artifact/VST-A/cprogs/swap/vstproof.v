Require Import VST.floyd.proofauto.
Require Import Lia.
Require Import cprogs.swap.program.
Require Import cprogs.swap.definitions.

Definition int_swap_spec :=
  DECLARE _int_swap
    WITH x: Z, y: Z, px0: val, py0: val
    PRE [ _px OF tptr tint, _py OF tptr tint ]
      PROP ()
      LOCAL (temp _px px0; temp _py py0)
      SEP (store_int px0 x; store_int py0 y)
    POST [ tvoid ]
      PROP ()
      LOCAL ()
      SEP (store_int px0 y; store_int py0 x).

Definition int_pair_swap_spec :=
  DECLARE _int_pair_swap
    WITH x: Z, y: Z, p0: val
    PRE [ _p OF tptr (Tstruct _int_pair noattr) ]
      PROP ()
      LOCAL (temp _p p0)
      SEP (store_int_pair p0 x y)
    POST [ tvoid ]
      PROP ()
      LOCAL ()
      SEP (store_int_pair p0 y x).

Definition int_pair_swap2_spec :=
  DECLARE _int_pair_swap2
    WITH x: Z, y: Z, p0: val
    PRE [ _p OF tptr (Tstruct _int_pair noattr) ]
      PROP ()
      LOCAL (temp _p p0)
      SEP (store_int_pair p0 x y)
    POST [ tvoid ]
      PROP ()
      LOCAL ()
      SEP (store_int_pair p0 y x).

Definition int_swap_arith_spec :=
  DECLARE _int_swap_arith
    WITH x: Z, y: Z, px0: val, py0: val
    PRE [ _px OF tptr tint, _py OF tptr tint ]
      PROP (0 <= x <= 100; 0 <= y <= 100)
      LOCAL (temp _px px0; temp _py py0)
      SEP (store_int px0 x; store_int py0 y)
    POST [ tvoid ]
      PROP ()
      LOCAL ()
      SEP (store_int px0 y; store_int py0 x).

Definition Gprog : funspecs :=
  ltac:(with_library prog [int_swap_spec; int_pair_swap_spec; int_pair_swap2_spec; int_swap_arith_spec]).

Theorem f_int_swap_functionally_correct :
  semax_body Vprog Gprog f_int_swap int_swap_spec.
Proof.
  start_function.
  forward.
  forward.
  forward.
  forward.
  entailer!.
Qed.

Theorem f_int_pair_swap_functionally_correct :
  semax_body Vprog Gprog f_int_pair_swap int_pair_swap_spec.
Proof.
  start_function.
  forward.
  forward.
  forward.
  forward.
  entailer!.
Qed.

Ltac field_address_solver :=
  match goal with
  | |- @eq val ?p (field_address _ _ ?p) => idtac
  | |- @eq val (offset_val _ ?p) (field_address _ _ ?p) => idtac
  | |- @eq val (field_address _ _ ?p) ?p => idtac
  | |- @eq val (field_address _ _ ?p) (offset_val _ ?p) => idtac
  | _ => fail 1 "The proof goal is not in a form of (p = field_address _ _ p) or (offset_val _ p = field_address _ _ p)"
  end;
  unfold field_address; simpl;
  (rewrite if_true by auto with field_compatible || fail 1 "Not enough field_compatible information to derive the equality.");
  rewrite ? isptr_offset_val_zero; auto.

Theorem f_int_pair_swap2_functionally_correct :
  semax_body Vprog Gprog f_int_pair_swap2 int_pair_swap2_spec.
Proof.
  start_function.
  unfold_data_at (store_int_pair p0 x y).
  forward_call (x, y, (field_address (Tstruct _int_pair noattr) [StructField _a] p0), (field_address (Tstruct _int_pair noattr) [StructField _b] p0)).
  {
    entailer!.
    split; f_equal; field_address_solver.
  }
  {
    unfold_data_at (store_int_pair p0 y x).
    entailer!.
  }
Qed.

Theorem f_int_swap_arith_functionally_correct :
  semax_body Vprog Gprog f_int_swap_arith int_swap_arith_spec.
Proof.
  start_function.
  forward. forward.
  forward. forward.
  forward. forward.
  forward. forward.
  forward. entailer!.
  replace (x + y - (x + y - y)) with y by lia.
  replace (x + y - y) with x by lia.
  entailer!.
Qed.
