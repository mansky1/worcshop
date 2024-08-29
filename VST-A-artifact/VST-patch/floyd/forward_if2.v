Lemma sem_cast_i2bool_of_bool : forall (b : bool),
  sem_cast_i2bool (Val.of_bool b) = Some (Val.of_bool b).
Proof.
  destruct b; auto.
Qed.

Ltac forward_if2 :=
  repeat apply seq_assoc1;
  apply semax_if_seq;
  forward_if.
Ltac step2 := first [step | forward_if2].
Ltac info_step2 := first [simpl eval_binop; rewrite sem_cast_i2bool_of_bool | info_step | forward_if2; idtac "forward_if2."].

Definition typed_true_bool (t : type) (v : val) :=
   eqb_option Bool.eqb (strict_bool_val v t) (Some true).

Definition typed_false_bool (t : type) (v : val) :=
   eqb_option Bool.eqb (strict_bool_val v t) (Some false).

Definition cond (b : bool) (s : statement) :=
  if b then s else Sskip.




Definition val_of_bool (b : bool) :=
  if b then Vtrue else Vfalse.

Lemma val_of_bool_strict_bool_val : forall b,
  strict_bool_val (val_of_bool b) tint = Some b.
Proof.
  destruct b; auto.
Qed.

