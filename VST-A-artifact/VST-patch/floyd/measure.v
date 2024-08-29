
Definition size_is (n: Z) : Prop := False.

Lemma assert_size_is_Type (n: Z) :
  forall (A: Type), size_is n -> A.
Proof.
intros. elimtype False; apply H.
Qed.

Lemma assert_size_is_Prop (n: Z) :
  forall (A: Prop), size_is n -> A.
Proof.
intros. elimtype False; apply H.
Qed.

Opaque size_is.


Ltac composite i :=
  match i with
  | _ _ => idtac
  | (fun _ => _) => idtac
  end.

Ltac primary i := try (composite i; fail 1).
