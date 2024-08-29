Require Import Lia.
Require Import FloydSeq.precise_lemmas.
Require Import FloydSeq.precise_proofauto.
Require Import FloydSeq.proofauto.
Require Import cprogs.bst.program.
Local Open Scope logic.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Notation "'IntRepr'" := (Int.repr).
Notation "'store_int' p x" :=
  (@data_at CompSpecs Tsh tint (Vint(IntRepr(x))) p)
  (x at level 0, p at level 0, at level 0).
Notation "'store_tree_cell' p k v q1 q2" :=
  (@data_at CompSpecs Tsh (Tstruct _tree noattr) (Vint(IntRepr(k)), (v, (q1, q2))) p)
  (k at level 0, v at level 0, q1 at level 0, q2 at level 0, p at level 0, at level 0).
Notation "'store_tree_cell_' p" :=
  (@data_at_ CompSpecs Tsh (Tstruct _tree noattr) p)
  (p at level 0, at level 0).
Notation "'store_tree_ptr' p q" :=
  (@data_at CompSpecs Tsh (tptr (Tstruct _tree noattr)) q p)
  (q at level 0, p at level 0, at level 0).
Notation "'store_void_ptr' p q" :=
  (@data_at CompSpecs Tsh (tptr Tvoid) q p)
  (q at level 0, p at level 0, at level 0).
Notation "'tc_val_ptr'" := (tc_val (tptr Tvoid)).

Ltac simpl_if :=
  repeat match goal with
  | |- context [?n <? ?m] => first
    [ replace (n <? m) with true;
      [| symmetry; apply Zaux.Zlt_bool_true; lia]
    | replace (n <? m) with false;
      [| symmetry; apply Zaux.Zlt_bool_false; lia]
    ]
  | |- context [?n =? ?m] => first
    [ replace (n =? m) with true;
      [| symmetry; apply Z.eqb_eq; lia]
    | replace (n =? m) with false;
      [| symmetry; apply Z.eqb_neq; lia]
    ]
  end.

Definition key := Z.

Inductive tree : Type :=
  | E : tree
  | T : tree -> key -> val -> tree -> tree.

Fixpoint lookup (x : key) (t : tree) : val :=
  match t with
  | E => nullval
  | T tl k v tr =>
      if x <? k
      then lookup x tl
      else if k <? x
              then lookup x tr
              else v
  end.

Fixpoint insert (x: key) (v: val) (t: tree) : tree :=
  match t with
  | E => T E x v E
  | T a y v' b => if x <? y then T (insert x v a) y v' b
                  else if y <? x then T a y v' (insert x v b)
                  else T a x v b
  end.

Fixpoint pushdown_left (a: tree) (bc: tree) : tree :=
  match bc with
  | E => a
  | T b y vy c => T (pushdown_left a b) y vy c
  end.

Fixpoint delete (x: key) (s: tree) : tree :=
  match s with
  | E => E
  | T a y v' b => if x <? y then T (delete x a) y v' b
                  else if y <? x then T a y v' (delete x b)
                  else pushdown_left a b
  end.

Fixpoint tree_rep (t : tree) (p : val) : mpred :=
  match t with
  | E => !!(p = nullval) && emp
  | T a x v b =>
      !!(Int.min_signed <= x <= Int.max_signed /\ tc_val (tptr Tvoid) v) &&
      EX pa:val, EX pb:val,
        store_tree_cell p x v pa pb *
        tree_rep a pa *
        tree_rep b pb
  end.

Definition treebox_rep (t: tree) (b: val) : mpred :=
  EX p: val, store_tree_ptr b p * tree_rep t p.

Lemma tree_rep_local_facts:
  forall t p,
    tree_rep t p |--
    !!(is_pointer_or_null p /\ (p = nullval <-> t = E)).
Proof.
  induction t; unfold tree_rep; fold tree_rep; intros; normalize.
  - apply prop_right; split; simpl; auto. tauto.
  - entailer!.
    split; intros.
    inv H2. inv H7.
    congruence.
Qed.

Hint Resolve tree_rep_local_facts: saturate_local.

Lemma tree_rep_valid_pointer:
  forall t p,
    tree_rep t p
    |-- valid_pointer p.
Proof.
  intros.
  destruct t; simpl; normalize; auto with valid_pointer.
Qed.

Hint Resolve tree_rep_valid_pointer: valid_pointer.

Lemma treebox_rep_local_facts:
  forall t b,
    treebox_rep t b
    |-- !! field_compatible (tptr (Tstruct _tree noattr)) [] b.
Proof.
  intros. unfold treebox_rep.
  Intros p. entailer!.
Qed.

Hint Resolve treebox_rep_local_facts: saturate_local.

Lemma tree_rep_nullval:
  forall t,
    tree_rep t nullval
    |-- !!(t = E).
Proof.
  intros.
  destruct t; [entailer! |].
  simpl tree_rep.
  Intros pa pb. entailer!.
Qed.

Hint Resolve tree_rep_nullval: saturate_local.

Lemma treebox_rep_E:
  forall b:val,
    store_tree_ptr b nullval
    |-- treebox_rep E b.
Proof.
  intros. unfold treebox_rep. Exists nullval.
  simpl. entailer!.
Qed.

Lemma tree_rep_is_not_null:
  forall t p,
    p <> nullval ->
    tree_rep t p |--
      EX k v tl tr (pl:val) (pr:val),
        !!((t = T tl k v tr) /\ (Int.min_signed <= k <= Int.max_signed) /\ tc_val (tptr Tvoid) v) &&
        store_tree_cell p k v pl pr *
        tree_rep tl pl *
        tree_rep tr pr.
Proof.
  intros. saturate_local.
  destruct t; simpl.
  - pose proof proj2 H0 eq_refl.
    subst; tauto.
  - Intros pa pb. Exists k v t1 t2 pa pb.
    entailer!.
Qed.

Lemma store_tree_rep:
  forall k v (pl:val) (pr:val) tl tr p,
    !!(Int.min_signed <= k <= Int.max_signed /\ tc_val (tptr Tvoid) v) &&
    store_tree_cell p k v pl pr *
    tree_rep tl pl *
    tree_rep tr pr
    |-- tree_rep (T tl k v tr) p.
Proof.
  intros.
  unfold tree_rep; fold tree_rep.
  entailer!.
  Exists pl pr.
  entailer!.
Qed.

Lemma treerep_treebox_rep:
  forall t p b,
    tree_rep t p * store_tree_ptr b p
    |-- treebox_rep t b.
Proof.
  intros. unfold treebox_rep.
  Exists p. entailer!.
Qed.

Lemma treebox_rep_leaf:
  forall n p b (v: val),
    is_pointer_or_null v ->
    Int.min_signed <= n <= Int.max_signed ->
    store_tree_cell p n v nullval nullval * store_tree_ptr b p
    |-- treebox_rep (T E n v E) b.
Proof.
  intros.
  unfold treebox_rep, tree_rep. Exists p nullval nullval. entailer!.
Qed.

Lemma bst_left_entail:
  forall (t1 t1' t2: tree) k (v p1 p2 p b: val),
    Int.min_signed <= k <= Int.max_signed ->
    is_pointer_or_null v ->
    store_tree_ptr b p *
    store_tree_cell p k v p1 p2 *
    tree_rep t1 p1 * tree_rep t2 p2
    |-- treebox_rep t1 (field_address (Tstruct _tree noattr) [StructField _left] p) *
        (treebox_rep t1'
          (field_address (Tstruct _tree noattr) [StructField _left] p) -*
          treebox_rep (T t1' k v t2) b).
Proof.
  intros.
  unfold_data_at (data_at _ _ _ p).
  rewrite (field_at_data_at _ _ [StructField _left]).
  unfold treebox_rep at 1. Exists p1. cancel.
  rewrite <- wand_sepcon_adjoint.
  clear p1.
  unfold treebox_rep.
  Exists p.
  simpl.
  Intros p1.
  Exists p1 p2.
  entailer!.
  unfold_data_at (data_at _ _ _ p).
  rewrite (field_at_data_at _ _ [StructField _left]).
  cancel.
Qed.

Lemma bst_right_entail:
  forall (t1 t2 t2': tree) k (v p1 p2 p b: val),
    Int.min_signed <= k <= Int.max_signed ->
    is_pointer_or_null v ->
    store_tree_ptr b p *
    store_tree_cell p k v p1 p2 *
    tree_rep t1 p1 * tree_rep t2 p2
    |-- treebox_rep t2 (field_address (Tstruct _tree noattr) [StructField _right] p) *
        (treebox_rep t2'
          (field_address (Tstruct _tree noattr) [StructField _right] p) -*
          treebox_rep (T t1 k v t2') b).
Proof.
  intros.
  unfold_data_at (data_at _ _ _ p).
  rewrite (field_at_data_at _ _ [StructField _right]).
  unfold treebox_rep at 1. Exists p2. cancel.
  rewrite <- wand_sepcon_adjoint.
  clear p2.
  unfold treebox_rep.
  Exists p.
  simpl.
  Intros p2.
  Exists p1 p2.
  entailer!.
  unfold_data_at (data_at _ _ _ p).
  rewrite (field_at_data_at _ _ [StructField _right]).
  cancel.
Qed.

Lemma tree_rep_sameloc_eq:
  forall p t1 t2,
    (tree_rep t1 p * TT) && (tree_rep t2 p * TT)
    |-- !! (t1 = t2).
Proof.
  intros.
  generalize dependent p.
  generalize dependent t2.
  induction t1; destruct t2; intros.
  - apply prop_right; auto.
  - unfold_once tree_rep; normalize.
    data_at_nullval_left.
  - unfold_once tree_rep; normalize.
    data_at_nullval_left.
  - do_on_both saturate_local.
    unfold_once tree_rep. Intros pa1 pb1 pa2 pb2.
    unfold_data_at_composite.
    do_on_both saturate_local.
    repeat rewrite <- sepcon_assoc.
    left_assoc_sepcon_TT_to_fold_right.
    subst_data_at_sameloc_eq.
    apply prop_right. congruence.
Qed.

Lemma treebox_rep_sameloc_eq:
  forall b t1 t2,
    (treebox_rep t1 b * TT) && (treebox_rep t2 b * TT)
    |-- !! (t1 = t2).
Proof.
  intros. unfold treebox_rep.
  Intros p1 p2.
  do_on_both saturate_local.
  repeat rewrite <- sepcon_assoc.
  left_assoc_sepcon_TT_to_fold_right.
  subst_data_at_sameloc_eq.
  simpl fold_right. apply tree_rep_sameloc_eq.
Qed.

Hint Resolve tree_rep_sameloc_eq: precise_rel.
Hint Resolve treebox_rep_sameloc_eq: precise_rel.

Lemma precise_tree_rep:
  forall t p,
    precise_pred (tree_rep t p).
Proof.
  intros t.
  induction t; intros.
  - unfold tree_rep.
    apply andp_prop_precise.
    apply precise_emp.
  - unfold_once tree_rep.
    apply andp_prop_precise.
    rewrite exp_uncurry. apply exp_precise.
    + intros. destruct_all.
      simpl fst; simpl snd.
      unfold_data_at_composite.
      do_on_both saturate_local.
      repeat rewrite <- sepcon_assoc.
      left_assoc_sepcon_TT_to_fold_right.
      subst_data_at_sameloc_eq.
      apply prop_right; auto.
    + intros.
      unfold_data_at_composite.
      prove_precise_pred_sepcon.
Qed.

Lemma precise_treebox_rep:
  forall t p,
    precise_pred (treebox_rep t p).
Proof.
  intros. unfold treebox_rep.
  apply exp_precise.
  - intros.
    do_on_both saturate_local.
    repeat rewrite <- sepcon_assoc.
    left_assoc_sepcon_TT_to_fold_right.
    subst_data_at_sameloc_eq.
    apply prop_right; auto.
  - intros. prove_precise_pred_sepcon.
    apply precise_tree_rep.
Qed.

Hint Resolve precise_tree_rep: precise_pred.
Hint Resolve precise_treebox_rep: precise_pred.

Lemma z_order (m n: Z):
  m < n \/ n < m \/ m = n.
Proof. lia. Qed.

Section BST.

Fixpoint ForallT (P: key -> val -> Prop) (t: tree): Prop :=
  match t with
  | E => True
  | T l k v r => P k v /\ ForallT P l /\ ForallT P r
  end.

Lemma ForallT_conseq:
  forall (P1 P2: key -> val -> Prop) t,
    (forall k v, P1 k v -> P2 k v) ->
    ForallT P1 t ->
    ForallT P2 t.
Proof.
  intros. induction t.
  - auto.
  - inv H0. simpl. pose proof H k v.
    tauto.
Qed.

Inductive BST: tree -> Prop :=
  | BST_E: BST E
  | BST_T: forall l x v r,
      ForallT (fun y _ => y < x) l ->
      ForallT (fun y _ => x < y) r ->
      BST l -> BST r ->
      BST (T l x v r).

Hint Constructors BST: core.

Theorem empty_tree_BST: BST E.
Proof. constructor. Qed.

Lemma ForallT_insert:
  forall P t,
    ForallT P t ->
    forall k v,
      P k v -> ForallT P (insert k v t).
Proof.
  intros. induction t; simpl.
  - auto.
  - inv H.
    destruct (z_order k k0) as [? | [? | ?]]; simpl_if;
      simpl; tauto.
Qed.

Lemma ForallT_pushdown_left:
  forall P t1 t2,
    ForallT P t1 ->
    ForallT P t2 ->
    ForallT P (pushdown_left t1 t2).
Proof.
  intros. induction t2; simpl.
  - auto.
  - inv H0. tauto.
Qed.

Lemma ForallT_delete:
  forall P t,
    ForallT P t ->
    forall k, ForallT P (delete k t).
Proof.
  intros. induction t; simpl.
  - auto.
  - inv H.
    destruct (z_order k k0) as [? | [? | ?]]; simpl_if;
      simpl; try tauto.
    apply ForallT_pushdown_left; tauto.
Qed.

Theorem insert_BST:
  forall k v t,
    BST t -> BST (insert k v t).
Proof.
  intros. induction H; simpl.
  - constructor; unfold ForallT; auto.
  - destruct (z_order x k) as [? | [? | ?]]; simpl_if.
    + constructor; auto.
      apply ForallT_insert; auto.
    + constructor; auto.
      apply ForallT_insert; auto.
    + subst. auto.
Qed.

Lemma pushdown_left_BST:
  forall l r,
    BST l -> BST r ->
    (exists k,
      ForallT (fun y _ => y < k) l /\
      ForallT (fun y _ => k < y) r) ->
    BST (pushdown_left l r).
Proof.
  intros. destruct H1 as [? [? ?]].
  induction r; simpl.
  - auto.
  - inv H0. inv H2. constructor; auto.
    apply ForallT_pushdown_left; auto.
    + apply ForallT_conseq with (fun y _ => y < x); auto.
      intros. lia.
    + tauto.
Qed.

Theorem delete_BST:
  forall k t,
    BST t -> BST (delete k t).
Proof.
  intros. induction H; simpl; auto.
  destruct (z_order x k) as [? | [? | ?]]; simpl_if.
  - constructor; auto.
    apply ForallT_delete; auto.
  - constructor; auto.
    apply ForallT_delete; auto.
  - subst. apply pushdown_left_BST; auto.
    exists k; auto. 
Qed.

End BST.

Section ABS.

Definition partial_map (A: Type) := Z -> option A.

Definition empty {A: Type} : partial_map A :=
  fun _ => None.

Definition get {A: Type} (default: A) (m: partial_map A) (k: Z) : A :=
  match m k with
  | Some v => v
  | None => default
  end.

Definition update {A: Type} (m: partial_map A) (k: Z) (v: A) : partial_map A :=
  fun x => if x =? k then Some v else m x.

Definition remove {A: Type} (m: partial_map A) (k: Z) : partial_map A :=
  fun x => if x =? k then None else m x.

Definition combine {A: Type} (pivot: Z) (m1 m2: partial_map A): partial_map A :=
  fun x => if x <? pivot then m1 x else m2 x.

Lemma update_same:
  forall A (m: partial_map A) k v1 v2,
    update (update m k v1) k v2 = update m k v2.
Proof.
  intros. apply functional_extensionality; intro.
  unfold update.
  destruct (Z.eq_dec x k);
    simpl_if; auto.
Qed.

Lemma update_permute:
  forall A (m: partial_map A) k1 v1 k2 v2,
    k1 <> k2 ->
    update (update m k1 v1) k2 v2 = update (update m k2 v2) k1 v1.
Proof.
  intros. apply functional_extensionality; intro.
  unfold update.
  destruct (Z.eq_dec x k2), (Z.eq_dec x k2);
    simpl_if; auto; contradiction.
Qed.

Inductive Abs: tree -> partial_map val -> Prop :=
  | Abs_E: Abs E empty
  | Abs_T: forall a b l k v r,
      Abs l a -> Abs r b ->
      Abs (T l k v r) (update (combine k a b) k v).

Lemma Abs_exist:
  forall t: tree,
    exists m: partial_map val,
      Abs t m.
Proof.
  intro t. induction t.
  - exists empty. constructor.
  - destruct IHt1, IHt2.
    eexists. econstructor; eauto.
Qed.

Lemma Abs_injection:
  forall t m1 m2,
    Abs t m1 -> Abs t m2 ->
    m1 = m2.
Proof.
  intro t.
  induction t; intros; inv H; inv H0; auto.
  assert (a = a0) by auto.
  assert (b = b0) by auto.
  subst; auto.
Qed.

Lemma Abs_ForallT_forall:
  forall P t m,
    Abs t m ->
    ForallT P t ->
    forall k,
      match m k with
      | Some v => P k v
      | None => True
      end.
Proof.
  intros. induction H; simpl; auto.
  inv H0. unfold update, combine.
  destruct (z_order k k0) as [? | [? | ?]]; simpl_if.
  - apply IHAbs1. tauto.
  - apply IHAbs2. tauto.
  - subst; auto.
Qed.

Theorem empty_relate: Abs E empty.
Proof. constructor. Qed.

Theorem lookup_relate:
  forall k t m,
    Abs t m ->
    lookup k t = get nullval m k.
Proof.
  intros. induction H.
  - auto.
  - unfold update, combine; unfold get in *; simpl.
    destruct (z_order k k0) as [? | [? | ?]]; simpl_if; auto.
Qed.

Theorem insert_relate:
  forall k v t m,
    Abs t m ->
    Abs (insert k v t) (update m k v).
Proof.
  intros. induction H.
  - simpl. replace empty with (@combine val k empty empty).
    repeat constructor.
    apply functional_extensionality; intro.
    unfold combine. destruct (x <? k); auto.
  - simpl; destruct (z_order k k0) as [? | [? | ?]]; simpl_if.
    + replace (update (update (combine k0 a b) k0 v0) k v)
         with (update (combine k0 (update a k v) b) k0 v0).
      constructor; auto.
      rewrite update_permute by lia.
      f_equal. apply functional_extensionality. intro.
      unfold combine, update.
      destruct (z_order x k0); simpl_if; auto.
    + replace (update (update (combine k0 a b) k0 v0) k v)
         with (update (combine k0 a (update b k v)) k0 v0).
      constructor; auto.
      rewrite update_permute by lia.
      f_equal. apply functional_extensionality. intro.
      unfold combine, update.
      destruct (z_order x k0); simpl_if; auto.
    + subst. rewrite update_same.
      constructor; auto.
Qed.

Lemma pushdown_left_relate:
  forall l r a b k,
    Abs l a ->
    Abs r b ->
    ForallT (fun y _ => y < k) l ->
    ForallT (fun y _ => k < y) r ->
    Abs (pushdown_left l r) (combine k a b).
Proof.
  intros. induction H0; simpl.
  - replace (combine k a empty) with a; auto.
    apply functional_extensionality; intro.
    unfold combine.
    destruct (z_order x k); simpl_if; auto.
    pose proof Abs_ForallT_forall _ _ _ H H1 x.
    simpl in H3.
    destruct (a x); auto. lia.
  - inv H2. destruct H3.
    replace (combine k a (update (combine k0 a0 b) k0 v))
       with (update (combine k0 (combine k a a0) b) k0 v).
    constructor; auto.
    apply functional_extensionality; intro.
    unfold update, combine.
    destruct (z_order x k0); simpl_if; auto.
Qed.

Theorem delete_relate:
  forall k t m,
    BST t ->
    Abs t m ->
    Abs (delete k t) (remove m k).
Proof.
  intros. induction H0.
  - simpl. replace (remove empty k) with (@empty val).
    constructor.
    apply functional_extensionality; intro.
    unfold remove, empty.
    destruct (x =? k); auto.
  - inv H. simpl; destruct (z_order k k0) as [? | [? | ?]]; simpl_if.
    + replace (remove (update (combine k0 a b) k0 v) k)
         with (update (combine k0 (remove a k) b) k0 v).
      constructor; auto.
      apply functional_extensionality; intro.
      unfold update, combine, remove.
      destruct (z_order x k0); simpl_if; auto.
    + replace (remove (update (combine k0 a b) k0 v) k)
         with (update (combine k0 a (remove b k)) k0 v).
      constructor; auto.
      apply functional_extensionality; intro.
      unfold update, combine, remove.
      destruct (z_order x k0) as [? | [? | ?]]; simpl_if; auto.
    + subst.
      replace (remove (update (combine k0 a b) k0 v) k0)
         with (combine k0 a b).
      apply pushdown_left_relate; auto.
      apply functional_extensionality; intro.
      unfold update, remove, combine.
      destruct (Z.eq_dec x k0); simpl_if; auto.
      subst. pose proof Abs_ForallT_forall _ _ _ H0_0 H5 k0.
      simpl in H. destruct (b k0); auto; lia.
Qed.

End ABS.

Definition map_rep (m: partial_map val) (p: val) :=
  EX t: tree,
    !!(Abs t m /\ BST t) && tree_rep t p.

Definition mapbox_rep (m: partial_map val) (b: val) :=
  EX t: tree,
    !!(Abs t m /\ BST t) && treebox_rep t b.

Lemma map_rep_sameloc_eq:
  forall p m1 m2,
    (map_rep m1 p * TT) && (map_rep m2 p * TT)
    |-- !! (m1 = m2).
Proof.
  intros. unfold map_rep. Intros t1 t2.
  sep_apply tree_rep_sameloc_eq. Intros; subst.
  apply prop_right.
  eapply Abs_injection; eauto.
Qed.

Lemma mapbox_rep_sameloc_eq:
  forall b m1 m2,
    (mapbox_rep m1 b * TT) && (mapbox_rep m2 b * TT)
    |-- !! (m1 = m2).
Proof.
  intros. unfold mapbox_rep. Intros t1 t2.
  sep_apply treebox_rep_sameloc_eq. Intros; subst.
  apply prop_right.
  eapply Abs_injection; eauto.
Qed.

Hint Resolve map_rep_sameloc_eq: precise_rel.
Hint Resolve mapbox_rep_sameloc_eq: precise_rel.

Lemma precise_map_rep:
  forall m p,
    precise_pred (map_rep m p).
Proof.
  intros. unfold map_rep.
  apply exp_precise.
  - intros. Intros. apply tree_rep_sameloc_eq.
  - intros. apply andp_prop_precise.
    apply precise_tree_rep.
Qed.

Lemma precise_mapbox_rep:
  forall m p,
    precise_pred (mapbox_rep m p).
Proof.
  intros. unfold mapbox_rep.
  apply exp_precise.
  - intros. Intros. apply treebox_rep_sameloc_eq.
  - intros. apply andp_prop_precise.
    apply precise_treebox_rep.
Qed.

Hint Resolve precise_map_rep: precise_pred.
Hint Resolve precise_mapbox_rep: precise_pred.

Tactic Notation "tree_intros"
    simple_intropattern(k) simple_intropattern(v)
    simple_intropattern(tl) simple_intropattern(tr)
    simple_intropattern(pl) simple_intropattern(pr) :=
  match goal with
  | H: ?p <> nullval |- context [tree_rep ?t ?p] =>
    sep_apply (tree_rep_is_not_null t p)
  end;
  Intros k v tl tr pl pr.
