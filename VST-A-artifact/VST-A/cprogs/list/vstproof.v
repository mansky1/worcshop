Require Import VST.floyd.proofauto.
Require Import Lia.
Require Import cprogs.list.program.
Require Import cprogs.list.definitions.

Definition malloc_list_cell_spec :=
  DECLARE _malloc_list_cell
    WITH _: unit
    PRE [ ]
      PROP ()
      LOCAL ()
      SEP ()
    POST [ tptr (Tstruct _list noattr) ]
      EX r: val,
        PROP ()
        LOCAL (temp ret_temp r)
        SEP (store_list_cell_ r).

Definition free_list_cell_spec :=
  DECLARE _free_list_cell
    WITH p: val
    PRE [ _p OF tptr (Tstruct _list noattr) ]
      PROP ()
      LOCAL (temp _p p)
      SEP (store_list_cell_ p)
    POST [ tvoid ]
      PROP ()
      LOCAL ()
      SEP ().

Definition malloc_list_2p_spec :=
  DECLARE _malloc_list_2p
    WITH _: unit
    PRE [ ]
      PROP ()
      LOCAL ()
      SEP ()
    POST [ tptr (tptr (Tstruct _list noattr)) ]
      EX r: val, EX p: val,
        PROP ()
        LOCAL (temp ret_temp r)
        SEP (store_list_ptr r p).

Definition free_list_2p_spec :=
  DECLARE _free_list_2p
    WITH p2: val
    PRE [ 9%positive OF tptr (tptr (Tstruct _list noattr)) ]
      PROP ()
      LOCAL (temp 9%positive p2)
      SEP (store_list_ptr_ p2)
    POST [ tvoid ]
      PROP ()
      LOCAL ()
      SEP ().

Definition reverse_pre_post :=
  WITH p: val, l: list Z
  PRE [ _p OF tptr (Tstruct _list noattr) ]
    PROP ()
    LOCAL (temp _p p)
    SEP (listrep l p)
  POST [ tptr (Tstruct _list noattr) ]
    EX r: val,
      PROP ()
      LOCAL (temp ret_temp r)
      SEP (listrep (rev l) r).

Definition reverse_spec :=
  DECLARE _reverse reverse_pre_post.

Definition append_pre_post :=
  WITH x: val, y: val, s1: list Z, s2: list Z
  PRE [ _x OF tptr (Tstruct _list noattr), _y OF tptr (Tstruct _list noattr) ]
    PROP ()
    LOCAL (temp _x x; temp _y y)
    SEP (listrep s1 x; listrep s2 y)
  POST [ tptr (Tstruct _list noattr) ]
    EX r: val,
      PROP ()
      LOCAL (temp ret_temp r)
      SEP (listrep (s1 ++ s2) r).

Definition append_spec :=
  DECLARE _append append_pre_post.

Definition append_2p_spec :=
  DECLARE _append_2p append_pre_post.

Definition append2_spec :=
  DECLARE _append2 append_pre_post.

Definition rev_append_spec :=
  DECLARE _rev_append
    WITH l1: list Z, l2: list Z, p: val, q: val
    PRE [ _p OF tptr (Tstruct _list noattr), _q OF tptr (Tstruct _list noattr) ]
      PROP ()
      LOCAL (temp _p p; temp _q q)
      SEP (listrep l1 p; listrep l2 q)
    POST [ tptr (Tstruct _list noattr) ]
      EX r: val,
        PROP ()
        LOCAL (temp ret_temp r)
        SEP (listrep (rev l1 ++ l2) r).

Definition max_spec :=
  DECLARE _max
    WITH l: list Z, p: val
    PRE [ _p OF tptr (Tstruct _list noattr) ]
      PROP (all_nonneg l)
      LOCAL (temp _p p)
      SEP (listrep l p)
    POST [ tint ]
      PROP ()
      LOCAL (temp ret_temp (Vint (IntRepr (max l))))
      SEP (listrep l p).

Definition push_spec :=
  DECLARE _push
    WITH n: Z, l: list Z, p: val, q: val
    PRE [ _p OF tptr (tptr (Tstruct _list noattr)), _x OF tint ]
      PROP ()
      LOCAL (temp _x (Vint (IntRepr n)); temp _p p)
      SEP (store_list_ptr p q; listrep l q)
    POST [ tvoid ]
      EX q:val,
        PROP ()
        LOCAL ()
        SEP (store_list_ptr p q; listrep (n :: l) q).

Definition pop_spec :=
  DECLARE _pop
    WITH n: Z, l: list Z, p: val, q: val
    PRE [ _p OF tptr (tptr (Tstruct _list noattr)) ]
      PROP ()
      LOCAL (temp _p p)
      SEP (store_list_ptr p q; listrep (n :: l) q)
    POST [ tint ]
      EX q:val,
        PROP ()
        LOCAL (temp ret_temp (Vint (IntRepr n)))
        SEP (store_list_ptr p q; listrep l q).

Definition enqueue_spec :=
  DECLARE _enqueue
    WITH n: Z, s: list Z, l: val
    PRE [ _l OF tptr (Tstruct _queue noattr), _x OF tint ]
      PROP ()
      LOCAL (temp _x (Vint (IntRepr n)); temp _l l)
      SEP (qrep s l)
    POST [ tvoid ]
      PROP ()
      LOCAL ()
      SEP (qrep (s ++ singleton n) l).

Definition dequeue_spec :=
  DECLARE _dequeue
    WITH n: Z, s: list Z, l: val
    PRE [ _l OF tptr (Tstruct _queue noattr) ]
      PROP ()
      LOCAL (temp _l l)
      SEP (qrep (n :: s) l)
    POST [ tint ]
      PROP ()
      LOCAL (temp ret_temp (Vint (IntRepr n)))
      SEP (qrep s l).

Definition merge_spec :=
  DECLARE _merge
    WITH s1: list Z, s2: list Z, x: val, y: val
    PRE [ _x OF tptr (Tstruct _list noattr), _y OF tptr (Tstruct _list noattr) ]
      PROP (all_nonneg s1; all_nonneg s2)
      LOCAL (temp _x x; temp _y y)
      SEP (listrep s1 x; listrep s2 y)
    POST [ tptr (Tstruct _list noattr) ]
      EX s3: list Z, EX r:val,
        PROP (merge_rel s1 s2 s3)
        LOCAL (temp ret_temp r)
        SEP (listrep s3 r).

Definition split_rec_spec :=
  DECLARE _split_rec
    WITH l: list Z, l1: list Z, l2: list Z,
      x: val, p: val, q: val, p0: val, q0: val
    PRE [ _x OF tptr (Tstruct _list noattr),
          _p OF tptr (tptr (Tstruct _list noattr)),
          _q OF tptr (tptr (Tstruct _list noattr)) ]
      PROP (all_nonneg l; all_nonneg l1; all_nonneg l2)
      LOCAL (temp _x x; temp _p p; temp _q q)
      SEP (store_list_ptr p p0; store_list_ptr q q0;
        listrep l x; listrep l1 p0; listrep l2 q0)
    POST [ tvoid ]
      EX s1: list Z, EX s2: list Z, EX p0: val, EX q0: val,
        PROP (split_rec l l1 l2 s1 s2)
        LOCAL ()
        SEP (store_list_ptr p p0; store_list_ptr q q0;
          listrep s1 p0; listrep s2 q0).

Definition merge_sort_rec_spec :=
  DECLARE _merge_sort_rec
    WITH l: list Z, x: val, p: val, q: val
    PRE [ _x OF tptr (Tstruct _list noattr),
          _p OF tptr (tptr (Tstruct _list noattr)),
          _q OF tptr (tptr (Tstruct _list noattr)) ]
      PROP (all_nonneg l)
      LOCAL (temp _x x; temp _p p; temp _q q)
      SEP (store_list_ptr_ p; store_list_ptr_ q; listrep l x)
    POST [ tptr (Tstruct _list noattr) ]
      EX l0: list Z, EX r: val,
        PROP (merge_sort l l0)
        LOCAL (temp ret_temp r)
        SEP (store_list_ptr_ p; store_list_ptr_ q;
          listrep l0 r).

Definition merge_sort_spec :=
  DECLARE _merge_sort
    WITH l: list Z, x: val
    PRE [ _x OF tptr (Tstruct _list noattr) ]
      PROP (all_nonneg l)
      LOCAL (temp _x x)
      SEP (listrep l x)
    POST [ tptr (Tstruct _list noattr) ]
      EX l0: list Z, EX r: val,
        PROP (increasing l0; Permutation l l0)
        LOCAL (temp ret_temp r)
        SEP (listrep l0 r).

Definition reverse1_spec :=
  DECLARE _reverse1 reverse_pre_post.

Definition reverse2_spec :=
  DECLARE _reverse2 reverse_pre_post.

Definition merge_alter_pre_post :=
  WITH s1: list Z, s2: list Z, x: val, y: val
  PRE [ _x OF tptr (Tstruct _list noattr), _y OF tptr (Tstruct _list noattr) ]
    PROP (all_nonneg s1; increasing s1; all_nonneg s2; increasing s2)
    LOCAL (temp _x x; temp _y y)
    SEP (listrep s1 x; listrep s2 y)
  POST [ tptr (Tstruct _list noattr) ]
    EX s3: list Z, EX r: val,
      PROP (Permutation (s1 ++ s2) s3; increasing s3)
      LOCAL (temp ret_temp r)
      SEP (listrep s3 r).

Definition merge_alter_proof_spec :=
  DECLARE _merge_alter_proof merge_alter_pre_post.

Definition merge_alter_spec_spec :=
  DECLARE _merge_alter_spec merge_alter_pre_post.

Definition Gprog : funspecs :=
  ltac:(with_library prog [malloc_list_cell_spec; free_list_cell_spec; malloc_list_2p_spec; free_list_2p_spec; reverse_spec; append_spec; append_2p_spec; append2_spec; rev_append_spec; max_spec; push_spec; pop_spec; enqueue_spec; dequeue_spec; merge_spec; split_rec_spec; merge_sort_rec_spec; merge_sort_spec; reverse1_spec; reverse2_spec; merge_alter_proof_spec; merge_alter_spec_spec]).

Theorem f_reverse_functionally_correct :
  semax_body Vprog Gprog f_reverse reverse_spec.
Proof.
  start_function.
  forward.
  forward.
  forward_while (EX w v l1 l2,
    PROP (l = rev l1 ++ l2)
    LOCAL (temp _w w; temp _v v)
    SEP (listrep l1 w; listrep l2 v)).
  - Exists nullval p (@nil Z) l.
    entailer!.
    unfold listrep. entailer!.
  - entailer!.
  - sep_apply (listrep_isptr l2 v).
    Intros a l2b t.
    do 4 forward.
    Exists (v, t, a :: l1, l2b).
    entailer!.
    + simpl. rewrite <- app_assoc. reflexivity.
    + sep_apply store_listrep. entailer!.
  - forward.
    Exists w. entailer!.
    sep_apply listrep_null. Intros.
    subst. rewrite app_nil_r. rewrite rev_involutive.
    entailer!.
Qed.

Theorem f_append_functionally_correct :
  semax_body Vprog Gprog f_append append_spec.
Proof.
  start_function.
  forward_if.
  - forward.
    Exists y. entailer!.
    sep_apply listrep_null. Intros.
    subst. simpl. entailer!.
  - sep_apply listrep_is_not_null.
    Intros a s1' x'.
    forward.
    forward_if.
    + subst. forward.
      forward.
      Exists x. entailer!.
      sep_apply listrep_null. Intros.
      subst. sep_apply store_listrep.
      simpl. entailer!.
    + forward. forward.
      forward_while (EX u t s1a b s1c,
        PROP (s1a ++ b :: s1c = s1)
        LOCAL (temp _x x; temp _y y; temp _u u; temp _t t)
        SEP (lseg s1a x t; store_list_cell t b u; listrep s1c u; listrep s2 y)
      ).
      { Exists x' x (@nil Z) a s1'.
        entailer!.
        unfold lseg. entailer!. }
      { entailer!. }
      { forward.
        sep_apply listrep_is_not_null. Intros c s1d w.
        forward.
        Exists (w, u, s1a ++ b :: nil, c, s1d).
        entailer!.
        { rewrite <- H2. rewrite <- app_assoc.
          reflexivity. }
        { sep_apply lseg_store.
          entailer!. }
      }
      forward.
      forward.
      Exists x. sep_apply listrep_null.
      entailer!.
      sep_apply store_listrep.
      sep_apply lseg_listrep.
      rewrite <- H2.
      rewrite <- app_assoc. simpl.
      entailer!.
Qed.

Theorem f_append_2p_functionally_correct:
  semax_body Vprog Gprog f_append_2p append_2p_spec.
Proof.
  start_function.
  forward_call tt.
  Intros ret.
  destruct ret as [t' t].
  simpl fst; simpl snd.
  forward.
  forward.
  forward_loop
    (EX s1a s1b u t y px,
      (PROP (((app s1a s1b) = s1))
      LOCAL (temp _t t; temp _y y; temp _px px)
      SEP ((lbseg s1a px t); (store_list_ptr t u); (listrep s1b u); (listrep s2 y))))
    break: (EX u t y px,
      (PROP ()
      LOCAL (temp _t t; temp _y y; temp _px px)
      SEP ((lbseg s1 px t); (store_list_ptr t u); (listrep s2 y)))).
  - Exists (@nil Z) s1 x t' y t'.
    unfold lbseg.
    entailer!.
  - clear t t'. Intros s1a s1b u t y' px.
    change val in u.
    subst s1.
    forward. forward_if.
    + sep_apply listrep_is_not_null.
      Intros b s1c q.
      forward. forward.
      Exists (s1a ++ b :: nil) s1c q (field_address (Tstruct _list noattr) [StructField _tail] u) y' px.
      entailer!.
      { rewrite <- app_assoc.
        reflexivity. }
      { unfold_data_at (store_list_cell u b q).
        sep_apply lbseg_store.
        entailer!. }
    + forward. subst u.
      sep_apply listrep_null. Intros. subst.
      Exists nullval t y' px.
      entailer!. rewrite app_nil_r. entailer!.
  - clear t t'. Intros u t y' px.
    forward.
    sep_apply lbseg_listrep.
    Intros x'.
    forward.
    forward_call px.
    forward.
    Exists x'. entailer!.
Qed.

Theorem f_append2_functionally_correct :
  semax_body Vprog Gprog f_append2 append2_spec.
Proof.
  start_function.
  forward_if.
  - forward.
    Exists y. entailer!.
    sep_apply listrep_null. Intros.
    subst. simpl. entailer!.
  - sep_apply listrep_is_not_null.
    Intros a s1b z.
    forward.
    forward_if.
    + subst. forward.
      forward.
      Exists x. entailer!.
      sep_apply listrep_null. Intros.
      subst. sep_apply store_listrep.
      simpl. entailer!.
    + forward. forward.
      forward_while (EX a s1b t x y u,
        (PROP ()
        LOCAL (temp _t t; temp _x x; temp _y y; temp _u u)
        SEP ((wand (listrep (app (cons a s1b) s2) t) (listrep (app s1 s2) x)); (store_list_cell t a u); (listrep s1b u); (listrep s2 y)))).
      { sep_apply listrep_is_not_null.
        Intros b s1c w. subst.
        Exists a (b :: s1c) x x y z.
        entailer!.
        unfold listrep at 4; fold listrep.
        Exists w.
        cancel. apply wand_sepcon_adjoint.
        cancel. }
      { entailer!. }
      { sep_apply listrep_is_not_null.
        Intros b s1c w.
        forward. forward.
        Exists (b, s1c, u, x0, y0, w).
        entailer!. cancel.
        rewrite <- wand_sepcon_adjoint.
        sep_apply store_listrep.
        rewrite sepcon_comm, -> wand_sepcon_adjoint.
        simpl app.
        entailer!.
      }
      forward.
      forward.
      Exists x0. sep_apply listrep_null.
      entailer!.
      sep_apply store_listrep.
      simpl app. rewrite sepcon_comm, -> wand_sepcon_adjoint.
      entailer!.
Qed.

Theorem f_rev_append_functionally_correct :
  semax_body Vprog Gprog f_rev_append rev_append_spec.
Proof.
  start_function.
  forward_if.
  - 
    forward.
    rewrite listrep_null.
    Intros.
    Exists q.
    entailer!.
    simpl.
    entailer!.
  -
    forward.
    sep_apply listrep_is_not_null.
    Intros a l1b q'.
    forward.
    forward.
    forward_while 
      (EX (a : Z) (l1b l1c : list Z) (p w v q : val),
        PROP (l1 = ((a :: rev l1b) ++ l1c))
        LOCAL (temp _p p; temp _w w; temp _v v; temp _q q)
        SEP (store_list_cell p a nullval; lseg l1b w p; listrep l1c v; listrep l2 q)).
    *
      Exists a (@nil Z) l1b p p q' q.
      entailer!.
      unfold lseg.
      entailer.
    *
      entailer!.
    *
      sep_apply listrep_isptr.
      Intros c l1d v'.
      forward.
      forward.
      forward.
      forward.
      Exists (a0, (c :: l1b0), l1d, p0, v, v', q0).
      entailer!.
      { rewrite H1.
        simpl.
        rewrite <- app_assoc.
        reflexivity. }
      { sep_apply store_lseg.
        entailer!.
      }
    *
      subst v.
      sep_apply listrep_null.
      Intros.
      forward.
      forward.
      Exists w.
      sep_apply store_listrep.
      sep_apply lseg_listrep.
      simpl rev.
      rewrite app_nil_r in H1.
      inversion H1;subst.
      rewrite rev_involutive, <- app_assoc.
      entailer!.
Qed.


Theorem f_max_functionally_correct :
  semax_body Vprog Gprog f_max max_spec.
Proof.
  start_function.
  forward.
  forward_while 
    (EX (l1 l2 : list Z) (r0 : Z) (p0 r : val),
      PROP (r = Vint (IntRepr r0); r0 <= Int.max_signed; 0 <= r0; 
      max l = max_aux l2 r0; l = (l1 ++ l2); all_nonneg l2)
      LOCAL (temp _p p0; temp _r r)  SEP (lseg l1 p p0; listrep l2 p0)).
  -
    Exists (@nil Z) l 0 p (Vint (IntRepr 0)).
    entailer!.
    unfold lseg.
    entailer!.
  -
    entailer!.
  -
    subst r.
    sep_apply listrep_isptr.
    Intros a l2b q.
    subst l2.
    simpl in H5.
    destruct H5.
    forward. 
    forward_if (
      PROP ( )
      LOCAL (temp _t'1 (Vint (IntRepr a)); temp _p p0; 
            temp _r (Vint (IntRepr (Z.max r0 a))))
      SEP (store_list_cell p0 a q; listrep l2b q; lseg l1 p p0)).
    *
      forward.
      entailer!.
      assert (Z.max r0 a = a) by lia.
      rewrite H4.
      tauto.
    *
      forward.
      entailer!.
      assert (Z.max r0 a = r0) by lia.
      rewrite H4.
      tauto.
    *
      forward.
      Exists ((l1 ++ a :: nil), l2b, (Z.max r0 a),
                   q, (Vint (IntRepr (Z.max r0 a)))).
      entailer!.
      +
        split.
        { lia. }
        split.
        { lia. }
        rewrite <- app_assoc.
        reflexivity.
      +
        sep_apply lseg_store.
        entailer!.
  -
    forward.
    sep_apply listrep_null.
    Intros.
    subst l2.
    simpl in H3.
    subst r0.
    rewrite app_nil_r.
    entailer!.
    sep_apply lseg_nullval_ending.
    entailer!.
Qed.


Theorem f_push_functionally_correct :
  semax_body Vprog Gprog f_push push_spec.
Proof.
  start_function.
  Intros.
  forward_call tt.
  Intros p1.
  forward.
  simpl.
  forward.
  forward.
  forward.
  Exists p1.
  entailer!.
  unfold listrep; fold listrep.
  Exists q.
  entailer!.
Qed.

Theorem f_pop_functionally_correct :
  semax_body Vprog Gprog f_pop pop_spec.
Proof.
  start_function.
  unfold listrep; fold listrep.
  Intros y.
  forward.
  forward.
  forward.
  forward.
  forward_call q.
  forward.
  Exists y.
  entailer!.
Qed.

Theorem f_enqueue_functionally_correct :
  semax_body Vprog Gprog f_enqueue enqueue_spec.
Proof.
  start_function.
  unfold qrep at 1.
  Intros l1 l2 q1 q2.
  unfold_data_at (store_queue l q1 q2).
  forward_call (n, l2, field_address (Tstruct _queue noattr) [StructField _l2] l, q2).
  { entailer!. f_equal. 
    unfold field_address; simpl;
    (rewrite if_true by auto with field_compatible || fail 1 "Not enough field_compatible information to derive the equality.");
    rewrite ? isptr_offset_val_zero; auto.
  }
  Intros q2'.
  change val in q2'.
  entailer!.
  unfold qrep.
  Exists l1 (n :: l2) q1 q2'.
  entailer!.
  + simpl.
    rewrite app_assoc.
    reflexivity.
  + unfold_data_at (store_queue l q1 q2').
    entailer!.
Qed.

Theorem f_dequeue_functionally_correct :
  semax_body Vprog Gprog f_dequeue dequeue_spec.
Proof.
  start_function.
  unfold qrep.
  Intros l1 l2 q1 q2.
  forward. 
  forward_if
  (EX q1' q2' l1' l2',
    PROP (n :: l1' ++ rev l2' = n :: s)
    LOCAL (temp _l l)
    SEP (listrep (n :: l1') q1'; listrep l2' q2'; store_queue l q1' q2')).
  -
    subst q1.
    sep_apply listrep_null.
    Intros.
    subst l1.
    forward.
    forward_call (q2, l2).
    Intros q2'.
    forward.
    forward.
    forward.
    simpl in H.
    Exists q2' (Vint (IntRepr 0)) s (@nil Z).
    entailer!.
    + rewrite app_nil_r.
      reflexivity.
    + rewrite H.
      entailer!.
      unfold listrep.
      entailer!.
  -
    sep_apply listrep_is_not_null.
    Intros a l1b q1'.
    subst l1.
    simpl in H.
    inversion H;subst.
    forward.
    Exists q1 q2 l1b l2.
    entailer!.
    unfold listrep;fold listrep.
    Exists q1'.
    entailer!.
  -
    Intros q1' q2' l1' l2'.
    unfold_data_at (store_queue l q1' q2').
    forward_call (n, l1', field_address (Tstruct _queue noattr) [StructField _l1] l, q1').
    { entailer!. f_equal.
      unfold field_address; simpl;
      (rewrite if_true by auto with field_compatible || fail 1 "Not enough field_compatible information to derive the equality.");
      rewrite ? isptr_offset_val_zero; auto.
    }
    Intros ret.
    forward.
    unfold qrep.
    Exists l1' l2' ret q2'.
    entailer!.
    + inversion H0;subst.
      reflexivity.
    +
      unfold_data_at (store_queue l ret q2').
      entailer!.
Qed.

Theorem f_merge_functionally_correct :
  semax_body Vprog Gprog f_merge merge_spec.
Proof.
  start_function.
  forward_call tt.
  Intros ret.
  destruct ret as [pret p2].
  simpl fst; simpl snd.
  forward.
  forward_loop
    (EX (l1 l2 l3 : list Z) 
      (u : reptype (tptr (Tstruct _list noattr))) 
      (t x y pret  : val),
    PROP (merge_steps s1 s2 [] l1 l2 l3; all_nonneg l2; all_nonneg l1)
    LOCAL (temp _t t; temp _x x; temp _y y; temp _pret pret)
    SEP (lbseg l3 pret t; listrep l1 x; 
        listrep l2 y; store_list_ptr t u))
    
  break:
    (EX (b:bool) (l1 l2 l3 : list Z) 
      (t x y pret : val)
      (p' : reptype (tptr (Tstruct _list noattr))),
      PROP (merge_steps s1 s2 [] 
              (if b then [] else l1) 
              (if b then l2 else []) l3;
            all_nonneg (if b then l2 else l1))
      LOCAL (temp _t t; temp _x (if b then nullval else x); 
             temp _y (if b then y else nullval); temp _pret pret)
      SEP (store_list_ptr pret p';
          listrep (l3 ++ (if b then l2 else l1)) p')
    ).
  -
    Exists s1 s2 (@nil Z) p2 pret x y pret.
    entailer!.
    + unfold merge_steps; reflexivity.
    + unfold lbseg.
      entailer!.
  -
    Intros l1 l2 l3 u t x0 y0 pret0.
    change val in u.
    forward_if.
    {
      subst.
      sep_apply listrep_null.
      Intros.
      subst l1.
      forward.
      forward.
      Exists true (@nil Z) l2 l3 t x y0 pret0.
      sep_apply lbseg_listrep.
      Intros p'.
      Exists p'.
      entailer!.
    }
    forward_if.
    {
      subst.
      sep_apply listrep_null.
      Intros.
      subst l2.
      forward.
      forward.
      Exists false l1 (@nil Z) l3 t x0 y pret0.
      sep_apply lbseg_listrep.
      Intros p'.
      Exists p'.
      entailer!.
    }

    sep_apply (listrep_is_not_null l1 x0).
    Intros a1 l1' x'.
    subst l1.
    sep_apply (listrep_is_not_null l2 y0).
    Intros a2 l2' y'.
    subst l2.
    simpl in H2, H3.
    forward.
    forward.
    forward_if.
    +
      forward.
      forward.
      forward.
      Exists l1' (a2 :: l2') (l3 ++ [a1])
         x'
         (field_address (Tstruct _list noattr) [StructField _tail] x0)
         x' y0 pret0.
      entailer!.
      ++ split.
        -- unfold merge_steps.
          transitivity_n1 (a1 :: l1', a2 :: l2', l3).
          * tauto.
          * constructor.
            lia.
        -- tauto.
      ++ unfold_data_at (store_list_cell x0 a1 x').
          sep_apply lbseg_store.
          unfold listrep; fold listrep.
          Exists y'.
          entailer!.
    + 
      forward.
      forward.
      forward.
      Exists (a1 :: l1') l2' (l3 ++ [a2])
        y'
        (field_address (Tstruct _list noattr) [StructField _tail] y0)
        x0 y' pret0.
      entailer!.
      ++ split.
        -- unfold merge_steps.
          transitivity_n1 (a1 :: l1', a2 :: l2', l3).
          * tauto.
          * constructor.
            lia.
        -- tauto.
      ++ unfold_data_at (store_list_cell y0 a2 y').
        sep_apply lbseg_store.
        unfold listrep; fold listrep.
        Exists x'.
        entailer!.
  - 
    Intros b l1 l2 l3 t x0 y0 pret0 ret'.
    destruct b.
    +
      forward.
      forward_call pret0.
      forward.
      Exists (l3 ++ l2) ret'.
      entailer!.
      apply merge_r. tauto.
    +
      forward.
      forward_call pret0.
      forward.
      Exists (l3 ++ l1) ret'.
      entailer!.
      apply merge_l. tauto.
Qed.


Theorem f_split_rec_functionally_correct :
  semax_body Vprog Gprog f_split_rec split_rec_spec.
Proof.
  start_function.
  forward_if.
  -
    subst x.
    forward.
    sep_apply listrep_null.
    Intros.
    subst l.
    Exists l1 l2 p0 q0.
    entailer!.
    constructor.
  -
    sep_apply listrep_is_not_null.
    Intros a l' x1.
    subst l.
    forward. 
    forward. 
    forward. 
    forward.
    forward_call (l', l2, (a:: l1), x1, q, p, q0, x).
    { entailer!.
      unfold listrep at 2; fold listrep.
      Exists p0.
      entailer!.
    }
    { simpl in H. simpl. tauto. }
    Intros ret.
    destruct ret as [ [ [s2 s1] q0'] p0'].
    simpl in H3.
    simpl fst; simpl snd.
    Exists s1 s2 p0' q0'.
    entailer!.
    constructor.
    auto.
Qed.


Theorem f_merge_sort_rec_functionally_correct :
  semax_body Vprog Gprog f_merge_sort_rec merge_sort_rec_spec.
Proof.
  start_function.
  forward.
  forward.

  forward_call (l, @nil Z, @nil Z, x, p, q, nullval, nullval).
  { unfold listrep; entailer!. }
  Intros ret.
  destruct ret as [ [ [s1 s2] p0] q0].
  simpl in H0; simpl fst; simpl snd.
  forward. 
  forward. 
  forward_if. 
  +
    subst q0.
    sep_apply listrep_null.
    Intros.
    subst s2.
    forward.
    Exists s1 p0.
    entailer!.
    apply merge_sort_base.
    tauto.
  +
    sep_apply (listrep_is_not_null_no_expand s2).
    Intros s2a s2b. 
    rename H2 into s2_not_nil. 
    clear H1.
    pose proof split_rel_all_nonneg _ _ _ H0.
    forward_call (s1, p0, p, q).
    { tauto. }
    Intros ret.
    destruct ret as [s1' p1].
    simpl in H2.
    simpl fst; simpl snd.
    forward_call (s2, q0, p, q).
    { tauto. }
    Intros ret.
    destruct ret as [s2' p2].
    simpl in H3.
    simpl fst; simpl snd.
    pose proof merge_sort_all_nonneg _ _ H2.
    pose proof merge_sort_all_nonneg _ _ H3.
    forward_call (s1', s2', p1, p2).
    { tauto. }
    Intros ret.
    destruct ret as [s r].
    simpl fst; simpl snd; simpl in H6.
    forward.
    Exists s r.
    entailer!.
    pose proof merge_sort_rec _ _ _ s1' s2' s H0.
    apply H9; auto.
    congruence.
Qed.

Theorem f_merge_sort_functionally_correct :
  semax_body Vprog Gprog f_merge_sort merge_sort_spec.
Proof.
  start_function.
  forward_call tt.
  Intros ret.
  destruct ret as [p0 ptr_p].
  forward_call tt.
  Intros ret.
  destruct ret as [q0 ptr_q].
  simpl fst; simpl snd.
  forward_call (l, x, p0, q0).
  Intros ret.
  destruct ret as [l0 x0'].
  simpl in H0.
  simpl fst; simpl snd.
  forward_call p0.
  forward_call q0.
  forward.
  Exists l0 x0'.
  entailer!.
  split.
  + pose proof merge_sort_increasing _ _ H0.
    tauto.
  + pose proof merge_sort_perm _ _ H0.
    tauto.
Qed.

Theorem f_reverse1_functionally_correct :
  semax_body Vprog Gprog f_reverse1 reverse1_spec.
Proof.
  start_function.
  forward.
  forward.
  forward_while 
    (EX (l1 l2 : list Z) (w v : val),
      PROP (l = (rev l1 ++ l2))
      LOCAL (temp _w w; temp _v v)  
      SEP (listrep l1 w; listrep l2 v)).
  -
    Exists (@nil Z) l nullval p.
    entailer!.
    unfold listrep.
    entailer!.
  -
    entailer!.
  -
    sep_apply (listrep_isptr l2 v).
    Intros a l2b t.
    forward.
    forward.
    forward.
    forward.
    Exists ( a :: l1, l2b, v, t).
    entailer!.
    + simpl. rewrite <- app_assoc. reflexivity.
    + sep_apply store_listrep. entailer!.
  -
    forward.
    sep_apply listrep_null.
    Intros.
    subst l2.
    Exists w.
    entailer!.
    rewrite app_nil_r, rev_involutive.
    entailer!.
Qed.


Theorem f_reverse2_functionally_correct :
  semax_body Vprog Gprog f_reverse2 reverse2_spec.
Proof.
  start_function.
  forward.
  forward.
  forward_while 
    (EX (l1 : list Z) (w : val) (l2 : list Z) (v: val),
      PROP (l = (rev l1 ++ l2))
      LOCAL (temp _w w; temp _v v)  
      SEP (listrep l1 w; listrep l2 v)).
  -
    Exists (@nil Z) nullval l p.
    entailer!.
    unfold listrep.
    entailer!.
  -
    entailer!.
  -
    sep_apply (listrep_isptr l2 v).
    Intros a l2b t.
    forward.
    forward.
    forward.
    forward.
    Exists ( a :: l1, v, l2b, t).
    entailer!.
    + simpl. rewrite <- app_assoc. reflexivity.
    + sep_apply store_listrep. entailer!.
  -
    forward.
    sep_apply listrep_null.
    Intros.
    subst l2.
    Exists w.
    entailer!.
    rewrite app_nil_r, rev_involutive.
    entailer!.
Qed.


Theorem f_merge_alter_proof_functionally_correct :
  semax_body Vprog Gprog f_merge_alter_proof merge_alter_proof_spec.
Proof.
  start_function.
  forward_call tt.
  Intros ret.
  destruct ret as [pret p2].
  simpl fst; simpl snd.
  forward.
  forward_loop
    (EX (l1 l2 l3 : list Z) 
      (u : reptype (tptr (Tstruct _list noattr))) 
      (t x y pret : val),
    PROP (Permutation (s1 ++ s2) (l3 ++ (l1 ++ l2));
          all_nonneg l2; increasing (l3 ++ l2); 
          all_nonneg l1; increasing (l3 ++ l1))
    LOCAL (temp _t t; temp _x x; temp _y y; temp _pret pret)
    SEP (lbseg l3 pret t; listrep l1 x; 
          listrep l2 y; store_list_ptr t u))
  
  break:
    (EX (b:bool) (l1 l2 l3 : list Z) 
      (t x y pret : val)
      (p' : reptype (tptr (Tstruct _list noattr))),
      PROP (Permutation (s1 ++ s2) (l3 ++ (if b then l2 else l1));
            all_nonneg (if b then l2 else l1); 
            increasing (l3 ++ l2);
            increasing (l3 ++ l1))
      LOCAL (temp _t t; temp _x (if b then nullval else x); 
             temp _y (if b then y else nullval); temp _pret pret)
      SEP (store_list_ptr pret p';
          listrep (l3 ++ (if b then l2 else l1)) p')
    ).
  -
    Exists s1 s2 (@nil Z) p2 pret x y pret.
    entailer!.
    + unfold lbseg.
      entailer!.
  -
    Intros l1 l2 l3 u t x0 y0 pret0.
    change val in u.
    forward_if.
    {
      subst.
      sep_apply listrep_null.
      Intros.
      subst l1.
      forward.
      forward.
      Exists true (@nil Z) l2 l3 t x y0 pret0.
      sep_apply lbseg_listrep.
      Intros p'.
      Exists p'.
      entailer!.
    }
    forward_if.
    {
      subst.
      sep_apply listrep_null.
      Intros.
      subst l2.
      forward.
      forward.
      Exists false l1 (@nil Z) l3 t x0 y pret0.
      sep_apply lbseg_listrep.
      Intros p'.
      Exists p'.
      entailer!.
      rewrite app_nil_r in H3.
      tauto.
    }

    sep_apply (listrep_is_not_null l1 x0).
    Intros a1 l1' x'.
    subst l1.
    sep_apply (listrep_is_not_null l2 y0).
    Intros a2 l2' y'.
    subst l2.
    simpl in H4, H6.
    forward.
    forward.
    forward_if.
    +
      forward.
      forward.
      forward.
      Exists l1' (a2 :: l2') (l3 ++ [a1])
         x'
         (field_address (Tstruct _list noattr) [StructField _tail] x0)
         x' y0 pret0.
      entailer!.
      ++ split; [| split; [| split] ].
        -- rewrite H3.
          simpl.
          rewrite <- !app_assoc.
          reflexivity.
        -- rewrite <- app_assoc.
          apply increasing_app_cons.
          * apply increasing_app_cons_inv1 in H7.
            tauto.
          * split;[lia|].
            apply increasing_app_cons_inv2 in H5.
            tauto.
        -- tauto.
        -- rewrite <- app_assoc.
          tauto.
      ++ unfold_data_at (store_list_cell x0 a1 x').
          sep_apply lbseg_store.
          unfold listrep; fold listrep.
          Exists y'.
          entailer!.
    + 
      forward.
      forward.
      forward.
      Exists (a1 :: l1') l2' (l3 ++ [a2])
        y'
        (field_address (Tstruct _list noattr) [StructField _tail] y0)
        x0 y' pret0.
      entailer!.
      ++ split; [| split; [| split] ].
        -- rewrite H3.
          rewrite <- !app_assoc.  
          apply Permutation_app; [reflexivity |].
          rewrite Permutation_app_comm.
          simpl.
          apply perm_skip.
          rewrite Permutation_app_comm.
          reflexivity.
        -- tauto.
        -- rewrite <- app_assoc.
            tauto.
        
        -- rewrite <- app_assoc.
          simpl.
          apply increasing_app_cons.
          * eapply increasing_app_cons_inv1.
            apply H5.
          * apply increasing_app_cons_inv2 in H7.
            split; [lia | tauto].
      ++ unfold_data_at (store_list_cell y0 a2 y').
        sep_apply lbseg_store.
        unfold listrep; fold listrep.
        Exists x'.
        entailer!.
  - 
    Intros b l1 l2 l3 t x0 y0 pret0 ret'.
    destruct b.
    +
      forward.
      forward_call pret0.
      forward.
      Exists (l3 ++ l2) ret'.
      entailer!.
    +
      forward.
      forward_call pret0.
      forward.
      Exists (l3 ++ l1) ret'.
      entailer!.
Qed.


Theorem f_merge_alter_spec_functionally_correct :
  semax_body Vprog Gprog f_merge_alter_spec merge_alter_spec_spec.
Proof.
  start_function.
  forward_call tt.
  Intros ret.
  destruct ret as [pret p2].
  simpl fst; simpl snd.
  forward.
  forward_loop
    (EX (l1 l2 l3 : list Z) 
        (u : reptype (tptr (Tstruct _list noattr)))
      (t x y pret : val),
    PROP (merge_steps s1 s2 [] l1 l2 l3; 
          all_nonneg l2; increasing s2;
          all_nonneg l1; increasing s1)
    LOCAL (temp _t t; temp _x x; temp _y y; temp _pret pret)
    SEP (lbseg l3 pret t; listrep l1 x; 
          listrep l2 y; store_list_ptr t u))

  break:
    (EX (b:bool) (l1 l2 l3 : list Z) 
      (t x y pret : val)
      (p' : reptype (tptr (Tstruct _list noattr))),
      PROP (merge_steps s1 s2 [] 
              (if b then [] else l1) 
              (if b then l2 else []) l3;
            all_nonneg l2;
            all_nonneg l1;
            increasing s2;
            increasing s1)
      LOCAL (temp _t t; temp _x (if b then nullval else x); 
            temp _y (if b then y else nullval); temp _pret pret)
      SEP (store_list_ptr pret p';
          listrep (l3 ++ (if b then l2 else l1)) p')
    ).
  -
    Exists s1 s2 (@nil Z) p2 pret x y pret.
    entailer!.
    + unfold merge_steps; reflexivity.
    + unfold lbseg.
      entailer!.
  -
    Intros l1 l2 l3 u t x0 y0 pret0.
    change val in u.
    forward_if.
    {
      subst.
      sep_apply listrep_null.
      Intros.
      subst l1.
      forward.
      forward.
      Exists true (@nil Z) l2 l3 t x y0 pret0.
      sep_apply lbseg_listrep.
      Intros p'.
      Exists p'.
      entailer!.
    }
    forward_if.
    {
      subst.
      sep_apply listrep_null.
      Intros.
      subst l2.
      forward.
      forward.
      Exists false l1 (@nil Z) l3 t x0 y pret0.
      sep_apply lbseg_listrep.
      Intros p'.
      Exists p'.
      entailer!.
    }

    sep_apply (listrep_is_not_null l1 x0).
    Intros a1 l1' x'.
    subst l1.
    sep_apply (listrep_is_not_null l2 y0).
    Intros a2 l2' y'.
    subst l2.
    simpl in H4, H5.
    forward.
    forward.
    forward_if.
    +
      forward.
      forward.
      forward.
      Exists l1' (a2 :: l2') (l3 ++ [a1])
        x'
        (field_address (Tstruct _list noattr) [StructField _tail] x0)
        x' y0 pret0.
      entailer!.
      ++ split.
        -- unfold merge_steps.
          transitivity_n1 (a1 :: l1', a2 :: l2', l3).
          * tauto.
          * constructor.
            lia.
        -- tauto.
      ++ unfold_data_at (store_list_cell x0 a1 x').
          sep_apply lbseg_store.
          unfold listrep; fold listrep.
          Exists y'.
          entailer!.
    + 
      forward.
      forward.
      forward.
      Exists (a1 :: l1') l2' (l3 ++ [a2])
        y'
        (field_address (Tstruct _list noattr) [StructField _tail] y0)
        x0 y' pret0.
      entailer!.
      ++ split.
        -- unfold merge_steps.
          transitivity_n1 (a1 :: l1', a2 :: l2', l3).
          * tauto.
          * constructor.
            lia.
        -- tauto.
      ++ unfold_data_at (store_list_cell y0 a2 y').
        sep_apply lbseg_store.
        unfold listrep; fold listrep.
        Exists x'.
        entailer!.
  - 
    Intros b l1 l2 l3 t x0 y0 pret0 ret'.
    destruct b.
    +
      forward.
      forward_call pret0.
      forward.
      Exists (l3 ++ l2) ret'.
      entailer!.
      pose proof merge_steps_increasing _ _ _ _ _ _ H3.
      simpl in H6.
      pose proof merge_steps_perm _ _ _ _ _ _ H3.
      simpl in H7.
      tauto.
    +
      forward.
      forward_call pret0.
      forward.
      Exists (l3 ++ l1) ret'.
      entailer!.
      pose proof merge_steps_increasing _ _ _ _ _ _ H3.
      simpl in H6.
      pose proof merge_steps_perm _ _ _ _ _ _ H3.
      simpl in H7.
      rewrite app_nil_r in H7.
      tauto.
  Qed.


