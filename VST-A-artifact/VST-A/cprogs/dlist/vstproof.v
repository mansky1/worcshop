Require Import VST.floyd.proofauto.
Require Import Lia.
Require Import cprogs.dlist.program.
Require Import cprogs.dlist.definitions.

Definition malloc_list_cell_spec :=
  DECLARE _malloc_list_cell
    WITH _: unit
    PRE [ ]
      PROP ()
      LOCAL ()
      SEP ()
    POST [ tptr (Tstruct _list noattr) ]
      EX r:val,
        PROP ()
        LOCAL (temp ret_temp r)
        SEP (store_list_cell_ r).

Definition free_list_cell_spec :=
  DECLARE _free_list_cell
    WITH p: val
    PRE [ 9%positive OF tptr (Tstruct _list noattr) ]
      PROP ()
      LOCAL (temp 9%positive p)
      SEP (store_list_cell_ p)
    POST [ tvoid ]
      PROP ()
      LOCAL ()
      SEP ().

Definition reverse_spec :=
  DECLARE _reverse
    WITH l: list Z, p: val
    PRE [ _p OF tptr (Tstruct _list noattr) ]
      PROP ()
      LOCAL (temp _p p)
      SEP (listrep l p)
    POST [ tptr (Tstruct _list noattr) ]
      EX r:val,
        PROP ()
        LOCAL (temp ret_temp r)
        SEP (listrep (rev l) r).

Definition append_spec :=
  DECLARE _append
    WITH l1: list Z, l2: list Z, x: val, y: val
    PRE [ _x OF tptr (Tstruct _list noattr), _y OF tptr (Tstruct _list noattr) ]
      PROP ()
      LOCAL (temp _x x; temp _y y)
      SEP (listrep l1 x; listrep l2 y)
    POST [ tptr (Tstruct _list noattr) ]
      EX r:val,
        PROP ()
        LOCAL (temp ret_temp r)
        SEP (listrep (l1 ++ l2) r).

Definition enqueue_spec :=
  DECLARE _enqueue
    WITH x: Z, s: list Z, l: val
    PRE [ _l OF tptr (Tstruct _listbox noattr), _x OF tuint ]
      PROP ()
      LOCAL (temp _x (Vint (IntRepr x)); temp _l l)
      SEP (lbrep s l)
    POST [ tvoid ]
      PROP ()
      LOCAL ()
      SEP (lbrep (s ++ singleton x) l).

Definition dequeue_spec :=
  DECLARE _dequeue
    WITH x: Z, s: list Z, l: val
    PRE [ _l OF tptr (Tstruct _listbox noattr) ]
      PROP ()
      LOCAL (temp _l l)
      SEP (lbrep (x :: s) l)
    POST [ tuint ]
        PROP ()
        LOCAL (temp ret_temp (Vint (IntRepr x)))
        SEP (lbrep s l).

Definition Gprog : funspecs :=
  ltac:(with_library prog [malloc_list_cell_spec; free_list_cell_spec; reverse_spec; append_spec; enqueue_spec; dequeue_spec]).

Theorem f_reverse_functionally_correct:
  semax_body Vprog Gprog f_reverse reverse_spec.
Proof.
  start_function.
  forward.
  forward.
  forward_while (EX w v l1 l2,
    PROP (l = rev l1 ++ l2)
    LOCAL (temp _w w; temp _v v)
    SEP (listrep_pre l1 w v; listrep_pre l2 v w)
  ).
  - Exists nullval p (@nil Z) l.
    entailer!.
    unfold listrep.
    simpl listrep_pre. entailer!.
  - entailer!.
  - sep_apply (listrep_pre_isptr l2).
    Intros a l2b t.
    forward. forward.
    forward. forward.
    forward.
    Exists (v, t, a :: l1, l2b).
    entailer!.
    + simpl. rewrite <- app_assoc. reflexivity.
    + unfold listrep_pre; fold listrep_pre.
      Exists w. entailer!.
  - forward.
    Exists w. entailer!.
    sep_apply listrep_pre_null.
    Intros.
    entailer!.
    rewrite app_nil_r, rev_involutive.
    unfold listrep. entailer!.
Qed.

Theorem f_append_functionally_correct:
  semax_body Vprog Gprog f_append append_spec.
Proof.
  start_function.
  forward_if.
  - forward.
    Exists y.
    unfold listrep.
    sep_apply listrep_pre_null.
    entailer!. simpl app.
    entailer!.
  - forward.
    unfold listrep.
    sep_apply listrep_pre_is_not_null.
    Intros z l3 w.
    forward.
    forward_while (EX x y t u l4 l5 a b,
      PROP (l4 ++ a :: l5 = z :: l3;
        l1 = z :: l3)
      LOCAL (temp _t t; temp _x x; temp _y y; temp _u u)
      SEP (lseg_pre l4 x t nullval b;
        listrep_pre l5 u t;
        store_list_cell t a u b;
        listrep_pre l2 y nullval)
    ).
    + Exists x y x w (@nil Z) l3 z nullval.
      entailer!.
      unfold lseg_pre.
      entailer!.
    + entailer!.
    + forward.
      sep_apply (listrep_pre_is_not_null l5).
      Intros c l6 q.
      forward.
      Exists (x0, y0, u, q, l4 ++ [a], l6, c, t).
      entailer!.
      { rewrite <- H1.
        rewrite <- app_assoc. reflexivity. }
      { sep_apply singleton_lseg_pre.
        rewrite sepcon_comm.
        sep_apply lseg_pre_lseg_pre.
        entailer!. }
    + forward.
      forward_if (EX r:val,
        PROP ()
        LOCAL (temp _x r)
        SEP (listrep (l1 ++ l2) r)).
      { sep_apply (listrep_pre_is_not_null l2).
        Intros x1 l' q.
        forward.
        Exists x0.
        entailer!.
        sep_apply singleton_lseg_pre.
        sep_apply lseg_pre_listrep_pre_app.
        sep_apply singleton_lseg_pre.
        sep_apply (lseg_pre_lseg_pre l4 [a]).
        sep_apply lseg_pre_listrep_pre_app.
        sep_apply listrep_pre_null.
        Intros. subst. rewrite H1.
        unfold listrep.
        simpl app.
        entailer!. }
      { forward.
        Exists x0. entailer!.
        rewrite <- H1.
        sep_apply listrep_pre_null.
        sep_apply listrep_pre_null.
        Intros. subst.
        rewrite app_nil_r.
        entailer!.
        sep_apply singleton_lseg_pre.
        unfold listrep.
        sep_apply lseg_pre_listrep_pre.
        sep_apply lseg_pre_listrep_pre_app.
        entailer!. }
      { Intros r.
        forward.
        Exists r.
        entailer!. }
Qed.

Theorem f_enqueue_functionally_correct:
  semax_body Vprog Gprog f_enqueue enqueue_spec.
Proof.
  start_function.
  forward_call tt.
  Intros r.
  unfold lbrep.
  Intros p q.
  forward. forward.
  forward_if.
  - forward. forward.
    forward. forward.
    subst p.
    sep_apply lseg_pre_null.
    Intros. subst s.
    entailer!.
    simpl app.
    unfold lbrep.
    Exists r r.
    unfold singleton.
    unfold lseg_pre.
    Exists nullval.
    entailer!.
  - forward.
    sep_apply (lseg_pre_neq_tail).
    Intros b s1a u.
    forward. forward.
    forward. forward.
    forward.
    entailer!. unfold singleton.
    unfold lbrep; unfold lseg_pre; fold lseg_pre.
    Exists p r.
    sep_apply lseg_pre_store.
    sep_apply lseg_pre_store.
    change (Vint (IntRepr 0)) with nullval.
    entailer!.
Qed.

Theorem f_dequeue_functionally_correct:
  semax_body Vprog Gprog f_dequeue dequeue_spec.
Proof.
  start_function.
  unfold lbrep.
  Intros p q.
  unfold lseg_pre; fold lseg_pre.
  Intros u.
  forward. forward.
  forward. forward.
  forward_call p.
  forward.
  forward_if (
    PROP ()
    LOCAL (temp _x (Vint (IntRepr x)))
    SEP (lbrep s l)
  ).
  - forward.
    subst u.
    sep_apply lseg_pre_null.
    Intros. subst s.
    unfold lbrep.
    Exists nullval nullval.
    entailer!.
    unfold lseg_pre. entailer!.
  - sep_apply (lseg_pre_neq_head).
    Intros b s1a v.
    forward. forward.
    unfold lbrep.
    Exists u q.
    entailer!.
    unfold lseg_pre; fold lseg_pre.
    Exists v.
    entailer!.
  - forward.
Qed.
