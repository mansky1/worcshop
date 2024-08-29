Require Import VST.floyd.proofauto.
Require Import Lia.
Require Import cprogs.bst.program.
Require Import cprogs.bst.definitions.

Definition malloc_tree_node_spec :=
  DECLARE _malloc_tree_node
    WITH _: unit
    PRE [ ]
      PROP ()
      LOCAL ()
      SEP ()
    POST [ tptr (Tstruct _tree noattr) ]
      EX r: val,
        PROP ()
        LOCAL (temp ret_temp r)
        SEP (store_tree_cell_ r).

Definition free_tree_node_spec :=
  DECLARE _free_tree_node
    WITH p: val
    PRE [ 7%positive OF tptr (Tstruct _tree noattr) ]
      PROP ()
      LOCAL (temp 7%positive p)
      SEP (store_tree_cell_ p)
    POST [ tvoid ]
      PROP ()
      LOCAL ()
      SEP ().

Definition lookup_spec :=
  DECLARE _lookup
    WITH m: partial_map val, n: Z, p_old: val
    PRE [ _x OF tint, _p OF tptr (Tstruct _tree noattr) ]
      PROP (Int.min_signed <= n <= Int.max_signed)
      LOCAL (temp _x (Vint (IntRepr n)); temp _p p_old)
      SEP (map_rep m p_old)
    POST [ tptr tvoid ]
      EX r:val,
        PROP (r = get nullval m n)
        LOCAL (temp ret_temp r)
        SEP (map_rep m p_old).

Definition insert_spec :=
  DECLARE _insert
    WITH v: val, m: partial_map val, n: Z, b_old: val
    PRE [ _b OF tptr (tptr (Tstruct _tree noattr)), _x OF tint, _value OF tptr tvoid ]
      PROP (is_pointer_or_null v;
        Int.min_signed <= n <= Int.max_signed)
      LOCAL (temp _value v; temp _x (Vint (IntRepr n)); temp _b b_old)
      SEP (mapbox_rep m b_old)
    POST [ tvoid ]
      PROP ()
      LOCAL ()
      SEP (mapbox_rep (update m n v) b_old).

Definition pushdown_left_spec :=
  DECLARE _pushdown_left
    WITH b_old: val, t: val, n: Z, v: val, ta: tree, tb: tree
    PRE [ _b OF tptr (tptr (Tstruct _tree noattr)) ]
      PROP (is_pointer_or_null v;
        Int.min_signed <= n <= Int.max_signed)
      LOCAL (temp _b b_old)
      SEP (store_tree_ptr b_old t;
        store_int (field_address (Tstruct _tree noattr) [StructField _key] t) n;
        store_void_ptr (field_address (Tstruct _tree noattr) [StructField _value] t) v;
        treebox_rep ta (field_address (Tstruct _tree noattr) [StructField _left] t);
        treebox_rep tb (field_address (Tstruct _tree noattr) [StructField _right] t))
    POST [ tvoid ]
      PROP ()
      LOCAL ()
      SEP (treebox_rep (pushdown_left ta tb) b_old).

Definition delete_spec :=
  DECLARE _delete
    WITH m: partial_map val, n: Z, b_old: val
    PRE [ _b OF tptr (tptr (Tstruct _tree noattr)), _x OF tint ]
      PROP (Int.min_signed <= n <= Int.max_signed)
      LOCAL (temp _x (Vint (IntRepr n)); temp _b b_old)
      SEP (mapbox_rep m b_old)
    POST [ tvoid ]
      PROP ()
      LOCAL ()
      SEP (mapbox_rep (remove m n) b_old).

Definition Gprog : funspecs :=
  ltac:(with_library prog [malloc_tree_node_spec; free_tree_node_spec; lookup_spec; insert_spec; pushdown_left_spec; delete_spec]).

Theorem f_lookup_functionally_correct:
  semax_body Vprog Gprog f_lookup lookup_spec.
Proof.
  start_function.
  forward_while (EX t t1 p,
    PROP (Abs t m; BST t;
      Int.min_signed <= n <= Int.max_signed;
      lookup n t1 = lookup n t)
    LOCAL (temp _x (Vint (IntRepr n)); temp _p p)
    SEP (tree_rep t1 p -* tree_rep t p_old;
      tree_rep t1 p)
  ).
  - unfold map_rep. Intros t.
    Exists t t p_old.
    entailer!.
    apply wand_refl_cancel_right.
  - entailer!.
  - sep_apply tree_rep_is_not_null.
    Intros k v tl tr pl pr.
    forward.
    forward_if.
    + forward.
      Exists (t, tl, pl).
      entailer!.
      { rewrite <- H3. simpl.
        simpl_if.
        auto. }
      { cancel.
        rewrite <- wand_sepcon_adjoint.
        sep_apply store_tree_rep. auto.
        apply wand_frame_elim. }
    + forward_if.
      { forward.
        Exists (t, tr, pr).
        entailer!.
        { rewrite <- H3. simpl.
          simpl_if.
          auto. }
        { cancel.
          rewrite <- wand_sepcon_adjoint.
          sep_apply store_tree_rep. auto.
          apply wand_frame_elim. } }
      { forward.
        forward.
        assert (n = k) by lia.
        subst.
        Exists v. entailer!.
        { erewrite <- lookup_relate; eauto.
          rewrite <- H3.
          simpl. simpl_if.
          auto. }
    + unfold map_rep.
      Exists t.
      entailer!.
      sep_apply store_tree_rep. auto.
      apply wand_frame_elim. }
  - forward.
    Exists nullval.
    entailer!.
    + rewrite <- (lookup_relate n t).
      simpl in H3. auto. auto.
    + unfold map_rep.
      Exists t. entailer!.
      rewrite sepcon_comm.
      apply wand_frame_elim.
Qed.

Theorem f_insert_functionally_correct:
  semax_body Vprog Gprog f_insert insert_spec.
Proof.
  start_function.
  forward_loop (EX t t1 b,
    PROP (Abs t m; BST t;
      Int.min_signed <= n <= Int.max_signed;
      is_pointer_or_null v)
    LOCAL (temp _value v; temp _x (Vint (IntRepr n)); temp _b b)
    SEP (treebox_rep (insert n v t1) b -* treebox_rep (insert n v t) b_old;
      treebox_rep t1 b)
  ).
  - unfold mapbox_rep.
    Intros t.
    Exists t t b_old.
    entailer!.
    apply wand_refl_cancel_right.
  - Intros t t1 b.
    unfold treebox_rep at 3.
    Intros p.
    forward.
    forward_if.
    + forward_call tt.
      Intros alloc_p.
      forward. forward.
      forward. forward.
      forward. forward.
      change (Vint (Int.repr 0)) with nullval.
      sep_apply treebox_rep_leaf.
      entailer!.
      unfold mapbox_rep. Exists (insert n v t).
      entailer!.
      { split.
        { apply insert_relate; auto. }
        { apply insert_BST; auto. } }
      { simpl. entailer!.
        apply wand_frame_elim. }
    + sep_apply tree_rep_is_not_null.
      Intros k v0 tl tr pl pr.
      forward.
      forward_if.
      { forward.
        Exists t tl (field_address (Tstruct _tree noattr) [StructField _left] p).
        entailer!.
        simpl treebox_rep.
        simpl_if.
        sep_apply (bst_left_entail tl (insert n v tl) tr k v0 pl pr p b).
        cancel. apply wand_frame_ver. }
      { forward_if.
        { forward.
          Exists t tr (field_address (Tstruct _tree noattr) [StructField _right] p).
          entailer!. simpl treebox_rep.
          simpl_if.
          sep_apply (bst_right_entail tl tr (insert n v tr) k v0 pl pr p b).
          cancel. apply wand_frame_ver. }
        { forward.
          forward.
          assert (k = n) by lia. subst n.
          sep_apply store_tree_rep; auto.
          replace (insert k v (T tl k v0 tr)) with (T tl k v tr).
          sep_apply treerep_treebox_rep. unfold mapbox_rep.
          Exists (insert k v t). entailer!.
          - split. apply insert_relate; auto. apply insert_BST; auto.
          - apply wand_frame_elim.
          - simpl. simpl_if.
            reflexivity. } }
Qed.

Theorem f_pushdown_left_functionally_correct:
  semax_body Vprog Gprog f_pushdown_left pushdown_left_spec.
Proof.
  start_function.
  forward_loop (EX b ta1 tb1 n1 v1,
    PROP (Int.min_signed <= n <= Int.max_signed;
      tc_val_ptr(v))
    LOCAL (temp _b b)
    SEP (treebox_rep (T ta1 n1 v1 tb1) b;
      treebox_rep (pushdown_left ta1 tb1) b -* treebox_rep (pushdown_left ta tb) b_old)
  ).
  - Exists b_old ta tb n v.
    unfold treebox_rep at 3.
    unfold treebox_rep at 1. Intros pa.
    unfold treebox_rep at 1. Intros pb.
    Exists t.
    gather_SEP 1 2 3 5.
    replace_SEP 0 (store_tree_cell t n v pa pb).
    { entailer!. unfold_data_at (store_tree_cell t n v pa pb).
      entailer!. }
    entailer!. sep_apply store_tree_rep; auto.
    cancel. apply wand_refl_cancel_right.
  - Intros b ta1 tb1 n1 v1.
    unfold treebox_rep at 1. Intros p.
    forward.
    unfold tree_rep at 1; fold tree_rep.
    Intros pa pb.
    forward.
    forward_if.
    + subst.
      forward. forward.
      forward_call p.
      forward.
      sep_apply treerep_treebox_rep.
      simpl. entailer!.
      apply wand_frame_elim.
    + sep_apply (tree_rep_is_not_null tb1).
      Intros k v0 tl tr pl pr.
      forward. forward.
      forward. forward.
      forward.
      simpl offset_val.
      simpl pushdown_left.
      Exists (field_address (Tstruct _tree noattr) [StructField _left] pb) ta1 tl n1 v1.
      entailer!.
      sep_apply (store_tree_rep n1 v1 pa pl ta1 tl p); auto.
      sep_apply (bst_left_entail (T ta1 n1 v1 tl) (pushdown_left ta1 tl) tr k v0 p pr pb b).
      cancel. apply wand_frame_ver.
Qed.

Theorem f_delete_functionally_correct:
  semax_body Vprog Gprog f_delete delete_spec.
Proof.
  start_function.
  forward_loop (EX b t t1,
    PROP (Abs t m; BST t;
      Int.min_signed <= n <= Int.max_signed)
    LOCAL (temp _x (Vint (IntRepr n)); temp _b b)
    SEP (treebox_rep t1 b;
      treebox_rep (delete n t1) b -* treebox_rep (delete n t) b_old)
  ).
  - unfold mapbox_rep.
    Intros t.
    Exists b_old t t.
    entailer!.
    apply wand_refl_cancel_right.
  - Intros b t t1.
    unfold treebox_rep at 1.
    Intros p.
    forward.
    forward_if.
    + forward.
      unfold mapbox_rep.
      Exists (delete n t).
      entailer!.
      { split.
        { apply delete_relate; auto. }
        { apply delete_BST; auto. } }
      { sep_apply treebox_rep_E.
        simpl. entailer!.
        apply wand_frame_elim. }
    + sep_apply tree_rep_is_not_null.
      Intros k v tl tr pl pr.
      forward.
      forward_if.
      { forward.
        simpl offset_val.
        Exists (field_address (Tstruct _tree noattr) [StructField _left] p) t tl.
        entailer!.
        simpl delete.
        simpl_if.
        sep_apply (bst_left_entail tl (delete n tl) tr k v pl pr p b).
        cancel. apply wand_frame_ver. }
      { forward_if.
        { forward.
          simpl offset_val.
          Exists (field_address (Tstruct _tree noattr) [StructField _right] p) t tr.
          entailer!.
          simpl delete.
          simpl_if.
          sep_apply (bst_right_entail tl tr (delete n tr) k v pl pr p b).
          cancel. apply wand_frame_ver. }
        { subst t1. simpl delete.
          assert_PROP (is_pointer_or_null p). entailer!.
          forward_call (b, p, k, v, tl, tr).
          { unfold_data_at (store_tree_cell p k v pl pr).
            sep_apply treerep_treebox_rep.
            sep_apply treerep_treebox_rep.
            cancel. }
          forward. assert (k = n) by lia. subst n.
          simpl_if. unfold mapbox_rep.
          Exists (delete k t). entailer!.
          - split.
            apply delete_relate; auto.
            apply delete_BST; auto.
          - apply wand_frame_elim. } }
Qed.
