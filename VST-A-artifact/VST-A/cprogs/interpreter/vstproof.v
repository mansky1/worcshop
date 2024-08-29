Require Import VST.floyd.proofauto.
Require Import Lia.
Require Import cprogs.interpreter.program.
Require Import cprogs.interpreter.definitions.

Definition malloc_cont_list_spec :=
  DECLARE _malloc_cont_list
    WITH _: unit
    PRE [ ]
      PROP ()
      LOCAL ()
      SEP ()
    POST [ tptr tvoid ]
      EX r: val,
        PROP ()
        LOCAL (temp ret_temp r)
        SEP (store_cont_list_ r).

Definition free_cont_list_spec :=
  DECLARE _free_cont_list
    WITH p: val
    PRE [ 18%positive OF tptr (Tstruct _cont_list noattr) ]
      PROP ()
      LOCAL (temp 18%positive p)
      SEP (store_cont_list_ p)
    POST [ tvoid ]
      PROP ()
      LOCAL ()
      SEP ().

Definition free_cmd_spec :=
  DECLARE _free_cmd
    WITH p: val
    PRE [ 18%positive OF tptr (Tstruct _cmd noattr) ]
      PROP ()
      LOCAL (temp 18%positive p)
      SEP (store_cmd_ p)
    POST [ tvoid ]
      PROP ()
      LOCAL ()
      SEP ().

Definition free_expr_spec :=
  DECLARE _free_expr
    WITH p: val
    PRE [ 18%positive OF tptr (Tstruct _expr noattr) ]
      PROP ()
      LOCAL (temp 18%positive p)
      SEP (store_expr_ p)
    POST [ tvoid ]
      PROP ()
      LOCAL ()
      SEP ().

Definition exit_spec :=
  DECLARE _exit
    WITH code: val
    PRE [ 19%positive OF tint ]
      PROP (code = Vint (IntRepr 1))
      LOCAL (temp 19%positive code)
      SEP ()
    POST [ tvoid ]
      PROP (False)
      LOCAL ()
      SEP ().

Definition hash_table_get_spec :=
  DECLARE _hash_table_get
    WITH tbl: val
    PRE [ 20%positive OF tptr (Tstruct _hash_table noattr), 22%positive OF (tptr tschar) ]
      PROP ()
      LOCAL (temp 20%positive tbl)
      SEP (hash_table_rep tbl)
    POST [ tuint ]
      EX r:val,
        PROP (tc_val_uint r)
        LOCAL (temp ret_temp r)
        SEP (hash_table_rep tbl).

Definition hash_table_set_spec :=
  DECLARE _hash_table_set
    WITH tbl: val
    PRE [ 20%positive OF tptr (Tstruct _hash_table noattr), 22%positive OF (tptr tschar), 23%positive OF tuint ]
      PROP ()
      LOCAL (temp 20%positive tbl)
      SEP (hash_table_rep tbl)
    POST [ tvoid ]
      PROP ()
      LOCAL ()
      SEP (hash_table_rep tbl).

Definition mem_alloc_spec :=
  DECLARE _mem_alloc
    WITH mem: val
    PRE [ 24%positive OF tptr (Tstruct _memory noattr) ]
      PROP ()
      LOCAL (temp 24%positive mem)
      SEP (memory_rep mem)
    POST [ tuint ]
      EX r:val,
        PROP (tc_val_uint r)
        LOCAL (temp ret_temp r)
        SEP (memory_rep mem).

Definition mem_get_spec :=
  DECLARE _mem_get
    WITH mem: val
    PRE [ 24%positive OF tptr (Tstruct _memory noattr), 26%positive OF tuint ]
      PROP ()
      LOCAL (temp 24%positive mem)
      SEP (memory_rep mem)
    POST [ tuint ]
      EX r:val,
        PROP (tc_val_uint r)
        LOCAL (temp ret_temp r)
        SEP (memory_rep mem).

Definition mem_set_spec :=
  DECLARE _mem_set
    WITH mem: val
    PRE [ 24%positive OF tptr (Tstruct _memory noattr), 26%positive OF tuint, 27%positive OF tuint ]
      PROP ()
      LOCAL (temp 24%positive mem)
      SEP (memory_rep mem)
    POST [ tvoid ]
      PROP ()
      LOCAL ()
      SEP (memory_rep mem).

Definition copy_cmd_spec :=
  DECLARE _copy_cmd
    WITH cmd: val
    PRE [ 11%positive OF tptr (Tstruct _cmd noattr) ]
      PROP ()
      LOCAL (temp 11%positive cmd)
      SEP (cmd_rep cmd)
    POST [ tptr (Tstruct _cmd noattr) ]
      EX r:val,
        PROP ()
        LOCAL (temp ret_temp r)
        SEP (cmd_rep cmd; cmd_rep r).

Definition free_expr_rec_spec :=
  DECLARE _free_expr_rec
    WITH e: val
    PRE [ _e OF tptr (Tstruct _expr noattr) ]
      PROP ()
      LOCAL (temp _e e)
      SEP (expr_rep e)
    POST [ tvoid ]
      PROP ()
      LOCAL ()
      SEP ().

Definition free_cmd_rec_spec :=
  DECLARE _free_cmd_rec
    WITH c: val
    PRE [ _c OF tptr (Tstruct _cmd noattr) ]
      PROP ()
      LOCAL (temp _c c)
      SEP (cmd_rep c)
    POST [ tvoid ]
      PROP ()
      LOCAL ()
      SEP ().

Definition CL_Cons_spec :=
  DECLARE _CL_Cons
    WITH c: val, cont: val
    PRE [ _c OF tptr (Tstruct _cmd noattr), _cont OF tptr (Tstruct _cont_list noattr) ]
      PROP ()
      LOCAL (temp _c c; temp _cont cont)
      SEP (cmd_rep c; cont_list_rep cont)
    POST [ tptr (Tstruct _cont_list noattr) ]
      EX r:val,
        PROP ()
        LOCAL (temp ret_temp r)
        SEP (cont_list_rep r).

Definition eval_spec :=
  DECLARE _eval
    WITH st: val, m: val, expr: val
    PRE [ _state OF tptr (Tstruct _hash_table noattr), _mem OF tptr (Tstruct _memory noattr), _e OF tptr (Tstruct _expr noattr) ]
      PROP ()
      LOCAL (temp _state st; temp _mem m; temp _e expr)
      SEP (hash_table_rep st; memory_rep m; expr_rep expr)
    POST [ tuint ]
      EX r:val,
        PROP (tc_val_uint r)
        LOCAL (temp ret_temp r)
        SEP (hash_table_rep st; memory_rep m; expr_rep expr).

Definition step_spec :=
  DECLARE _step
    WITH st: val, m: val, prog: val
    PRE [ _state OF tptr (Tstruct _hash_table noattr), _mem OF tptr (Tstruct _memory noattr), _r OF tptr (Tstruct _res_prog noattr) ]
      PROP ()
      LOCAL (temp _state st; temp _mem m; temp _r prog)
      SEP (hash_table_rep st; memory_rep m; prog_rep prog)
    POST [ tvoid ]
      PROP ()
      LOCAL ()
      SEP (hash_table_rep st; memory_rep m; prog_rep_or_end prog).

Definition Gprog : funspecs :=
  ltac:(with_library prog [malloc_cont_list_spec; free_cont_list_spec; free_cmd_spec; free_expr_spec; exit_spec; hash_table_get_spec; hash_table_set_spec; mem_alloc_spec; mem_get_spec; mem_set_spec; copy_cmd_spec; free_expr_rec_spec; free_cmd_rec_spec; CL_Cons_spec; eval_spec; step_spec]).

Theorem f_free_expr_rec_functionally_correct:
  semax_body Vprog Gprog f_free_expr_rec free_expr_rec_spec.
Proof.
  start_function.
  set (Post := PROP ()  LOCAL () SEP ()).
  unfold expr_rep. Intros expr.
  destruct expr; simpl expr_rep'; Intros.
  - forward.
    forward_if Post.
    + forward_call e. unfold Post.
      entailer!.
    + discriminate.
    + unfold Post. forward.
  - forward.
    forward_if Post.
    + contradiction.
    + forward_if.
      { forward_call e. unfold Post.
        entailer!. }
      { discriminate. }
    + unfold Post. forward.
  - Intros arg1 arg2.
    forward.
    forward_if Post.
    + contradiction.
    + forward_if.
      { contradiction. }
      { forward_if.
        { forward. forward.
          forward_call e.
          forward_call arg1.
          { unfold expr_rep. Exists expr1.
            cancel. }
          forward_call arg2.
          { unfold expr_rep. Exists expr2.
            cancel. }
          unfold Post. entailer!. }
        { discriminate. } }
    + unfold Post. forward.
  - Intros arg.
    forward.
    forward_if Post.
    + contradiction.
    + forward_if.
      { contradiction. }
      { forward_if.
        { contradiction. }
        { forward_if.
          { forward.
            forward_call e.
            forward_call arg.
            { unfold expr_rep. Exists expr.
              cancel. }
            unfold Post. entailer!. }
        { discriminate. } } }
    + unfold Post. forward.
  - forward.
    forward_if Post.
    + contradiction.
    + forward_if.
      { contradiction. }
      { forward_if.
        { contradiction. }
        { forward_if.
          { contradiction. }
          { forward_if.
            { forward_call e.
              unfold Post. entailer!. }
            { discriminate. } } } }
    + unfold Post. forward.
Qed.

Theorem f_free_cmd_rec_functionally_correct:
  semax_body Vprog Gprog f_free_cmd_rec free_cmd_rec_spec.
Proof.
  start_function.
  set (Post := PROP ()  LOCAL () SEP ()).
  unfold cmd_rep. Intros cmd.
  destruct cmd; simpl cmd_rep'; Intros.
  - forward.
    forward_if Post.
    + forward_call c. unfold Post.
      entailer!.
    + discriminate.
    + unfold Post. forward.
  - Intros arg1 arg2.
    forward.
    forward_if Post.
    + contradiction.
    + forward_if.
      { forward. forward.
        forward_call c.
        forward_call arg1.
        { unfold expr_rep. Exists e1.
          cancel. }
        forward_call arg2.
        { unfold expr_rep. Exists e2.
          cancel. }
        unfold Post.
        entailer!. }
      { discriminate. }
    + unfold Post. forward.
  - Intros sub1 sub2.
    forward.
    forward_if Post.
    + contradiction.
    + forward_if.
      { contradiction. }
      { forward_if.
        { forward. forward.
          forward_call c.
          forward_call sub1.
          { unfold cmd_rep. Exists cmd1.
            cancel. }
          forward_call sub2.
          { unfold cmd_rep. Exists cmd2.
            cancel. }
          unfold Post. entailer!. }
        { discriminate. } }
    + unfold Post. forward.
  - Intros arg sub1 sub2.
    forward.
    forward_if Post.
    + contradiction.
    + forward_if.
      { contradiction. }
      { forward_if.
        { contradiction. }
        { forward_if.
          { forward. forward.
            forward.
            forward_call c.
            forward_call arg.
            { unfold expr_rep. Exists cond.
              cancel. }
            forward_call sub1.
            { unfold cmd_rep. Exists cmd1.
              cancel. }
            forward_call sub2.
            { unfold cmd_rep. Exists cmd2.
              cancel. }
            unfold Post. entailer!. }
        { discriminate. } } }
    + unfold Post. forward.
  - Intros arg sub.
    forward.
    forward_if Post.
    + contradiction.
    + forward_if.
      { contradiction. }
      { forward_if.
        { contradiction. }
        { forward_if.
          { contradiction. }
          { forward_if.
            { forward. forward.
              forward_call c.
              forward_call arg.
              { unfold expr_rep. Exists cond.
                cancel. }
              forward_call sub.
              { unfold cmd_rep. Exists cmd.
                cancel. }
              unfold Post. entailer!. }
            { discriminate. } } } }
    + unfold Post. forward.
Qed.

Theorem f_CL_Cons_functionally_correct:
  semax_body Vprog Gprog f_CL_Cons CL_Cons_spec.
Proof.
  start_function.
  forward_call tt.
  Intros ret.
  forward.
  forward.
  forward.
  Exists ret. entailer!.
  sep_apply store_cont_list_rep.
  entailer!.
Qed.

Theorem f_eval_functionally_correct:
  semax_body Vprog Gprog f_eval eval_spec.
Proof.
  start_function.
  set (Post := EX r:val,
    PROP (tc_val_uint r)
    LOCAL (temp ret_temp r)
    SEP (hash_table_rep st; memory_rep m; expr_rep expr)).
  unfold expr_rep. Intros e.
  destruct e; simpl expr_rep'; Intros.
  - forward.
    forward_if Post.
    + forward. forward.
      Exists (Vint (IntRepr v)).
      entailer!. sep_apply const_expr_rep.
      entailer!.
    + discriminate.
    + unfold Post. Intros r. forward.
      Exists (Vint (IntRepr 0)).
      entailer!.
  - forward.
    forward_if Post.
    + contradiction.
    + forward_if.
      { forward.
        forward_call st.
        Intros ret.
        forward. Exists (Vint ret).
        sep_apply var_expr_rep.
        entailer!. }
      { discriminate. }
    + unfold Post. Intros r.
      forward. Exists (Vint (IntRepr 0)).
      entailer!.
  - Intros arg1 arg2.
    forward.
    forward_if Post.
    + contradiction.
    + forward_if.
      { contradiction. }
      { forward_if.
        { forward. forward.
          forward.
          forward_call (st, m, arg1).
          { unfold expr_rep. Exists e1.
            cancel. }
          Intros ret.
          forward_if.
          { forward_if.
            { forward_call (st, m, arg2).
              { unfold expr_rep. Exists e2.
                cancel. }
              Intros ret1.
              forward. Exists (Vint ret1).
              sep_apply expr_rep'_expr_rep.
              sep_apply binop_expr_rep.
              entailer!. }
            { forward. Exists (Vint (IntRepr 0)).
              sep_apply expr_rep'_expr_rep.
              sep_apply binop_expr_rep.
              entailer!. } }
          { forward_if.
            { forward_if.
              { forward. Exists (Vint (IntRepr 1)).
                sep_apply expr_rep'_expr_rep.
                sep_apply binop_expr_rep.
                entailer!. }
              { forward_call (st, m, arg2).
                { unfold expr_rep. Exists e2.
                  cancel. }
                Intros ret1. forward.
                Exists (Vint ret1).
                sep_apply expr_rep'_expr_rep.
                sep_apply binop_expr_rep.
                entailer!. } }
            { forward_if.
              { forward_call (st, m, arg2).
                { unfold expr_rep at 2. Exists e2.
                  cancel. }
                Intros ret1.
                forward. Exists (Vint (Int.add ret ret1)).
                sep_apply binop_expr_rep.
                entailer!. }
              { forward_if.
                { forward_call (st, m, arg2).
                  { unfold expr_rep at 2. Exists e2.
                    cancel. }
                  Intros ret1.
                  forward. Exists (Vint (Int.sub ret ret1)).
                  sep_apply binop_expr_rep.
                  entailer!. }
                { forward_if.
                  { forward_call (st, m, arg2).
                    { unfold expr_rep at 2. Exists e2.
                      cancel. }
                    Intros ret1.
                    forward. Exists (Vint (Int.mul ret ret1)).
                    sep_apply binop_expr_rep.
                    entailer!. }
                  { forward_if.
                    { forward_call (st, m, arg2).
                      { unfold expr_rep at 2. Exists e2.
                        cancel. }
                      Intros ret1.
                      forward_if.
                      { forward. Exists (Vint (IntRepr 0)).
                        sep_apply binop_expr_rep.
                        entailer!. }
                      { forward.
                        { entailer!. discriminate. }
                        { Exists (Vint (Int.divu ret ret1)).
                          sep_apply binop_expr_rep.
                          entailer!. } } }
                    { forward_if.
                      { forward_call (st, m, arg2).
                        { unfold expr_rep at 2. Exists e2.
                          cancel. }
                        Intros ret1.
                        forward_if.
                        { forward. Exists (Vint (IntRepr 0)).
                          sep_apply binop_expr_rep.
                          entailer!. }
                        { forward.
                          { entailer!. discriminate. }
                          { Exists (Vint (Int.modu ret ret1)).
                            sep_apply binop_expr_rep.
                            entailer!. } } }
                      { forward_if.
                        { forward_call (st, m, arg2).
                          { unfold expr_rep at 2. Exists e2.
                            cancel. }
                          Intros ret1.
                          forward_if.
                          { forward. Exists (Vint (IntRepr 1)).
                            sep_apply binop_expr_rep.
                            entailer!. }
                          { forward. Exists (Vint (IntRepr 0)).
                            sep_apply binop_expr_rep.
                            entailer!. } }
                        { forward_if.
                          { forward_call (st, m, arg2).
                            { unfold expr_rep at 2. Exists e2.
                              cancel. }
                            Intros ret1.
                            forward_if.
                            { forward. Exists (Vint (IntRepr 1)).
                              sep_apply binop_expr_rep.
                              entailer!. }
                            { forward. Exists (Vint (IntRepr 0)).
                              sep_apply binop_expr_rep.
                              entailer!. } }
                          { destruct op; contradiction. } } } } } } } } } }
        { discriminate. } }
    + unfold Post. Intros r.
      forward. Exists (Vint (IntRepr 0)).
      entailer!.
  - Intros arg.
    forward.
    forward_if Post.
    + contradiction.
    + forward_if.
      { contradiction. }
      { forward_if.
        { contradiction. }
        { forward_if.
          { forward.
            forward_call (st, m, arg).
            { unfold expr_rep. Exists e.
              cancel. }
            Intros ret.
            forward_call m.
            Intros ret1.
            forward. Exists (Vint ret1).
            sep_apply deref_expr_rep.
            entailer!. }
        { discriminate. } } }
    + unfold Post. Intros r.
      forward. Exists (Vint (IntRepr 0)).
      entailer!.
  - forward.
    forward_if Post.
    + contradiction.
    + forward_if.
      { contradiction. }
      { forward_if.
        { contradiction. }
        { forward_if.
          { contradiction. }
          { forward_if.
            { forward_call m.
              Intros ret.
              forward. Exists (Vint ret).
              sep_apply malloc_expr_rep.
              entailer!. }
            { discriminate. } } } }
    + unfold Post. Intros r.
      forward. Exists (Vint (IntRepr 0)).
      entailer!.
Qed.

Theorem f_step_functionally_correct:
  semax_body Vprog Gprog f_step step_spec.
Proof.
  start_function.
  set (Post :=
    PROP ()
    LOCAL ()
    SEP (hash_table_rep st; memory_rep m; prog_rep_or_end prog)).
  unfold prog_rep. Intros pr.
  destruct pr; simpl prog_rep'; Intros. 
  { Intros foc ectx.
    forward.
    forward_if Post.
    { subst. sep_apply cmd_rep'_local_facts.
      Intros. contradiction. }
    { forward.
      set (Post' :=
        PROP ()
        LOCAL (temp _c foc)
        SEP (hash_table_rep st; memory_rep m; prog_rep_or_end prog; store_cmd_ foc)).
      destruct c; simpl cmd_rep'; Intros.
      - forward.
        forward_if Post'.
        + forward. unfold Post'.
          sep_apply cont_list_rep'_cont_list_rep.
          change (Vint (IntRepr 0)) with nullval.
          sep_apply ectx_prog_rep_or_end.
          entailer!.
        + discriminate.
        + unfold Post', Post.
          forward_call foc.
          entailer!.
      - Intros arg1 arg2.
        forward.
        forward_if Post'.
        + contradiction.
        + forward_if.
          { forward. forward.
            set (Post'' :=
              PROP ()
              LOCAL (temp _c foc; temp _arg1 arg1; temp _arg2 arg2; temp _r prog)
              SEP (hash_table_rep st; memory_rep m; store_cmd_ foc; store_expr_ arg1; expr_rep arg2; store_res_prog prog foc ectx; cont_list_rep ectx)).
            destruct e1; simpl expr_rep'; Intros;
              sep_apply expr_rep'_expr_rep;
              sep_apply cont_list_rep'_cont_list_rep.
            { forward.
              forward_if Post''.
              { contradiction. }
              { forward_if.
                { contradiction. }
                { forward_call (Vint (IntRepr 1)).
                  contradiction. } }
              { unfold Post''.
                forward_call arg1.
                forward_call arg2.
                forward.
                unfold Post'.
                change (Vint (IntRepr 0)) with nullval.
                sep_apply ectx_prog_rep_or_end.
                entailer!. } }
            { forward.
              forward_if Post''.
              { forward.
                forward_call (st, m, arg2).
                Intros ret.
                forward_call st.
                unfold Post''.
                entailer!. }
              { discriminate. }
              { unfold Post''.
                forward_call arg1.
                forward_call arg2.
                forward.
                unfold Post'.
                change (Vint (IntRepr 0)) with nullval.
                sep_apply ectx_prog_rep_or_end.
                entailer!. } }
            { Intros arg3 arg4.
              forward.
              forward_if Post''.
              { contradiction. }
              { forward_if.
                { contradiction. }
                { forward_call (Vint (IntRepr 1)).
                  contradiction. } }
              { unfold Post''.
                forward_call arg1.
                forward_call arg2.
                forward.
                unfold Post'.
                change (Vint (IntRepr 0)) with nullval.
                sep_apply ectx_prog_rep_or_end.
                entailer!. } }
            { Intros arg3.
              forward.
              forward_if Post''.
              { contradiction. }
              { forward_if.
                { forward.
                  sep_apply expr_rep'_expr_rep.
                  forward_call (st, m, arg3).
                  Intros ret.
                  forward_call (st, m, arg2).
                  Intros ret1.
                  forward_call m.
                  forward_call arg3.
                  unfold Post''. entailer!. }
                { discriminate. } }
              { unfold Post''.
                forward_call arg1.
                forward_call arg2.
                forward.
                unfold Post'.
                change (Vint (IntRepr 0)) with nullval.
                sep_apply ectx_prog_rep_or_end.
                entailer!. } }
            { forward.
              forward_if Post''.
              { contradiction. }
              { forward_if.
                { contradiction. }
                { forward_call (Vint (IntRepr 1)).
                  contradiction. } }
              { unfold Post''.
                forward_call arg1.
                forward_call arg2.
                forward.
                unfold Post'.
                change (Vint (IntRepr 0)) with nullval.
                sep_apply ectx_prog_rep_or_end.
                entailer!. } } }
          { discriminate. }
        + unfold Post', Post.
          forward_call foc.
          entailer!.
      - Intros sub1 sub2.
        forward.
        forward_if Post'.
        + contradiction.
        + forward_if.
          { contradiction. }
          { forward_if.
            { forward. forward.
              forward. forward.
              repeat sep_apply cmd_rep'_cmd_rep.
              sep_apply cont_list_rep'_cont_list_rep.
              forward_call (sub2, ectx).
              Intros ret.
              forward.
              unfold Post'.
              sep_apply foc_prog_rep_or_end.
              entailer!. }
            { discriminate. } }
        + unfold Post', Post.
          forward_call foc.
          entailer!.
      - Intros arg sub1 sub2.
        forward.
        forward_if Post'.
        + contradiction.
        + forward_if.
          { contradiction. }
          { forward_if.
            { contradiction. }
            { forward_if.
              { forward.
                sep_apply expr_rep'_expr_rep.
                repeat sep_apply cmd_rep'_cmd_rep.
                forward_call (st, m, arg).
                Intros ret.
                forward. forward.
                forward_if (
                  PROP ( )
                  LOCAL (temp _arg1 arg; temp _c foc)
                  SEP (hash_table_rep st; memory_rep m; prog_rep_or_end prog; expr_rep arg; store_cmd_ foc)).
                { forward.
                  forward_call sub2.
                  sep_apply cont_list_rep'_cont_list_rep.
                  sep_apply foc_prog_rep_or_end.
                  entailer!. }
                { forward.
                  forward_call sub1.
                  sep_apply cont_list_rep'_cont_list_rep.
                  sep_apply foc_prog_rep_or_end.
                  entailer!. }
                { forward_call arg.
                  unfold Post'. entailer!. } }
            { discriminate. } } }
        + unfold Post', Post.
          forward_call foc.
          entailer!.
      - Intros arg sub.
        forward.
        forward_if Post'.
        + contradiction.
        + forward_if.
          { contradiction. }
          { forward_if.
            { contradiction. }
            { forward_if.
              { contradiction. }
              { forward_if.
                { forward.
                  sep_apply expr_rep'_expr_rep.
                  sep_apply cmd_rep'_cmd_rep.
                  sep_apply cont_list_rep'_cont_list_rep.
                  forward_call (st, m, arg).
                  Intros ret.
                  forward_if.
                  { forward.
                    forward_call sub.
                    Intros ret1.
                    forward. forward.
                    sep_apply while_cmd_rep.
                    forward_call (foc, ectx).
                    Intros ret2.
                    forward. forward.
                    sep_apply foc_prog_rep_or_end.
                    entailer!. }
                  { forward. forward.
                    forward_call arg.
                    forward_call sub.
                    unfold Post'.
                    change (Vint (IntRepr 0)) with nullval.
                    sep_apply ectx_prog_rep_or_end.
                    entailer!. } }
                { discriminate. } } } }
        + unfold Post', Post.
          forward_call foc.
          entailer!. }
        { unfold Post. forward. } }
  { Intros ectx cp link.
    forward.
    forward_if Post.
    { forward. forward.
      forward. forward.
      forward.
      forward_call ectx.
      unfold Post.
      sep_apply cmd_rep'_cmd_rep.
      sep_apply cont_list_rep'_cont_list_rep.
      sep_apply foc_prog_rep_or_end.
      entailer!. }
    { discriminate. }
    { unfold Post. forward. } }
Qed.
