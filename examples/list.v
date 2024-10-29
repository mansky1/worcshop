From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Local Open Scope Z_scope.

Module Info.
  Definition version := "3.6"%string.
  Definition build_number := ""%string.
  Definition build_tag := ""%string.
  Definition arch := "x86"%string.
  Definition model := "32sse2"%string.
  Definition abi := "standard"%string.
  Definition bitsize := 32.
  Definition big_endian := false.
  Definition source_file := "list.c"%string.
  Definition normalized := false.
End Info.

Definition ___builtin_ais_annot : ident := 7%positive.
Definition ___builtin_annot : ident := 16%positive.
Definition ___builtin_annot_intval : ident := 17%positive.
Definition ___builtin_bswap : ident := 9%positive.
Definition ___builtin_bswap16 : ident := 11%positive.
Definition ___builtin_bswap32 : ident := 10%positive.
Definition ___builtin_bswap64 : ident := 8%positive.
Definition ___builtin_clz : ident := 42%positive.
Definition ___builtin_clzl : ident := 43%positive.
Definition ___builtin_clzll : ident := 44%positive.
Definition ___builtin_ctz : ident := 45%positive.
Definition ___builtin_ctzl : ident := 46%positive.
Definition ___builtin_ctzll : ident := 47%positive.
Definition ___builtin_debug : ident := 59%positive.
Definition ___builtin_fabs : ident := 12%positive.
Definition ___builtin_fmadd : ident := 50%positive.
Definition ___builtin_fmax : ident := 48%positive.
Definition ___builtin_fmin : ident := 49%positive.
Definition ___builtin_fmsub : ident := 51%positive.
Definition ___builtin_fnmadd : ident := 52%positive.
Definition ___builtin_fnmsub : ident := 53%positive.
Definition ___builtin_fsqrt : ident := 13%positive.
Definition ___builtin_membar : ident := 18%positive.
Definition ___builtin_memcpy_aligned : ident := 14%positive.
Definition ___builtin_nop : ident := 58%positive.
Definition ___builtin_read16_reversed : ident := 54%positive.
Definition ___builtin_read32_reversed : ident := 55%positive.
Definition ___builtin_sel : ident := 15%positive.
Definition ___builtin_va_arg : ident := 20%positive.
Definition ___builtin_va_copy : ident := 21%positive.
Definition ___builtin_va_end : ident := 22%positive.
Definition ___builtin_va_start : ident := 19%positive.
Definition ___builtin_write16_reversed : ident := 56%positive.
Definition ___builtin_write32_reversed : ident := 57%positive.
Definition ___compcert_i64_dtos : ident := 27%positive.
Definition ___compcert_i64_dtou : ident := 28%positive.
Definition ___compcert_i64_sar : ident := 39%positive.
Definition ___compcert_i64_sdiv : ident := 33%positive.
Definition ___compcert_i64_shl : ident := 37%positive.
Definition ___compcert_i64_shr : ident := 38%positive.
Definition ___compcert_i64_smod : ident := 35%positive.
Definition ___compcert_i64_smulh : ident := 40%positive.
Definition ___compcert_i64_stod : ident := 29%positive.
Definition ___compcert_i64_stof : ident := 31%positive.
Definition ___compcert_i64_udiv : ident := 34%positive.
Definition ___compcert_i64_umod : ident := 36%positive.
Definition ___compcert_i64_umulh : ident := 41%positive.
Definition ___compcert_i64_utod : ident := 30%positive.
Definition ___compcert_i64_utof : ident := 32%positive.
Definition ___compcert_va_composite : ident := 26%positive.
Definition ___compcert_va_float64 : ident := 25%positive.
Definition ___compcert_va_int32 : ident := 23%positive.
Definition ___compcert_va_int64 : ident := 24%positive.
Definition _append : ident := 72%positive.
Definition _append2 : ident := 75%positive.
Definition _append_2p : ident := 74%positive.
Definition _dequeue : ident := 84%positive.
Definition _enqueue : ident := 83%positive.
Definition _free_list_2p : ident := 63%positive.
Definition _free_list_cell : ident := 61%positive.
Definition _head : ident := 1%positive.
Definition _l : ident := 82%positive.
Definition _l1 : ident := 4%positive.
Definition _l2 : ident := 5%positive.
Definition _list : ident := 2%positive.
Definition _main : ident := 97%positive.
Definition _malloc_list_2p : ident := 62%positive.
Definition _malloc_list_cell : ident := 60%positive.
Definition _max : ident := 79%positive.
Definition _merge : ident := 87%positive.
Definition _merge_alter_proof : ident := 95%positive.
Definition _merge_alter_spec : ident := 96%positive.
Definition _merge_sort : ident := 92%positive.
Definition _merge_sort_rec : ident := 91%positive.
Definition _p : ident := 64%positive.
Definition _p1 : ident := 89%positive.
Definition _pop : ident := 81%positive.
Definition _pret : ident := 85%positive.
Definition _push : ident := 80%positive.
Definition _px : ident := 73%positive.
Definition _q : ident := 76%positive.
Definition _q1 : ident := 90%positive.
Definition _queue : ident := 6%positive.
Definition _r : ident := 78%positive.
Definition _ret : ident := 86%positive.
Definition _rev_append : ident := 77%positive.
Definition _reverse : ident := 68%positive.
Definition _reverse1 : ident := 93%positive.
Definition _reverse2 : ident := 94%positive.
Definition _split_rec : ident := 88%positive.
Definition _t : ident := 66%positive.
Definition _tail : ident := 3%positive.
Definition _u : ident := 71%positive.
Definition _v : ident := 67%positive.
Definition _w : ident := 65%positive.
Definition _x : ident := 69%positive.
Definition _y : ident := 70%positive.
Definition _t'1 : ident := 98%positive.
Definition _t'2 : ident := 99%positive.
Definition _t'3 : ident := 100%positive.

Definition f_reverse := {|
  fn_return := (tptr (Tstruct _list noattr));
  fn_callconv := cc_default;
  fn_params := ((_p, (tptr (Tstruct _list noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_w, (tptr (Tstruct _list noattr))) ::
               (_t, (tptr (Tstruct _list noattr))) ::
               (_v, (tptr (Tstruct _list noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _w (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
  (Ssequence
    (Sset _v (Etempvar _p (tptr (Tstruct _list noattr))))
    (Ssequence
      (Swhile
        (Etempvar _v (tptr (Tstruct _list noattr)))
        (Ssequence
          (Sset _t
            (Efield
              (Ederef (Etempvar _v (tptr (Tstruct _list noattr)))
                (Tstruct _list noattr)) _tail (tptr (Tstruct _list noattr))))
          (Ssequence
            (Sassign
              (Efield
                (Ederef (Etempvar _v (tptr (Tstruct _list noattr)))
                  (Tstruct _list noattr)) _tail
                (tptr (Tstruct _list noattr)))
              (Etempvar _w (tptr (Tstruct _list noattr))))
            (Ssequence
              (Sset _w (Etempvar _v (tptr (Tstruct _list noattr))))
              (Sset _v (Etempvar _t (tptr (Tstruct _list noattr))))))))
      (Sreturn (Some (Etempvar _w (tptr (Tstruct _list noattr))))))))
|}.

Definition f_append := {|
  fn_return := (tptr (Tstruct _list noattr));
  fn_callconv := cc_default;
  fn_params := ((_x, (tptr (Tstruct _list noattr))) ::
                (_y, (tptr (Tstruct _list noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t, (tptr (Tstruct _list noattr))) ::
               (_u, (tptr (Tstruct _list noattr))) :: nil);
  fn_body :=
(Sifthenelse (Ebinop Oeq (Etempvar _x (tptr (Tstruct _list noattr)))
               (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
  (Sreturn (Some (Etempvar _y (tptr (Tstruct _list noattr)))))
  (Ssequence
    (Sset _u
      (Efield
        (Ederef (Etempvar _x (tptr (Tstruct _list noattr)))
          (Tstruct _list noattr)) _tail (tptr (Tstruct _list noattr))))
    (Ssequence
      (Sifthenelse (Ebinop Oeq (Etempvar _u (tptr (Tstruct _list noattr)))
                     (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                     tint)
        (Ssequence
          (Sassign
            (Efield
              (Ederef (Etempvar _x (tptr (Tstruct _list noattr)))
                (Tstruct _list noattr)) _tail (tptr (Tstruct _list noattr)))
            (Etempvar _y (tptr (Tstruct _list noattr))))
          (Sreturn (Some (Etempvar _x (tptr (Tstruct _list noattr))))))
        Sskip)
      (Ssequence
        (Sset _t (Etempvar _x (tptr (Tstruct _list noattr))))
        (Ssequence
          (Sset _u
            (Efield
              (Ederef (Etempvar _t (tptr (Tstruct _list noattr)))
                (Tstruct _list noattr)) _tail (tptr (Tstruct _list noattr))))
          (Ssequence
            (Swhile
              (Ebinop Cop.One (Etempvar _u (tptr (Tstruct _list noattr)))
                (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
              (Ssequence
                (Sset _t (Etempvar _u (tptr (Tstruct _list noattr))))
                (Sset _u
                  (Efield
                    (Ederef (Etempvar _t (tptr (Tstruct _list noattr)))
                      (Tstruct _list noattr)) _tail
                    (tptr (Tstruct _list noattr))))))
            (Ssequence
              (Sassign
                (Efield
                  (Ederef (Etempvar _t (tptr (Tstruct _list noattr)))
                    (Tstruct _list noattr)) _tail
                  (tptr (Tstruct _list noattr)))
                (Etempvar _y (tptr (Tstruct _list noattr))))
              (Sreturn (Some (Etempvar _x (tptr (Tstruct _list noattr))))))))))))
|}.

Definition f_append_2p := {|
  fn_return := (tptr (Tstruct _list noattr));
  fn_callconv := cc_default;
  fn_params := ((_x, (tptr (Tstruct _list noattr))) ::
                (_y, (tptr (Tstruct _list noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t, (tptr (tptr (Tstruct _list noattr)))) ::
               (_px, (tptr (tptr (Tstruct _list noattr)))) ::
               (_t'1, (tptr (tptr (Tstruct _list noattr)))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _malloc_list_2p (Tfunction Tnil
                              (tptr (tptr (Tstruct _list noattr)))
                              cc_default)) nil)
    (Sset _px (Etempvar _t'1 (tptr (tptr (Tstruct _list noattr))))))
  (Ssequence
    (Sset _t (Etempvar _px (tptr (tptr (Tstruct _list noattr)))))
    (Ssequence
      (Sassign
        (Ederef (Etempvar _t (tptr (tptr (Tstruct _list noattr))))
          (tptr (Tstruct _list noattr)))
        (Etempvar _x (tptr (Tstruct _list noattr))))
      (Ssequence
        (Swhile
          (Ebinop Cop.One
            (Ederef (Etempvar _t (tptr (tptr (Tstruct _list noattr))))
              (tptr (Tstruct _list noattr)))
            (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
          (Sset _t
            (Eaddrof
              (Efield
                (Ederef
                  (Ederef (Etempvar _t (tptr (tptr (Tstruct _list noattr))))
                    (tptr (Tstruct _list noattr))) (Tstruct _list noattr))
                _tail (tptr (Tstruct _list noattr)))
              (tptr (tptr (Tstruct _list noattr))))))
        (Ssequence
          (Sassign
            (Ederef (Etempvar _t (tptr (tptr (Tstruct _list noattr))))
              (tptr (Tstruct _list noattr)))
            (Etempvar _y (tptr (Tstruct _list noattr))))
          (Ssequence
            (Sset _x
              (Ederef (Etempvar _px (tptr (tptr (Tstruct _list noattr))))
                (tptr (Tstruct _list noattr))))
            (Ssequence
              (Scall None
                (Evar _free_list_2p (Tfunction
                                      (Tcons
                                        (tptr (tptr (Tstruct _list noattr)))
                                        Tnil) tvoid cc_default))
                ((Etempvar _px (tptr (tptr (Tstruct _list noattr)))) :: nil))
              (Sreturn (Some (Etempvar _x (tptr (Tstruct _list noattr))))))))))))
|}.

Definition f_append2 := {|
  fn_return := (tptr (Tstruct _list noattr));
  fn_callconv := cc_default;
  fn_params := ((_x, (tptr (Tstruct _list noattr))) ::
                (_y, (tptr (Tstruct _list noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t, (tptr (Tstruct _list noattr))) ::
               (_u, (tptr (Tstruct _list noattr))) :: nil);
  fn_body :=
(Sifthenelse (Ebinop Oeq (Etempvar _x (tptr (Tstruct _list noattr)))
               (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
  (Sreturn (Some (Etempvar _y (tptr (Tstruct _list noattr)))))
  (Ssequence
    (Sset _u
      (Efield
        (Ederef (Etempvar _x (tptr (Tstruct _list noattr)))
          (Tstruct _list noattr)) _tail (tptr (Tstruct _list noattr))))
    (Ssequence
      (Sifthenelse (Ebinop Oeq (Etempvar _u (tptr (Tstruct _list noattr)))
                     (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                     tint)
        (Ssequence
          (Sassign
            (Efield
              (Ederef (Etempvar _x (tptr (Tstruct _list noattr)))
                (Tstruct _list noattr)) _tail (tptr (Tstruct _list noattr)))
            (Etempvar _y (tptr (Tstruct _list noattr))))
          (Sreturn (Some (Etempvar _x (tptr (Tstruct _list noattr))))))
        Sskip)
      (Ssequence
        (Sset _t (Etempvar _x (tptr (Tstruct _list noattr))))
        (Ssequence
          (Sset _u
            (Efield
              (Ederef (Etempvar _t (tptr (Tstruct _list noattr)))
                (Tstruct _list noattr)) _tail (tptr (Tstruct _list noattr))))
          (Ssequence
            (Swhile
              (Ebinop Cop.One (Etempvar _u (tptr (Tstruct _list noattr)))
                (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
              (Ssequence
                (Sset _t (Etempvar _u (tptr (Tstruct _list noattr))))
                (Sset _u
                  (Efield
                    (Ederef (Etempvar _t (tptr (Tstruct _list noattr)))
                      (Tstruct _list noattr)) _tail
                    (tptr (Tstruct _list noattr))))))
            (Ssequence
              (Sassign
                (Efield
                  (Ederef (Etempvar _t (tptr (Tstruct _list noattr)))
                    (Tstruct _list noattr)) _tail
                  (tptr (Tstruct _list noattr)))
                (Etempvar _y (tptr (Tstruct _list noattr))))
              (Sreturn (Some (Etempvar _x (tptr (Tstruct _list noattr))))))))))))
|}.

Definition f_rev_append := {|
  fn_return := (tptr (Tstruct _list noattr));
  fn_callconv := cc_default;
  fn_params := ((_p, (tptr (Tstruct _list noattr))) ::
                (_q, (tptr (Tstruct _list noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_w, (tptr (Tstruct _list noattr))) ::
               (_t, (tptr (Tstruct _list noattr))) ::
               (_v, (tptr (Tstruct _list noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Eunop Onotbool (Etempvar _p (tptr (Tstruct _list noattr)))
                 tint)
    (Sreturn (Some (Etempvar _q (tptr (Tstruct _list noattr)))))
    Sskip)
  (Ssequence
    (Sset _w (Etempvar _p (tptr (Tstruct _list noattr))))
    (Ssequence
      (Sset _v
        (Efield
          (Ederef (Etempvar _p (tptr (Tstruct _list noattr)))
            (Tstruct _list noattr)) _tail (tptr (Tstruct _list noattr))))
      (Ssequence
        (Sassign
          (Efield
            (Ederef (Etempvar _p (tptr (Tstruct _list noattr)))
              (Tstruct _list noattr)) _tail (tptr (Tstruct _list noattr)))
          (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
        (Ssequence
          (Swhile
            (Etempvar _v (tptr (Tstruct _list noattr)))
            (Ssequence
              (Sset _t
                (Efield
                  (Ederef (Etempvar _v (tptr (Tstruct _list noattr)))
                    (Tstruct _list noattr)) _tail
                  (tptr (Tstruct _list noattr))))
              (Ssequence
                (Sassign
                  (Efield
                    (Ederef (Etempvar _v (tptr (Tstruct _list noattr)))
                      (Tstruct _list noattr)) _tail
                    (tptr (Tstruct _list noattr)))
                  (Etempvar _w (tptr (Tstruct _list noattr))))
                (Ssequence
                  (Sset _w (Etempvar _v (tptr (Tstruct _list noattr))))
                  (Sset _v (Etempvar _t (tptr (Tstruct _list noattr))))))))
          (Ssequence
            (Sassign
              (Efield
                (Ederef (Etempvar _p (tptr (Tstruct _list noattr)))
                  (Tstruct _list noattr)) _tail
                (tptr (Tstruct _list noattr)))
              (Etempvar _q (tptr (Tstruct _list noattr))))
            (Sreturn (Some (Etempvar _w (tptr (Tstruct _list noattr)))))))))))
|}.

Definition f_max := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_p, (tptr (Tstruct _list noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_r, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _r (Econst_int (Int.repr 0) tint))
  (Ssequence
    (Swhile
      (Etempvar _p (tptr (Tstruct _list noattr)))
      (Ssequence
        (Sifthenelse (Ebinop Ogt
                       (Efield
                         (Ederef (Etempvar _p (tptr (Tstruct _list noattr)))
                           (Tstruct _list noattr)) _head tint)
                       (Etempvar _r tint) tint)
          (Sset _r
            (Efield
              (Ederef (Etempvar _p (tptr (Tstruct _list noattr)))
                (Tstruct _list noattr)) _head tint))
          Sskip)
        (Sset _p
          (Efield
            (Ederef (Etempvar _p (tptr (Tstruct _list noattr)))
              (Tstruct _list noattr)) _tail (tptr (Tstruct _list noattr))))))
    (Sreturn (Some (Etempvar _r tint)))))
|}.

Definition f_push := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_p, (tptr (tptr (Tstruct _list noattr)))) :: (_x, tint) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_px, (tptr (Tstruct _list noattr))) ::
               (_t'1, (tptr (Tstruct _list noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _malloc_list_cell (Tfunction Tnil (tptr (Tstruct _list noattr))
                                cc_default)) nil)
    (Sset _px (Etempvar _t'1 (tptr (Tstruct _list noattr)))))
  (Ssequence
    (Sassign
      (Efield
        (Ederef (Etempvar _px (tptr (Tstruct _list noattr)))
          (Tstruct _list noattr)) _head tint) (Etempvar _x tint))
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _px (tptr (Tstruct _list noattr)))
            (Tstruct _list noattr)) _tail (tptr (Tstruct _list noattr)))
        (Ederef (Etempvar _p (tptr (tptr (Tstruct _list noattr))))
          (tptr (Tstruct _list noattr))))
      (Sassign
        (Ederef (Etempvar _p (tptr (tptr (Tstruct _list noattr))))
          (tptr (Tstruct _list noattr)))
        (Etempvar _px (tptr (Tstruct _list noattr)))))))
|}.

Definition f_pop := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_p, (tptr (tptr (Tstruct _list noattr)))) :: nil);
  fn_vars := nil;
  fn_temps := ((_px, (tptr (Tstruct _list noattr))) :: (_x, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _px
    (Ederef (Etempvar _p (tptr (tptr (Tstruct _list noattr))))
      (tptr (Tstruct _list noattr))))
  (Ssequence
    (Sset _x
      (Efield
        (Ederef (Etempvar _px (tptr (Tstruct _list noattr)))
          (Tstruct _list noattr)) _head tint))
    (Ssequence
      (Sassign
        (Ederef (Etempvar _p (tptr (tptr (Tstruct _list noattr))))
          (tptr (Tstruct _list noattr)))
        (Efield
          (Ederef (Etempvar _px (tptr (Tstruct _list noattr)))
            (Tstruct _list noattr)) _tail (tptr (Tstruct _list noattr))))
      (Ssequence
        (Scall None
          (Evar _free_list_cell (Tfunction
                                  (Tcons (tptr (Tstruct _list noattr)) Tnil)
                                  tvoid cc_default))
          ((Etempvar _px (tptr (Tstruct _list noattr))) :: nil))
        (Sreturn (Some (Etempvar _x tint)))))))
|}.

Definition f_enqueue := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_l, (tptr (Tstruct _queue noattr))) :: (_x, tint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Scall None
  (Evar _push (Tfunction
                (Tcons (tptr (tptr (Tstruct _list noattr)))
                  (Tcons tint Tnil)) tvoid cc_default))
  ((Eaddrof
     (Efield
       (Ederef (Etempvar _l (tptr (Tstruct _queue noattr)))
         (Tstruct _queue noattr)) _l2 (tptr (Tstruct _list noattr)))
     (tptr (tptr (Tstruct _list noattr)))) :: (Etempvar _x tint) :: nil))
|}.

Definition f_dequeue := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_l, (tptr (Tstruct _queue noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t, (tptr (Tstruct _list noattr))) :: (_t'2, tint) ::
               (_t'1, (tptr (Tstruct _list noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Oeq
                 (Efield
                   (Ederef (Etempvar _l (tptr (Tstruct _queue noattr)))
                     (Tstruct _queue noattr)) _l1
                   (tptr (Tstruct _list noattr)))
                 (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Evar _reverse (Tfunction
                           (Tcons (tptr (Tstruct _list noattr)) Tnil)
                           (tptr (Tstruct _list noattr)) cc_default))
          ((Efield
             (Ederef (Etempvar _l (tptr (Tstruct _queue noattr)))
               (Tstruct _queue noattr)) _l2 (tptr (Tstruct _list noattr))) ::
           nil))
        (Sset _t (Etempvar _t'1 (tptr (Tstruct _list noattr)))))
      (Ssequence
        (Sassign
          (Efield
            (Ederef (Etempvar _l (tptr (Tstruct _queue noattr)))
              (Tstruct _queue noattr)) _l1 (tptr (Tstruct _list noattr)))
          (Etempvar _t (tptr (Tstruct _list noattr))))
        (Sassign
          (Efield
            (Ederef (Etempvar _l (tptr (Tstruct _queue noattr)))
              (Tstruct _queue noattr)) _l2 (tptr (Tstruct _list noattr)))
          (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))))
    Sskip)
  (Ssequence
    (Scall (Some _t'2)
      (Evar _pop (Tfunction (Tcons (tptr (tptr (Tstruct _list noattr))) Tnil)
                   tint cc_default))
      ((Eaddrof
         (Efield
           (Ederef (Etempvar _l (tptr (Tstruct _queue noattr)))
             (Tstruct _queue noattr)) _l1 (tptr (Tstruct _list noattr)))
         (tptr (tptr (Tstruct _list noattr)))) :: nil))
    (Sreturn (Some (Etempvar _t'2 tint)))))
|}.

Definition f_merge := {|
  fn_return := (tptr (Tstruct _list noattr));
  fn_callconv := cc_default;
  fn_params := ((_x, (tptr (Tstruct _list noattr))) ::
                (_y, (tptr (Tstruct _list noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_pret, (tptr (tptr (Tstruct _list noattr)))) ::
               (_t, (tptr (tptr (Tstruct _list noattr)))) ::
               (_ret, (tptr (Tstruct _list noattr))) ::
               (_t'1, (tptr (tptr (Tstruct _list noattr)))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _malloc_list_2p (Tfunction Tnil
                              (tptr (tptr (Tstruct _list noattr)))
                              cc_default)) nil)
    (Sset _pret (Etempvar _t'1 (tptr (tptr (Tstruct _list noattr))))))
  (Ssequence
    (Sset _t (Etempvar _pret (tptr (tptr (Tstruct _list noattr)))))
    (Ssequence
      (Sloop
        (Ssequence
          Sskip
          (Ssequence
            (Sifthenelse (Ebinop Oeq
                           (Etempvar _x (tptr (Tstruct _list noattr)))
                           (Ecast (Econst_int (Int.repr 0) tint)
                             (tptr tvoid)) tint)
              (Ssequence
                (Sassign
                  (Ederef (Etempvar _t (tptr (tptr (Tstruct _list noattr))))
                    (tptr (Tstruct _list noattr)))
                  (Etempvar _y (tptr (Tstruct _list noattr))))
                Sbreak)
              Sskip)
            (Ssequence
              (Sifthenelse (Ebinop Oeq
                             (Etempvar _y (tptr (Tstruct _list noattr)))
                             (Ecast (Econst_int (Int.repr 0) tint)
                               (tptr tvoid)) tint)
                (Ssequence
                  (Sassign
                    (Ederef
                      (Etempvar _t (tptr (tptr (Tstruct _list noattr))))
                      (tptr (Tstruct _list noattr)))
                    (Etempvar _x (tptr (Tstruct _list noattr))))
                  Sbreak)
                Sskip)
              (Sifthenelse (Ebinop Olt
                             (Efield
                               (Ederef
                                 (Etempvar _x (tptr (Tstruct _list noattr)))
                                 (Tstruct _list noattr)) _head tint)
                             (Efield
                               (Ederef
                                 (Etempvar _y (tptr (Tstruct _list noattr)))
                                 (Tstruct _list noattr)) _head tint) tint)
                (Ssequence
                  (Sassign
                    (Ederef
                      (Etempvar _t (tptr (tptr (Tstruct _list noattr))))
                      (tptr (Tstruct _list noattr)))
                    (Etempvar _x (tptr (Tstruct _list noattr))))
                  (Ssequence
                    (Sset _t
                      (Eaddrof
                        (Efield
                          (Ederef (Etempvar _x (tptr (Tstruct _list noattr)))
                            (Tstruct _list noattr)) _tail
                          (tptr (Tstruct _list noattr)))
                        (tptr (tptr (Tstruct _list noattr)))))
                    (Sset _x
                      (Efield
                        (Ederef (Etempvar _x (tptr (Tstruct _list noattr)))
                          (Tstruct _list noattr)) _tail
                        (tptr (Tstruct _list noattr))))))
                (Ssequence
                  (Sassign
                    (Ederef
                      (Etempvar _t (tptr (tptr (Tstruct _list noattr))))
                      (tptr (Tstruct _list noattr)))
                    (Etempvar _y (tptr (Tstruct _list noattr))))
                  (Ssequence
                    (Sset _t
                      (Eaddrof
                        (Efield
                          (Ederef (Etempvar _y (tptr (Tstruct _list noattr)))
                            (Tstruct _list noattr)) _tail
                          (tptr (Tstruct _list noattr)))
                        (tptr (tptr (Tstruct _list noattr)))))
                    (Sset _y
                      (Efield
                        (Ederef (Etempvar _y (tptr (Tstruct _list noattr)))
                          (Tstruct _list noattr)) _tail
                        (tptr (Tstruct _list noattr))))))))))
        Sskip)
      (Ssequence
        (Sset _ret
          (Ederef (Etempvar _pret (tptr (tptr (Tstruct _list noattr))))
            (tptr (Tstruct _list noattr))))
        (Ssequence
          (Scall None
            (Evar _free_list_2p (Tfunction
                                  (Tcons (tptr (tptr (Tstruct _list noattr)))
                                    Tnil) tvoid cc_default))
            ((Etempvar _pret (tptr (tptr (Tstruct _list noattr)))) :: nil))
          (Sreturn (Some (Etempvar _ret (tptr (Tstruct _list noattr))))))))))
|}.

Definition f_split_rec := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_x, (tptr (Tstruct _list noattr))) ::
                (_p, (tptr (tptr (Tstruct _list noattr)))) ::
                (_q, (tptr (tptr (Tstruct _list noattr)))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t, (tptr (Tstruct _list noattr))) :: nil);
  fn_body :=
(Sifthenelse (Ebinop Oeq (Etempvar _x (tptr (Tstruct _list noattr)))
               (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
  (Sreturn None)
  (Ssequence
    (Sset _t
      (Efield
        (Ederef (Etempvar _x (tptr (Tstruct _list noattr)))
          (Tstruct _list noattr)) _tail (tptr (Tstruct _list noattr))))
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _x (tptr (Tstruct _list noattr)))
            (Tstruct _list noattr)) _tail (tptr (Tstruct _list noattr)))
        (Ederef (Etempvar _p (tptr (tptr (Tstruct _list noattr))))
          (tptr (Tstruct _list noattr))))
      (Ssequence
        (Sassign
          (Ederef (Etempvar _p (tptr (tptr (Tstruct _list noattr))))
            (tptr (Tstruct _list noattr)))
          (Etempvar _x (tptr (Tstruct _list noattr))))
        (Scall None
          (Evar _split_rec (Tfunction
                             (Tcons (tptr (Tstruct _list noattr))
                               (Tcons (tptr (tptr (Tstruct _list noattr)))
                                 (Tcons (tptr (tptr (Tstruct _list noattr)))
                                   Tnil))) tvoid cc_default))
          ((Etempvar _t (tptr (Tstruct _list noattr))) ::
           (Etempvar _q (tptr (tptr (Tstruct _list noattr)))) ::
           (Etempvar _p (tptr (tptr (Tstruct _list noattr)))) :: nil))))))
|}.

Definition f_merge_sort_rec := {|
  fn_return := (tptr (Tstruct _list noattr));
  fn_callconv := cc_default;
  fn_params := ((_x, (tptr (Tstruct _list noattr))) ::
                (_p, (tptr (tptr (Tstruct _list noattr)))) ::
                (_q, (tptr (tptr (Tstruct _list noattr)))) :: nil);
  fn_vars := nil;
  fn_temps := ((_p1, (tptr (Tstruct _list noattr))) ::
               (_q1, (tptr (Tstruct _list noattr))) ::
               (_t'3, (tptr (Tstruct _list noattr))) ::
               (_t'2, (tptr (Tstruct _list noattr))) ::
               (_t'1, (tptr (Tstruct _list noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sassign
    (Ederef (Etempvar _p (tptr (tptr (Tstruct _list noattr))))
      (tptr (Tstruct _list noattr)))
    (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
  (Ssequence
    (Sassign
      (Ederef (Etempvar _q (tptr (tptr (Tstruct _list noattr))))
        (tptr (Tstruct _list noattr)))
      (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
    (Ssequence
      (Scall None
        (Evar _split_rec (Tfunction
                           (Tcons (tptr (Tstruct _list noattr))
                             (Tcons (tptr (tptr (Tstruct _list noattr)))
                               (Tcons (tptr (tptr (Tstruct _list noattr)))
                                 Tnil))) tvoid cc_default))
        ((Etempvar _x (tptr (Tstruct _list noattr))) ::
         (Etempvar _p (tptr (tptr (Tstruct _list noattr)))) ::
         (Etempvar _q (tptr (tptr (Tstruct _list noattr)))) :: nil))
      (Ssequence
        (Sset _p1
          (Ederef (Etempvar _p (tptr (tptr (Tstruct _list noattr))))
            (tptr (Tstruct _list noattr))))
        (Ssequence
          (Sset _q1
            (Ederef (Etempvar _q (tptr (tptr (Tstruct _list noattr))))
              (tptr (Tstruct _list noattr))))
          (Ssequence
            (Sifthenelse (Ebinop Oeq
                           (Etempvar _q1 (tptr (Tstruct _list noattr)))
                           (Ecast (Econst_int (Int.repr 0) tint)
                             (tptr tvoid)) tint)
              (Sreturn (Some (Etempvar _p1 (tptr (Tstruct _list noattr)))))
              Sskip)
            (Ssequence
              (Ssequence
                (Scall (Some _t'1)
                  (Evar _merge_sort_rec (Tfunction
                                          (Tcons
                                            (tptr (Tstruct _list noattr))
                                            (Tcons
                                              (tptr (tptr (Tstruct _list noattr)))
                                              (Tcons
                                                (tptr (tptr (Tstruct _list noattr)))
                                                Tnil)))
                                          (tptr (Tstruct _list noattr))
                                          cc_default))
                  ((Etempvar _p1 (tptr (Tstruct _list noattr))) ::
                   (Etempvar _p (tptr (tptr (Tstruct _list noattr)))) ::
                   (Etempvar _q (tptr (tptr (Tstruct _list noattr)))) :: nil))
                (Sset _p1 (Etempvar _t'1 (tptr (Tstruct _list noattr)))))
              (Ssequence
                (Ssequence
                  (Scall (Some _t'2)
                    (Evar _merge_sort_rec (Tfunction
                                            (Tcons
                                              (tptr (Tstruct _list noattr))
                                              (Tcons
                                                (tptr (tptr (Tstruct _list noattr)))
                                                (Tcons
                                                  (tptr (tptr (Tstruct _list noattr)))
                                                  Tnil)))
                                            (tptr (Tstruct _list noattr))
                                            cc_default))
                    ((Etempvar _q1 (tptr (Tstruct _list noattr))) ::
                     (Etempvar _p (tptr (tptr (Tstruct _list noattr)))) ::
                     (Etempvar _q (tptr (tptr (Tstruct _list noattr)))) ::
                     nil))
                  (Sset _q1 (Etempvar _t'2 (tptr (Tstruct _list noattr)))))
                (Ssequence
                  (Scall (Some _t'3)
                    (Evar _merge (Tfunction
                                   (Tcons (tptr (Tstruct _list noattr))
                                     (Tcons (tptr (Tstruct _list noattr))
                                       Tnil)) (tptr (Tstruct _list noattr))
                                   cc_default))
                    ((Etempvar _p1 (tptr (Tstruct _list noattr))) ::
                     (Etempvar _q1 (tptr (Tstruct _list noattr))) :: nil))
                  (Sreturn (Some (Etempvar _t'3 (tptr (Tstruct _list noattr))))))))))))))
|}.

Definition f_merge_sort := {|
  fn_return := (tptr (Tstruct _list noattr));
  fn_callconv := cc_default;
  fn_params := ((_x, (tptr (Tstruct _list noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_p, (tptr (tptr (Tstruct _list noattr)))) ::
               (_q, (tptr (tptr (Tstruct _list noattr)))) ::
               (_t'3, (tptr (Tstruct _list noattr))) ::
               (_t'2, (tptr (tptr (Tstruct _list noattr)))) ::
               (_t'1, (tptr (tptr (Tstruct _list noattr)))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _malloc_list_2p (Tfunction Tnil
                              (tptr (tptr (Tstruct _list noattr)))
                              cc_default)) nil)
    (Sset _p (Etempvar _t'1 (tptr (tptr (Tstruct _list noattr))))))
  (Ssequence
    (Ssequence
      (Scall (Some _t'2)
        (Evar _malloc_list_2p (Tfunction Tnil
                                (tptr (tptr (Tstruct _list noattr)))
                                cc_default)) nil)
      (Sset _q (Etempvar _t'2 (tptr (tptr (Tstruct _list noattr))))))
    (Ssequence
      (Ssequence
        (Scall (Some _t'3)
          (Evar _merge_sort_rec (Tfunction
                                  (Tcons (tptr (Tstruct _list noattr))
                                    (Tcons
                                      (tptr (tptr (Tstruct _list noattr)))
                                      (Tcons
                                        (tptr (tptr (Tstruct _list noattr)))
                                        Tnil))) (tptr (Tstruct _list noattr))
                                  cc_default))
          ((Etempvar _x (tptr (Tstruct _list noattr))) ::
           (Etempvar _p (tptr (tptr (Tstruct _list noattr)))) ::
           (Etempvar _q (tptr (tptr (Tstruct _list noattr)))) :: nil))
        (Sset _x (Etempvar _t'3 (tptr (Tstruct _list noattr)))))
      (Ssequence
        (Scall None
          (Evar _free_list_2p (Tfunction
                                (Tcons (tptr (tptr (Tstruct _list noattr)))
                                  Tnil) tvoid cc_default))
          ((Etempvar _p (tptr (tptr (Tstruct _list noattr)))) :: nil))
        (Ssequence
          (Scall None
            (Evar _free_list_2p (Tfunction
                                  (Tcons (tptr (tptr (Tstruct _list noattr)))
                                    Tnil) tvoid cc_default))
            ((Etempvar _q (tptr (tptr (Tstruct _list noattr)))) :: nil))
          (Sreturn (Some (Etempvar _x (tptr (Tstruct _list noattr))))))))))
|}.

Definition f_reverse1 := {|
  fn_return := (tptr (Tstruct _list noattr));
  fn_callconv := cc_default;
  fn_params := ((_p, (tptr (Tstruct _list noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_w, (tptr (Tstruct _list noattr))) ::
               (_t, (tptr (Tstruct _list noattr))) ::
               (_v, (tptr (Tstruct _list noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _w (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
  (Ssequence
    (Sset _v (Etempvar _p (tptr (Tstruct _list noattr))))
    (Ssequence
      (Swhile
        (Etempvar _v (tptr (Tstruct _list noattr)))
        (Ssequence
          (Sset _t
            (Efield
              (Ederef (Etempvar _v (tptr (Tstruct _list noattr)))
                (Tstruct _list noattr)) _tail (tptr (Tstruct _list noattr))))
          (Ssequence
            (Sassign
              (Efield
                (Ederef (Etempvar _v (tptr (Tstruct _list noattr)))
                  (Tstruct _list noattr)) _tail
                (tptr (Tstruct _list noattr)))
              (Etempvar _w (tptr (Tstruct _list noattr))))
            (Ssequence
              (Sset _w (Etempvar _v (tptr (Tstruct _list noattr))))
              (Sset _v (Etempvar _t (tptr (Tstruct _list noattr))))))))
      (Sreturn (Some (Etempvar _w (tptr (Tstruct _list noattr))))))))
|}.

Definition f_reverse2 := {|
  fn_return := (tptr (Tstruct _list noattr));
  fn_callconv := cc_default;
  fn_params := ((_p, (tptr (Tstruct _list noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_w, (tptr (Tstruct _list noattr))) ::
               (_t, (tptr (Tstruct _list noattr))) ::
               (_v, (tptr (Tstruct _list noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _w (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
  (Ssequence
    (Sset _v (Etempvar _p (tptr (Tstruct _list noattr))))
    (Ssequence
      (Swhile
        (Etempvar _v (tptr (Tstruct _list noattr)))
        (Ssequence
          (Sset _t
            (Efield
              (Ederef (Etempvar _v (tptr (Tstruct _list noattr)))
                (Tstruct _list noattr)) _tail (tptr (Tstruct _list noattr))))
          (Ssequence
            (Sassign
              (Efield
                (Ederef (Etempvar _v (tptr (Tstruct _list noattr)))
                  (Tstruct _list noattr)) _tail
                (tptr (Tstruct _list noattr)))
              (Etempvar _w (tptr (Tstruct _list noattr))))
            (Ssequence
              (Sset _w (Etempvar _v (tptr (Tstruct _list noattr))))
              (Sset _v (Etempvar _t (tptr (Tstruct _list noattr))))))))
      (Sreturn (Some (Etempvar _w (tptr (Tstruct _list noattr))))))))
|}.

Definition f_merge_alter_proof := {|
  fn_return := (tptr (Tstruct _list noattr));
  fn_callconv := cc_default;
  fn_params := ((_x, (tptr (Tstruct _list noattr))) ::
                (_y, (tptr (Tstruct _list noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_pret, (tptr (tptr (Tstruct _list noattr)))) ::
               (_t, (tptr (tptr (Tstruct _list noattr)))) ::
               (_ret, (tptr (Tstruct _list noattr))) ::
               (_t'1, (tptr (tptr (Tstruct _list noattr)))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _malloc_list_2p (Tfunction Tnil
                              (tptr (tptr (Tstruct _list noattr)))
                              cc_default)) nil)
    (Sset _pret (Etempvar _t'1 (tptr (tptr (Tstruct _list noattr))))))
  (Ssequence
    (Sset _t (Etempvar _pret (tptr (tptr (Tstruct _list noattr)))))
    (Ssequence
      (Sloop
        (Ssequence
          Sskip
          (Ssequence
            (Sifthenelse (Ebinop Oeq
                           (Etempvar _x (tptr (Tstruct _list noattr)))
                           (Ecast (Econst_int (Int.repr 0) tint)
                             (tptr tvoid)) tint)
              (Ssequence
                (Sassign
                  (Ederef (Etempvar _t (tptr (tptr (Tstruct _list noattr))))
                    (tptr (Tstruct _list noattr)))
                  (Etempvar _y (tptr (Tstruct _list noattr))))
                Sbreak)
              Sskip)
            (Ssequence
              (Sifthenelse (Ebinop Oeq
                             (Etempvar _y (tptr (Tstruct _list noattr)))
                             (Ecast (Econst_int (Int.repr 0) tint)
                               (tptr tvoid)) tint)
                (Ssequence
                  (Sassign
                    (Ederef
                      (Etempvar _t (tptr (tptr (Tstruct _list noattr))))
                      (tptr (Tstruct _list noattr)))
                    (Etempvar _x (tptr (Tstruct _list noattr))))
                  Sbreak)
                Sskip)
              (Sifthenelse (Ebinop Olt
                             (Efield
                               (Ederef
                                 (Etempvar _x (tptr (Tstruct _list noattr)))
                                 (Tstruct _list noattr)) _head tint)
                             (Efield
                               (Ederef
                                 (Etempvar _y (tptr (Tstruct _list noattr)))
                                 (Tstruct _list noattr)) _head tint) tint)
                (Ssequence
                  (Sassign
                    (Ederef
                      (Etempvar _t (tptr (tptr (Tstruct _list noattr))))
                      (tptr (Tstruct _list noattr)))
                    (Etempvar _x (tptr (Tstruct _list noattr))))
                  (Ssequence
                    (Sset _t
                      (Eaddrof
                        (Efield
                          (Ederef (Etempvar _x (tptr (Tstruct _list noattr)))
                            (Tstruct _list noattr)) _tail
                          (tptr (Tstruct _list noattr)))
                        (tptr (tptr (Tstruct _list noattr)))))
                    (Sset _x
                      (Efield
                        (Ederef (Etempvar _x (tptr (Tstruct _list noattr)))
                          (Tstruct _list noattr)) _tail
                        (tptr (Tstruct _list noattr))))))
                (Ssequence
                  (Sassign
                    (Ederef
                      (Etempvar _t (tptr (tptr (Tstruct _list noattr))))
                      (tptr (Tstruct _list noattr)))
                    (Etempvar _y (tptr (Tstruct _list noattr))))
                  (Ssequence
                    (Sset _t
                      (Eaddrof
                        (Efield
                          (Ederef (Etempvar _y (tptr (Tstruct _list noattr)))
                            (Tstruct _list noattr)) _tail
                          (tptr (Tstruct _list noattr)))
                        (tptr (tptr (Tstruct _list noattr)))))
                    (Sset _y
                      (Efield
                        (Ederef (Etempvar _y (tptr (Tstruct _list noattr)))
                          (Tstruct _list noattr)) _tail
                        (tptr (Tstruct _list noattr))))))))))
        Sskip)
      (Ssequence
        (Sset _ret
          (Ederef (Etempvar _pret (tptr (tptr (Tstruct _list noattr))))
            (tptr (Tstruct _list noattr))))
        (Ssequence
          (Scall None
            (Evar _free_list_2p (Tfunction
                                  (Tcons (tptr (tptr (Tstruct _list noattr)))
                                    Tnil) tvoid cc_default))
            ((Etempvar _pret (tptr (tptr (Tstruct _list noattr)))) :: nil))
          (Sreturn (Some (Etempvar _ret (tptr (Tstruct _list noattr))))))))))
|}.

Definition f_merge_alter_spec := {|
  fn_return := (tptr (Tstruct _list noattr));
  fn_callconv := cc_default;
  fn_params := ((_x, (tptr (Tstruct _list noattr))) ::
                (_y, (tptr (Tstruct _list noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_pret, (tptr (tptr (Tstruct _list noattr)))) ::
               (_t, (tptr (tptr (Tstruct _list noattr)))) ::
               (_ret, (tptr (Tstruct _list noattr))) ::
               (_t'1, (tptr (tptr (Tstruct _list noattr)))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _malloc_list_2p (Tfunction Tnil
                              (tptr (tptr (Tstruct _list noattr)))
                              cc_default)) nil)
    (Sset _pret (Etempvar _t'1 (tptr (tptr (Tstruct _list noattr))))))
  (Ssequence
    (Sset _t (Etempvar _pret (tptr (tptr (Tstruct _list noattr)))))
    (Ssequence
      (Sloop
        (Ssequence
          Sskip
          (Ssequence
            (Sifthenelse (Ebinop Oeq
                           (Etempvar _x (tptr (Tstruct _list noattr)))
                           (Ecast (Econst_int (Int.repr 0) tint)
                             (tptr tvoid)) tint)
              (Ssequence
                (Sassign
                  (Ederef (Etempvar _t (tptr (tptr (Tstruct _list noattr))))
                    (tptr (Tstruct _list noattr)))
                  (Etempvar _y (tptr (Tstruct _list noattr))))
                Sbreak)
              Sskip)
            (Ssequence
              (Sifthenelse (Ebinop Oeq
                             (Etempvar _y (tptr (Tstruct _list noattr)))
                             (Ecast (Econst_int (Int.repr 0) tint)
                               (tptr tvoid)) tint)
                (Ssequence
                  (Sassign
                    (Ederef
                      (Etempvar _t (tptr (tptr (Tstruct _list noattr))))
                      (tptr (Tstruct _list noattr)))
                    (Etempvar _x (tptr (Tstruct _list noattr))))
                  Sbreak)
                Sskip)
              (Sifthenelse (Ebinop Olt
                             (Efield
                               (Ederef
                                 (Etempvar _x (tptr (Tstruct _list noattr)))
                                 (Tstruct _list noattr)) _head tint)
                             (Efield
                               (Ederef
                                 (Etempvar _y (tptr (Tstruct _list noattr)))
                                 (Tstruct _list noattr)) _head tint) tint)
                (Ssequence
                  (Sassign
                    (Ederef
                      (Etempvar _t (tptr (tptr (Tstruct _list noattr))))
                      (tptr (Tstruct _list noattr)))
                    (Etempvar _x (tptr (Tstruct _list noattr))))
                  (Ssequence
                    (Sset _t
                      (Eaddrof
                        (Efield
                          (Ederef (Etempvar _x (tptr (Tstruct _list noattr)))
                            (Tstruct _list noattr)) _tail
                          (tptr (Tstruct _list noattr)))
                        (tptr (tptr (Tstruct _list noattr)))))
                    (Sset _x
                      (Efield
                        (Ederef (Etempvar _x (tptr (Tstruct _list noattr)))
                          (Tstruct _list noattr)) _tail
                        (tptr (Tstruct _list noattr))))))
                (Ssequence
                  (Sassign
                    (Ederef
                      (Etempvar _t (tptr (tptr (Tstruct _list noattr))))
                      (tptr (Tstruct _list noattr)))
                    (Etempvar _y (tptr (Tstruct _list noattr))))
                  (Ssequence
                    (Sset _t
                      (Eaddrof
                        (Efield
                          (Ederef (Etempvar _y (tptr (Tstruct _list noattr)))
                            (Tstruct _list noattr)) _tail
                          (tptr (Tstruct _list noattr)))
                        (tptr (tptr (Tstruct _list noattr)))))
                    (Sset _y
                      (Efield
                        (Ederef (Etempvar _y (tptr (Tstruct _list noattr)))
                          (Tstruct _list noattr)) _tail
                        (tptr (Tstruct _list noattr))))))))))
        Sskip)
      (Ssequence
        (Sset _ret
          (Ederef (Etempvar _pret (tptr (tptr (Tstruct _list noattr))))
            (tptr (Tstruct _list noattr))))
        (Ssequence
          (Scall None
            (Evar _free_list_2p (Tfunction
                                  (Tcons (tptr (tptr (Tstruct _list noattr)))
                                    Tnil) tvoid cc_default))
            ((Etempvar _pret (tptr (tptr (Tstruct _list noattr)))) :: nil))
          (Sreturn (Some (Etempvar _ret (tptr (Tstruct _list noattr))))))))))
|}.

Definition composites : list composite_definition :=
(Composite _list Struct
   ((_head, tint) :: (_tail, (tptr (Tstruct _list noattr))) :: nil)
   noattr ::
 Composite _queue Struct
   ((_l1, (tptr (Tstruct _list noattr))) ::
    (_l2, (tptr (Tstruct _list noattr))) :: nil)
   noattr :: nil).

Definition global_definitions : list (ident * globdef fundef type) :=
((___builtin_ais_annot,
   Gfun(External (EF_builtin "__builtin_ais_annot"
                   (mksignature (AST.Tint :: nil) None
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tvoid
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_bswap64,
   Gfun(External (EF_builtin "__builtin_bswap64"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tlong)
                     cc_default)) (Tcons tulong Tnil) tulong cc_default)) ::
 (___builtin_bswap,
   Gfun(External (EF_builtin "__builtin_bswap"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap32,
   Gfun(External (EF_builtin "__builtin_bswap32"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap16,
   Gfun(External (EF_builtin "__builtin_bswap16"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tushort Tnil) tushort cc_default)) ::
 (___builtin_fabs,
   Gfun(External (EF_builtin "__builtin_fabs"
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_fsqrt,
   Gfun(External (EF_builtin "__builtin_fsqrt"
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_memcpy_aligned,
   Gfun(External (EF_builtin "__builtin_memcpy_aligned"
                   (mksignature
                     (AST.Tint :: AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     None cc_default))
     (Tcons (tptr tvoid)
       (Tcons (tptr tvoid) (Tcons tuint (Tcons tuint Tnil)))) tvoid
     cc_default)) ::
 (___builtin_sel,
   Gfun(External (EF_builtin "__builtin_sel"
                   (mksignature (AST.Tint :: nil) None
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons tbool Tnil) tvoid
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot,
   Gfun(External (EF_builtin "__builtin_annot"
                   (mksignature (AST.Tint :: nil) None
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tvoid
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot_intval,
   Gfun(External (EF_builtin "__builtin_annot_intval"
                   (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint)
                     cc_default)) (Tcons (tptr tschar) (Tcons tint Tnil))
     tint cc_default)) ::
 (___builtin_membar,
   Gfun(External (EF_builtin "__builtin_membar"
                   (mksignature nil None cc_default)) Tnil tvoid cc_default)) ::
 (___builtin_va_start,
   Gfun(External (EF_builtin "__builtin_va_start"
                   (mksignature (AST.Tint :: nil) None cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___builtin_va_arg,
   Gfun(External (EF_builtin "__builtin_va_arg"
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default)) (Tcons (tptr tvoid) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_va_copy,
   Gfun(External (EF_builtin "__builtin_va_copy"
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default))
     (Tcons (tptr tvoid) (Tcons (tptr tvoid) Tnil)) tvoid cc_default)) ::
 (___builtin_va_end,
   Gfun(External (EF_builtin "__builtin_va_end"
                   (mksignature (AST.Tint :: nil) None cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___compcert_va_int32,
   Gfun(External (EF_external "__compcert_va_int32"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons (tptr tvoid) Tnil) tuint cc_default)) ::
 (___compcert_va_int64,
   Gfun(External (EF_external "__compcert_va_int64"
                   (mksignature (AST.Tint :: nil) (Some AST.Tlong)
                     cc_default)) (Tcons (tptr tvoid) Tnil) tulong
     cc_default)) ::
 (___compcert_va_float64,
   Gfun(External (EF_external "__compcert_va_float64"
                   (mksignature (AST.Tint :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons (tptr tvoid) Tnil) tdouble
     cc_default)) ::
 (___compcert_va_composite,
   Gfun(External (EF_external "__compcert_va_composite"
                   (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint)
                     cc_default)) (Tcons (tptr tvoid) (Tcons tuint Tnil))
     (tptr tvoid) cc_default)) ::
 (___compcert_i64_dtos,
   Gfun(External (EF_runtime "__compcert_i64_dtos"
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tlong)
                     cc_default)) (Tcons tdouble Tnil) tlong cc_default)) ::
 (___compcert_i64_dtou,
   Gfun(External (EF_runtime "__compcert_i64_dtou"
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tlong)
                     cc_default)) (Tcons tdouble Tnil) tulong cc_default)) ::
 (___compcert_i64_stod,
   Gfun(External (EF_runtime "__compcert_i64_stod"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons tlong Tnil) tdouble cc_default)) ::
 (___compcert_i64_utod,
   Gfun(External (EF_runtime "__compcert_i64_utod"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons tulong Tnil) tdouble cc_default)) ::
 (___compcert_i64_stof,
   Gfun(External (EF_runtime "__compcert_i64_stof"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tsingle)
                     cc_default)) (Tcons tlong Tnil) tfloat cc_default)) ::
 (___compcert_i64_utof,
   Gfun(External (EF_runtime "__compcert_i64_utof"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tsingle)
                     cc_default)) (Tcons tulong Tnil) tfloat cc_default)) ::
 (___compcert_i64_sdiv,
   Gfun(External (EF_runtime "__compcert_i64_sdiv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tlong Tnil)) tlong cc_default)) ::
 (___compcert_i64_udiv,
   Gfun(External (EF_runtime "__compcert_i64_udiv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tulong (Tcons tulong Tnil)) tulong cc_default)) ::
 (___compcert_i64_smod,
   Gfun(External (EF_runtime "__compcert_i64_smod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tlong Tnil)) tlong cc_default)) ::
 (___compcert_i64_umod,
   Gfun(External (EF_runtime "__compcert_i64_umod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tulong (Tcons tulong Tnil)) tulong cc_default)) ::
 (___compcert_i64_shl,
   Gfun(External (EF_runtime "__compcert_i64_shl"
                   (mksignature (AST.Tlong :: AST.Tint :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tint Tnil)) tlong cc_default)) ::
 (___compcert_i64_shr,
   Gfun(External (EF_runtime "__compcert_i64_shr"
                   (mksignature (AST.Tlong :: AST.Tint :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tulong (Tcons tint Tnil)) tulong cc_default)) ::
 (___compcert_i64_sar,
   Gfun(External (EF_runtime "__compcert_i64_sar"
                   (mksignature (AST.Tlong :: AST.Tint :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tint Tnil)) tlong cc_default)) ::
 (___compcert_i64_smulh,
   Gfun(External (EF_runtime "__compcert_i64_smulh"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tlong Tnil)) tlong cc_default)) ::
 (___compcert_i64_umulh,
   Gfun(External (EF_runtime "__compcert_i64_umulh"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tulong (Tcons tulong Tnil)) tulong cc_default)) ::
 (___builtin_clz,
   Gfun(External (EF_builtin "__builtin_clz"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_clzl,
   Gfun(External (EF_builtin "__builtin_clzl"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_clzll,
   Gfun(External (EF_builtin "__builtin_clzll"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tint)
                     cc_default)) (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_ctz,
   Gfun(External (EF_builtin "__builtin_ctz"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_ctzl,
   Gfun(External (EF_builtin "__builtin_ctzl"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_ctzll,
   Gfun(External (EF_builtin "__builtin_ctzll"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tint)
                     cc_default)) (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_fmax,
   Gfun(External (EF_builtin "__builtin_fmax"
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble Tnil)) tdouble cc_default)) ::
 (___builtin_fmin,
   Gfun(External (EF_builtin "__builtin_fmin"
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble Tnil)) tdouble cc_default)) ::
 (___builtin_fmadd,
   Gfun(External (EF_builtin "__builtin_fmadd"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fmsub,
   Gfun(External (EF_builtin "__builtin_fmsub"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fnmadd,
   Gfun(External (EF_builtin "__builtin_fnmadd"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fnmsub,
   Gfun(External (EF_builtin "__builtin_fnmsub"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_read16_reversed,
   Gfun(External (EF_builtin "__builtin_read16_reversed"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons (tptr tushort) Tnil) tushort cc_default)) ::
 (___builtin_read32_reversed,
   Gfun(External (EF_builtin "__builtin_read32_reversed"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons (tptr tuint) Tnil) tuint cc_default)) ::
 (___builtin_write16_reversed,
   Gfun(External (EF_builtin "__builtin_write16_reversed"
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default)) (Tcons (tptr tushort) (Tcons tushort Tnil))
     tvoid cc_default)) ::
 (___builtin_write32_reversed,
   Gfun(External (EF_builtin "__builtin_write32_reversed"
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default)) (Tcons (tptr tuint) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_nop,
   Gfun(External (EF_builtin "__builtin_nop"
                   (mksignature nil None cc_default)) Tnil tvoid cc_default)) ::
 (___builtin_debug,
   Gfun(External (EF_external "__builtin_debug"
                   (mksignature (AST.Tint :: nil) None
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons tint Tnil) tvoid
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (_malloc_list_cell,
   Gfun(External (EF_external "malloc_list_cell"
                   (mksignature nil (Some AST.Tint) cc_default)) Tnil
     (tptr (Tstruct _list noattr)) cc_default)) ::
 (_free_list_cell,
   Gfun(External (EF_external "free_list_cell"
                   (mksignature (AST.Tint :: nil) None cc_default))
     (Tcons (tptr (Tstruct _list noattr)) Tnil) tvoid cc_default)) ::
 (_malloc_list_2p,
   Gfun(External (EF_external "malloc_list_2p"
                   (mksignature nil (Some AST.Tint) cc_default)) Tnil
     (tptr (tptr (Tstruct _list noattr))) cc_default)) ::
 (_free_list_2p,
   Gfun(External (EF_external "free_list_2p"
                   (mksignature (AST.Tint :: nil) None cc_default))
     (Tcons (tptr (tptr (Tstruct _list noattr))) Tnil) tvoid cc_default)) ::
 (_reverse, Gfun(Internal f_reverse)) ::
 (_append, Gfun(Internal f_append)) ::
 (_append_2p, Gfun(Internal f_append_2p)) ::
 (_append2, Gfun(Internal f_append2)) ::
 (_rev_append, Gfun(Internal f_rev_append)) ::
 (_max, Gfun(Internal f_max)) :: (_push, Gfun(Internal f_push)) ::
 (_pop, Gfun(Internal f_pop)) :: (_enqueue, Gfun(Internal f_enqueue)) ::
 (_dequeue, Gfun(Internal f_dequeue)) :: (_merge, Gfun(Internal f_merge)) ::
 (_split_rec, Gfun(Internal f_split_rec)) ::
 (_merge_sort_rec, Gfun(Internal f_merge_sort_rec)) ::
 (_merge_sort, Gfun(Internal f_merge_sort)) ::
 (_reverse1, Gfun(Internal f_reverse1)) ::
 (_reverse2, Gfun(Internal f_reverse2)) ::
 (_merge_alter_proof, Gfun(Internal f_merge_alter_proof)) ::
 (_merge_alter_spec, Gfun(Internal f_merge_alter_spec)) :: nil).

Definition public_idents : list ident :=
(_merge_alter_spec :: _merge_alter_proof :: _reverse2 :: _reverse1 ::
 _merge_sort :: _merge_sort_rec :: _split_rec :: _merge :: _dequeue ::
 _enqueue :: _pop :: _push :: _max :: _rev_append :: _append2 ::
 _append_2p :: _append :: _reverse :: _free_list_2p :: _malloc_list_2p ::
 _free_list_cell :: _malloc_list_cell :: ___builtin_debug ::
 ___builtin_nop :: ___builtin_write32_reversed ::
 ___builtin_write16_reversed :: ___builtin_read32_reversed ::
 ___builtin_read16_reversed :: ___builtin_fnmsub :: ___builtin_fnmadd ::
 ___builtin_fmsub :: ___builtin_fmadd :: ___builtin_fmin ::
 ___builtin_fmax :: ___builtin_ctzll :: ___builtin_ctzl :: ___builtin_ctz ::
 ___builtin_clzll :: ___builtin_clzl :: ___builtin_clz ::
 ___compcert_i64_umulh :: ___compcert_i64_smulh :: ___compcert_i64_sar ::
 ___compcert_i64_shr :: ___compcert_i64_shl :: ___compcert_i64_umod ::
 ___compcert_i64_smod :: ___compcert_i64_udiv :: ___compcert_i64_sdiv ::
 ___compcert_i64_utof :: ___compcert_i64_stof :: ___compcert_i64_utod ::
 ___compcert_i64_stod :: ___compcert_i64_dtou :: ___compcert_i64_dtos ::
 ___compcert_va_composite :: ___compcert_va_float64 ::
 ___compcert_va_int64 :: ___compcert_va_int32 :: ___builtin_va_end ::
 ___builtin_va_copy :: ___builtin_va_arg :: ___builtin_va_start ::
 ___builtin_membar :: ___builtin_annot_intval :: ___builtin_annot ::
 ___builtin_sel :: ___builtin_memcpy_aligned :: ___builtin_fsqrt ::
 ___builtin_fabs :: ___builtin_bswap16 :: ___builtin_bswap32 ::
 ___builtin_bswap :: ___builtin_bswap64 :: ___builtin_ais_annot :: nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.


