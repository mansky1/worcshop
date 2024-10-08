Require Import FloydSeq.base2.
Require Import FloydSeq.client_lemmas.
Require Import FloydSeq.closed_lemmas.
Require Import VST.floyd.mapsto_memory_block.
Require Import FloydSeq.local2ptree_denote.
Require Import FloydSeq.local2ptree_eval.
Require Import Csplit.strong.
Require Import Csplit.strongFacts.

Import LiftNotation.
Local Open Scope logic.

Definition NDfunspec_sub (f1 f2 : funspec) :=
 let Delta := (funsig_tycontext (funsig_of_funspec f1)) in
 match f1 with
 | mk_funspec fsig1 cc1 (rmaps.ConstType A1) P1 Q1 _ _ =>
 match f2 with
 | mk_funspec fsig2 cc2 (rmaps.ConstType A2) P2 Q2 _ _ =>
   fsig1 = fsig2 /\ cc1 = cc2 /\  forall x2,
        ENTAIL Delta, P2 nil x2 |-- EX x1:_, EX F:mpred,
                             ((`F * P1 nil x1) &&
                             (!! (ENTAIL (ret0_tycon Delta), `F * Q1 nil x1 
                                      |-- Q2 nil x2)))
 | _ => False end
 | _ => False end.

Definition is_NDfunspec (fs: funspec) :=
 match fs with
 | mk_funspec _ _ (rmaps.ConstType A) P Q _ _ =>
    (forall ts, P ts = P nil /\ Q ts = Q nil)
 | _ => False
 end.

Lemma NDsubsume_subsume:
  forall f1 f2, 
   is_NDfunspec f2 ->
   NDfunspec_sub f1 f2 ->
   funspec_sub f1 f2.
Proof.
intros f1 f2. pose proof I. intros H0 H1.
destruct f1, f2; hnf in H1.
destruct A; try contradiction. destruct A0; try contradiction.
destruct H1 as [? [? ?]]; split3; auto.
subst f0 c0.
intros ts1 x1 rho.
specialize (H3 x1).
simpl in H0.
specialize (H0 ts1). destruct H0 as [H0 H0'].
rewrite H0.
eapply predicates_hered.derives_trans; [apply H3 | clear H3 ].
apply (predicates_hered.exp_right (@nil Type)).
apply predicates_hered.exp_derives; intros x2.
apply predicates_hered.exp_derives; intros F.
apply predicates_hered.andp_derives; trivial. hnf. rewrite H0'. auto.
Qed.

Inductive empty_type : Type := .

Definition withtype_of_NDfunspec fs := match fs with
  mk_funspec _ _ (rmaps.ConstType A) _ _ _ _ => A | _ => empty_type end.
 

Definition withtype_of_funspec fs := match fs with
  mk_funspec _ _ A _ _ _ _ => A end.

Lemma sepcon_ENTAIL:
 forall Delta P Q P' Q',
  ENTAIL Delta, P |-- P' ->
  ENTAIL Delta, Q |-- Q' ->
  ENTAIL Delta, P * Q |-- P' * Q'.
Proof.
intros.
intro rho; specialize (H rho); specialize (H0 rho); simpl in *.
unfold local, lift1 in *.
normalize.
rewrite prop_true_andp in H,H0 by auto.
apply sepcon_derives; auto.
Qed.

Lemma NDfunspec_sub_refl:
  forall fsig cc A P Q, 
   NDfunspec_sub (NDmk_funspec fsig cc A P Q) (NDmk_funspec fsig cc A P Q).
Proof.
intros.
simpl.
split3; auto.
intros.
Exists x2. Exists emp.
unfold_lift.
rewrite !emp_sepcon.
apply andp_right.
apply andp_left2; auto.
apply prop_right.
intros rho'.
rewrite emp_sepcon.
apply andp_left2; auto.
Qed.

Lemma NDfunspec_sub_trans:
  forall fsig1 cc1 A1 P1 Q1 fsig2 cc2 A2 P2 Q2 fsig3 cc3 A3 P3 Q3, 
   NDfunspec_sub (NDmk_funspec fsig1 cc1 A1 P1 Q1) (NDmk_funspec fsig2 cc2 A2 P2 Q2) ->
   NDfunspec_sub (NDmk_funspec fsig2 cc2 A2 P2 Q2) (NDmk_funspec fsig3 cc3 A3 P3 Q3) ->
   NDfunspec_sub (NDmk_funspec fsig1 cc1 A1 P1 Q1) (NDmk_funspec fsig3 cc3 A3 P3 Q3).
Proof.
intros.
destruct H as [?E [?E H]]. 
destruct H0 as [?E [?E H0]].
subst.
split3; auto.
intro x3; simpl in x3.
specialize (H0 x3).
eapply ENTAIL_trans; [apply H0 | ].
clear H0.
Intros x2 F.
simpl in x2.
specialize (H x2).
eapply derives_trans.
apply sepcon_ENTAIL.
apply ENTAIL_refl.
apply H.
clear H.
Intros x1. simpl in x1.
Intros F1.
Exists x1 (F*F1).
apply andp_right.
intro rho.
unfold_lift. unfold local, lift1. simpl. normalize.
rewrite sepcon_assoc. auto.
apply prop_right.
apply ENTAIL_trans with (`F * (`F1 * Q1 x1)).
apply andp_left2.
clear. unfold_lift; intro rho; simpl. rewrite sepcon_assoc; auto.
simpl funsig_tycontext in *.
eapply ENTAIL_trans; [ | apply H0].
apply sepcon_ENTAIL.
apply ENTAIL_refl.
 auto.
Qed.

Lemma later_exp'' (A: Type) (ND: NatDed A)(Indir: Indir A):
      forall T : Type,
       (exists x: T, True) ->
       forall F : T -> A,
       |> (EX x : _, F x) = EX x : T, |> F x.
Proof.
intros.
destruct H as [x _].
apply later_exp'; auto.
Qed.

Lemma semax_call_subsume:
  forall (fs1: funspec) A P Q NEP NEQ argsig retsig cc,
    funspec_sub fs1 (mk_funspec (argsig,retsig) cc A P Q NEP NEQ) ->
    forall {CS: compspecs} {Espec: OracleKind}
        Delta ts x (F: environ -> mpred) ret a bl b id,
      Cop.classify_fun (typeof a) =
      Cop.fun_case_f (type_of_params argsig) retsig cc ->
      (retsig = Tvoid -> ret = None) ->   
      tc_fn_return Delta ret retsig ->
      precise_context Delta ->
      (glob_specs Delta) ! id = Some fs1 ->
      @semax CS Espec Delta
        (((tc_expr Delta a) && (tc_exprlist Delta (snd (split argsig)) bl))  &&
         (local (fun rho =>
            gvar_injection (ge_of rho) /\
            eval_expr a rho = Vptr b Ptrofs.zero /\
            global_block rho id b) &&
          |>(F * `(P ts x: environ -> mpred) (make_args' (argsig,retsig) (eval_exprlist (snd (split argsig)) bl)))))
         (Scall ret a bl)
         (normal_ret_assert
          (EX old:val, substopt ret (`old) F * maybe_retval (Q ts x) retsig ret)).
Proof. intros.
eapply semax_pre.
2: apply semax_call_forward with (P0:=P)(NEP0:=NEP)(NEQ0:=NEQ)(fs:=fs1)(cc0:=cc); trivial; eassumption.
apply andp_left2. apply andp_derives; trivial. apply andp_derives; trivial.
unfold liftx, lift. simpl. intros rho.
remember (mk_funspec (argsig, retsig) cc A P Q NEP NEQ) as gs.
remember (eval_expr a rho) as v.
rewrite <- add_andp. apply derives_refl.
apply derives_trans with TT. apply TT_right.
apply funspec_sub_sub_si. assumption.
Qed.

Lemma semax_call_subsume_si:
  forall (fs1: funspec) A P Q NEP NEQ argsig retsig cc
      {CS: compspecs} {Espec: OracleKind} Delta ts x
      (F: environ -> mpred) ret a bl b id,
    Cop.classify_fun (typeof a) =
    Cop.fun_case_f (type_of_params argsig) retsig cc ->
    (retsig = Tvoid -> ret = None) ->   
    tc_fn_return Delta ret retsig ->
    precise_context Delta ->
    (glob_specs Delta) ! id = Some fs1 ->
    @semax CS Espec Delta
      (((tc_expr Delta a) && (tc_exprlist Delta (snd (split argsig)) bl)) && 
        (local (fun rho =>
          gvar_injection (ge_of rho) /\
          eval_expr a rho = Vptr b Ptrofs.zero /\
          global_block rho id b) &&
          `(funspec_sub_si fs1 (mk_funspec (argsig,retsig) cc A P Q NEP NEQ)) &&
          |>(F * `(P ts x: environ -> mpred) (make_args' (argsig,retsig) (eval_exprlist (snd (split argsig)) bl)))))
         (Scall ret a bl)
         (normal_ret_assert
          (EX old:val, substopt ret (`old) F * maybe_retval (Q ts x) retsig ret)).
Proof. intros.
apply semax_call_forward with (P0:=P)(NEP0:=NEP)(NEQ0:=NEQ)(fs:=fs1)(cc0:=cc);
  eassumption.
Qed.

Lemma semax_call_NDsubsume :
  forall (fs1: funspec) A P Q argsig retsig cc,
      NDfunspec_sub fs1 
    (NDmk_funspec (argsig,retsig) cc A P Q)  ->
    forall {CS: compspecs} {Espec: OracleKind}
        Delta x (F: environ -> mpred) ret a bl b id,
      Cop.classify_fun (typeof a) =
      Cop.fun_case_f (type_of_params argsig) retsig cc ->
      (retsig = Tvoid -> ret = None) ->
      tc_fn_return Delta ret retsig ->
      precise_context Delta ->
      (glob_specs Delta) ! id = Some fs1 ->
      @semax CS Espec Delta
        (((tc_expr Delta a) && (tc_exprlist Delta (snd (split argsig)) bl)) &&
         (local (fun rho =>
            gvar_injection (ge_of rho) /\
            eval_expr a rho = Vptr b Ptrofs.zero /\
            global_block rho id b) &&
          |>(F * `(P x: environ -> mpred) (make_args' (argsig,retsig) (eval_exprlist (snd (split argsig)) bl)))))
         (Scall ret a bl)
         (normal_ret_assert
          (EX old:val, substopt ret (`old) F * maybe_retval (Q x) retsig ret)).
Proof.
intros.
apply (semax_call_subsume fs1 (rmaps.ConstType A) (fun _ => P) (fun _ => Q)
   (const_super_non_expansive A _) (const_super_non_expansive A _)
    argsig retsig cc); auto.
clear - H.
apply NDsubsume_subsume. simpl; auto. apply H. apply nil.
Qed.
