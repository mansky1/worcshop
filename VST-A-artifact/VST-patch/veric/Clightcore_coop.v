Require Import VST.sepcomp.semantics.
Require Import VST.sepcomp.semantics_lemmas.
Require Import VST.sepcomp.mem_lemmas.
Require Import VST.veric.Clight_base.
Require Import VST.veric.Clight_core.

Lemma alloc_variables_mem_step: forall cenv vars m e e2 m'
      (M: alloc_variables cenv e m vars e2 m'), mem_step m m'.
Proof. intros.
  induction M.
  apply mem_step_refl.
  eapply semantics.mem_step_trans.
    eapply semantics.mem_step_alloc; eassumption. eassumption.
Qed.

Lemma assign_loc_mem_step g t m b z v m' (A:assign_loc g t m b z v m'):
    mem_step m m'.
Proof.
  inv A.
  { simpl in H0. eapply mem_step_storebytes. eapply Mem.store_storebytes; eauto. }
  { eapply mem_step_storebytes; eauto. }
Qed.

Lemma bind_parameters_mem_step: forall cenv e m pars vargs m'
      (M: bind_parameters cenv e m pars vargs m'), semantics.mem_step m m'.
Proof. intros.
  induction M.
  apply mem_step_refl.
  inv H0.
+ eapply semantics.mem_step_trans; try eassumption. simpl in H2.
  eapply mem_step_store; eassumption.
+ eapply semantics.mem_step_trans; try eassumption.
  eapply semantics.mem_step_storebytes; eassumption.
Qed.


Lemma extcall_mem_step g: forall ef vargs m t vres m' (E:Events.external_call ef g vargs m t vres m'),
  mem_step m m'.
Proof.
  destruct ef; simpl; intros; try solve [inv E; apply mem_step_refl].
  { eapply extcall_sem_mem_step; eassumption. }
  { eapply extcall_sem_mem_step; eassumption. }
  { eapply extcall_sem_mem_step; eassumption. }
  { inv E. inv H. eapply mem_step_refl.
    apply Mem.store_storebytes in H1. eapply mem_step_storebytes. eassumption. }
  { inv E. apply Mem.store_storebytes in H0.
    eapply mem_step_trans. eapply mem_step_alloc; eassumption.
    eapply mem_step_storebytes; eassumption. }
  { inv E. eapply mem_step_free; eassumption. }
  { inv E. eapply mem_step_storebytes. eassumption. }
  { eapply inline_assembly_memstep; eassumption. }
Qed.
  
Lemma CLC_corestep_mem:
  forall (g : genv) c (m : mem) c'  (m' : mem),
    semantics.corestep (cl_core_sem g) c m c' m' ->
    semantics.mem_step m m'.
Proof. simpl; intros. inv H; simpl in *;
  try apply mem_step_refl.
   eapply assign_loc_mem_step; eauto.
   eapply mem_step_freelist; eauto.
   eapply mem_step_freelist; eauto.
   eapply mem_step_freelist; eauto.
   inv H0.
   eapply alloc_variables_mem_step; eauto.
   apply extcall_mem_step in H1; auto.
Qed. 

Program Definition CLC_memsem  (ge : Clight.genv) :
  @MemSem state.
apply Build_MemSem with (csem := cl_core_sem ge).
eapply CLC_corestep_mem.
Defined.



