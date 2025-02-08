Require Import Reals.
Require Import Coquelicot.Complex.
Require Import Strings.String.
Require Import Lists.List.
Import ListNotations.

Require Import Coq.Init.Datatypes.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Arith.PeanoNat. Import Nat. 
From Coq Require Import Lia.

Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Arith.Peano_dec.

From Quan Require Import Matrix.
From Quan Require Import Quantum.
From Quan Require Import QState_L.
From Quan Require Import QIMP_L.
From Quan Require Import QAssert_L.
From Quan Require Import Mixed_State.
From Quan Require Import QSepar.
From Quan Require Import QRule_E_L.
From Quan Require Import QRule_I_L.
Import Reduced.
Import Basic.
Import Ceval_Prop.
Local Open Scope nat_scope.

Local Open Scope com_scope.

Local Open Scope rule_scope.
Local Open Scope nat_scope.
Theorem rule_Qinit_aux:  forall  s e (s' e':nat) (st :state s' e') (st': state s' e'),
WF_state st->
ceval_single (QInit s e) [st] [st'] ->
State_eval (QExp_s s e  (∣ 0 ⟩_ (2^(e-s)))) st'.
Proof. 
      intros s e s' e' st st' H'. intros. simpl in *.
      destruct st. destruct st'. 
      inversion H; subst.  inversion H1; subst. 
      simpl. injection H6. intros.  
      rewrite <-H3.  rewrite <-Reduced_scale.
      rewrite Reduced_ceval_swap_Qinit.
      rewrite QInit_trace.
      split. apply Pure_State_Vector_base . apply pow_gt_0.  
      split. dom_solve. split. dom_solve.  split. dom_solve. 
      unfold QInit_fun. remember ((Reduced q s e)).
      rewrite (big_sum_eq_bounded  _   
      (fun i0:nat=> (∣ 0 ⟩_ (2^(e - s)) × (⟨ i0 ∣_ (2^(e - s)) × q1 
      × (∣ i0 ⟩_ (2^(e - s)))) × ⟨ 0 ∣_ (2^(e - s))))).
      rewrite <-(@Mmult_Msum_distr_r (2^(e-s)) 1 (2^(e-s))).
      rewrite <-(@Mmult_Msum_distr_l 1 1 (2^(e-s))).
      rewrite trace_base. unfold c_to_Vector1.  rewrite Mscale_mult_dist_r.
      rewrite Mmult_1_r. rewrite Rdiv_unfold.
      rewrite Rmult_1_l.  rewrite Heqq1.
      rewrite Reduced_trace. rewrite Mscale_mult_dist_l.
      rewrite Mscale_assoc.  unfold RtoC. 
      assert(@trace (2^(e'-s')) q= (fst (@trace (2^(e'-s')) q), snd (@trace (2^(e'-s')) q))).
      destruct (trace q).  
      reflexivity. rewrite H5.  rewrite nz_mixed_state_trace_real.
      unfold Cmult. simpl. repeat  rewrite Rmult_0_l. rewrite Rmult_0_r.
      rewrite Rplus_0_l. rewrite Rminus_0_r. 
      rewrite Cmod_snd_0. simpl. rewrite Rinv_l.
      rewrite Mscale_1_l. unfold outer_product. reflexivity.
      assert((0 < fst (@trace (2^(e'-s')) q))%R). 
      apply nz_mixed_state_trace_gt0. apply H'.  lra.
      apply nz_mixed_state_trace_gt0. apply H'. simpl. reflexivity.
      apply H'. dom_solve.  apply WF_NZ_Mixed.  apply H'.
      apply WF_base. apply pow_gt_0.  rewrite Heqq1.
      apply WF_NZ_Mixed. apply WF_qstate_Reduced. dom_solve.   apply H'. 
      intros. repeat rewrite Nat.sub_diag. rewrite kron_1_l. 
      rewrite kron_1_r. 
      unfold q_update. unfold super. rewrite Mmult_adjoint.
      rewrite adjoint_involutive. rewrite Mmult_assoc_5.
      reflexivity. assert(0<2^(e-s)). lia. auto_wf. dom_solve. 
       apply WF_NZ_Mixed. apply H'. dom_solve.  
      apply WF_NZ_Mixed. apply H'.
Qed.

Lemma ceval_eq{s e:nat}: forall (mu mu' mu1:list (cstate * qstate s e)) c,
mu1=mu'->
ceval_single c mu mu'->
ceval_single c mu mu1.
Proof. intros. rewrite H. assumption.
Qed.


Theorem rule_Qinit_aux' :  forall 
(s e s' e' :nat) (mu : list (cstate * qstate s' e')) (mu': list (cstate * qstate s' e')),
WF_dstate_aux mu->
ceval_single (QInit s e) mu mu' ->
State_eval_dstate (BTrue) mu->
State_eval_dstate ((QExp_s s e  (∣ 0 ⟩_ (2^(e-s))))) mu'.
Proof. intros s e s' e' mu. induction mu; intros mu'; intros. inversion H0; subst.
  --simpl in *. split; try lia. apply WF_base. apply pow_gt_0. 
  -- destruct mu. inversion H0; subst. inversion H7; subst.
     rewrite map2_nil_r in *.
      * econstructor.
       apply rule_Qinit_aux with ((sigma, rho)). 
       inversion_clear H. assumption. 
       assumption.  apply Forall_nil.
      
       *destruct a. inversion H0; subst. 
       apply d_seman_app_aux. 
       apply WF_ceval with (QInit s e) ([(c,q)]).
       apply WF_state_dstate_aux.  inversion_clear H. assumption.
       assert([(c, QInit_fun s e q)]= (StateMap.Raw.map2 (@option_app s' e') ([(c, QInit_fun s e q)])  ([]))).
       reflexivity.   rewrite H2. apply E_Qinit.  apply E_nil.
       dom_solve. 
       eapply ceval_single_dom. apply H8. 

      apply WF_ceval with (QInit s e) ((p :: mu)).
      inversion_clear H. assumption. assumption.

      econstructor. apply rule_Qinit_aux with ((c, q)). 
      inversion_clear H. assumption.
      apply ceval_eq with ((StateMap.Raw.map2 (@option_app s' e') ([(c, QInit_fun s e q)])  ([]))).
      reflexivity. apply E_Qinit. apply E_nil. dom_solve. 
      eapply ceval_single_dom. apply H8. 
      apply Forall_nil.

      apply IHmu.  inversion_clear H.  assumption.  

      intuition. inversion_clear H1.  apply State_eval_dstate_Forall.
      discriminate.  assumption.
Qed.   


Theorem rule_QInit: forall s e,
{{BTrue}} 
[[ s e ]] :Q= 0
{{(QExp_s s e  (∣ 0 ⟩_ (2^(e-s))))}}.
Proof. 
unfold hoare_triple.
intros s e s' e' (mu,IHmu) (mu', IHmu').
intros. 
inversion_clear H; simpl in H2.
rewrite sat_Assert_to_State in *.
inversion_clear H0.
apply sat_F.
eapply WF_ceval. apply H. apply H2. 
apply rule_Qinit_aux' with  mu.
intuition. intuition. assumption. 
Qed.

Lemma Unitary_I{n:nat}: forall (U:Square n),
WF_Unitary U -> (U) † × U = I n .
Proof. intros. destruct H. assumption.
Qed.


Definition U_v {m n:nat}(s' e' s e:nat) (U: Square (2^m)) (v: Vector (2^n)):
Vector (2^(e-s)) := 
@Mmult ((2^(e-s)))  (2^(e-s)) 1  (I (2^(s'-s)) ⊗ U ⊗ (I (2^(e-e')))) v.

Lemma WF_U_v:forall s' e' s e (v:Vector (2^(e-s))) (M:Square (2^(e'-s'))),
s<=s'/\ s' <= e'/\ e'<=e->
WF_Matrix v-> WF_Matrix M-> WF_Matrix (U_v s' e' s e M v).
Proof. intros. unfold U_v. auto_wf.
Qed.
#[export] Hint Resolve WF_U_v: wf_db. 

Local Open Scope assert_scope.
Local Open Scope nat_scope.

Lemma U_v_inv{s' e' s e}: forall (U: Square (2 ^ (e' - s'))) (v: Vector (2 ^ (e - s))),
s<=s' /\ s' <=e' /\ e' <=e ->WF_Unitary U->
WF_Matrix v->
U_v s' e' s e U (U_v s' e' s e (U) † v) = v.
Proof. intros. unfold U_v. 
       rewrite <-Mmult_assoc.
       assert(2 ^ (s' - s) * 2 ^ (e' - s') * 2 ^ (e - e')= 2 ^ (e - s)).
      type_sovle'. destruct H2.
      repeat  rewrite kron_mixed_product.
      Msimpl. 
      apply transpose_unitary in H0.
      destruct H0.
      rewrite adjoint_involutive in H2.
      rewrite H2. 
      rewrite id_kron.
      rewrite id_kron.
      Msimpl. reflexivity.
Qed.


Theorem rule_QUnit_aux:  forall s' e' s e (U: Square (2^(e'-s'))) (v: Vector (2^(e-s)))
(s0 e0:nat) (st :state s0 e0) (st': state s0 e0),
s<=s' /\ e' <=e ->
WF_state st->(WF_Matrix v )->
ceval_single (QUnit_One s' e' U) [st] [st'] ->
State_eval (QExp_s s  e  (U_v s' e' s e U† v) ) st->
State_eval (QExp_s s  e  v ) st'.
Proof. intros. simpl in *. destruct H3. destruct H4.
       destruct st.  
      inversion H2; subst. inversion H7; subst.
      clear H7. apply inj_pair2_eq_dec in H9.
      apply inj_pair2_eq_dec in H9. subst.
      injection H13. intros.
      split. rewrite <-(U_v_inv  U); try dom_solve; try assumption. 
      apply pure_state_vector_unitary_pres.
      assumption.
      assert(2 ^ (s' - s) * 2 ^ (e' - s') * 2 ^ (e - e')= 2 ^ (e - s)).
      type_sovle'. destruct H8.
      repeat apply kron_unitary; auto; try apply id_unitary. 
      split. intuition. split. intuition. split. intuition. 
      rewrite <-H7.
      simpl in *. rewrite <-Reduced_scale in *.
      rewrite QUnit_One_trace. 
      rewrite Reduced_ceval_swap_QUnit_one.
      rewrite QUnit_One_fun_scale.
      destruct H5. destruct  H9. 
      rewrite H10. unfold U_v. 
      unfold outer_product.
      unfold QUnit_One_fun.
      unfold q_update. unfold super.
      repeat rewrite Mmult_adjoint.
      assert(2 ^ (s' - s) * 2 ^ (e' - s') * 2 ^ (e - e')= 2 ^ (e - s)).
      type_sovle'. destruct H11.
      repeat rewrite kron_adjoint.
      repeat rewrite id_adjoint_eq.
      rewrite<-(Mmult_assoc _ (v) †) .
      rewrite (Mmult_assoc _ v ).
      rewrite Mmult_assoc_5. rewrite adjoint_involutive.
      assert((I (2 ^ (s' - s)) ⊗ (U) ⊗ I (2 ^ (e - e')))=
      ((I (2 ^ (s' - s)) ⊗ ((U) †) ⊗ I (2 ^ (e - e'))))†).
      repeat rewrite kron_adjoint. 
      repeat rewrite id_adjoint_eq. rewrite adjoint_involutive.  reflexivity.
      rewrite H11. rewrite Unitary_I.
      repeat rewrite Mmult_1_l; auto_wf.
      repeat rewrite Mmult_1_r; auto_wf.
      reflexivity.  apply kron_unitary.
      apply kron_unitary. apply id_unitary.
      apply transpose_unitary. dom_solve.
      apply id_unitary. lia.  apply WF_NZ_Mixed. apply H0.
      dom_solve. dom_solve.  apply WF_NZ_Mixed. apply H0.
      dom_solve. 
        apply Nat.eq_dec. apply Nat.eq_dec.
Qed.

Theorem rule_QUnit_One_aux' : forall s' e' s e (U: Square (2^(e'-s'))) (v: Vector (2^(e-s)))
(s0 e0:nat) (mu : list (cstate * qstate s0 e0)) (mu': list (cstate * qstate s0 e0)),
s<=s' /\ e' <=e ->
WF_dstate_aux mu->WF_Matrix v->
ceval_single (QUnit_One s' e' U) mu mu' ->
State_eval_dstate (QExp_s s  e  (U_v s' e' s e U† v) ) mu->
State_eval_dstate (QExp_s s  e  v ) mu'.
Proof. intros s' e' s e U v s0 e0 mu. induction mu; intros.
      inversion H2; subst. simpl in *.  split. assumption. lia. 
  -- destruct mu. inversion H2; subst. inversion H10; subst. 
     apply inj_pair2_eq_dec in H7. apply inj_pair2_eq_dec in H7.
     destruct H7. rewrite map2_nil_r in *.
      * econstructor.
       apply rule_QUnit_aux with s' e' U1 ((sigma, rho)). intuition. 
       inversion_clear H0. assumption. apply H1. 
       assumption. inversion_clear H3. assumption.  apply Forall_nil.
       apply Nat.eq_dec. apply Nat.eq_dec.
      
       *destruct a. inversion H2; subst.  
       apply inj_pair2_eq_dec in H7. apply inj_pair2_eq_dec in H7.
       destruct H7.
       apply d_seman_app_aux. 
       apply WF_ceval with (QUnit_One s' e' U1) ([(c,q)]).
       apply WF_state_dstate_aux.  inversion_clear H0. assumption.
       apply ceval_eq with ((StateMap.Raw.map2 (@option_app s0 e0) ([(c, QUnit_One_fun s' e' U1 q)])  ([]))).
       reflexivity.  apply E_Qunit_One.   apply E_nil. dom_solve. 
       eapply ceval_single_dom. apply H11.

      apply WF_ceval with (QUnit_One s' e' U1) ((p :: mu)).
      inversion_clear H0. assumption. assumption.

      econstructor.  apply rule_QUnit_aux with s' e' U1 ((c, q)). intuition. 
      inversion_clear H0. assumption. apply H1. 
      apply ceval_eq with ((StateMap.Raw.map2 (@option_app s0 e0) ([(c, QUnit_One_fun s' e' U1 q)])  ([]))).
      reflexivity.  apply E_Qunit_One.   apply E_nil.
      dom_solve.  eapply ceval_single_dom. apply H11.
      inversion_clear H3. assumption.
      apply Forall_nil.

      apply IHmu. intuition. inversion_clear H0.  assumption. assumption. 
      intuition. inversion_clear H3.  apply State_eval_dstate_Forall.
      discriminate.  assumption. apply Nat.eq_dec. apply Nat.eq_dec.
Qed.    

Theorem rule_QUnit_One : forall s' e' s e (U: Square (2^(e'-s'))) (v: Vector (2^(e-s))),
s<=s' /\ e' <=e ->WF_Matrix v->
{{ QExp_s s  e  (U_v s' e' s e U† v) }} <{ U [[ s' e' ]] }> {{ QExp_s s  e  v }}.
Proof. unfold hoare_triple;
intros s' e' s e U v Hs Hv s0 e0 (mu,IHmu) (mu', IHmu').
intros. 
inversion_clear H; simpl in H2.
rewrite sat_Assert_to_State in *.
inversion_clear H0.
apply sat_F. 
eapply WF_ceval. apply H1. apply H2.
apply rule_QUnit_One_aux' with s' e' U mu.
intuition. intuition. assumption. simpl. assumption. assumption.
Qed.


Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Arith.Peano_dec.
Theorem rule_QUnit_One' : forall s' e' s e (U: Square (2^(e'-s'))) (v: Vector (2^(e-s))),
s<=s' /\ e' <=e ->
{{ QExp_s s  e  v }} <{ U [[ s' e' ]] }> {{ QExp_s s  e  (U_v s' e' s e U v) }}.
Proof. intros s' e' s e U v H Hu. unfold hoare_triple. intros. 
inversion_clear H0. destruct mu. destruct mu'. simpl in *.
inversion H3; subst. 
rewrite sat_Assert_to_State in *. inversion_clear H1. simpl in *. econstructor. econstructor.
simpl. split. apply WF_U_v; try  lia. apply H6.  apply H0. lia.    
assert(v= U_v s' e' s e (adjoint U1) (U_v s' e' s e U1 v) ).
unfold U_v. 
assert(2^(s'-s) * 2^(e'-s')* 2^(e-e')=2^(e-s)). dom_solve. 
 destruct H0.
rewrite <-Mmult_assoc.
repeat rewrite kron_mixed_product. 
repeat rewrite Mmult_1_r; auto_wf. 
apply inj_pair2_eq_dec in H6. apply inj_pair2_eq_dec in H6.
 destruct H6. dom_solve. destruct H5.
 rewrite H9. repeat rewrite id_kron.   
 rewrite Mmult_1_l. reflexivity.  
 rewrite sat_Assert_to_State in H1. inversion_clear H1.
 simpl in H11. inversion_clear H11. destruct H1. destruct H1.
 assert(2^(e-s)= 2^(s'-s) * 2^(e'-s')* 2^(e-e')). type_sovle'.
 destruct H14. apply H1.
 apply Nat.eq_dec. apply Nat.eq_dec.  
 assert(s <= s' /\ e' <= e). lia. 
apply (rule_QUnit_One _ _ _ _ ( U1) (U_v s' e' s e ( U1) v)) in H4. 
unfold hoare_triple in H4.
 apply H4 with (StateMap.Build_slist sorted).
 econstructor. assumption. 
 apply E_Qunit_One. assumption. 
 rewrite<- H0. assumption.
 apply pure_state_vector_unitary_pres.  
 rewrite sat_Assert_to_State in H1. inversion_clear H1.
 simpl in H7. inversion_clear H7. destruct H1. assumption.
 assert(2^(s'-s) * 2^(e'-s')* 2^(e-e')=2^(e-s)). dom_solve.
 destruct H5. 
 apply kron_unitary. apply kron_unitary. apply id_unitary.
 dom_solve. apply id_unitary.
Qed.

Definition UCtrl_v (s0 e0 s1 e1 s e: nat) (U: nat->Square (2^(e1-s1))) (v: Vector (2^(e-s))) :=
  (big_sum (fun i:nat =>
       (I (2^(s0-s)) ⊗ (∣ i ⟩_ (2^(e0-s0)) × ⟨ i ∣_ (2^(e0-s0)) ) ⊗ (I (2^(e-e0)))) ×
       (I (2^(s1-s)) ⊗ (U i) ⊗ (I (2^(e-e1))))) (2^(e0 -s0))) × v.


Local Open Scope nat_scope.
Lemma  pure_vector_UCtrl:forall (s0 e0 s1 e1 s e: nat) (U: nat->Square (2^(e1-s1))) (v: Vector (2^(e-s))),
( and (s <= s0 /\ s0 <= e0 <= s1) (s1 <= e1 <= e))%nat -> 
( forall i : nat, WF_Unitary (U i)) ->
Pure_State_Vector v ->
Pure_State_Vector (UCtrl_v s0 e0 s1 e1 s e U v).
Proof. intros. unfold UCtrl_v.
assert((2 ^ (s0 - s) * 2 ^ (e0 - s0) * 2 ^ (e - e0))%nat=(2 ^ (e - s))%nat ).
type_sovle'. destruct H2.
apply pure_state_vector_unitary_pres. assumption.
assert((2 ^ (e - s)= (2 ^ (s0 - s) * 2 ^ (e0 - s0) * 2 ^ (e - e0))%nat )).
type_sovle'. destruct H2.
apply (@QUnit_Ctrl_unitary s e s0 e0 s1 e1); try lia. 
apply H0. 
Qed.



Theorem rule_QUnit_Ctrl_aux{s' e':nat}:  forall s0 e0 s1 e1 s e (U: nat -> Square (2^(e1-s1))) (v: Vector (2^(e-s)))
 (st :state s' e') (st': state s' e'),
s<=s0 /\ e1 <=e ->
WF_state st->
ceval_single (QUnit_Ctrl s0 e0 s1 e1 U) [st] [st'] ->
State_eval (QExp_s s  e   v ) st->
State_eval (QExp_s s  e  (UCtrl_v s0 e0 s1 e1 s e ( U) v)) st'.
Proof. 
intros. simpl in *. destruct H2. destruct H3.
destruct st.  
inversion H1; subst. inversion H6; subst.
clear H6. apply inj_pair2_eq_dec in H10.
apply inj_pair2_eq_dec in H10. subst.
injection H14. intros.
split.
assert((2 ^ (s0 - s) * 2 ^ (e0 - s0) * 2 ^ (e - e0))%nat=(2 ^ (e - s))%nat ).
dom_solve. destruct H8.
 apply pure_vector_UCtrl; try lia; try assumption. dom_solve. dom_solve.
 assert((2 ^ (e - s)= (2 ^ (s0 - s) * 2 ^ (e0 - s0) * 2 ^ (e - e0))%nat )).
dom_solve. destruct H8.  assumption.
split. intuition. split. intuition. split. intuition. 
rewrite <-H6.
simpl in *. rewrite <-Reduced_scale in *.
rewrite QUnit_Ctrl_trace; try lia; try auto_wf; try assumption.  
rewrite Reduced_ceval_swap_QUnit_Ctrl; try lia; try auto_wf; try assumption.
rewrite QUnit_Ctrl_fun_scale.
destruct H4. destruct  H8. 
rewrite H9. unfold UCtrl_v . 
unfold outer_product.
unfold QUnit_Ctrl_fun.
unfold q_update. unfold super.
assert(2 ^ (s0 - s) * 2 ^ (e0 - s0) * 2 ^ (e - e0)= 2 ^ (e - s)).
type_sovle'. destruct H10.
repeat rewrite Mmult_adjoint.
rewrite<-(Mmult_assoc _ (v) †) .
rewrite (Mmult_assoc _ v ). reflexivity.
apply H5. apply H5.  
 apply Nat.eq_dec. apply Nat.eq_dec.
Qed.


Theorem rule_QUnit_Ctrl_aux'{s' e':nat} : forall s0 e0 s1 e1 s e (U: nat -> Square (2^(e1-s1))) (v: Vector (2^(e-s)))
(mu : list (cstate * qstate s' e')) (mu': list (cstate * qstate s' e')),
s<=s0 /\ e1 <=e ->
WF_dstate_aux mu->
ceval_single (QUnit_Ctrl s0 e0 s1 e1 U) mu mu' ->
State_eval_dstate (QExp_s s  e  v ) mu->
State_eval_dstate (QExp_s s  e  (UCtrl_v s0 e0 s1 e1 s e ( U) v) ) mu'.
Proof.  induction mu; intros  mu' H H0 . intros. inversion H1; subst.
  -- simpl in *. split. unfold UCtrl_v.  
  assert((2 ^ (e - s))%nat =(2 ^ (s0 - s) * 2 ^ (e0 - s0) * 2 ^ (e - e0))%nat ).
  dom_solve. destruct H5. apply WF_mult.
  apply WF_Msum. intros. 
  apply WF_mult.  auto_wf.  
  apply WF_kron; type_sovle'; auto_wf. 
  apply WF_kron; type_sovle'; auto_wf. 
  apply H3. apply H2. lia.   
  -- destruct mu; intros. inversion H1; subst. inversion H11; subst. 
     apply inj_pair2_eq_dec in H8. apply inj_pair2_eq_dec in H8.
     destruct H8. rewrite map2_nil_r in *.
      * econstructor. inversion_clear H2.
       apply rule_QUnit_Ctrl_aux with  ((sigma, rho));
       try apply WF_state_dstate_aux in H0; try assumption. 
       econstructor. 
       apply Nat.eq_dec. apply Nat.eq_dec.
      
       *destruct a. inversion H1; subst.  
       apply inj_pair2_eq_dec in H8. apply inj_pair2_eq_dec in H8.
       destruct H8. 
       apply d_seman_app_aux. 
       apply WF_ceval with (QUnit_Ctrl s0 e0 s1 e1 U1) ([(c,q)]).
       apply WF_state_dstate_aux.  inversion_clear H0. assumption.
       apply ceval_QUnit_Ctrl; try dom_solve; try assumption.  

      apply WF_ceval with (QUnit_Ctrl s0 e0 s1 e1 U1) ((p :: mu)).
      inversion_clear H0. assumption. assumption.

      econstructor. inversion_clear H2.
      apply rule_QUnit_Ctrl_aux with  ((c,q));
      try inversion_clear H0; try assumption. 
      apply ceval_QUnit_Ctrl;try dom_solve; try assumption. 
      econstructor. 

      apply IHmu. intuition. inversion_clear H0.  assumption. assumption. 
      intuition. inversion_clear H2.  apply State_eval_dstate_Forall.
      discriminate.  assumption. apply Nat.eq_dec. apply Nat.eq_dec.
Qed.    


Theorem rule_QUnit_Ctrl : forall s0 e0 s1 e1 s e (U: nat -> Square (2^(e1-s1))) (v: Vector (2^(e-s))),
s<=s0 /\ e1 <=e ->
{{ QExp_s s  e  v }} <{U [[s0 e0]] [[s1 e1]]}> {{ QExp_s s  e  ( UCtrl_v s0 e0 s1 e1 s e U v) }}.
Proof. unfold hoare_triple.
intros  s0 e0 s1 e1 s e U v Hs s' e' (mu,IHmu) (mu', IHmu').
intros. 
inversion_clear H; simpl in H2.
rewrite sat_Assert_to_State in *.
inversion_clear H0.
apply sat_F. 
eapply WF_ceval. apply H1. apply H2. 
apply  rule_QUnit_Ctrl_aux' with mu .
intuition. intuition. assumption. assumption.  
Qed.

Lemma fst_mult_swap: forall (x:R) (y:C),
fst (x * y)%C=  (x * fst y)%R
 .
Proof. intros. destruct y. simpl. rewrite Rmult_0_l.
      rewrite Rminus_0_r. reflexivity. Qed.


Lemma  RtoC_eq: forall r1 r2,
r1=r2-> RtoC r1= RtoC r2  .
Proof. intros. rewrite<-H. reflexivity. Qed.


Local Open Scope C_scope.
Lemma Reduced_Meas_trace_eq{s0 e0:nat}: forall s' e' s e z (v:Vector (2^(e-s))) (q:Square (2^(e0-s0))),
WF_qstate q->
s0<=s/\ s<=s'/\ s' <= e'/\ e'<=e /\ e<=e0-> (z< 2^(e'-s')) ->WF_Matrix v->
(R1 / Cmod (trace q))%R .* Reduced q s e = outer_product v v->
(norm (@U_v (e'-s') (e-s) s' e' s e (∣ z ⟩_ (2^(e' - s')) × ⟨ z ∣_ (2^(e' - s'))) v) *
norm (@U_v (e'-s') (e-s) s' e' s e (∣ z ⟩_ (2^(e' - s')) × ⟨ z ∣_ (2^(e' - s'))) v))%R * (trace q) = 
@trace (2^(e0-s0)) (QMeas_fun  s' e' z q).
Proof. intros s' e' s e z v q Uq. intros. 
rewrite <-(Reduced_trace _ _ _ s e).
rewrite <-(Reduced_trace _ _ ((QMeas_fun s' e' z q)) s e).
rewrite Reduced_ceval_swap_QMeas.
assert(Reduced q s e = (Cmod (trace q)).*  (outer_product v v)).
rewrite<-H2. rewrite Rdiv_unfold. rewrite Rmult_1_l.
rewrite Mscale_assoc. rewrite Mixed_State.RtoC_mult.
 rewrite Rinv_r. rewrite Mscale_1_l. reflexivity.
 assert(Cmod (trace q) > 0%R)%R. apply nz_mixed_state_Cmod_1.
 apply Uq. lra. rewrite H3. rewrite <-QMeas_fun_scale.
repeat rewrite trace_mult_dist.
rewrite Cmult_comm. rewrite <-Cmult_assoc.
 f_equal. unfold QMeas_fun. 
 assert(trace (outer_product v v)= C1).
 rewrite <-H2. rewrite trace_mult_dist.
  rewrite Reduced_trace. rewrite Rdiv_unfold.
  rewrite Rmult_1_l. 
  assert(trace q= (fst (trace q), snd (trace q))).
  destruct (trace q). reflexivity.
  rewrite H4. rewrite Cmod_snd_0. 
  rewrite nz_mixed_state_trace_real.
  simpl. unfold Cmult. simpl. 
  repeat rewrite Rmult_0_l. rewrite Rmult_0_r.
  rewrite Rplus_0_r. rewrite Rminus_0_r.
  rewrite Rinv_l. reflexivity.
  assert(fst (trace q) > 0%R)%R.
  apply nz_mixed_state_trace_gt0. apply Uq.
  lra. apply Uq. simpl. 
  apply nz_mixed_state_trace_gt0. apply Uq.
  simpl. rewrite nz_mixed_state_trace_real.
  reflexivity. apply Uq. simpl.
  lia. apply WF_NZ_Mixed. apply Uq. rewrite H4.
  rewrite Cmult_1_l.
    
rewrite inner_trace. unfold U_v.
  unfold q_update. unfold super.
  unfold outer_product. 
  repeat rewrite Mmult_adjoint.
  assert(2 ^ (s' - s) * 2 ^ (e' - s') * 2 ^ (e - e')= 2 ^ (e - s))%nat.
type_sovle'.  destruct H5.
  repeat rewrite kron_adjoint.
  repeat rewrite id_adjoint_eq.
  rewrite <-Mmult_assoc. rewrite (Mmult_assoc _ v).
  rewrite Mmult_adjoint. rewrite adjoint_involutive.
  remember ((I (2 ^ (s' - s))
  ⊗ (∣ z ⟩_ (2^(e' - s')) × ⟨ z ∣_ (2^(e' - s')))
  ⊗ I (2 ^ (e - e')) × (v × (v) †)
  × (I (2 ^ (s' - s))
     ⊗ (∣ z ⟩_ (2^(e' - s')) × ⟨ z ∣_ (2^(e' - s')))
     ⊗ I (2 ^ (e - e'))))).
  assert(m=Zero \/ m<>Zero). 
  apply Classical_Prop.classic.
  destruct H5. rewrite H5. rewrite Zero_trace.
  reflexivity. 
assert(@trace ((2 ^ (s' - s) * 2 ^ (e' - s') *
2 ^ (e - e'))) m=
(fst (@trace ((2 ^ (s' - s) * 2 ^ (e' - s') *
2 ^ (e - e'))) m), snd (@trace ((2 ^ (s' - s) * 2 ^ (e' - s') *
2 ^ (e - e'))) m))). 
destruct (trace m). reflexivity. rewrite H6. 
rewrite nz_mixed_state_trace_real_aux. simpl. reflexivity.
assert(super (I (2 ^ (s' - s))
⊗ (∣ z ⟩_ (2^(e' - s')) × ⟨ z ∣_ (2^(e' - s')))
⊗ I (2 ^ (e - e')))  ((v × (v) †)) = m).
rewrite Heqm. unfold super.
repeat rewrite kron_adjoint. 
rewrite Mmult_adjoint. repeat rewrite id_adjoint_eq.
 rewrite adjoint_involutive. reflexivity.
 rewrite <-H7. 
  apply nz_mixed_super_aux. auto_wf.
  apply Vector_nz_Mix_State_aux. assumption. 
 intro. rewrite H8 in *. unfold outer_product  in *.
 rewrite Mmult_0_l in *. rewrite Zero_trace in *.
 injection H4. lra.  rewrite H7. assumption.
   apply WF_U_v. lia. auto_wf. auto_wf.
   lia. apply WF_NZ_Mixed. apply Uq.
   assumption. lia. unfold QMeas_fun. 
   unfold q_update. apply WF_super.
   auto_wf. apply WF_NZ_Mixed. apply Uq.
   lia.     apply WF_NZ_Mixed. apply Uq.
Qed. 

Lemma QMeas_not_Zero_trace{s0 e0:nat}: forall s' e' z (q:Square (2^(e0-s0)))(c:cstate ),
WF_qstate q->
s0 <= s' /\ s' <= e' <= e0 ->
(z< 2^(e'-s')) ->
(QMeas_fun  s' e' z q)= Zero <->
@trace (2^(e0-s0)) (QMeas_fun  s' e' z q) = C0.
Proof. intros. split. intros. rewrite H2. rewrite Zero_trace.
       reflexivity. intros. 
       apply  Classical_Prop.NNPP. intro. 
       assert( WF_qstate (QMeas_fun s' e' z q) ).
       apply WF_qstate_QMeas; try assumption.
      apply WF_qstate_in_01 in H4. unfold q_trace in H4. 
       rewrite H2 in H4. rewrite Cmod_0 in H4. lra.
Qed.
       

Lemma  Rmult_pow: forall r:R, 
(r*r = r^2)%R .
Proof. simpl. intros. rewrite  Rmult_1_r. auto.
Qed.


Lemma QMeas_not_Zero{s0 e0:nat}: forall s' e' s e z (v:Vector (2^(e-s))) (q:Square (2^(e0-s0))) (c:cstate),
WF_qstate q->
s0<=s/\ s<=s'/\ s' <= e'/\ e'<=e /\ e<=e0-> 
(z< 2^(e'-s')) ->WF_Matrix v->
(R1 / Cmod (trace q))%R .* Reduced q s e = outer_product v v->
(QMeas_fun  s' e' z q) = Zero <->
(norm (@U_v (e'-s') (e-s) s' e' s e (∣ z ⟩_ (2^(e' - s')) × ⟨ z ∣_ (2^(e' - s'))) v)) = 0%R.
Proof. intros. split; intros. 
       apply QMeas_not_Zero_trace in H4; try assumption; try lia. 
       rewrite <-(Reduced_Meas_trace_eq _ _  s e _ v) in H4; try assumption.
       apply WF_qstate_in_01 in H. unfold q_trace in *. 
       apply Cmult_integral in H4. destruct H4. 
       rewrite Rmult_pow in H4. rewrite <-Rsqr_pow2 in H4.
       injection H4. intros.
       apply Rsqr_0_uniq in H5. assumption. rewrite H4 in H. 
       rewrite Cmod_0 in H. lra.
       apply Classical_Prop.NNPP. intro.
       assert( @trace (2^(e0-s0)) (QMeas_fun  s' e' z q) <> C0).
       intro.  apply QMeas_not_Zero_trace in H6; try assumption.
       rewrite H6 in H5. destruct H5. reflexivity. lia. 
       rewrite <-(Reduced_Meas_trace_eq _ _  s e _ v) in H6; try assumption.
       rewrite H4 in H6.
        rewrite Rmult_0_l in H6. rewrite Cmult_0_l in H6.
        destruct H6. reflexivity.
Qed.



Lemma big_and_eval{ s e}: forall (F: nat-> State_formula) n i (st: state s e),
State_eval (big_Sand F n) st ->
 i<n ->State_eval (F i) st.
Proof. induction n; intros.  lia.
       simpl in H. destruct (eq_dec i n).
       rewrite e0. apply H.
       apply IHn. apply H. lia. 
Qed.

Require Import Mixed_State.
Local Open Scope nat_scope.
Lemma normalize_Pure_State_Vector{n:nat}:forall (v:Vector n), 
WF_Matrix v->norm v <> 0%R->
Pure_State_Vector (/norm v .* v).
Proof. intros. econstructor. auto_wf.
       assert(WF_Matrix ((/ norm v .* v) † × (/ norm v .* v))). auto_wf.
       prep_matrix_equality.
       destruct x. destruct y. 
        assert(((/ norm v .* v) † × (/ norm v .* v)) 0 0= ⟨ (/ norm v .* v) , (/ norm v .* v) ⟩). unfold inner_product. simpl. reflexivity.
        rewrite H2.
       rewrite <-inner_trace'. 
       rewrite Mscale_adj.
       rewrite Mscale_mult_dist_r.
       repeat rewrite Mscale_mult_dist_l. rewrite Mscale_assoc. rewrite trace_mult_dist. 
       rewrite <-RtoC_inv. rewrite Cconj_R. rewrite RtoC_mult.  rewrite <-Rinv_mult.
        rewrite trace_mult at 1.  
        rewrite inner_trace; try assumption. 
        assert(NZ_Mixed_State_aux (v × (v) †)). apply Vector_nz_Mix_State_aux; try assumption.  intro. destruct H0.
        apply norm_zero_iff_zero; try assumption.  unfold I.  simpl.
        assert(trace (v × (v) †)= (fst (trace (v × (v) †)), snd (trace (v × (v) †)))). destruct (trace (v × (v) †)). reflexivity.
        rewrite H4. simpl. 
        rewrite nz_mixed_state_trace_real_aux; try assumption. rewrite RtoC_inv. apply Cinv_l. apply C0_fst_neq.
        simpl. apply nz_mixed_state_trace_gt0_aux in H3.
        lra. apply nz_mixed_state_trace_gt0_aux in H3.
        lra. assumption.
        assert( WF_Matrix ( I 1)). auto_wf.
     
        unfold WF_Matrix in *.
        rewrite H1. rewrite H2.
        reflexivity. right. lia. 
        right. lia.
        assert( WF_Matrix ( I 1)). auto_wf.
        unfold WF_Matrix in *.
        rewrite H1. rewrite H2.
        reflexivity. left. lia. 
        left. lia.     
Qed.




Local Open Scope C_scope.
Theorem rule_Meas_aux:  forall s' e' s e (v: Vector (2^(e-s))) z x
(s0 e0:nat) (st :state s0 e0) (st': state s0 e0) (P:nat-> Pure_formula),
(norm (U_v s' e' s e (∣ z ⟩_ (2^(e' - s')) × ⟨ z ∣_ (2^(e' - s'))) v)<> 0%R) ->
s0 <= s /\ s <= s' /\ s' <= e' /\ e' <= e <= e0-> 
WF_state st-> (z< 2^(e'-s'))->
(State_eval ((QExp_s  s  e  v ) /\s (big_Sand (fun i:nat => (PAssn x (ANum i) (P i))) (2^(e'-s')))) st ) ->
State_eval ( (P z) /\s  
(QExp_s  s  e  ((/ (@norm (2^(e-s)) ((U_v s' e' s e (∣ z ⟩_ (2^(e' - s')) × ⟨ z ∣_ (2^(e' - s'))) v))))%R .* 
                                                (U_v s' e' s e (∣ z ⟩_ (2^(e' - s')) × ⟨ z ∣_ (2^(e' - s'))) v)))) 
(s_scale (( / ((@norm (2^(e-s)) ((U_v s' e' s e  (∣ z ⟩_ (2^(e' - s')) × ⟨ z ∣_ (2^(e' - s'))) v)))%R ^ 2))) 
                                                    (c_update x z (fst st), QMeas_fun s' e' z (snd st))).
Proof. 
      intros s' e' s e v z x s0 e0 st st'. intros.
      remember (( norm (U_v s' e' s e (∣ z ⟩_ (2^(e' - s')) × ⟨ z ∣_ (2^(e' - s'))) v))%R). 
      destruct H3. destruct H3.  
      split.  unfold s_scale. simpl. 
      assert(State_eval_dstate (P z)  [(c_update x z (fst st),(snd st))]).
      apply rule_PAssgn_aux with x (ANum z) [st]. 
      apply WF_state_dstate_aux. assumption.
      assert([(c_update x z (fst st), snd st)]= StateMap.Raw.map2 option_app ([(c_update x z (fst st), snd st)])  ([])).
      reflexivity. rewrite H6. assert(z= aeval st (ANum z)). 
      simpl. reflexivity. remember ((ANum z) ). destruct st.
      rewrite H7.  apply E_Asgn. apply E_nil. simpl. auto.
      apply subset_empty. 
      econstructor.  
      apply (big_and_eval _ _ z) in H4; try assumption.
       apply Forall_nil.     
      simpl in *.  inversion_clear H6. 
      apply state_eq_Pure with ((c_update x z (fst st), snd st)).
      simpl. reflexivity. apply H7. 
      split. rewrite Heqr. rewrite RtoC_inv; try lra.  apply normalize_Pure_State_Vector; try lra.  apply WF_U_v; try lia.  destruct H3. auto_wf. auto_wf.
      split. intuition. split. intuition.
      split. intuition. 
      destruct st. destruct st'.  simpl in *. unfold q_scale. rewrite Mscale_assoc.
      rewrite Cmult_comm. rewrite Rmult_1_r.
      rewrite <-Reduced_scale in *.  rewrite <-Mscale_assoc.
      remember ((R1 / Cmod (trace q))%R).
      remember ((R1 / Cmod (trace ((/ (r * r))%R .* QMeas_fun s' e' z q)))%R).
      rewrite Reduced_ceval_swap_QMeas; try assumption; try lia. 
      rewrite  QMeas_fun_scale; try lia; auto_wf .
      assert(r1=r0). 
      rewrite Heqr1. rewrite Heqr0. f_equal. f_equal.
      rewrite trace_mult_dist. rewrite Heqr.
      rewrite <-(Reduced_Meas_trace_eq _ _ s e _ v); try assumption; try lia. 
      rewrite Cmult_assoc. rewrite RtoC_mult.
      rewrite Rinv_l.   apply Cmult_1_l.
      apply Rmult_integral_contrapositive_currified; try rewrite <-Heqr; try assumption.
      apply H3.  rewrite <-Heqr0. apply H5. rewrite H6.
      destruct H5. destruct H7. destruct H8.
      rewrite H9.   unfold U_v. unfold outer_product. 
      assert(((2 ^ (s' - s) * 2 ^ (e' - s') *
      2 ^ (e - e')))=2^((e0-s0)-(e0-e)-(s-s0)))%nat. type_sovle'. destruct H9.
      rewrite Mscale_mult_dist_l. rewrite Mscale_adj.
      rewrite Mscale_mult_dist_r. repeat rewrite <-Mscale_mult_dist_l.
      rewrite Mscale_assoc. rewrite Cconj_R. rewrite RtoC_mult.
      repeat rewrite Mscale_mult_dist_l. f_equal.
      rewrite Rinv_mult. reflexivity.
       unfold QMeas_fun.  unfold q_update. unfold super.
       assert(2 ^ (s' - s) * 2 ^ (e' - s') * 2 ^ (e - e')= 2 ^ (e - s))%nat.
      type_sovle'. destruct H9.
      repeat rewrite Mmult_adjoint. repeat rewrite kron_adjoint. 
      repeat rewrite id_adjoint_eq. repeat rewrite adjoint_involutive.
      repeat  rewrite Mmult_assoc. reflexivity.
      apply WF_NZ_Mixed. apply H1.
Qed.

Lemma dstate_to_list_app{s e:nat}: forall (mu1 mu2: list (dstate s e)),
dstate_to_list (mu1++ mu2) = (dstate_to_list mu1) ++ (dstate_to_list mu2).
Proof. induction mu1; intros. simpl. reflexivity.
      simpl. f_equal. apply IHmu1.
  
Qed.


Lemma fun_dstate_to_list {s e:nat}: forall n_0 (f: nat-> dstate s e),
dstate_to_list (fun_to_list f  n_0)=
fun_to_list (fun i:nat => StateMap.this (f i)) n_0  .
Proof. induction n_0. intros. simpl. reflexivity.
       intros. simpl.  rewrite dstate_to_list_app. 
       rewrite IHn_0. simpl.  reflexivity.
Qed.

Local Open Scope nat_scope.


Lemma  big_app_map2'{s e:nat}: forall n0 (f1: nat-> R) (f2: nat-> ((cstate * qstate s e)))  mu mu',
(forall i, i < n0->snd (f2 i) = Zero -> f1 i =0%R) ->
big_map2' (fun_to_list f1 n0) (fun_to_list (fun i=> [f2 i]) n0) mu ->
big_app' (fun x =>s_scale  (f1 x) (f2 x)) n0 mu'->
mu= mu'.
Proof.  induction n0; intros. inversion_clear H0; inversion_clear H1. 
 reflexivity. 
 simpl in H0.
 apply big_map2_app' in H0. 
 destruct H0. destruct H0. destruct H0.
 destruct H0.  
 
 inversion_clear H1.
simpl in H4.
destruct (Req_dec (f1 n0) 0).
rewrite H1 in *. inversion H3; subst.
inversion H11; subst. inversion_clear H12.
simpl. rewrite map2_nil_r. apply IHn0 with f1 f2; try assumption.
intros. apply H; try assumption; try lia. 
lra. assert(snd (f2 n0) = Zero).
apply (scale_Zero (f1 n0) (snd (f2 n0)) H4). 
apply C0_fst_neq.  assumption. apply H in H6.
rewrite H6 in *. lra. lia.  rewrite H2.
f_equal.  apply IHn0 with f1 f2; try assumption.
intros. apply H; try assumption; try lia. 
inversion_clear H3.  inversion_clear H6. 
rewrite map2_nil_r. inversion H1; subst.
rewrite<-H6 in *. simpl in *. rewrite Mscale_0_l in *.
destruct H4. reflexivity. unfold s_scale.
destruct (f2 n0). simpl. reflexivity.
repeat rewrite fun_to_list_length. reflexivity.
reflexivity.
Qed.


Local Open Scope com_scope.


Lemma  big_app_eq_bound{s e:nat}: forall (f1 f2: nat-> list (cstate *qstate s e)) n0,
(forall i, (i<n0)%nat -> f1 i = f2 i) -> big_app f1 n0 = big_app f2 n0.
Proof. intros. induction n0; intros. simpl. reflexivity.
    simpl. f_equal. apply IHn0. intros. apply H. lia. 
    apply H. lia.
  
Qed.


Lemma  big_app_eq_bound'{s e:nat}: forall (f1 f2: nat->  (cstate *qstate s e)) n0 mu1 mu2,
big_app' f1 n0 mu1->
big_app' f2 n0 mu2->
(forall i, (i<n0)%nat -> f1 i = f2 i) -> mu1 =mu2.
Proof.  induction n0; intros; inversion_clear H; inversion_clear H0. 
       simpl. reflexivity.
       apply IHn0; try assumption. intros. apply H1. lia.
       rewrite H1 in H2 . rewrite H2 in H. destruct H. reflexivity.
       lia. 
       rewrite <-H1 in H. rewrite H in H2. destruct H2. reflexivity.
       lia. 
       
      f_equal. apply IHn0; try assumption. intros. apply H1. lia.
      f_equal. 
    apply H1. lia.
Qed.


Lemma  big_sum_mult_l_R: forall r (f:nat-> R) n,
(r * big_sum f n)%R = (big_sum (fun i=> (r * (f i)))%R n) .
Proof. induction n; intros. simpl. rewrite Rmult_0_r.
       reflexivity.
       simpl. rewrite Rmult_plus_distr_l.
       rewrite IHn. reflexivity.
Qed.



Lemma fst_mult:forall (c1 c2: C), 
snd c1=0%R \/ snd c2=0%R ->
fst (c1 * c2)%C= (fst c1 * fst c2)%R.
Proof. intros. destruct c1. destruct c2. 
      simpl in *. destruct H; rewrite H;
      [rewrite Rmult_0_l| rewrite Rmult_0_r]; rewrite Rminus_0_r;
      reflexivity. 
Qed.

Lemma Cinv_snd: forall (c:C),
snd c = 0%R ->
snd ( / c) = 0%R.
Proof. intros. destruct c. simpl.
       simpl in H. rewrite H.
       rewrite Rdiv_unfold.
       rewrite Ropp_0.
       repeat rewrite Rmult_0_l.
       reflexivity.
  
Qed.


Lemma scale_0{s e:nat}: forall (q:qstate s e) (c:C),
q <> Zero->
@scale (2^(e-s)) (2^(e-s)) c  q = Zero ->
c=C0.
Proof. intros. destruct (Ceq_dec c C0); auto.
      apply scale_Zero in H0; try assumption.
       destruct H; try assumption. 
Qed.

Lemma scale_not_0{s e:nat}: forall (q:qstate s e) (c:C),
q <> Zero-> c<>C0 ->
@scale (2^(e-s)) (2^(e-s)) c  q <> Zero.
Proof. intros. intro. 
       destruct (Ceq_dec c C0); auto.
       apply scale_Zero in H1; try assumption.
       destruct H. assumption.
Qed.

Lemma Meas_distribution_formula:forall s' e' s e (v: Vector (2^(e-s)))  (P :nat-> (Pure_formula)),
s <= s' /\ s' < e' /\ e' <= e->
Pure_State_Vector v->
distribution_formula (big_pOplus 
(fun i:nat=> (@norm (2^(e-s)) ((U_v s' e' s e (∣ i ⟩_ (2^(e'-s')) × ⟨ i ∣_ (2^(e'-s'))) v))) ^ 2)%R
(fun i:nat=>  ((P i)) /\s (QExp_s  s  e 
(( / ((@norm (2^(e-s)) ((U_v  s' e' s e (∣ i ⟩_ (2^(e'-s')) × ⟨ i ∣_ (2^(e'-s'))) v)))))%R.* 
(U_v s' e' s e (∣ i ⟩_ (2^(e'-s')) × ⟨ i ∣_ (2^(e'-s'))) v)))) (2^(e'-s'))) .
Proof.

intros. 
econstructor. 
rewrite big_pOplus_get_npro. rewrite <-fun_to_list_big_Oplus_eq.
apply Forall_fun_to_list. simpl. intros. split. auto.
split; try lia.
apply WF_scale.
apply WF_U_v; try lia. apply H0.
auto_wf. 
split.
rewrite big_pOplus_get_pro.
apply Forall_fun_to_list.   intros.
rewrite <-Rsqr_pow2.
apply Rle_0_sqr. 



rewrite sum_over_list_big_pOplus.
simpl. 
erewrite (big_sum_eq_bounded); intros;
try rewrite <-inner_trace; try rewrite Rmult_1_r;
try reflexivity. rewrite<- big_sum_fst.
unfold U_v. destruct H0.   
erewrite (big_sum_eq_bounded); intros;
try  rewrite Mmult_adjoint;
try rewrite trace_mult;
[| assert(2^(s'-s) * 2^(e'-s') * 2^(e-e')=2^(e-s)); type_sovle'; destruct H3];
try repeat rewrite kron_adjoint; try repeat rewrite id_adjoint_eq;
try rewrite Mmult_adjoint; try rewrite adjoint_involutive; try
remember ((I (2 ^ (s' - s))
⊗ (∣ x ⟩_ (2 ^ (e' - s')) × ⟨ x ∣_ (2 ^ (e' - s')))
⊗ I (2 ^ (e - e'))));try rewrite<- Mmult_assoc; try 
try rewrite (Mmult_assoc _ m m); try rewrite Heqm; try repeat rewrite kron_mixed_product;
[| Msimpl;  rewrite<- Mmult_assoc ;
try rewrite (Mmult_assoc _ (⟨ x ∣_ (2 ^ (e' - s'))) ); rewrite base_inner_1; unfold c_to_Vector1; Msimpl; try assumption;
try reflexivity].
rewrite <-big_sum_trace. rewrite <-Mmult_Msum_distr_r.
rewrite <-Mmult_Msum_distr_l. rewrite <-kron_Msum_distr_r.
rewrite <-kron_Msum_distr_l. rewrite big_sum_I.
repeat rewrite id_kron. rewrite Mmult_1_r.
assert(2^(e-s)=2^(s'-s) * 2^(e'-s') * 2^(e-e')); type_sovle'; destruct H2.
 rewrite H1. rewrite trace_I. reflexivity.
 assert(2^(e-s)=2^(s'-s) * 2^(e'-s') * 2^(e-e')); type_sovle'; destruct H2.
 auto_wf. apply WF_U_v; auto_wf; try lia. 
 destruct H0. assumption.
Qed.


Local Open Scope nat_scope.
Theorem rule_Meas_aux':forall s' e' s e (v: Vector (2^(e-s))) x (P :nat-> (Pure_formula))
(s0 e0:nat) (st :state s0 e0) (mu: dstate s0 e0),
s <= s' /\ e' <= e->
ceval (QMeas x s' e') st mu-> 
sat_Assert st ((QExp_s  s  e  v) /\s big_Sand (fun i:nat => (PAssn x (ANum i) (P i))) (2^(e'-s'))) ->
sat_Assert mu ((big_pOplus 
(fun i:nat=> (@norm (2^(e-s)) ((U_v s' e' s e (∣ i ⟩_ (2^(e'-s')) × ⟨ i ∣_ (2^(e'-s'))) v))) ^ 2)%R
(fun i:nat=>  ((P i)) /\s (QExp_s  s  e 
(( / ((@norm (2^(e-s)) ((U_v  s' e' s e (∣ i ⟩_ (2^(e'-s')) × ⟨ i ∣_ (2^(e'-s'))) v)))))%R.* 
(U_v s' e' s e (∣ i ⟩_ (2^(e'-s')) × ⟨ i ∣_ (2^(e'-s'))) v)))) (2^(e'-s')))).
Proof. 
intros s' e' s e v x P s0 e0 st mu He  H H0 . 
intros. destruct mu as [ mu IHmu]. 
inversion_clear H; simpl in H2.
inversion H2; subst. 
inversion H9; subst. clear H9. 
rewrite sat_Assert_to_State in *.

remember (fun j:nat => (@norm (2^(e-s))
(U_v s' e' s e(∣ j ⟩_ (2^(e'-s')) × ⟨ j ∣_ (2^(e'-s'))) v))).


pose (@big_app'_exsist s0 e0 ((2 ^ (e' - s'))) ((fun j : nat =>
s_scale ((r j) ^2) 
(s_scale ( /( r j ^ 2))%R (c_update x j (fst st),  QMeas_fun s' e' j (snd st)))))).
destruct e1.

inversion_clear H0. apply State_eval_conj in H6. 
destruct H6. inversion_clear H0. simpl in H7.
apply WF_state_dstate in H5.

assert(x0 = mu''). eapply big_app_eq_bound'. apply H4. apply H10.
intros.  unfold s_scale. simpl.

assert((QMeas_fun s' e' i (snd st)= Zero) \/ QMeas_fun s' e' i (snd st)<> Zero).
apply Classical_Prop.classic. destruct H9. 
assert( r i= 0%R). rewrite Heqr. 
eapply (@QMeas_not_Zero s0 e0 s' e' _ _ _ _ (snd st));
try assumption; try rewrite Reduced_scale;try apply (fst st); try apply H7.
try dom_solve. 
 rewrite H9. rewrite H11.
repeat rewrite Rmult_0_l. rewrite Mscale_0_l. reflexivity. 
assert( r i <>0%R).   rewrite Heqr.  intro.  
eapply (@QMeas_not_Zero s0 e0 s' e' _ _ _ _ (snd st)) in H11;
try assumption; try rewrite Reduced_scale;try apply (fst st); try apply H7.
destruct H9. 
 try assumption. dom_solve. 
rewrite Mscale_assoc.  rewrite RtoC_mult. 
rewrite Rinv_r. rewrite Mscale_1_l.  unfold QMeas_fun.
reflexivity. rewrite Rmult_1_r. rewrite Rmult_pow.
rewrite <-Rsqr_pow2. intro. apply Rsqr_0_uniq in H12. 
destruct H11; assumption.  rewrite H0 in *.

assert(forall j,  Sorted.Sorted(StateMap.Raw.PX.ltk (elt:=qstate s0 e0)) 
[s_scale (/( r j ^ 2))%R (c_update x j (fst st),  QMeas_fun s' e' j (snd st))]).
intros. apply Sorted.Sorted_cons. apply Sorted.Sorted_nil. apply Sorted.HdRel_nil.
rewrite Heqr in *. 

pose (big_dapp_exsist (fun_to_list (fun j : nat => ( r j ^ 2)%R) (2 ^ (e' - s'))) 
(fun_to_list (fun j : nat => StateMap.Build_slist (H9 j) ) (2 ^ (e' - s')))).
destruct e1.  repeat rewrite fun_to_list_length. reflexivity.

rewrite Heqr in *. 


assert(dstate_eq x1
{| StateMap.this :=
    StateMap.Raw.map2 option_app mu'' [];
  StateMap.sorted := IHmu
|}). unfold dstate_eq. simpl. rewrite map2_nil_r.
apply big_dapp_this  in H11.
 rewrite (@fun_dstate_to_list s0 e0 ((2 ^ (e' - s')))
 ) in H11. simpl in H11. 
 remember ((fun j : nat =>
 (norm (U_v s' e' s e (∣ j ⟩_ (2^(e'-s')) × ⟨ j ∣_ (2^(e'-s'))) v) *
  (norm (U_v s' e' s e (∣ j ⟩_ (2^(e'-s')) × ⟨ j ∣_ (2^(e'-s'))) v) * 1))%R) ) as f1.
  remember ((fun i : nat =>
  s_scale
     (/
      (norm (U_v s' e' s e (∣ i ⟩_ (2^(e'-s')) × ⟨ i ∣_ (2^(e'-s'))) v) *
       (norm (U_v s' e' s e (∣ i ⟩_ (2^(e'-s')) × ⟨ i ∣_ (2^(e'-s'))) v) * 1)))
     (c_update x i (fst st), QMeas_fun s' e' i (snd st)))) as f2.
 assert(forall i, i< 2^(e'-s')-> snd (f2 i)= Zero-> f1 i = 0 %R).
 rewrite Heqf1. rewrite Heqf2. unfold s_scale. simpl. intros.

assert((QMeas_fun s' e' i (snd st)= Zero) \/ QMeas_fun s' e' i (snd st)<> Zero).
apply Classical_Prop.classic. destruct H14. 
rewrite (@QMeas_not_Zero s0 e0 s' e' s e _ v (snd st)) in H14;
try assumption;  try rewrite Reduced_scale;try apply (fst st); try apply H7.
rewrite H14. rewrite Rmult_0_l. reflexivity. dom_solve.  
pose (H14). 
rewrite (@QMeas_not_Zero s0 e0 s' e' s e _ v (snd st)) in n;
try assumption; try rewrite Reduced_scale;try apply (fst st); try apply H7.
remember ((/
(norm (U_v s' e' s e (∣ i ⟩_ (2^(e'-s')) × ⟨ i ∣_ (2^(e'-s'))) v) *
 (norm (U_v s' e' s e (∣ i ⟩_ (2^(e'-s')) × ⟨ i ∣_ (2^(e'-s'))) v) * 1)))%R).
eapply (scale_not_0 _ r0) in H14. destruct H14; try assumption.
rewrite Heqr0. apply C0_fst_neq.
 apply Rinv_neq_0_compat; rewrite Rmult_1_r.
 rewrite Rmult_pow. rewrite <-Rsqr_pow2.
 intro. destruct n. apply Rsqr_0_uniq. assumption.
 dom_solve. 

 assert((fun i : nat =>
 [s_scale
    (/
     (norm (U_v s' e' s e (∣ i ⟩_ (2^(e'-s')) × ⟨ i ∣_ (2^(e'-s'))) v) *
      (norm (U_v s' e' s e (∣ i ⟩_ (2^(e'-s')) × ⟨ i ∣_ (2^(e'-s'))) v) * 1)))
    (c_update x i (fst st), QMeas_fun s' e' i (snd st))])=
  fun i:nat=> [f2 i]). rewrite Heqf2. simpl. reflexivity.
  rewrite H13 in H11.
 apply (big_app_map2' _ _ _ _ _ H12 H11);
 subst; try assumption.



econstructor. 
apply WF_ceval with <{ x :=M [[s' e']] }> [(fst st, snd st)].
apply WF_state_dstate_aux. apply H5. assumption.

apply Meas_distribution_formula; try dom_solve; try apply H5.



eapply big_pOplus_sat .   apply H11. 
apply dstate_eq_sym. assumption.

intros. split. 
econstructor;  simpl in *.
unfold WF_dstate. simpl.
apply WF_state_dstate_aux. 
unfold s_scale. simpl. unfold WF_state.
simpl.   unfold WF_qstate. split. unfold q_scale.  
apply nz_Mixed_State_aux_to_01'.
apply WWF_qstate_QMeas; try lia. 
intro. apply (QMeas_not_Zero _ _ s e _ v) in H15; 
try assumption;  try rewrite Reduced_scale; try apply H7.
rewrite H15 in H14.  rewrite Rmult_0_l in *. lra.  
 apply (fst st). dom_solve. apply WWF_qstate_to_WF_qstate. apply H5.
rewrite Rmult_1_r in *. rewrite Rmult_pow.
apply Rinv_0_lt_compat. rewrite <-Rsqr_pow2.
apply Rlt_0_sqr. intro.
rewrite H15 in H14.  rewrite Rmult_0_l in *. lra. 
 rewrite trace_mult_dist.
rewrite <- (Reduced_Meas_trace_eq _ _ s e _ v); 
try lia; try assumption; try rewrite Reduced_scale; try apply H5.
 rewrite Cmult_assoc. rewrite Rmult_1_r in *.
 rewrite RtoC_mult.
rewrite Rinv_l; try assumption. rewrite Cmult_1_l.
apply nz_mixed_state_Cmod_1. apply H5.  lra. 
dom_solve. apply H17. apply H7. dom_solve. 
econstructor. apply rule_Meas_aux; try assumption. 
 intro.  rewrite H15 in *. 
 rewrite Rmult_0_l in *. lra.  dom_solve. 
simpl. inversion_clear H8. split; try assumption.
destruct st. simpl in *.
inversion_clear H6. assumption. 
 econstructor. 


intros. unfold dstate_eq in *. 
unfold d_trace. simpl. 
rewrite  (QMeas_trace s' e' x i (fst st) (snd st)); try assumption. 
 unfold s_trace. simpl. rewrite Rplus_0_r.
rewrite Rmult_1_r. unfold q_trace.  f_equal. unfold q_scale. rewrite trace_mult_dist.
rewrite <-(Reduced_Meas_trace_eq _ _ s e _ v); try apply H7;
try rewrite Reduced_scale; try assumption. 
rewrite Cmult_assoc. rewrite RtoC_mult. 
rewrite Rinv_l. rewrite Cmult_1_l. reflexivity.
rewrite Rmult_pow. lra. dom_solve. apply H7. dom_solve.
 apply WWF_qstate_to_WF_qstate.
apply WF_state_dstate. assumption.
rewrite map2_nil_r. apply H10.
Qed.


Fixpoint list_and{s e:nat} (mu_n1 mu_n2: list (dstate s e)) :=
match mu_n1, mu_n2 with 
|[], _ => []
|_,  [] =>[]
|(h1::t1), (h2::t2)=> (d_app h1 h2) :: (list_and t1 t2)
end.

Lemma lits_and_length{s e:nat}: forall (mu_n1 mu_n2: list (dstate s e)),
length mu_n1 = length mu_n2->
length (list_and mu_n1 mu_n2)= length mu_n1.
Proof. induction mu_n1; intros. simpl. reflexivity.
       destruct mu_n2. simpl. simpl in H. intuition. 
       simpl. f_equal. apply IHmu_n1. injection H. intuition. 
Qed.


Lemma big_dapp'_length{s e:nat}: forall p_n (mu_n:list (dstate s e)) (mu:dstate s e),
big_dapp' p_n mu_n mu -> length p_n = length mu_n.
Proof. induction p_n; intros; destruct mu_n. reflexivity.
      inversion_clear H. inversion_clear H.
      inversion H; subst.
      simpl. f_equal. apply IHp_n with d0 .
      assumption.
Qed.




Lemma big_dapp_list_and{s e:nat}: forall (p_n:list R)(mu_n1 mu_n2:list (dstate s e)) mu1 mu2 mu3,
length mu_n1= length mu_n2->
(big_dapp' p_n mu_n1 mu1) ->
(big_dapp' p_n mu_n2 mu2) ->
(big_dapp' p_n (list_and mu_n1 mu_n2) mu3)->
dstate_eq (d_app mu1 mu2) mu3.
Proof. induction p_n; intros; destruct mu_n1; destruct mu_n2; inversion_clear H0; inversion_clear H1; inversion_clear H2.
         apply d_app_empty_l. 
       
         injection H; intros. 
         eapply IHp_n in H2;[| apply H4| apply H5| apply H6].
         apply dstate_eq_trans with ((d_app (d_app r r0) d3)).
         apply dstate_eq_trans with (d_app (d_app (d_app r d1) r0) d2).
         apply dstate_eq_sym.
         apply d_app_assoc'.
         apply dstate_eq_trans with (d_app (d_app  r0 (d_app r d1)) d2).
         apply d_app_eq. apply d_app_comm. apply dstate_eq_refl.
         apply dstate_eq_trans with (d_app (d_app (d_app r0 r) d1) d2).
         apply d_app_eq. apply dstate_eq_sym. apply d_app_assoc'.
         apply dstate_eq_refl.  
         apply dstate_eq_trans with ( (d_app (d_app r0 r) (d_app d1 d2))).
         apply d_app_assoc'. apply d_app_eq. apply d_app_comm. assumption.
         apply d_app_eq. eapply d_scale_app_distr. apply H3. apply H0. apply H1.
         apply dstate_eq_refl.
Qed.

Lemma big_and_list_and{s e:nat}: forall (mu_n1 mu_n2:list (dstate s e)) (pF:pro_formula),
(Forall_two (fun i j =>(0<(fst j))%R -> sat_State i (snd j)) mu_n1 pF)->
(Forall_two (fun i j =>(0<(fst j))%R -> sat_State i (snd j)) mu_n2 pF)->
(Forall_two (fun i j=> (0<(fst j))%R ->WF_dstate i) (list_and mu_n1 mu_n2) pF)->
(Forall_two (fun i j =>(0<(fst j))%R -> sat_State i (snd j))  (list_and mu_n1 mu_n2) pF).
Proof. induction mu_n1.  intros. destruct mu_n2. destruct pF. simpl.
     intuition. simpl in *. inversion_clear H0. 
     destruct pF. simpl in *. inversion_clear H0.
     inversion_clear H. 
      intros. destruct mu_n2. destruct pF. simpl in *. inversion_clear H.
      simpl in *. inversion_clear H0. destruct pF. simpl in H. inversion_clear H.
      simpl in *. inversion_clear H. inversion_clear H0.
      econstructor. intros. 
      apply d_seman_app'. apply H2. assumption. apply H. assumption. 
      inversion_clear H1. apply H5. assumption. 
      apply IHmu_n1. assumption. assumption. inversion_clear H1. assumption.   
Qed.


Lemma list_and_trace{s e:nat}: forall (mu_n1 mu_n2:list (dstate s e)) (pF:pro_formula)  (mu1 mu2: dstate s e),
(Forall_two (fun x y=> (0< fst y)%R ->WWF_dstate x) ( mu_n1 ) pF)->
(Forall_two (fun x y=> (0< fst y)%R ->WWF_dstate x) ( mu_n2 ) pF)->
WWF_dstate mu1 -> WWF_dstate mu2 ->
Forall_two (fun (mu_i : dstate s e) y=>(0< fst y)%R ->d_trace mu_i = d_trace mu1) mu_n1 pF->
Forall_two (fun (mu_i : dstate s e) y=>(0< fst y)%R ->d_trace mu_i = d_trace mu2) mu_n2 pF->
Forall_two (fun (mu_i : dstate s e) y=>(0< fst y)%R ->d_trace mu_i = d_trace (d_app mu1 mu2))  (list_and mu_n1 mu_n2) pF.
Proof. induction mu_n1; intros; destruct mu_n2; destruct pF; simpl; try apply Forall_nil;
      inversion_clear H4; inversion_clear H3. 
       econstructor.
       econstructor. intros. rewrite d_trace_app. rewrite H4; try assumption.
       rewrite H5; try assumption. rewrite d_trace_app.  reflexivity. assumption.
       assumption.  
         inversion_clear H. apply H8; try assumption. inversion_clear H0. apply H8; try assumption.
         apply IHmu_n1. inversion_clear H. assumption. inversion_clear H0. 
         assumption. assumption. assumption. assumption. assumption. 
Qed.

Lemma WWF_list_and{s e:nat}: forall (mu_n1 mu_n2: list (dstate s e)) (pF:pro_formula),
(Forall_two (fun x y=> (0< fst y)%R ->WWF_dstate x) ( mu_n1 ) pF)->
(Forall_two (fun x y=> (0< fst y)%R ->WWF_dstate x) ( mu_n2 ) pF)->
(Forall_two (fun x y=> (0< fst y)%R ->WWF_dstate x) (list_and mu_n1 mu_n2) pF).
Proof. induction mu_n1; intros; destruct mu_n2; destruct pF; simpl; try econstructor;
       inversion_clear H0; inversion_clear H.
       intros. apply WWF_d_app. auto. auto. 
      apply IHmu_n1; try assumption.
Qed.




Lemma  Forall_WWF_WF{s e:nat}: forall (mu_n:list (dstate s e)) (pF:pro_formula),
(Forall_two (fun x y=> (0< fst y)%R ->WF_dstate x) ( mu_n ) pF)<->
((Forall_two (fun x y=> (0< fst y)%R ->WWF_dstate x) ( mu_n ) pF)/\
(Forall_two (fun x y=> (0< fst y)%R ->(d_trace x <=1)%R) ( mu_n ) pF)).
Proof. induction mu_n; destruct pF; split; intros; try split; try apply Forall_two_nil;
       inversion_clear H;
      try econstructor; intros; try  apply WWF_dstate_to_WF_dstate;
      try assumption; try apply H0;try  apply IHmu_n; try assumption.
      inversion_clear H0. inversion_clear H1. 
      inversion_clear H0. inversion_clear H1.
      auto.  
      inversion_clear H0. inversion_clear H1.
      auto.
Qed.

Lemma sat_dapp{s e:nat}: forall (mu1 mu2: (dstate s e)) (pF:pro_formula),
sat_Assert (mu1) pF ->
sat_Assert (mu2) pF ->
WF_dstate (d_app mu1 mu2)->
sat_Assert (d_app mu1 mu2) pF.
Proof. intros. inversion_clear H.  inversion_clear H4.
          inversion_clear H0. inversion_clear H8.
          econstructor. intuition. assumption. 
          pose(big_dapp_exsist  (get_pro_formula pF) (list_and mu_n mu_n0) ).
          destruct e0. rewrite lits_and_length. 
          rewrite <-(big_dapp'_length ((get_pro_formula pF)) mu_n mu'). 
          reflexivity. assumption. 
          rewrite <-(big_dapp'_length ((get_pro_formula pF)) mu_n mu').
          rewrite <-(big_dapp'_length ((get_pro_formula pF)) mu_n0 mu'0).
          reflexivity. try assumption. assumption. econstructor. apply H8.

          apply dstate_eq_trans with (d_app mu' mu'0). apply d_app_eq; try assumption.

          eapply big_dapp_list_and;[|apply H|apply H0| apply H8].
          rewrite <-(big_dapp'_length ((get_pro_formula pF)) mu_n mu').
          rewrite <-(big_dapp'_length ((get_pro_formula pF)) mu_n0 mu'0).
          reflexivity. try assumption. assumption.

          apply Forall_two_impli with ((fun (mu_i : dstate s e) (pF_i : R * State_formula) =>
          ((0 < fst pF_i)%R -> sat_State mu_i (snd pF_i)) /\ ((0 < fst pF_i)%R->d_trace mu_i = d_trace (d_app mu1 mu2)))).
          simpl. intros. split; apply H11; try assumption.
          apply (Forall_two_impli _ ((fun (mu_i : dstate s e) (pF_i : R * State_formula) =>
          ((0 < fst pF_i)%R -> sat_State mu_i (snd pF_i)) /\ ((0 < fst pF_i)%R->d_trace mu_i = d_trace mu1)))) in H6.
          apply (Forall_two_impli _ ((fun (mu_i : dstate s e) (pF_i : R * State_formula) =>
          ((0 < fst pF_i)%R -> sat_State mu_i (snd pF_i)) /\ ((0 < fst pF_i)%R->d_trace mu_i = d_trace mu2)))) in H10.
          apply Forall_two_Conj .  apply Forall_two_Conj in H6. apply Forall_two_Conj in H10.
          destruct H6. destruct H10. split.
          apply big_and_list_and. assumption. assumption.

        
          apply WF_big_and in H6. apply WF_big_and in H10.
          apply Forall_WWF_WF. split.
            apply WWF_list_and; 
          try apply Forall_WWF_WF; try assumption.  
          apply Forall_two_impli with 
          ((fun x y =>(0 < fst y)%R ->  d_trace x = d_trace(d_app mu1 mu2)%R));
          try apply list_and_trace;  try apply Forall_WWF_WF; try assumption.
          intros. rewrite H13. 
          try apply WWF_dstate_aux_to_WF_dstate_aux; try assumption. assumption.
          try apply WWF_dstate_aux_to_WF_dstate_aux; try assumption. 
          try apply WWF_dstate_aux_to_WF_dstate_aux; try assumption.
          apply WF_big_and in H6. apply WF_big_and in H10. 
          apply list_and_trace; try apply Forall_WWF_WF; try assumption.
          try apply WWF_dstate_aux_to_WF_dstate_aux; try assumption. 
          try apply WWF_dstate_aux_to_WF_dstate_aux; try assumption.
          simpl. intros. split; apply H11; try assumption.
          simpl. intros. split; apply H11; try assumption.
Qed.


Theorem rule_Meas_aux'':forall s' e' s e (v: Vector (2^(e-s))) x (P :nat-> (Pure_formula))
(s0 e0:nat) (mu mu': dstate s0 e0) ,
s <= s'  /\ e' <= e-> 
Pure_State_Vector v->
ceval (QMeas x s' e') mu mu'-> 
sat_State mu ((QExp_s  s  e  v) /\s big_Sand (fun i:nat => (PAssn x (ANum i) (P i))) (2^(e'-s'))) ->
sat_Assert mu' ((big_pOplus (fun i:nat=> (@norm (2^(e-s)) ((U_v s' e' s e (∣ i ⟩_ (2^(e'-s')) × ⟨ i ∣_ (2^(e'-s'))) v))) ^ 2)%R
(fun i:nat=>  ((P i)) /\s (QExp_s  s  e (( / ( (@norm (2^(e-s)) ((U_v s' e' s e (∣ i ⟩_ (2^(e'-s')) × ⟨ i ∣_ (2^(e'-s'))) v)))))%R.* 
(U_v  s' e' s e (∣ i ⟩_ (2^(e'-s')) × ⟨ i ∣_ (2^(e'-s'))) v)))) (2^(e'-s')) )).
Proof.  intros s' e' s e v x P s0 e0  (mu, IHmu). 
 induction mu;  intros mu'  ; intros H Hp; destruct mu' as(mu', IHmu').
 intros. 
-- simpl in H1. inversion_clear H0. inversion H3; subst.
 apply sat_Assert_empty. simpl. 
 apply Meas_distribution_formula; try dom_solve.     
 rewrite H7. reflexivity.
--intros. destruct mu. inversion_clear H0. simpl in H3 ; inversion H3; subst. inversion H9; subst.
clear H9. 
apply (rule_Meas_aux' s' e' s e v x P _ _ (sigma, rho)); try assumption.
simpl.  econstructor.  apply H2. apply H3. simpl. 
apply sat_Assert_dstate_eq with {|
  StateMap.this := [(sigma, rho)];
  StateMap.sorted := IHmu
|}. unfold dstate_eq. simpl. reflexivity.
rewrite sat_Assert_to_State. apply H1. 

inversion_clear H0. simpl in H3.  inversion H3; subst.
assert(Sorted.Sorted (StateMap.Raw.PX.ltk (elt:=qstate s0 e0)) (big_app
(fun j : nat =>
 [(c_update x j sigma, QMeas_fun s' e' j rho)])
(2 ^ (e' - s')))). apply big_app_sorted. intros. apply 
Sorted.Sorted_cons. apply 
Sorted.Sorted_nil. apply Sorted.HdRel_nil.
assert(Sorted.Sorted (StateMap.Raw.PX.ltk (elt:=qstate s0 e0)) mu'0). 
apply ceval_sorted with (<{ x :=M [[s' e']] }>)
(p::mu). inversion_clear IHmu. assumption. assumption.
assert(Sorted.Sorted (StateMap.Raw.PX.ltk (elt:=qstate s0 e0)) mu''). 
apply ceval_sorted with (<{ x :=M [[s' e']] }>)
([(sigma, rho)]). apply 
Sorted.Sorted_cons. apply 
Sorted.Sorted_nil. apply Sorted.HdRel_nil.
apply ceval_QMeas; try dom_solve. 
apply sat_Assert_dstate_eq with ((d_app {| StateMap.this := mu''; StateMap.sorted := H5 |}
{| StateMap.this := mu'0; StateMap.sorted := H4 |})).
unfold dstate_eq. simpl. reflexivity.
eapply sat_dapp.  

apply (rule_Meas_aux' s' e' s e v x P _ _ (sigma, rho)); try assumption.
econstructor. inversion_clear H2.  apply WF_state_dstate.
assumption. 
apply ceval_QMeas; try dom_solve. simpl. 
inversion_clear H1.
rewrite sat_Assert_to_State. econstructor. 
apply WF_state_dstate. inversion_clear H6. assumption.
inversion_clear H7. econstructor. apply H1.
econstructor.

inversion_clear IHmu.
apply IHmu0 with H6. assumption. apply Hp.  apply E_com; try assumption.
inversion_clear H2. assumption. 
 inversion_clear H1. inversion_clear H11. 
econstructor. inversion_clear H2. assumption.
 apply State_eval_dstate_Forall. discriminate.
assumption. 
eapply WF_ceval. apply H2. apply H3. 
Qed.

Theorem rule_QMeas : forall s' e' s e (v: Vector (2^(e-s))) x (P :nat-> (Pure_formula)) ,
s <= s'  /\ e' <= e ->
Pure_State_Vector v->
{{(QExp_s  s  e  v) /\s big_Sand (fun i:nat => (PAssn x (ANum i) (P i))) (2^(e'-s')) }}
 <{ x :=M [[ s' e' ]] }>
{{ big_pOplus (fun i:nat=> (@norm (2^(e-s)) ((U_v s' e' s e (∣ i ⟩_ (2^(e'-s')) × ⟨ i ∣_ (2^(e'-s'))) v))) ^ 2)%R
(fun i:nat=>  ((P i)) /\s (QExp_s  s  e (( / ( (@norm (2^(e-s)) ((U_v s' e' s e (∣ i ⟩_ (2^(e'-s')) × ⟨ i ∣_ (2^(e'-s'))) v)))))%R.* 
(U_v s' e' s e (∣ i ⟩_ (2^(e'-s')) × ⟨ i ∣_ (2^(e'-s'))) v)))) (2^(e'-s')) }}.
Proof. unfold hoare_triple.
intros. 
rewrite sat_Assert_to_State in *.
eapply rule_Meas_aux''. apply H. apply H0. apply H1.
assumption.
Qed.


