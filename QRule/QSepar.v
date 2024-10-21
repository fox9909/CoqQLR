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
From Quan Require Import ParDensityO.
From Quan Require Import QState.
From Quan Require Import QIMP_L.
From Quan Require Import QAssert.
From Quan Require Import Par_trace.
From Quan Require Import QRule_Q_L.
Import Basic.
Import Ceval_Linear.
(*From Quan Require Import QRule_E_L.
From Quan Require Import QRule_I_L. *)

Local Open Scope com_scope.

Local Open Scope nat_scope.




Lemma  subset_union: forall x y z, NSet.Subset (NSet.union x y) z ->
NSet.Subset x z /\ NSet.Subset y z.
Proof. intros. unfold NSet.Subset in *. 
       split. intros. 
       apply H. apply NSet.union_2.
       assumption.
       intros. apply H. apply NSet.union_3.
       assumption.
       
Qed.

(* Lemma subset_Qsys:forall s e l r, 
l<r->
NSet.Subset (Qsys_to_Set l r) (Qsys_to_Set s e ) ->
s<=l \/ r<=e. *)

Lemma In_Qsys_l_r: forall r l , 
l<r->
NSet.In l (Qsys_to_Set l r) /\
NSet.In (r-1) (Qsys_to_Set l r).
Proof. unfold Qsys_to_Set. induction r; induction l; intros; simpl.
 lia. lia.   
 simpl. split. destruct r.
 simpl.  
 apply NSet.add_1. reflexivity.
 apply NSet.add_2. 
 eapply IHr. lia.  
 rewrite sub_0_r.
 apply NSet.add_1. reflexivity.
 destruct r. lia.  
 pose H.
 apply Lt_n_i in l0. rewrite l0.
 split.
 bdestruct (l =? r).
 rewrite H0. apply NSet.add_1.
 reflexivity.
 apply NSet.add_2.
 apply IHr. lia.  
 rewrite sub_0_r.
 apply NSet.add_1.
 reflexivity.    
Qed.

Lemma In_empty: forall s, NSet.In s NSet.empty -> False .
Proof. intros. pose (NSet.empty_1). unfold NSet.Empty in *. 
        apply e in H. destruct H.
Qed.

Lemma In_Qsys: forall r l s, 
l<r->
NSet.In s (Qsys_to_Set l r)<-> l<=s<r.
Proof. unfold Qsys_to_Set. 
induction r; intros.
lia.
destruct l.
simpl. split. intros.
bdestruct (s=?r).
rewrite H1. 
lia.
destruct r.  
apply NSet.add_3 in H0.
simpl in H0.
apply In_empty in H0.
destruct H0.
 intuition.
apply NSet.add_3 in H0.
apply IHr in H0. lia. 
lia.
intuition.
intros.
bdestruct (s=?r).
rewrite H1.
apply NSet.add_1.
reflexivity.
destruct r. 
assert(s=0). lia.
rewrite H2.  
apply NSet.add_1.
reflexivity.
apply NSet.add_2.
apply IHr. lia.  
lia.


simpl.  pose H.
apply Lt_n_i in l0.
rewrite l0.

bdestruct (S l <?r).
split; intros.
bdestruct (s=? r).
rewrite H2. lia.
apply NSet.add_3 in H1.
apply IHr in H1.
lia. intuition. intuition.

bdestruct (s=? r).
rewrite H2. apply NSet.add_1. reflexivity.
apply NSet.add_2. 
apply IHr . assumption.
lia. 

assert(forall l r, l>=r ->(Qsys_to_Set_aux l r NSet.empty = NSet.empty)).
intros. induction r0. 
 simpl. reflexivity.
 simpl. 
 assert(l1 <? S r0 = false).
 apply ltb_ge. 
 assumption.
 rewrite H2. reflexivity.
rewrite H1.
bdestruct (s=? r).
rewrite H2.
split;intros. lia.
apply NSet.add_1. reflexivity.
split; intros. 
apply NSet.add_3 in H3.
apply In_empty in H3.
destruct H3.
intuition.
lia. 
assumption.    
Qed.


Lemma subset_Qsys:forall s e l r, 
l<r-> 
NSet.Subset (Qsys_to_Set l r) (Qsys_to_Set s e ) ->
 s<=l /\ r<=e.
Proof. intro. intro. intro. intro. intro. 
apply NF_1. intros.
 apply Classical_Prop.not_and_or in H0.
unfold not. intros. 
destruct H0. unfold not in H0.
assert(s>l). intuition. 
unfold NSet.Subset in H1.
pose (H1 l). 
assert(NSet.In l (Qsys_to_Set s e)).
apply i. apply In_Qsys_l_r. assumption.
apply In_Qsys in H3. lia.
assert(s<e\/ ~ (s<e)).
apply Classical_Prop.classic.
destruct H5. assumption.
assert(s >= e). lia.
apply ltb_ge in H6.
unfold Qsys_to_Set in H3.
destruct e.  
simpl in H3.  
apply In_empty in H3.
destruct H3.
 simpl in H3. rewrite H6 in H3.
 apply In_empty in H3. destruct H3.

assert(r>e). intuition. 
unfold NSet.Subset in H1.
pose (H1 (r-1)). 
assert(NSet.In (r-1) (Qsys_to_Set s e)).
apply i. apply In_Qsys_l_r. assumption.
apply In_Qsys in H3. lia.
assert(s<e\/ ~ (s<e)).
apply Classical_Prop.classic.
destruct H5. assumption.
assert(s >= e). lia.
apply ltb_ge in H6.
unfold Qsys_to_Set in H3.
destruct e.  
simpl in H3.  
apply In_empty in H3.
destruct H3.
 simpl in H3. rewrite H6 in H3.
 apply In_empty in H3. destruct H3.
Qed.




Import ParDensityO.
Local Open Scope nat_scope.
Lemma Par_trace_ceval_swap: forall c s e (mu mu': list (cstate *qstate s e)) l r,
s<=l /\ l<=r /\ r<=e ->
NSet.Subset (snd (MVar c)) (Qsys_to_Set l r)
->
WF_dstate_aux mu ->
ceval_single c mu mu'->
ceval_single c (d_par_trace mu l r )
(d_par_trace mu' l r ).
Proof. induction c. intros. 
       {apply ceval_skip_1 in H2.
       subst. apply ceval_skip. }
       { admit. }
       { induction mu; intros. inversion_clear H2.
        simpl. econstructor.
        destruct a0. inversion H2 ;subst.
        rewrite d_par_trace_map2.
        simpl d_par_trace.
        rewrite (state_eq_aexp  _ (c,(PMpar_trace q l r) )).
        econstructor. apply IHmu. assumption.
        assumption. inversion_clear H1. intuition.
        assumption. reflexivity.  }
       { admit. }
       {intros. apply ceval_seq_1 in H2. 
       destruct H2. 
       apply ceval_seq with ((d_par_trace x l r)).
       apply IHc1. intuition.
       simpl in H0. apply subset_union in H0.
       intuition.  intuition. intuition.
       apply IHc2. intuition. 
       simpl in H0. apply subset_union in H0.
       intuition. apply WF_ceval with c1 mu; try assumption.
       apply H2. intuition.  }
       {induction mu; intros. inversion H2; subst.
       simpl. econstructor.
       inversion H2; subst. 
       rewrite d_par_trace_map2.
      econstructor. rewrite (state_eq_bexp _  (sigma, rho)).
      intuition. reflexivity.
      apply IHmu.  intuition.
      intuition. inversion_clear H1.  assumption. assumption. 
      assert(d_par_trace [(sigma, rho)] l r = [(sigma, PMpar_trace rho l r)]).
      reflexivity. rewrite <-H3. apply IHc1. assumption.
      simpl in H0. apply subset_union in H0.
       intuition. apply WF_state_dstate_aux.
        inversion_clear H1.  assumption. assumption. 
      rewrite d_par_trace_map2.
      apply E_IF_false. rewrite (state_eq_bexp _  (sigma, rho)).
      intuition. reflexivity.
      apply IHmu.  intuition.
      intuition. inversion_clear H1. assumption. assumption. 
      assert(d_par_trace [(sigma, rho)] l r = [(sigma, PMpar_trace rho l r)]).
      reflexivity. rewrite <-H3. apply IHc2.
      assumption.  
      simpl in H0. apply subset_union in H0.
       intuition.  inversion_clear H1. 
       apply WF_state_dstate_aux. assumption. 
      assumption. 
          }
      { admit. }
      { induction mu; intros. inversion H2; subst.
      simpl. econstructor.
      inversion H2; subst.
      rewrite d_par_trace_map2.
      simpl d_par_trace.
      rewrite PMpar_trace_ceval_swap_Qinit.
     econstructor.  simpl in H0.   
     apply subset_Qsys in H0. intuition. 
     lia. 
     apply IHmu.  intuition. 
     intuition. inversion_clear H1. intuition.
     assumption.
     split. intuition. simpl in H0.
     apply subset_Qsys in H0. lia. lia.  
       inversion_clear H1. apply WF_Mixed.
       apply H3. 
     }
     { induction mu; intros. inversion H2; subst.
      simpl. econstructor.
      inversion H2; subst.
      apply inj_pair2_eq_dec in H5.
      apply inj_pair2_eq_dec in H5.
      subst.
      rewrite d_par_trace_map2.
      simpl d_par_trace.
     rewrite  PMpar_trace_ceval_swap_QUnit_one.
     econstructor.  simpl in H0.
     apply subset_Qsys in H0. lia. lia. assumption.  
     apply IHmu.  intuition. assumption. 
     inversion_clear H1. intuition.
     intuition. simpl in H0.
     apply subset_Qsys in H0. lia. lia.
       inversion_clear H1. apply WF_Mixed.
       apply H3. assumption.
    apply Nat.eq_dec.
     apply Nat.eq_dec.
     }
     { induction mu; intros. inversion H2; subst.
      simpl. econstructor.
      inversion H2; subst.
      apply inj_pair2_eq_dec in H8.
      apply inj_pair2_eq_dec in H8.
      subst.
      rewrite d_par_trace_map2.
      simpl d_par_trace.
      rewrite PMpar_trace_ceval_swap_QUnit_Ctrl.
     econstructor. 
     simpl in H0.  apply subset_union in H0. 
     destruct H0. apply subset_Qsys in H3.
     apply subset_Qsys in H0. lia. lia. lia.   
     assumption.  
     apply IHmu.  intuition.
     intuition.
     inversion_clear H1. assumption.
     assumption.
     simpl in H0.  apply subset_union in H0. 
     destruct H0. apply subset_Qsys in H3.
     apply subset_Qsys in H0. lia. lia. lia. 
     inversion_clear H1.  apply WF_Mixed.
     apply H3. 
     assumption.
     apply Nat.eq_dec.
     apply Nat.eq_dec.
     }
     { induction mu; intros. inversion H2; subst.
      simpl. econstructor.
      inversion H2; subst.
      rewrite d_par_trace_map2.
      simpl d_par_trace. econstructor.
     simpl in H0.  
     apply subset_Qsys in H0. lia. lia. 
     apply IHmu.  intuition.
     intuition. inversion_clear H1. assumption.
     assumption. apply (d_par_trace_app' _ l r) in H11.
     destruct H11. simpl in H3.  destruct H3.
     rewrite H4. eapply big_app_eq_bound''.
     apply H3. intros.
      rewrite  <-PMpar_trace_ceval_swap_QMeas; try reflexivity.
     simpl in H0.  
     apply subset_Qsys in H0. lia. lia. 
      inversion_clear H1;  apply WF_Mixed.
      apply H6.
     assumption. lia.  
    intros.
     simpl. 
     assert(QMeas_fun s e i0 rho = Zero \/ QMeas_fun s e i0 rho <> Zero).
     apply Classical_Prop.classic. destruct H4. 
     right. assumption. left. apply WWF_qstate_QMeas; try lia; 
     try assumption.    inversion_clear H1.
     apply WWF_qstate_to_WF_qstate. apply H5.
     }
Admitted.

(*----------------------------separ-------------------*)

Lemma big_sum_sum' : forall a b m n (f: nat->Matrix a b), 
  big_sum f (m + n) = big_sum f m .+ big_sum (fun x => f (m + x)%nat) n.
Proof. intros. rewrite big_sum_sum.
      reflexivity. 
Qed.


Lemma big_sum_kron : forall m n  a1 a2 b1 b2 (f: nat ->Matrix a1 a2) (g: nat->Matrix b1 b2), 
  n <> O ->
  kron (big_sum f m)  (big_sum g n) = big_sum (fun x => kron (f (x / n)%nat)  (g (x mod n)%nat)) (m * n). 
Proof.
 intros.
  induction m; simpl.
  + rewrite kron_0_l; reflexivity. 
  + rewrite kron_plus_distr_r.
    rewrite IHm. clear IHm.
    rewrite kron_Msum_distr_l.    
    remember ((fun x : nat => f (x / n) ⊗ g (x mod n))) as h.
    replace (big_sum (fun x : nat => f m ⊗ g x) n) with
            (big_sum (fun x : nat => h ((m * n) + x)%nat) n). 
    2:{
      subst.
      apply big_sum_eq_bounded.
      intros x Hx.
      rewrite Nat.div_add_l by assumption.
      rewrite Nat.div_small; trivial.
      rewrite Nat.add_0_r.
      rewrite Nat.add_mod by assumption.
      rewrite Nat.mod_mul by assumption.
      rewrite Nat.add_0_l.
      repeat rewrite Nat.mod_small; trivial. }
      remember (m * n).
      rewrite <-big_sum_sum'.
    rewrite Nat.add_comm.
    reflexivity.
Qed. 



Lemma Separ{m n: nat}: forall (v:Vector (2^(m+n))),
WF_Matrix v ->
(exists (e: nat-> C) (f: nat-> C), 
forall z, (z< (2^(m+n)))-> (v z 0)= (Cmult (e (z/(2^n)))  (f (z mod (2^n) ))))
-> exists (v1: Vector (2^m)) (v2 : Vector (2^n)),
and (WF_Matrix v1 /\ WF_Matrix v2)
(kron v1 v2 =v).
Proof. intros. destruct H0. destruct H0.
       exists (big_sum (fun i=> (x i) .* (Vec (2^m) i)) (2^m)).
       exists (big_sum (fun i=> (x0 i) .* (Vec (2^n) i)) (2^n)).
       split. split. apply WF_Msum.
       intros. auto_wf. 
       apply WF_Msum.
       intros. auto_wf. 
       rewrite big_sum_kron.
       rewrite Vec_decom with v.
       rewrite Nat.pow_add_r.
       apply big_sum_eq_bounded.
       intros. 
       rewrite Mscale_kron_dist_l.
       rewrite Mscale_kron_dist_r.
       rewrite Mscale_assoc.
       rewrite <-H0.
       f_equal. 
       rewrite <-pow_add_r.
       rewrite Vec_kron.
       reflexivity. 
       rewrite pow_add_r. assumption.
       assumption.
       assert(2^n >0).
       apply pow_gt_0.
       intuition.   
Qed.


Lemma  outer_product_eq': forall m (φ ψ : Matrix m 1),
WF_Matrix φ -> WF_Matrix ψ ->
(exists c:C, and (c<> C0) ((outer_product φ φ) = (c.* outer_product ψ ψ) ))-> (exists c, and (c<> C0) (φ = c .* ψ)) .
Proof. intros m φ ψ Hphi Hpsi. intros. unfold outer_product in *.
      destruct H. destruct H.
      assert(φ × (φ) † ×  ψ = x .* ψ × (ψ) † ×  ψ ).
      rewrite H0. rewrite <-Mscale_mult_dist_l. reflexivity.
      repeat rewrite Mmult_assoc in H1.
      assert(((φ) † × ψ) = Zero \/ ((φ) † × ψ)  <> Zero).
      apply Classical_Prop.classic. destruct H2.
      rewrite H2 in H1. rewrite Mmult_0_r in H1.
      assert(ψ = Zero \/ ψ <> Zero). apply Classical_Prop.classic.
      destruct H3. rewrite H3 in H0.
      rewrite Mmult_0_l in H0. rewrite Mscale_0_r in H0.
      assert(φ = Zero). 
      assert(fst (trace (φ × (φ) †))=R0).
      rewrite H0. rewrite Zero_trace. reflexivity.
      rewrite <-inner_trace in H4.
      assert((norm φ * norm φ)%R = (norm φ) ^ 2)%R.
      simpl. rewrite Rmult_1_r. reflexivity.
      rewrite H5 in H4.  rewrite<- Rsqr_pow2 in H4.
      apply Rsqr_0_uniq in H4.  
      rewrite norm_zero_iff_zero in H4. assumption.
      assumption. assumption. 
      exists C1. rewrite H3. rewrite H4. rewrite Mscale_1_l. 
      split. intro. injection H5. lra. intuition.
      assert((inner_product ψ  ψ) <> C0). intro.
      rewrite inner_product_zero_iff_zero  in H4. 
      rewrite H4 in H3. destruct H3. reflexivity. 
      assumption. 
      unfold inner_product in H4. 
      assert((ψ) † × Zero = x.* (ψ) † × (ψ × ((ψ) † × ψ))).
      rewrite H1. rewrite Mscale_mult_dist_l. rewrite Mscale_mult_dist_r.
     rewrite <-Mscale_mult_dist_l.
       reflexivity. rewrite Mmult_0_r in H5.
      rewrite <-Mmult_assoc in H5.  
      symmetry in H5. repeat rewrite Mscale_mult_dist_l in H5. 
      apply (scale_Zero )in H5. 
      assert(@Zero 1  1 0 0=  ((ψ) † × ψ × ((ψ) † × ψ)) 0 0).
      rewrite H5. reflexivity.
      unfold Zero in H6. remember ((ψ) † × ψ). unfold Mmult in H6. 
      simpl in H6. repeat rewrite Cplus_0_l in H6.
      injection H6; intros.
      assert(m0 0 0 = trace ((ψ) † × ψ)). rewrite <-Heqm0.
      unfold trace. simpl. rewrite Cplus_0_l. reflexivity.
      rewrite <-trace_mult' in H9. 
      assert(snd (m0 0 0)=R0). rewrite H9.
      apply mixed_state_trace_real_aux.
      apply Vector_Mix_State. assumption. assumption. 
      rewrite H10 in *. rewrite Rmult_0_r in *. 
      rewrite Rminus_0_r in *. 
      assert((fst (m0 0%nat 0%nat) *
      fst (m0 0%nat 0%nat))%R = (fst (m0 0%nat 0%nat)) ^ 2
      )%R. simpl. rewrite Rmult_1_r. reflexivity.
      rewrite H11 in H8. rewrite <-Rsqr_pow2 in H8. symmetry in H8.
      apply Rsqr_0_uniq in H8. destruct (m0 0 0). simpl in *.
      subst. destruct H4. reflexivity. assumption.
      assert(φ × ((φ) † × ψ)= (((φ) † × ψ) 0 0) .* φ).
      prep_matrix_equality.  remember (((φ) † × ψ)).
      unfold Mmult. simpl.  rewrite Cplus_0_l.
      unfold scale. assert(WF_Matrix m0). rewrite Heqm0.
      auto_wf.  unfold WF_Matrix in *. 
      destruct y. apply Cmult_comm.  rewrite (Hphi _ (S y)).
      rewrite H3. repeat rewrite Cmult_0_r. reflexivity.
      right. lia. right. lia.  
      rewrite  H3 in H1. 
      assert(x .* ψ × (( ψ) † × ψ)= ((( ψ) † × ψ) 0 0) * x .*  ψ).
      prep_matrix_equality.  remember ((( ψ) † × ψ)). 
      unfold Mmult. simpl.  rewrite Cplus_0_l.
      unfold scale.   assert(WF_Matrix m0). rewrite Heqm0.
      auto_wf.  unfold WF_Matrix in *. 
      destruct y. rewrite Cmult_comm. rewrite Cmult_assoc.
      reflexivity.  rewrite (Hpsi _ (S y)).
      rewrite H4. repeat rewrite Cmult_0_r. reflexivity.
      right. lia. right. lia. 
      rewrite  H4 in H1. 
      remember (((φ) † × ψ) 0 0). 
      remember (((ψ) † × ψ) 0 0). 
      assert(  φ = /c .* (c0 * x .* ψ)).
      rewrite <-H1. rewrite Mscale_assoc.
      rewrite Cinv_l. rewrite Mscale_1_l. 
      reflexivity. rewrite Heqc. intro. 
      assert(WF_Matrix ((φ) † × ψ)). auto_wf.
      assert((φ) † × ψ = Zero). unfold Zero. prep_matrix_equality.
      unfold WF_Matrix in H6. destruct x0. destruct y. assumption.
      rewrite H6. reflexivity. right. lia. rewrite H6.
      reflexivity. left. lia. rewrite H7 in H2. destruct H2.
      reflexivity.  
      exists (/c * (c0 * x))%C.
      rewrite Mscale_assoc in H5.
      split. intro. rewrite H6 in H5. rewrite Mscale_0_l in H5.
      rewrite H5 in H2. rewrite zero_adjoint_eq in H2.
      rewrite Mmult_0_l in H2. destruct H2. reflexivity.
      assumption.
Qed.

Lemma big_sum_par: forall m n j  a b(f: nat-> Matrix a b),
j<n ->
(forall i :nat, j<> (i mod n) -> f i = Zero)->
big_sum f (m * n) = big_sum (fun i=> f (i * n +j)) m .
Proof. induction m; intros; simpl. reflexivity.
       rewrite add_comm.
       rewrite big_sum_sum'.
       rewrite (IHm _ j _ _ _ ).
       f_equal.
       apply big_sum_unique.
       exists j. split. assumption.
       split. reflexivity.
       intros. 
       rewrite H0. reflexivity.
       rewrite add_comm.
       rewrite mod_add.
       rewrite mod_small.
       assumption. assumption.
       lia. assumption.
       assumption.
Qed.

Lemma Vec_linear{ n:nat}: forall (v1 v2 :Vector n) p,
v1= p .* v2 ->
(forall i, (v1 i 0) = Cmult p  (v2 i 0)).
Proof. intros. rewrite H. unfold scale.
       reflexivity.
Qed.


Definition Par_Pure_State { n:nat}(q:Square n): Prop :=
exists (p:R) (q': Square n), and (0<p<=1)%R  (Pure_State q' /\ q= p .* q').


Lemma Mixed_pure': forall {n:nat} (ρ1 ρ2: Density n) (φ:Vector n), 
(Mixed_State_aux ρ1 \/ ρ1 = Zero)  ->
(Mixed_State_aux ρ2 \/ ρ2 = Zero)->
Pure_State_Vector φ ->
(exists p, and (0<p<=1)%R (ρ1 .+  ρ2= p .* (φ  × φ†)))
-> and (Mixed_State_aux ρ1 -> exists (c1: R), and (0<c1<=1)%R (ρ1= c1 .* ( φ  × φ† )))
(Mixed_State_aux ρ2->exists (c2: R), and (0<c2<=1)%R ((ρ2= c2.* ( φ  × φ† ))) ).
Proof. intros. destruct H2. destruct H2.
       assert(/x .* ρ1 .+ /x .* ρ2  = (φ × (φ) †)).
       rewrite <-Mscale_plus_distr_r.
       rewrite H3.
       rewrite Mscale_assoc.
       rewrite Cinv_l.
       rewrite Mscale_1_l.
       reflexivity.
       assert(x >0)%R. intuition. 
       unfold not. intros. 
       injection H5. intros.
      rewrite H6 in H4. lra.
     

      destruct H; destruct H0.
      apply Mixed_pure in H4.
      destruct H4. destruct H4.
      destruct H4. destruct H5.
      split. intros. 
      exists (x*x0)%R.
      split. apply Rmult_in01.   intuition .
      intuition. 
      repeat rewrite <-RtoC_mult.
      repeat rewrite <-Mscale_assoc.
      rewrite <-H5. 
      repeat rewrite Mscale_assoc.
      repeat rewrite Cinv_r.
      repeat rewrite Mscale_1_l.
     intuition. assert(x >0)%R. intuition. 
     unfold not. intros. 
     injection H9. intros. lra. 
     
     intros.
      exists (x*x1)%R.
      split. apply Rmult_in01.   intuition .
      intuition. 
       repeat rewrite <-RtoC_mult.
       repeat rewrite <-Mscale_assoc.
       rewrite <-H6.
       repeat rewrite Mscale_assoc.
       repeat rewrite Cinv_r.
       repeat rewrite Mscale_1_l.
      intuition. 
      assert(x >0)%R. intuition. 
      unfold not. intros. 
      injection H9. intros. lra.
      rewrite <-RtoC_inv.
      apply Mixed_State_aux_to_01'.
      assumption.
      apply Rinv_0_lt_compat. intuition. 
      apply Rle_trans with ((Cmod (trace (/ x .* ρ1 .+ / x .* ρ2 )))%R).
      rewrite mixed_state_Cmod_plus_aux.
      rewrite <-Rplus_0_r at 1.
      rewrite RtoC_inv. apply Rplus_le_compat_l.
      apply Cmod_ge_0.  lra. rewrite <-RtoC_inv.
       apply Mixed_State_scale_aux. 
       assumption. apply Rinv_0_lt_compat. lra.
       lra. rewrite <-RtoC_inv.
       apply Mixed_State_scale_aux. 
       assumption. apply Rinv_0_lt_compat. lra.
       lra. rewrite H4. destruct H1. rewrite trace_mult'.
       rewrite H5. rewrite trace_I. rewrite Cmod_1. lra.
       lra. 
       
       rewrite <-RtoC_inv.
       apply Mixed_State_aux_to_01'.
       assumption.
       apply Rinv_0_lt_compat. intuition. 
       apply Rle_trans with ((Cmod (trace (/ x .* ρ1 .+ / x .* ρ2 )))%R).
       rewrite mixed_state_Cmod_plus_aux.
       rewrite <-Rplus_0_l at 1.
       rewrite RtoC_inv. apply Rplus_le_compat_r.
       apply Cmod_ge_0.  lra. rewrite <-RtoC_inv.
        apply Mixed_State_scale_aux. 
        assumption. apply Rinv_0_lt_compat. lra.
        lra. rewrite <-RtoC_inv.
        apply Mixed_State_scale_aux. 
        assumption. apply Rinv_0_lt_compat. lra.
        lra. rewrite H4. destruct H1. rewrite trace_mult'.
        rewrite H5. rewrite trace_I. rewrite Cmod_1. lra.
        lra. 
       rewrite H4.
       apply Pure_Mixed. 
       econstructor. split. apply H1.
       reflexivity.
       assumption.

       rewrite H0 in *. rewrite Mplus_0_r in H3.
       split. intros. exists x. intuition.
       intros. apply Mixed_aux_not_Zero in H5. destruct H5.
        reflexivity. 

       rewrite H in *. rewrite Mplus_0_l in H3.
       split.  intros.  
       apply Mixed_aux_not_Zero in H5. destruct H5.
        reflexivity.  intros. exists x. intuition.
        
        split; intros; subst;
        apply Mixed_aux_not_Zero in H5; destruct H5;   reflexivity.
Qed.




Lemma Mixed_pure_sum: forall {n:nat} (f: nat-> Density n) m 
(φ : Vector n), 
Pure_State_Vector φ ->
(forall i, i< m -> (Mixed_State_aux (f i))  \/ (f i) = Zero)->
(exists p, and (0<p<=1)%R  ((big_sum f m) = p .* (φ  × φ†) ))->
(forall i, i<m ->  (Mixed_State_aux (f i)) ->
exists p, and (0<p<=1)%R  ( (f i)= p .* (φ  × φ†))).
Proof. induction m; intros.
       simpl in *. destruct H1.
       destruct H1. 
       assert(@trace n Zero = trace (x .* (φ × (φ) †))).
       rewrite H4. reflexivity.
       rewrite Zero_trace in H5.
       rewrite trace_mult_dist in H5.
       destruct H.  rewrite trace_mult' in H5.
       rewrite H6 in H5. rewrite trace_I in H5.
       rewrite Cmult_1_r in H5.
       injection H5. intros. lra. 
       simpl in *.
       assert(i=m \/ i<>m).
       apply Classical_Prop.classic.
       destruct H4.
       rewrite H4.
       apply (Mixed_pure' (big_sum f m) ) in H1.
       destruct H1. apply H5.
      rewrite <-H4.  intuition.
      assert(big_sum f m = Zero \/ big_sum f m<> Zero).
      apply Classical_Prop.classic. destruct H5.
      right. rewrite H5. reflexivity.
      left. apply Mixed_State_aux_big_sum.
      intro. rewrite H6 in H5. simpl in H5.
      destruct H5. reflexivity. intros. apply H0.
      lia.
      apply big_sum_not_0 in H5. destruct H5.
      exists x. assumption. 
        apply H0. lia. 
        assumption.
       apply IHm. 
       assumption. intros. apply H0. lia.  
       apply (Mixed_pure' (big_sum f m) ) in H1.
       apply H1.
       apply Mixed_State_aux_big_sum.
      intro. subst. destruct H4. lia.  intros. apply H0.
      lia. 
      exists i. split. lia.  apply Mixed_aux_not_Zero in H3. assumption.
      assert(big_sum f m = Zero \/ big_sum f m<> Zero).
      apply Classical_Prop.classic. destruct H5.
      right. rewrite H5. reflexivity.
      left. apply Mixed_State_aux_big_sum.
      intro. rewrite H6 in H5. simpl in H5.
      destruct H5. reflexivity. intros. apply H0.
      lia. 
      apply big_sum_not_0 in H5. destruct H5.
      exists x. assumption. 
        apply H0. lia. 
       assumption. lia.  assumption.
Qed.

Lemma Mixed_State_eq{n : nat}:  forall (q1 q2 : Square (2 ^ n)),
q1 = q2 -> Mixed_State q1 -> Mixed_State q2 .
Proof. intros. subst. intuition.
    
Qed.

Lemma Vector_Mix_State_aux{n:nat}: forall (v:Vector (2^n)), 
WF_Matrix v->
Mixed_State_aux (v × (adjoint v)) \/ v = Zero.
Proof. intros. assert(v = Zero \/ v<>Zero).
apply Classical_Prop.classic. destruct H0.
right. assumption.
left. apply Vector_Mix_State. assumption.
assumption.
Qed.  

Lemma big_sum_Vec_0{s e:nat}: forall (f:nat-> C) (g:nat->nat),
big_sum
        (fun r : nat => f (g r) .* ∣ r ⟩_ (e - s))
        (2 ^ (e - s)) = Zero ->
forall r, r<(2^(e-s)) -> f (g r) = C0.
Proof. intros. 
 assert(forall x, big_sum (fun r : nat => f (g r).* ∣ r ⟩_ (e - s))
 (2 ^ (e - s)) x 0 = C0).
 rewrite H. unfold Zero. intuition.
 pose (H1 (r)). 
 rewrite (Msum_Csum ) in e0.
 rewrite (big_sum_unique  (f (g r)))in e0.
 assumption. 
 exists (r). split. assumption.
 split. unfold scale.  
 rewrite Vec1. rewrite Cmult_1_r. reflexivity. reflexivity.
 intros.  unfold scale. 
 rewrite Vec0. rewrite Cmult_0_r. reflexivity.
 assumption.   
Qed.


Lemma Odot_Sepear{ s x e:nat}: forall (q: qstate s e),
s<=x/\x<=e ->
@Mixed_State (2^(e-s)) q->
@Par_Pure_State (2^(x-s)) (PMpar_trace q s x)->
exists (q1:qstate s x) (q2: qstate x e), 
and (@WF_Matrix  (2^(x-s))  (2^(x-s)) q1 /\ @WF_Matrix (2^(e-x))  (2^(e-x)) q2) 
(q = @kron (2^(x-s)) (2^(x-s)) (2^(e-x))  (2^(e-x)) q1 q2).
Proof. intros q Hs. intros H H0. induction H.   
     unfold Par_Pure_State in *.
       destruct H0. destruct H0.
       destruct H0. destruct H2.
       destruct H2. destruct H2.
       rewrite H4 in *. 
       rewrite PMpar_trace_L in *.
       induction H. destruct H1.
       destruct H1. subst.
       rewrite <-L_trace_scale in *.
       assert(p=x0).
       assert(@trace (2^(x-s)) (p .* PMLpar_trace (x3 × (x3) †) x)=
       trace (x0 .* (x2 × (x2) †))).
       rewrite H3. reflexivity.
       repeat rewrite trace_mult_dist in H4.
       rewrite <-PMpar_trace_L in H4.
       rewrite Ptrace_trace in H4.
        rewrite trace_mult' in H4. 
        rewrite (trace_mult' _ _ x2) in H4. 
       destruct H1. rewrite H6 in H4.
       destruct H2. rewrite H7 in H4.
       rewrite trace_I in H4. repeat rewrite Cmult_1_r in H4.
       injection H4. intuition.
       intuition. destruct H1. auto_wf. intuition.
       destruct H1.  auto_wf. 
       subst.
       assert(((/x0)* x0)%R .* PMLpar_trace (x3 × (x3) †) x 
       = ((/x0)* x0)%R .* (x2 × (x2) †)).
       rewrite <-RtoC_mult. repeat rewrite <-Mscale_assoc.
       rewrite H3. reflexivity.
       rewrite Rinv_l in H4. 
       rewrite Mscale_1_l in H4.
       unfold PMLpar_trace in H4.

       
       (*第一步*)
       assert(forall i : nat, i< (2 ^ (e - x)) ->
       (((@Mmult _ (2^(x-s) * 2^(e-x)) 1 (I (2 ^ (x - s)) ⊗ ⟨ i ∣_ (e - x))  x3) = Zero) \/ 
       (exists p, and (0<p<=1)%R ((I (2 ^ (x - s)) ⊗ ⟨ i ∣_ (e - x) × (x3 × (x3) †)
       × (I (2 ^ (x - s)) ⊗ ∣ i ⟩_ (e - x))) =
       p .* ( x2 × (x2) †))))).
       assert(forall i : nat, i< (2 ^ (e - x)) -> 
       ((@Mmult _ (2^(x-s) * 2^(e-x)) 1 (I (2 ^ (x - s)) ⊗ ⟨ i ∣_ (e - x))  x3) = Zero) \/ 
       ((@Mmult _ (2^(x-s) * 2^(e-x)) 1 (I (2 ^ (x - s)) ⊗ ⟨ i ∣_ (e - x))  x3) <> Zero)).
       intros. apply Classical_Prop.classic.
       intros. pose (H6 i  H7).
       destruct o.  left. assumption.
       right.
       apply (Mixed_pure_sum (fun i : nat =>
       I (2 ^ (x - s)) ⊗ ⟨ i ∣_ (e - x) × (x3 × (x3) †)
       × (I (2 ^ (x - s)) ⊗ ∣ i ⟩_ (e - x))) (2 ^ (e - x)) ).
       rewrite mul_1_r. assumption.
       intros.

      
       
       assert( 2^(e-s)= 2^(x-s) * 2^(e-x)).
       type_sovle'. destruct H10.
       rewrite <-Mmult_assoc. 
       rewrite (Mmult_assoc _ ((x3) †) _ ).
       assert((I (2 ^ (x - s)) ⊗ ∣ i0 ⟩_ (e - x))=
       adjoint (I (2 ^ (x - s)) ⊗⟨ i0 ∣_ (e - x))).
       rewrite kron_adjoint. rewrite id_adjoint_eq.
       rewrite adjoint_involutive. reflexivity.
       rewrite H10.
       assert(2^(x-s) * 2^(e-x) =  2^(e-s)).
       type_sovle'. destruct H11.
       rewrite <- Mmult_adjoint.
       assert(I (2 ^ (x - s)) ⊗ ⟨ i0 ∣_ (e - x) × x3 = Zero
       \/ I (2 ^ (x - s)) ⊗ ⟨ i0 ∣_ (e - x) × x3 <> Zero).
       apply Classical_Prop.classic. destruct H11.
       right. rewrite H11. rewrite Mmult_0_l. reflexivity.
       left. 
       apply Vector_Mix_State. destruct H1.
       auto_wf. assumption.
       rewrite Mscale_1_l in H4.
       exists 1%R. 
       split. intuition. 
       rewrite Mscale_1_l.  
       assumption. assumption.

       assert( 2^(e-s)= 2^(x-s) * 2^(e-x)).
       type_sovle'. destruct H9.
       rewrite <-Mmult_assoc. 
       rewrite (Mmult_assoc _ ((x3) †) _ ).
       assert((I (2 ^ (x - s)) ⊗ ∣ i⟩_ (e - x))=
       adjoint (I (2 ^ (x - s)) ⊗⟨ i ∣_ (e - x))).
       rewrite kron_adjoint. rewrite id_adjoint_eq.
       rewrite adjoint_involutive. reflexivity.
       rewrite H9.
       assert(2^(x-s) * 2^(e-x) =  2^(e-s)).
       type_sovle'. destruct H10.
       rewrite <- Mmult_adjoint.
       apply Vector_Mix_State. destruct H1. auto_wf.
       assumption.

       (* 第二步*)
       assert(forall i : nat,i< (2 ^ (e - x))-> 
       ((@Mmult _ (2^(x-s) * 2^(e-x)) 1 (I (2 ^ (x - s)) ⊗ ⟨ i ∣_ (e - x))  x3) = Zero) \/
       exists c : C, 
         (and (c<>C0)
          (@Mmult _ (2^(x-s) * 2^(e-x)) 1 (I (2 ^ (x - s)) ⊗ ⟨ i ∣_ (e - x))  x3
         = c .* x2))).
       intros.
       pose (H6 i H7). 
       destruct o. left. apply H8. 
       right.  apply (outer_product_eq' (2 ^ (x - s))).
       destruct H1. 
       assert( 2^(e-s)= 2^(x-s) * 2^(e-x)).
       type_sovle'. destruct H10.
      rewrite mul_1_r.
       auto_wf. destruct H2.  
       auto_wf.  
       destruct H8.  
       exists x1. 
       split. intro. injection H9. lra.
       unfold outer_product.
      remember ((I (2 ^ (x - s)) ⊗ ⟨ i ∣_ (e - x) × x3) ).
      assert ((@adjoint (Nat.pow (S (S O)) (sub x s)) (S O) m)=(m) †).
      rewrite Heqm. f_equal; lia. rewrite H9. 
      rewrite Heqm.  
       rewrite Mmult_adjoint.
       rewrite kron_adjoint.
       rewrite id_adjoint_eq.
       rewrite adjoint_involutive.
       destruct H8. rewrite<-H10. clear H9.
       assert(2^(x-s) * 2^(e-x) = 2^(e-s)).
       type_sovle'. destruct H9.
       remember (I (2 ^ (x - s)) ⊗ ⟨ i ∣_ (e - x)).
       rewrite <-Mmult_assoc. 
       rewrite Mmult_assoc. 
        f_equal; lia. 
   
      
       assert(forall i, i < 2 ^ (e - x) ->  (@Mmult _ (2^(x-s) * 2^(e-x)) 1 (I (2 ^ (x - s)) ⊗ ⟨ i ∣_ (e - x))  x3)=
       big_sum
       (fun r : nat => x3 (r * 2 ^ (e - x) + i) 0 .* ∣ r ⟩_ (x - s))
       (2 ^ (x - s))).
       intros.

       rewrite (Vec_decom x3) at 1.
       assert( 2^(e-s)=2^(x-s) * 2^(e-x)).
       type_sovle'. destruct H9.
       rewrite Mmult_Msum_distr_l. 
       rewrite (big_sum_eq_bounded _ (
              (fun i0 : nat =>
       (x3 i0 0) .*
       ( (∣ i0/(2^(e-x))  ⟩_ (x - s)) ⊗ 
        (⟨ i ∣_ (e - x) × ( ∣ i0 mod (2^(e-x))  ⟩_ (e - x)))) )))
        at 1.
        assert( 2^(x-s) * 2^(e-x)= 2^(e-s)).
        type_sovle'. destruct H9.
        rewrite (big_sum_par  _ _ i).
        apply big_sum_eq_bounded.
        intros. f_equal.
        lia. 
        assert((x1 * 2 ^ (e - x) + i) / 2 ^ (e - x) = x1).
        rewrite add_comm.
        rewrite div_add. 
         rewrite div_small.
         rewrite add_0_l. reflexivity.
         assumption. apply Nat.pow_nonzero.
         lia. 
        assert((x1 * 2 ^ (e - x) + i) mod 2 ^ (e - x)= i).
        rewrite add_comm.
        rewrite mod_add. 
        rewrite mod_small.
        reflexivity.
        assumption. 
        apply Nat.pow_nonzero.
        lia.
        rewrite H10. rewrite H11. rewrite Vec_inner_1. unfold c_to_Vector1.
        Msimpl.  reflexivity.
        assumption. assumption.
        intros. rewrite Vec_inner_0. unfold c_to_Vector1.
        Msimpl.  reflexivity. 
        assumption. assumption.
        apply mod_bound_pos.
        lia. apply pow_gt_0.  
       intros.
        rewrite Mscale_mult_dist_r.
        f_equal.
       assert(((x-s)+ (e-x) )=(e-s)).
       lia. destruct H10.
       rewrite <-Vec_kron.
       remember (I (2 ^ (x - s)) ⊗ ⟨ i ∣_ (e - x)).
       remember ((∣ x1 / 2 ^ (e - x) ⟩_ (x - s)
       ⊗ ∣ x1 mod 2 ^ (e - x) ⟩_ (e - x))).
       assert((@Mmult
       (Init.Nat.mul (Nat.pow (S (S O)) (sub x s)) (S O))
       (Nat.pow (S (S O)) (add (sub x s) (sub e x))) 
       (S O) m m0) = m × m0).
      f_equal; type_sovle'.
      rewrite H10.  rewrite Heqm. rewrite Heqm0.
       rewrite kron_mixed_product.
       rewrite Mmult_1_l; auto_wf. reflexivity.
       apply WF_vec.
       apply div_lt_upper_bound.
       apply Nat.pow_nonzero.
       lia. 
       assert(2 ^ (e - x) * 2 ^ (x - s) = 2^(x - s + (e - x))).
       type_sovle'. rewrite H11. 
       assumption.   destruct H1. assumption.


       (*第三步*)
       assert(forall i : nat, (i<(2^(e-x)))->
       ((big_sum (fun r=> (x3 (r*(2^(e-x))+ i)%nat 0) .* (Vec (2^(x-s)) r) ) (2^(x-s))) = Zero) 
       \/
       exists c: C,
         (and (c<>C0)
          (big_sum (fun r=> (x3 (r*(2^(e-x))+ i)%nat 0) .* (Vec (2^(x-s)) r) ) (2^(x-s))= c .* x2))%type).
       intros. 
       pose (H7 i H9).
       destruct o. left. rewrite <-H8. assumption. assumption. 
       right.
       destruct H10. destruct H10. 
       exists x1.
       split. intuition. rewrite<-H8.
       assumption. assumption.
       
       (* 第四步*)
      assert(exists i, and (i< 2 ^ (e - x))  ((big_sum
      (fun r : nat => x3 (r * 2 ^ (e - x) + i)%nat 0 .* ∣ r ⟩_ (x - s))
      (2 ^ (x - s))) <> Zero)).
      assert(big_sum
      (fun i : nat =>
       I (2 ^ (x - s)) ⊗ ⟨ i ∣_ (e - x) × (x3 × (x3) †)
       × (I (2 ^ (x - s)) ⊗ ∣ i ⟩_ (e - x))) (2 ^ (e - x))<> Zero).
       rewrite H4. rewrite Mscale_1_l.
       intro. assert(trace (x2 × (x2) †)=C0).
       rewrite H10. rewrite mul_1_r. apply Zero_trace.
        destruct H2. rewrite trace_mult' in H11.
        rewrite H12 in H11. rewrite trace_I in H11.
        injection H11. lra. 
        apply big_sum_not_0 in H10.
        destruct H10. destruct H10.
        assert(2^(x-s) * 2^(e-x) = 2^(e-s)).
        type_sovle'. destruct H12.
        rewrite<- Mmult_assoc in H11.
        assert(I (2 ^ (x - s)) ⊗ ⟨ x1 ∣_ (e - x) × x3 <> Zero).
        intro. rewrite H12 in H11.
        repeat rewrite Mmult_0_l in H11.
        destruct H11. reflexivity.
        exists x1. split. assumption.
        rewrite <-H8. assumption.
        assumption.
        destruct H10.
       assert(forall k, (k<(2^(e-x)))-> (exists lamda, forall j, 
       j < 2 ^ (x - s) ->
       (x3 (j * (2^(e-x)) + k) 0) = Cmult lamda (x3 (j * (2^(e-x))+ x1) 0))).
       (* 这里应该选择哪个 不是全0 的i*)
       intros. destruct H10.
       pose (H9 k H11). 
       pose (H9 x1 H10 ). 
       destruct o. exists 0%R.
       intros. 
       rewrite Cmult_0_l. 
       apply (@big_sum_Vec_0 s x ( fun i:nat=> x3 i 0) (fun r:nat => r * 2 ^ (e - x) + k)).
       assumption. assumption.
       destruct o0. 
       rewrite H14 in H12. destruct H12.
       reflexivity.   
        destruct H13.
      destruct H14.
       exists ( x4/  x5)%C. intros.
       remember (big_sum
       (fun r : nat =>
        x3 (r * 2 ^ (e - x) + k) 0
        .* ∣ r ⟩_ (x - s)) (2 ^ (x - s))).
        remember (big_sum
        (fun r : nat =>
         x3 (r * 2 ^ (e - x) + x1) 0
         .* ∣ r ⟩_ (x - s)) (2 ^ (x - s))).
       assert(  m j 0 = (( x4 /  x5)%C * m0 j 0)%C).
       apply (Vec_linear ). destruct H13.
       destruct H14.
       rewrite H16. rewrite H17. rewrite Mscale_assoc.
        rewrite Cdiv_unfold. 
       rewrite <-Cmult_assoc. rewrite Cinv_l.
       rewrite Cmult_1_r. reflexivity. assumption.
       (* unfold not. intros. injection H18.
       intros. apply sqrt_eq_0 in H19. lra. lra.
       apply sqrt_neq_0_compat. lra.*)
       subst.  
       repeat rewrite Msum_Csum in *.
        rewrite (big_sum_unique  (x3 (j * 2 ^ (e - x) + k) 0)) in H16.
        rewrite (big_sum_unique  (x3 (j * 2 ^ (e - x) + x1) 0)) in H16.
        assumption. 
        exists j. split. assumption. 
        split. unfold scale. rewrite Vec1.
        rewrite Cmult_1_r. 
        reflexivity. reflexivity. 
        intros. unfold scale. rewrite Vec0.
        rewrite Cmult_0_r. reflexivity.
        assumption.
        exists j. split. assumption.
        split. unfold scale. rewrite Vec1.
        rewrite Cmult_1_r. 
        reflexivity. reflexivity. 
        intros. unfold scale. rewrite Vec0.
        rewrite Cmult_0_r. reflexivity.
        assumption.
        
       (*第四步*)
       assert(exists (v1 : Vector (2^(x-s))) (v2 : Vector (2^(e-x))),
       and (WF_Matrix v1 /\ WF_Matrix v2) 
        (kron  v1 v2 = x3)).
       apply Separ.  destruct H1. 
       assert(e-s= x - s + (e - x)).
       lia. destruct H13.  apply H1.
       (*这里继续找 x i j 不等于0 的那个j 作为分布*) 
   assert( exists r, and (r < (2 ^ (x - s)) ) (x3 (r * 2 ^ (e - x) + x1) 0 <> 0%R)).
   destruct H10. apply (@big_sum_not_0 (2^(x-s)) ((fun r : nat => x3 (r * 2 ^ (e - x) + x1) 0 .* ∣ r ⟩_ (x - s)))
   (2^(x-s))) in H12. destruct H12.
   exists x4. split. intuition. 
   destruct H12. intro. rewrite H14 in H13.
   rewrite Mscale_0_l in H13. destruct H13.
   reflexivity.
    destruct H12.
   exists (fun i=> (x3 (i * 2 ^ (e - x) + x1 ) 0)). 
       exists (fun i=> Cdiv (x3 (x4 * 2 ^ (e - x) + i) 0 ) (x3 (x4 * 2 ^ (e - x) + x1) 0)).
       intros. 
       remember (z mod 2 ^ (e - x)).
       assert( exists j, z = j * 2 ^ (e - x) + n).
       exists (z/(2^(e-x))).
       rewrite Heqn. rewrite Nat.mul_comm.
       apply div_mod_eq. 
        destruct H14.
       assert(z / 2 ^ (e - x) = x5).
       rewrite H14. rewrite Heqn. 
       symmetry. rewrite add_comm.  rewrite div_add.
       rewrite div_small. rewrite add_0_l.
       reflexivity. 
       apply mod_bound_pos. lia.
       apply pow_gt_0. 
       apply Nat.pow_nonzero. lia.   rewrite H15.
       rewrite H14.
       assert(n < 2 ^ (e - x)).
       rewrite H14 in H15.
       rewrite add_comm in H15.
       rewrite div_add in H15.
       assert(n / 2 ^ (e - x) + x5 - x5 =  x5 -x5).
       rewrite H15. reflexivity.
       rewrite Nat.sub_diag in H16.
        repeat rewrite add_sub in H16.
        apply div_small_iff. apply Nat.pow_nonzero.
        lia. assumption. apply Nat.pow_nonzero. lia.  
      pose (H11 n H16).
      destruct e0.
      rewrite H17. rewrite H17. 
      rewrite Cdiv_unfold.
      rewrite <-Cmult_assoc. 
      rewrite Cinv_r. 
      rewrite Cmult_1_r.
      rewrite Cmult_comm. reflexivity.
      intuition. intuition.
       rewrite <-H15.   
       apply div_lt_upper_bound. 
       apply Nat.pow_nonzero. lia.
       rewrite <-pow_add_r.
       rewrite add_comm. 
       assumption. 
       destruct H12.
       destruct H12.
       destruct H12.
       rewrite <-H13.
       exists (sqrt x0 .*  (x4 × (x4 ) †)).
       exists (sqrt x0 .*  (x5 × (x5 ) †)).
       rewrite Mscale_kron_dist_l.
       rewrite Mscale_kron_dist_r.
       rewrite Mscale_assoc.
       rewrite RtoC_mult.
       rewrite sqrt_sqrt.
       assert( 2 ^ (x - s) * 2 ^ (e - x) = 2 ^ (e - s) ).
       type_sovle'. destruct H14.
       f_equal. 
       rewrite <-kron_mixed_product.
       f_equal. rewrite <-kron_adjoint.
       split. split. apply WF_scale. 
       apply WF_mult. intuition. 
       apply WF_adjoint. intuition.
       apply WF_scale. 
       apply WF_mult. intuition.
       apply WF_adjoint. intuition.

       f_equal. lra. lra. intuition.
       auto_wf. 
       
       destruct H0. rewrite PMtrace_plus in H0.
       destruct H0. destruct H0. destruct H5.
       destruct H5. destruct H5. rewrite H7 in *.
       assert( exists p, (and (0 < p <= 1)%R  (PMpar_trace (p1 .* ρ1) s x .+ PMpar_trace (p2 .* ρ2) s x =
       p .* (x2 × (x2) †)))).
       exists x0. intuition.
       assert(@Mixed_State_aux  (2^(x-s)) (PMpar_trace (p1 .* ρ1) s x) ).
       apply Mixed_State_aux_to_Mix_State.
       apply Mix_par_trace. intuition.
       unfold WF_qstate. split.
       apply Mixed_State_scale. assumption.
       assumption. intuition.
       assert(@Mixed_State_aux  (2^(x-s)) (PMpar_trace (p2 .* ρ2) s x)).
       apply Mixed_State_aux_to_Mix_State.
       apply Mix_par_trace. intuition.
       unfold WF_qstate. split. 
       apply Mixed_State_scale. assumption.
       assumption. intuition. 
       pose H9. pose H10.
       apply (Mixed_pure' (PMpar_trace (p1 .* ρ1) s x) (PMpar_trace (p2 .* ρ2) s x) x2) in m; try assumption. 
       apply (Mixed_pure' (PMpar_trace (p1 .* ρ1) s x) (PMpar_trace (p2 .* ρ2) s x) x2) in m0; try assumption.
       destruct m. destruct H11.
       destruct m0. destruct H13.
       rewrite <- PMtrace_scale in H12.
       rewrite <- PMtrace_scale in H14. 
       assert(PMpar_trace ρ1 s x = (/p1 * x3) .* (x2 × (x2) †)).
       rewrite <-Mscale_assoc. rewrite <-H12.
       rewrite Mscale_assoc. rewrite Cinv_l.
       rewrite Mscale_1_l. reflexivity.
       unfold not. intros. injection H15. intros. lra. 
       assert(@Par_Pure_State  (2^(x-s)) (PMpar_trace ρ1 s x)).
       econstructor. exists ((x2 × (x2) †)). 
        assert(0 < (/ p1 * x3) <= 1)%R.
        assert(Cmod (@trace (2^(x-s)) (PMpar_trace ρ1 s x)) =
        Cmod (trace (/ p1 * x3 .* (x2 × (x2) †))) ).
        rewrite H15. reflexivity.
        rewrite Ptrace_trace in H16; try auto_wf; try lia. 
        rewrite trace_mult_dist in H16.
        rewrite Cmod_mult in H16. 
        rewrite trace_mult' in H16.
        destruct H5. rewrite H17 in H16.
        rewrite trace_I in H16. 
        rewrite Cmod_1 in H16. rewrite Rmult_1_r in H16.
        rewrite <-RtoC_inv in H16.
        rewrite RtoC_mult in H16.
        rewrite Cmod_R in H16. 
        rewrite Rabs_right in H16.
        rewrite <-H16. apply mixed_state_Cmod_1.
        assumption.  
        assert(0<(/ p1 * x3 ))%R.
        apply Rmult_gt_0_compat.
        apply Rinv_0_lt_compat. intuition.
        intuition. lra. lra. 
         split. apply H16.
         split. econstructor.
       split. apply H5. reflexivity.
       rewrite <-RtoC_mult. rewrite RtoC_inv. assumption.
       lra. 
       assert(PMpar_trace ρ2 s x = (/p2 * x4) .* (x2 × (x2) †)).
       rewrite <-Mscale_assoc. rewrite <-H14.
       rewrite Mscale_assoc. rewrite Cinv_l.
       rewrite Mscale_1_l. reflexivity.
       unfold not. intros. injection H17. intros. lra. 
       assert(@Par_Pure_State  (2^(x-s)) (PMpar_trace ρ2 s x)).
       econstructor. exists ((x2 × (x2) †)). 
        assert(0 < (/ p2 * x4) <= 1)%R.
        assert(Cmod (@trace (2^(x-s)) (PMpar_trace ρ2 s x)) =
        Cmod (trace (/ p2 * x4 .* (x2 × (x2) †))) ).
        rewrite H17. reflexivity.
        rewrite Ptrace_trace in H18.
        rewrite trace_mult_dist in H18.
        rewrite Cmod_mult in H18. 
        rewrite trace_mult' in H18.
        destruct H5. rewrite H19 in H18.
        rewrite trace_I in H18. 
        rewrite Cmod_1 in H18. rewrite Rmult_1_r in H18.
        rewrite <-RtoC_inv in H18.
        rewrite RtoC_mult in H18.
        rewrite Cmod_R in H18. 
        rewrite Rabs_right in H18.
        rewrite <-H18. apply mixed_state_Cmod_1.
        assumption.  
        assert(0<(/ p2 * x4 ))%R.
        apply Rmult_gt_0_compat.
        apply Rinv_0_lt_compat. intuition.
        intuition. lra. lra. lia.
        apply WF_Mixed. assumption.
        split. apply H18.
         split. econstructor.
       split. apply H5. reflexivity.
       rewrite <-RtoC_mult. rewrite RtoC_inv. assumption.
       lra. 
       pose H16. pose H18.
      apply  IHMixed_State1 in p.
      apply IHMixed_State2 in p0.
      destruct p. destruct H19.
      destruct p0. destruct H20.
       destruct H19.
       destruct H20. rewrite H21. rewrite H22.
       pose H21. pose H22.
       apply PMpar_trace_l in e0; try apply H19; try apply H20; try auto_wf.
       apply PMpar_trace_l in e1; try apply H19; try apply H20; auto_wf.
       rewrite <-PMpar_trace_L in e0; try auto_wf; try lia. 
       rewrite <-PMpar_trace_L in e1; try auto_wf; try lia. 
       rewrite H15 in e0.
       rewrite H17 in e1.
     
       exists ( (x2 × (x2) †)).
       exists ((p1 * /@trace (2^(e-x)) x6 * /p1 * x3) .* x6 .+ 
       (p2 * /@trace (2^(e-x)) x8 * /p2 *  x4) .* x8).
       split. split. 
       destruct H5. auto_wf.
       apply WF_plus; auto_wf;
       apply WF_scale; intuition.
       rewrite kron_plus_distr_l.
       repeat rewrite Mscale_kron_dist_r.
       repeat rewrite <-Mscale_kron_dist_l.
       f_equal; type_sovle'.
       rewrite <-Mscale_assoc.
       rewrite <-Mscale_assoc.
       rewrite (Mscale_assoc _ _  (/p1) x3).
       rewrite e0.  rewrite  Mscale_assoc.
       rewrite <-Cmult_assoc.
       rewrite Cinv_l. rewrite Cmult_1_r.
       rewrite Mscale_kron_dist_l. reflexivity.
       intro. rewrite H23 in e0. rewrite Mscale_0_l in e0.
       apply (scale_Zero  (/ p1 * x3)  (x2 × (x2) †) ) in e0.
       assert(trace ( x2 × (x2) † )  =C0).
       rewrite e0. rewrite Zero_trace. reflexivity.
       destruct H5. rewrite trace_mult' in H24.
       rewrite H25 in H24. rewrite trace_I in H24.
       injection H24. lra. 
       apply C0_fst_neq. 
       rewrite<- RtoC_inv. rewrite RtoC_mult.
       simpl.
       apply Rmult_integral_contrapositive_currified.
       assert((/ p1)%R > 0%R)%R. 
       apply Rinv_0_lt_compat. lra.
       lra. lra. lra.

      
       rewrite <-Mscale_assoc.
       rewrite <-Mscale_assoc.
       rewrite (Mscale_assoc _ _  (/p2) x4).
       rewrite e1.  repeat rewrite Mscale_kron_dist_l.
       rewrite Mscale_assoc. 
       rewrite <-Cmult_assoc.
        rewrite Cinv_l. rewrite Cmult_1_r.
         reflexivity.
         intro. rewrite H23 in e1. rewrite Mscale_0_l in e1.
         apply (scale_Zero  (/ p2 * x4) ((x2)  × (x2) †) ) in e1.
         assert(trace ( (x2 × (x2) †) ) =C0).
         rewrite e1. rewrite Zero_trace. reflexivity.
         destruct H5. rewrite trace_mult' in H24.
         rewrite H25 in H24. rewrite trace_I in H24.
         injection H24. lra. 
         apply C0_fst_neq. 
         rewrite<- RtoC_inv. rewrite RtoC_mult.
         simpl.
         apply Rmult_integral_contrapositive_currified.
         assert((/ p2)%R > 0%R)%R. 
         apply Rinv_0_lt_compat. lra.
         lra. lra. lra.
      left. assumption.
      left. assumption.
      left. assumption.
      left. assumption.
Qed.

Lemma big_sum_mult_l_C: forall (c: C) (f: nat-> C) n, 
    (c * big_sum f n)%C = big_sum (fun x => (c * f x)%C) n.
Proof.
  intros.
  induction n.
  + simpl; apply Cmult_0_r.
  + simpl.
    rewrite Cmult_plus_distr_l. 
    rewrite IHn.
    reflexivity.
Qed.

Lemma big_sum_sum_C : forall m n (f: nat->C), 
  big_sum f (m + n) = (big_sum f m + big_sum (fun x => f (m + x)%nat) n)%C.
Proof. intros. rewrite big_sum_sum.
      reflexivity. 
Qed.

Lemma big_sum_product_C: forall m n (f g:nat-> C), 
  n <> O ->
  (big_sum f m * big_sum g n)%C = big_sum (fun x => (f (x / n)%nat * g (x mod n)%nat))%C (m * n). 
Proof.
  intros.
  induction m; simpl. 
  + rewrite Cmult_0_l; reflexivity. 
  + rewrite Cmult_plus_distr_r.
    rewrite IHm. clear IHm.
    rewrite big_sum_mult_l_C.
    remember ((fun x : nat => (f (x / n)%nat * g (x mod n)%nat))%C) as h.
    replace (big_sum (fun x : nat => (f m * g x)%C) n) with
            (big_sum (fun x : nat => h ((m * n) + x)%nat) n). 
    2:{
      subst.
      apply big_sum_eq_bounded.
      intros x Hx.
      rewrite Nat.div_add_l by assumption.
      rewrite Nat.div_small; trivial.
      rewrite Nat.add_0_r.
      rewrite Nat.add_mod by assumption.
      rewrite Nat.mod_mul by assumption.
      rewrite Nat.add_0_l.
      repeat rewrite Nat.mod_small; trivial. }
    rewrite <- big_sum_sum_C.
    rewrite Nat.add_comm.
    reflexivity.
Qed. 


Lemma trace_kron{m n}: forall (q1:Square m) (q2:Square n),
n<>0->
trace  (kron q1 q2)= (trace  (q1) * trace  q2)%C.
Proof. intros. unfold trace.
        rewrite big_sum_product_C.
        unfold kron. apply big_sum_eq_bounded.
        intros. reflexivity. assumption.  
Qed.

Lemma Odot_Sepear'{ s x e:nat}: forall (q: qstate s e),
s<=x/\x<=e ->
@Mixed_State (2^(e-s)) q->
@Par_Pure_State (2^(x-s)) (PMpar_trace q s x)->
@trace (2^(e-s)) (q) .* q = @kron (2^(x-s)) (2^(x-s)) (2^(e-x))  (2^(e-x)) (PMpar_trace q s x) 
(PMpar_trace q x e).
Proof. intros q H H0 H1. apply (Odot_Sepear q H H0) in H1.
       destruct H1. destruct H1. 
       destruct H1. 
       pose H2. pose H2.
       apply PMpar_trace_l in e0.
       rewrite PMpar_trace_L. 
       rewrite e0. 
       apply PMpar_trace_r in e1.
       rewrite PMpar_trace_R.
       rewrite e1. 
       rewrite Mscale_kron_dist_l.
       rewrite Mscale_kron_dist_r.
       rewrite Mscale_assoc.
       rewrite H2. f_equal.
       
       assert(2^(x-s)*2^(e-x)= 2^(e-s))%nat.
       type_sovle'. destruct H3.
       rewrite Cmult_comm.
       apply trace_kron. apply Nat.pow_nonzero. lia. reflexivity.
       apply WF_Mixed. assumption.
       intuition. intuition.
       apply WF_Mixed. assumption.
       intuition.
       apply WF_Mixed. assumption.
       intuition. intuition.
       apply WF_Mixed. assumption.
Qed.

Lemma  Mixed_State_aux_to01':forall {n} (ρ : Density n),
Mixed_State_aux ρ ->
Mixed_State (( / (trace ρ))%C .* ρ) .
Proof. intros.  
       assert(trace ρ= ((fst (trace ρ)), snd (trace ρ))).
    destruct (trace ρ). reflexivity.
    rewrite H0. 
    assert(/ (fst (trace ρ), snd (trace ρ)) 
    = (( / (Cmod (trace ρ )))%R, 0%R) ).
     rewrite Cmod_snd_0. rewrite mixed_state_trace_real_aux.
     assert(((/ fst (trace ρ))%R, 0%R) = RtoC ((/ fst (trace ρ))%R)).
     reflexivity. rewrite H1.
     rewrite RtoC_inv. f_equal.
     assert((0 < fst (trace ρ))%R).
     apply mixed_state_trace_gt0_aux.
     assumption. lra. 
     assumption.
     apply mixed_state_trace_gt0_aux.
     assumption. apply mixed_state_trace_real_aux.
     assumption. 
     rewrite H1. apply Mixed_State_aux_to01.
     assumption.
Qed. 

     


Lemma WF_qstate_to01{ s e:nat}: forall (q: qstate s e),
WF_qstate q ->
@WF_qstate  s e (/@trace (2^(e-s)) q .* q).
Proof. intros. unfold WF_qstate in *.
      split. apply Mixed_State_aux_to01'.
      apply Mixed_State_aux_to_Mix_State.
      intuition. intuition.
Qed.


Lemma Odot_Sepear''{ s x e:nat}: forall (q: qstate s e),
s<=x/\x<=e ->
@Mixed_State (2^(e-s)) q->
@Par_Pure_State (2^(x-s)) (PMpar_trace q s x)->
exists (q1:qstate s x) (q2: qstate x e), 
and (@WF_qstate  s x q1 /\ @WF_qstate x e q2) 
(q = @kron (2^(x-s)) (2^(x-s)) (2^(e-x))  (2^(e-x)) q1 q2).
Proof. intros q H H0 H1. assert(@trace (2^(e-s)) (q) .* q = @kron (2^(x-s)) (2^(x-s)) (2^(e-x))  (2^(e-x)) (PMpar_trace q s x) 
(PMpar_trace q x e)).
apply Odot_Sepear'. assumption. assumption. assumption.
exists (/(@trace (2^(e-s)) q) .* (PMpar_trace q s x)).
exists (PMpar_trace q x e).
split. split. rewrite <-(Ptrace_trace _ _ _ s x).
apply WF_qstate_to01. 
apply Mix_par_trace.  intuition.
unfold WF_qstate. split.  apply H0.
intuition. intuition. 
apply WF_Mixed. assumption.
apply (Mix_par_trace s e x e q).
intuition. unfold WF_qstate. split.  apply H0.
intuition. 
rewrite Mscale_kron_dist_l.
rewrite <-H2. rewrite Mscale_assoc.
rewrite Cinv_l. rewrite Mscale_1_l.
reflexivity.
assert(@trace (2^(e-s)) q= ((fst (@trace (2^(e-s)) q)), snd (@trace  (2^(e-s)) q))).
    destruct (@trace (2^(e-s)) q ). reflexivity.
    rewrite H3.
unfold not. intros.
injection H4.
intros. 
assert(fst (@trace (2^(e-s)) q) > 0%R)%R.
apply mixed_state_trace_gt0.
assumption. lra.
Qed.

Lemma Odot_Sepear'''{ s x e:nat}: forall (q: qstate s e),
s<=x/\x<=e ->
@Mixed_State (2^(e-s)) q->
@Par_Pure_State (2^(e-x)) (PMpar_trace q x e)->
exists (q1:qstate s x) (q2: qstate x e), 
and (@WF_qstate  s x q1 /\ @WF_qstate x e q2) 
(q = @kron (2^(x-s)) (2^(x-s)) (2^(e-x))  (2^(e-x)) q1 q2).
Proof. Admitted.


Lemma Par_Pure_State_wedge{ s e: nat}:forall (q:qstate s e) s' x' e',
s<=s'/\ s'<=x'/\ x'<=e' /\ e'<= e ->
WF_qstate q->
@Par_Pure_State (2^(x'-s')) (PMpar_trace q s' x')->
@Par_Pure_State (2^(e'-x')) (PMpar_trace q x' e')->
@Par_Pure_State (2^(e'-s')) (PMpar_trace q s' e').
Proof. intros.
assert((PMpar_trace q s' x') = 
PMpar_trace (PMpar_trace q s' e') s' x').
rewrite  PMpar_trace_assoc.
reflexivity. intuition.
rewrite H3 in H1. 
assert((PMpar_trace q x' e') =
PMpar_trace (PMpar_trace q s' e') x' e'). 
rewrite PMpar_trace_assoc.
reflexivity. intuition.
rewrite H4 in H2. 
remember ((PMpar_trace q s' e')).
assert(@trace (2^(e'-s')) (q0) .* q0 =@kron (2^(x'-s')) (2^(x'-s')) 
(2^(e'-x'))  (2^(e'-x')) (PMpar_trace q0 s' x') (PMpar_trace q0 x' e') ).
apply Odot_Sepear'. intuition.
rewrite Heqq0.
apply Mix_par_trace. intuition.
assumption.
assumption. 

unfold Par_Pure_State in *.
destruct H1. destruct H1. destruct H1.
destruct H6. destruct H6.
destruct H6. rewrite H8 in *.
destruct H2. destruct H2. destruct H2.
destruct H9. destruct H9.
destruct H9. rewrite H11 in *.
exists (x2 )%R.
exists (kron (x1 × (x1) †)  (x4 × (x4) †)).
assert( q0 =(C1 /  ( (@trace (2^(e'-s')) q0)))%C .* (x .* (x1 × (x1) †) ⊗ (x2 .* (x4 × (x4) †)))).
rewrite H7 in H5. rewrite H10 in H5.
rewrite <-H5. rewrite Cdiv_unfold.
rewrite Cmult_1_l. rewrite Mscale_assoc.
rewrite Cinv_l. rewrite Mscale_1_l.
reflexivity.

assert(@trace (2^(e'-s')) q0= ((fst (@trace (2^(e'-s')) q0)), snd (@trace  (2^(e'-s')) q0))).
    destruct (@trace (2^(e'-s')) q0 ). reflexivity.
    rewrite H12.
unfold not. intros.
injection H13.
intros. 
assert(fst (@trace (2^(e'-s')) q0) > 0%R)%R.
apply mixed_state_trace_gt0.
rewrite Heqq0. apply Mix_par_trace.
intuition. assumption. lra.
split. assumption. 
split. rewrite <-kron_mixed_product.
rewrite <-kron_adjoint.
unfold Pure_State. exists  (x1 ⊗ x4).
econstructor.
assert((2^(x'-s')) * (2^(e'-x'))= 2 ^ (e' - s')).
type_sovle'. destruct H13. 
 apply pure_state_vector_kron.
 assumption. assumption.
reflexivity.
 rewrite H12.
rewrite Mscale_kron_dist_l.
rewrite Mscale_kron_dist_r.
repeat rewrite Mscale_assoc.
remember ((x1 × (x1) † ⊗ (x4 × (x4) †))).
rewrite Cdiv_unfold. 
rewrite Cmult_1_l.
rewrite <-(Ptrace_trace _ _ _  s' x').
rewrite H7. 
rewrite trace_mult_dist.
assert(trace (x1 × (x1) †)= C1).
rewrite trace_mult'. 
destruct H6. rewrite H13.
rewrite trace_I.
reflexivity. rewrite H13.
rewrite Cmult_1_r.
rewrite <-RtoC_inv.
rewrite RtoC_mult.
rewrite Rinv_l. rewrite Cmult_1_l. reflexivity.
lra. lra.  intuition.
rewrite Heqq0. unfold PMpar_trace.
apply WF_PMRpar_trace. 
intuition. apply WF_PMLpar_trace.
intuition. apply WF_Mixed. apply H0.
Qed.

Lemma Odot_Sepear''''{ s x e:nat}: forall (q: qstate s e),
s<=x/\x<=e ->
@Mixed_State (2^(e-s)) q->
(@Par_Pure_State (2^(x-s)) (PMpar_trace q s x)\/ 
@Par_Pure_State (2^(e-x)) (PMpar_trace q x e)) ->
exists (q1:qstate s x) (q2: qstate x e), 
and (@WF_qstate  s x q1 /\ @WF_qstate x e q2) 
(q = @kron (2^(x-s)) (2^(x-s)) (2^(e-x))  (2^(e-x)) q1 q2).
Proof. intros. destruct H1;
[apply (@Odot_Sepear'' s x e) | apply (@Odot_Sepear''' s x e)]; 
try lia; try assumption.
Qed.


Lemma Par_Pure_State_kron{ s e: nat}:forall (q:qstate s e) x,
s<=x /\ x<= e ->
WF_qstate q->
(@Par_Pure_State (2^(x-s)) (PMpar_trace q s x)\/
@Par_Pure_State (2^(e-x)) (PMpar_trace q x e)) ->
/(@trace (2^(e-s)) q) .* q =
 @kron (2^(x-s)) (2^(x-s)) (2^(e-x)) (2^(e-x)) 
(/(@trace (2^(x-s)) ((PMpar_trace q s x))) .* (PMpar_trace q s x))
(/(@trace (2^(e-x)) ((PMpar_trace q x e))) .* (PMpar_trace q x e)).
Proof. intros. destruct H0.
apply (@Odot_Sepear'''' s x e) in H1; try lia; try assumption.  
destruct H1. destruct H1. 
destruct H1. destruct H1.
destruct H1. destruct H4. 
assert(PMpar_trace q s x=(@trace (2^(e-x)) x1) .* x0).
rewrite H3. rewrite PMpar_trace_L; try lia; try auto_wf.
rewrite (PMpar_trace_l _ x0 x1); try lia; try auto_wf; try reflexivity.
assert(PMpar_trace q x e=(@trace (2^(x-s)) x0) .* x1).
rewrite H3. rewrite PMpar_trace_R; try lia; try auto_wf.
rewrite (PMpar_trace_r _ x0 x1); try lia; try auto_wf; try reflexivity.
rewrite H7. rewrite H8. 
repeat rewrite trace_mult_dist. rewrite H3.
assert(2^(x-s) * (2^(e-x))= 2^(e-s)). type_sovle'.
destruct H9.  repeat rewrite trace_kron.
repeat rewrite Mscale_assoc. 
rewrite (Cmult_comm (@trace (2^(e-x)) x1)). 
 repeat rewrite Cinv_mult_distr; try apply C0_fst_neq;
 try apply Rgt_neq_0; try apply mixed_state_trace_gt0; try assumption.
 rewrite <- Cmult_assoc. rewrite Cinv_l; 
 try apply C0_fst_neq;
 try apply Rgt_neq_0; try apply mixed_state_trace_gt0; try assumption.
 Csimpl. rewrite (Cmult_comm (/(@trace (2^(x-s)) x0))).
 rewrite <- Cmult_assoc. rewrite Cinv_l; 
 try apply C0_fst_neq;
 try apply Rgt_neq_0; try apply mixed_state_trace_gt0; try assumption.
 Csimpl. 
 repeat rewrite  Mscale_kron_dist_r.
 repeat rewrite  Mscale_kron_dist_l.
 rewrite Mscale_assoc. reflexivity. apply Nat.pow_nonzero. 
  lia.

Qed.