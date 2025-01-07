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
From Quan Require Import Mixed_State.
From Quan Require Import QState.
From Quan Require Import QIMP_L.
From Quan Require Import QAssert.
From Quan Require Import Reduced.
From Quan Require Import Basic.
From Quan Require Import Ceval_Prop.
Require Import Mixed_State.
Local Open Scope nat_scope.
(*From Quan Require Import QRule_E_L.
From Quan Require Import QRule_I_L. *)

Local Open Scope com_scope.

Local Open Scope nat_scope.

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
       exists (big_sum (fun i=> (x i) .* (∣ i ⟩_ (2^m))) (2^m)).
       exists (big_sum (fun i=> (x0 i) .* (∣ i ⟩_ (2^n))) (2^n)).
       split. split. apply WF_Msum.
       intros. auto_wf. 
       apply WF_Msum.
       intros. auto_wf. 
       rewrite big_sum_kron.
       rewrite base_decom with v.
       rewrite Nat.pow_add_r.
       apply big_sum_eq_bounded.
       intros. 
       rewrite Mscale_kron_dist_l.
       rewrite Mscale_kron_dist_r.
       rewrite Mscale_assoc.
       rewrite <-H0.
       f_equal. 
       rewrite <-pow_add_r.
       rewrite base_kron.
       reflexivity. 
       rewrite pow_add_r. assumption.
       assumption.
       assert(2^n >0).
       apply pow_gt_0.
       intuition.   
Qed.

Lemma inner_trace: forall n (x: Vector (n)),
WF_Matrix x->
 ((norm x) * (norm x))%R = (fst (trace (x × x †))).
Proof. intros. unfold norm. rewrite sqrt_sqrt. 
f_equal. unfold inner_product. rewrite trace_mult.  unfold trace.
simpl. rewrite Cplus_0_l.  reflexivity. apply inner_product_ge_0.
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
      rewrite <-trace_mult in H9. 
      assert(snd (m0 0 0)=R0). rewrite H9.
      apply nz_mixed_state_trace_real_aux.
      apply Vector_nz_Mix_State_aux. assumption. assumption. 
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

Require Import Mixed_State.
Lemma Mixed_pure': forall {n:nat} (ρ1 ρ2: Density (2^n)) (φ:Vector (2^n)), 
(Mixed_State_aux ρ1 )  ->
(Mixed_State_aux ρ2 )->
Pure_State_Vector φ ->
(exists p, and (0<p<=1)%R (ρ1 .+  ρ2= p .* (φ  × φ†)))
-> 
and (NZ_Mixed_State_aux ρ1 -> exists (c1: R), and (0<c1<=1)%R (ρ1= c1 .* ( φ  × φ† )))
(NZ_Mixed_State_aux ρ2->exists (c2: R), and (0<c2<=1)%R ((ρ2= c2.* ( φ  × φ† ))) ).
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
     
      rewrite NZ_Mixed_State_aux_equiv' in H.
      rewrite NZ_Mixed_State_aux_equiv' in H0.
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
      apply nz_Mixed_State_aux_to_01'.
      assumption.
      apply Rinv_0_lt_compat. intuition. 
      apply Rle_trans with ((Cmod (trace (/ x .* ρ1 .+ / x .* ρ2 )))%R).
      rewrite nz_mixed_state_Cmod_plus_aux.
      rewrite <-Rplus_0_r at 1.
      rewrite RtoC_inv. apply Rplus_le_compat_l.
      apply Cmod_ge_0.  lra. rewrite <-RtoC_inv.
       apply nz_Mixed_State_scale_aux. 
       assumption. apply Rinv_0_lt_compat. lra.
       lra. rewrite <-RtoC_inv.
       apply nz_Mixed_State_scale_aux. 
       assumption. apply Rinv_0_lt_compat. lra.
       lra. rewrite H4. destruct H1. rewrite trace_mult.
       rewrite H5. rewrite trace_I. rewrite Cmod_1. lra.
       lra. 
       
       rewrite <-RtoC_inv.
       apply nz_Mixed_State_aux_to_01'.
       assumption.
       apply Rinv_0_lt_compat. intuition. 
       apply Rle_trans with ((Cmod (trace (/ x .* ρ1 .+ / x .* ρ2 )))%R).
       rewrite nz_mixed_state_Cmod_plus_aux.
       rewrite <-Rplus_0_l at 1.
       rewrite RtoC_inv. apply Rplus_le_compat_r.
       apply Cmod_ge_0.  lra. rewrite <-RtoC_inv.
        apply nz_Mixed_State_scale_aux. 
        assumption. apply Rinv_0_lt_compat. lra.
        lra. rewrite <-RtoC_inv.
        apply nz_Mixed_State_scale_aux. 
        assumption. apply Rinv_0_lt_compat. lra.
        lra. rewrite H4. destruct H1. rewrite trace_mult.
        rewrite H5. rewrite trace_I. rewrite Cmod_1. lra.
        lra. 
       rewrite H4.
       apply Pure_NZ_Mixed. 
       econstructor. split. apply H1.
       reflexivity.
       assumption.

       rewrite H0 in *. rewrite Mplus_0_r in H3.
       split. intros. exists x. intuition.
       intros. apply NZ_Mixed_aux_not_Zero in H5. destruct H5.
        reflexivity. 

       rewrite H in *. rewrite Mplus_0_l in H3.
       split.  intros.  
       apply NZ_Mixed_aux_not_Zero in H5. destruct H5.
        reflexivity.  intros. exists x. intuition.
        
        split; intros; subst;
        apply NZ_Mixed_aux_not_Zero in H5; destruct H5;   reflexivity.
Qed.



Local Open Scope nat_scope.
Lemma Mixed_pure_sum: forall {n:nat} (f: nat-> Density (2^n)) m 
(φ : Vector (2^n)), 
Pure_State_Vector φ ->
(forall i, i< m -> (Mixed_State_aux (f i)))->
(exists p, and (0<p<=1)%R  ((big_sum f m) = p .* (φ  × φ†) ))->
(forall i, i<m ->  (NZ_Mixed_State_aux (f i)) ->
exists p, and (0<p<=1)%R  ( (f i)= p .* (φ  × φ†))).
Proof. induction m; intros.
       simpl in *. destruct H1.
       destruct H1. 
       assert(@trace (2^n) Zero = trace (x .* (φ × (φ) †))).
       rewrite H4. reflexivity.
       rewrite Zero_trace in H5.
       rewrite trace_mult_dist in H5.
       destruct H.  rewrite trace_mult in H5.
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
      rewrite NZ_Mixed_State_aux_equiv'.
      assert(big_sum f m = Zero \/ big_sum f m<> Zero).
      apply Classical_Prop.classic. destruct H5.
      right. rewrite H5. reflexivity.
      left. apply nz_Mixed_State_aux_big_sum.
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
       apply nz_Mixed_State_aux_big_sum.
      intro. subst. destruct H4. lia.  intros. apply H0.
      lia. 
      exists i. split. lia.  apply NZ_Mixed_aux_not_Zero in H3. assumption.
      rewrite NZ_Mixed_State_aux_equiv'.
      assert(big_sum f m = Zero \/ big_sum f m<> Zero).
      apply Classical_Prop.classic. destruct H5.
      right. rewrite H5. reflexivity.
      left. apply nz_Mixed_State_aux_big_sum.
      intro. rewrite H6 in H5. simpl in H5.
      destruct H5. reflexivity. intros. apply H0.
      lia. 
      apply big_sum_not_0 in H5. destruct H5.
      exists x. assumption. 
        apply H0. lia. 
       assumption. lia.  assumption.
Qed.

Lemma NZ_Mixed_State_eq{n : nat}:  forall (q1 q2 : Square (2 ^ n)),
q1 = q2 -> NZ_Mixed_State q1 -> NZ_Mixed_State q2 .
Proof. intros. subst. intuition.
Qed.

Lemma Vector_nz_Mix_State_aux_aux{n:nat}: forall (v:Vector (2^n)), 
WF_Matrix v->
Mixed_State_aux (v × (adjoint v)).
Proof. intros. rewrite NZ_Mixed_State_aux_equiv'.
assert(v = Zero \/ v<>Zero).
apply Classical_Prop.classic.
destruct H0.
right. rewrite H0. Msimpl. reflexivity. 
left. apply Vector_nz_Mix_State_aux. assumption.
assumption.
Qed.  

Lemma big_sum_Vec_0{s e:nat}: forall (f:nat-> C) (g:nat->nat),
big_sum (fun r : nat => f (g r) .* ∣ r ⟩_ (e - s))
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
 rewrite base1. rewrite Cmult_1_r. reflexivity. reflexivity.
 intros.  unfold scale. 
 rewrite base0. rewrite Cmult_0_r. reflexivity.
 assumption.   
Qed.


Lemma Odot_Sepear{ s x e:nat}: forall (q: qstate s e),
s<=x/\x<=e ->
@NZ_Mixed_State (2^(e-s)) q->
@Par_Pure_State (2^(x-s)) (Reduced q s x)->
exists (q1:qstate s x) (q2: qstate x e), 
and (@WF_Matrix  (2^(x-s))  (2^(x-s)) q1 /\ @WF_Matrix (2^(e-x))  (2^(e-x)) q2) 
(q = @kron (2^(x-s)) (2^(x-s)) (2^(e-x))  (2^(e-x)) q1 q2).
Proof. intros q Hs. intros H H0. induction H.   
     unfold Par_Pure_State in *.
       destruct H0. destruct H0.
       destruct H0. destruct H2.
       destruct H2. destruct H2.
       rewrite H4 in *. 
       rewrite Reduced_L in *.
       induction H. destruct H1.
       destruct H1. subst.
       rewrite <-L_reduced_scale in *.
       assert(p=x0).
       assert(@trace (2^(x-s)) (p .* L_reduced (x3 × (x3) †) x)=
       trace (x0 .* (x2 × (x2) †))).
       rewrite H3. reflexivity.
       repeat rewrite trace_mult_dist in H4.
       rewrite <-Reduced_L in H4.
       rewrite Reduced_trace in H4.
        rewrite trace_mult in H4. 
        rewrite (trace_mult _ _ x2) in H4. 
       destruct H1. rewrite H6 in H4.
       destruct H2. rewrite H7 in H4.
       rewrite trace_I in H4. repeat rewrite Cmult_1_r in H4.
       injection H4. intuition.
       intuition. destruct H1. auto_wf. intuition.
       destruct H1.  auto_wf. 
       subst.
       assert(((/x0)* x0)%R .* L_reduced (x3 × (x3) †) x 
       = ((/x0)* x0)%R .* (x2 × (x2) †)).
       rewrite <-RtoC_mult. repeat rewrite <-Mscale_assoc.
       rewrite H3. reflexivity.
       rewrite Rinv_l in H4. 
       rewrite Mscale_1_l in H4.
       unfold L_reduced in H4.

       
       (*第一步*)
       assert(forall i : nat, i< (2 ^ (e - x)) ->
       (((@Mmult _ (2^(x-s) * 2^(e-x)) 1 (I (2 ^ (x - s)) ⊗ ⟨ i ∣_ (2^(e - x)))  x3) = Zero) \/ 
       (exists p, and (0<p<=1)%R ((I (2 ^ (x - s)) ⊗ ⟨ i ∣_ (2^(e - x)) × (x3 × (x3) †)
       × (I (2 ^ (x - s)) ⊗ ∣ i ⟩_ (2^(e - x)))) =
       p .* ( x2 × (x2) †))))).
       assert(forall i : nat, i< (2 ^ (e - x)) -> 
       ((@Mmult _ (2^(x-s) * 2^(e-x)) 1 (I (2 ^ (x - s)) ⊗ ⟨ i ∣_ (2^(e - x)))  x3) = Zero) \/ 
       ((@Mmult _ (2^(x-s) * 2^(e-x)) 1 (I (2 ^ (x - s)) ⊗ ⟨ i ∣_ (2^(e - x)))  x3) <> Zero)).
       intros. apply Classical_Prop.classic.
       intros. pose (H6 i  H7).
       destruct o.  left. assumption.
       right.
       apply (Mixed_pure_sum (fun i : nat =>
       I (2 ^ (x - s)) ⊗ ⟨ i ∣_ (2^(e - x)) × (x3 × (x3) †)
       × (I (2 ^ (x - s)) ⊗ ∣ i ⟩_ (2^(e - x)))) (2 ^ (e - x)) ).
       assumption.
       intros.

      
       
       assert( 2^(e-s)= 2^(x-s) * 2^(e-x)).
       type_sovle'. destruct H10.
       rewrite <-Mmult_assoc. 
       rewrite (Mmult_assoc _ ((x3) †) _ ).
       assert((I (2 ^ (x - s)) ⊗ ∣ i0 ⟩_ (2^(e - x)))=
       adjoint (I (2 ^ (x - s)) ⊗⟨ i0 ∣_ (2^(e - x)))).
       rewrite kron_adjoint. rewrite id_adjoint_eq.
       rewrite adjoint_involutive. reflexivity.
       rewrite H10.
       assert(2^(x-s) * 2^(e-x) =  2^(e-s)).
       type_sovle'. destruct H11.
       rewrite <- Mmult_adjoint.
       rewrite NZ_Mixed_State_aux_equiv'.
       assert(I (2 ^ (x - s)) ⊗ ⟨ i0 ∣_ (2^(e - x)) × x3 = Zero
       \/ I (2 ^ (x - s)) ⊗ ⟨ i0 ∣_ (2^(e - x)) × x3 <> Zero).
       apply Classical_Prop.classic. destruct H11.
       right. rewrite H11. rewrite Mmult_0_l. reflexivity.
       left. rewrite mul_1_r. 
       apply Vector_nz_Mix_State_aux. destruct H1.
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
       assert((I (2 ^ (x - s)) ⊗ ∣ i⟩_ (2^(e - x)))=
       adjoint (I (2 ^ (x - s)) ⊗⟨ i ∣_ (2^(e - x)))).
       rewrite kron_adjoint. rewrite id_adjoint_eq.
       rewrite adjoint_involutive. reflexivity.
       rewrite H9.
       assert(2^(x-s) * 2^(e-x) =  2^(e-s)).
       type_sovle'. destruct H10.
       rewrite <- Mmult_adjoint. rewrite Nat.mul_1_r.
       apply Vector_nz_Mix_State_aux. destruct H1. auto_wf.
       assumption.

       (* 第二步*)
       assert(forall i : nat,i< (2 ^ (e - x))-> 
       ((@Mmult _ (2^(x-s) * 2^(e-x)) 1 (I (2 ^ (x - s)) ⊗ ⟨ i ∣_ (2^(e - x)))  x3) = Zero) \/
       exists c : C, 
         (and (c<>C0)
          (@Mmult _ (2^(x-s) * 2^(e-x)) 1 (I (2 ^ (x - s)) ⊗ ⟨ i ∣_ (2^(e - x)))  x3
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
      remember ((I (2 ^ (x - s)) ⊗ ⟨ i ∣_ (2^(e - x)) × x3) ).
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
       remember (I (2 ^ (x - s)) ⊗ ⟨ i ∣_ (2^(e - x))).
       rewrite <-Mmult_assoc. 
       rewrite Mmult_assoc. 
        f_equal; lia. 
   
      
       assert(forall i, i < 2 ^ (e - x) ->  (@Mmult _ (2^(x-s) * 2^(e-x)) 1 (I (2 ^ (x - s)) ⊗ ⟨ i ∣_ (2^(e - x)))  x3)=
       big_sum
       (fun r : nat => x3 (r * 2 ^ (e - x) + i) 0 .* ∣ r ⟩_ (2^(x - s)))
       (2 ^ (x - s))).
       intros.

       rewrite (base_decom x3) at 1.
       assert( 2^(e-s)=2^(x-s) * 2^(e-x)).
       type_sovle'. destruct H9.
       rewrite Mmult_Msum_distr_l. 
       rewrite (big_sum_eq_bounded _ (
              (fun i0 : nat =>
       (x3 i0 0) .*
       ( (∣ i0/(2^(e-x))  ⟩_ (2^(x - s))) ⊗ 
        (⟨ i ∣_ (2^(e - x)) × ( ∣ i0 mod (2^(e-x))  ⟩_ (2^(e - x))))) )))
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
        rewrite H10. rewrite H11. rewrite base_inner_1. unfold c_to_Vector1.
        Msimpl.  reflexivity.
        assumption. assumption.
        intros. rewrite base_inner_0. unfold c_to_Vector1.
        Msimpl.  reflexivity. 
        assumption. assumption.
        apply mod_bound_pos.
        lia. apply pow_gt_0.  
       intros.
        rewrite Mscale_mult_dist_r.
        f_equal.
       assert(((x-s)+ (e-x) )=(e-s)).
       lia. destruct H10.
       rewrite pow_add_r.
       rewrite <-base_kron.
       remember (I (2 ^ (x - s)) ⊗ ⟨ i ∣_ (2^(e - x))).
       remember ((∣ x1 / 2 ^ (e - x) ⟩_ (2^(x - s))
       ⊗ ∣ x1 mod 2 ^ (e - x) ⟩_ (2^(e - x)))).
       assert((@Mmult (Init.Nat.mul (Nat.pow (S (S O)) (sub x s)) (S O))
       (mul (Nat.pow (S (S O)) (sub x s)) (Nat.pow (S (S O)) (sub e x))) 
       (S O) m m0) = m × m0).
      f_equal; type_sovle'. 
      rewrite H10.  rewrite Heqm. rewrite Heqm0.
       rewrite kron_mixed_product.
       rewrite Mmult_1_l; auto_wf. reflexivity.
       apply WF_base.
       apply div_lt_upper_bound.
       apply Nat.pow_nonzero.
       lia. 
       assert(2 ^ (e - x) * 2 ^ (x - s) = 2^(x - s + (e - x))).
       type_sovle'. rewrite H11. 
       assumption.   destruct H1. assumption.


       (*第三步*)
       assert(forall i : nat, (i<(2^(e-x)))->
       ((big_sum (fun r=> (x3 (r*(2^(e-x))+ i)%nat 0) .* (Base_vec (2^(x-s)) r) ) (2^(x-s))) = Zero) 
       \/
       exists c: C,
         (and (c<>C0)
          (big_sum (fun r=> (x3 (r*(2^(e-x))+ i)%nat 0) .* (Base_vec (2^(x-s)) r) ) (2^(x-s))= c .* x2))%type).
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
      (fun r : nat => x3 (r * 2 ^ (e - x) + i)%nat 0 .* ∣ r ⟩_ (2^(x - s)))
      (2 ^ (x - s))) <> Zero)).
      assert(big_sum
      (fun i : nat =>
       I (2 ^ (x - s)) ⊗ ⟨ i ∣_ (2^(e - x)) × (x3 × (x3) †)
       × (I (2 ^ (x - s)) ⊗ ∣ i ⟩_ (2^(e - x)))) (2 ^ (e - x))<> Zero).
       rewrite H4. rewrite Mscale_1_l.
       intro. assert(trace (x2 × (x2) †)=C0).
       rewrite H10. rewrite mul_1_r. apply Zero_trace.
        destruct H2. rewrite trace_mult in H11.
        rewrite H12 in H11. rewrite trace_I in H11.
        injection H11. lra. 
        apply big_sum_not_0 in H10.
        destruct H10. destruct H10.
        assert(2^(x-s) * 2^(e-x) = 2^(e-s)).
        type_sovle'. destruct H12.
        rewrite<- Mmult_assoc in H11.
        assert(I (2 ^ (x - s)) ⊗ ⟨ x1 ∣_ (2^(e - x)) × x3 <> Zero).
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
        .* ∣ r ⟩_ (2^(x - s))) (2 ^ (x - s))).
        remember (big_sum
        (fun r : nat =>
         x3 (r * 2 ^ (e - x) + x1) 0
         .* ∣ r ⟩_ (2^(x - s))) (2 ^ (x - s))).
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
        split. unfold scale. rewrite base1.
        rewrite Cmult_1_r. 
        reflexivity. reflexivity. 
        intros. unfold scale. rewrite base0.
        rewrite Cmult_0_r. reflexivity.
        assumption.
        exists j. split. assumption.
        split. unfold scale. rewrite base1.
        rewrite Cmult_1_r. 
        reflexivity. reflexivity. 
        intros. unfold scale. rewrite base0.
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
   destruct H10. apply (@big_sum_not_0 (2^(x-s)) ((fun r : nat => x3 (r * 2 ^ (e - x) + x1) 0 .* ∣ r ⟩_ (2^(x - s))))
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
       
       destruct H0. rewrite Reduced_plus in H0.
       destruct H0. destruct H0. destruct H5.
       destruct H5. destruct H5. rewrite H7 in *.
       assert( exists p, (and (0 < p <= 1)%R  (Reduced (p1 .* ρ1) s x .+ Reduced (p2 .* ρ2) s x =
       p .* (x2 × (x2) †)))).
       exists x0. intuition.
       assert(@NZ_Mixed_State_aux  (2^(x-s)) (Reduced (p1 .* ρ1) s x) ).
       apply nz_Mixed_State_aux_to_nz_Mix_State.
       apply WF_qstate_Reduced. intuition.
       unfold WF_qstate. split.
       apply nz_Mixed_State_scale.   assumption. lra.
     lia.
       assert(@NZ_Mixed_State_aux  (2^(x-s)) (Reduced (p2 .* ρ2) s x)).
       apply nz_Mixed_State_aux_to_nz_Mix_State.
       apply WF_qstate_Reduced. intuition.
       unfold WF_qstate. split. 
       apply nz_Mixed_State_scale. assumption. lra. lia. 
       pose H9. pose H10.
       apply (Mixed_pure' (Reduced (p1 .* ρ1) s x) (Reduced (p2 .* ρ2) s x) x2) in n; try assumption. 
       apply (Mixed_pure' (Reduced (p1 .* ρ1) s x) (Reduced (p2 .* ρ2) s x) x2) in n0; try assumption.
       destruct n. destruct H11.
       destruct n0. destruct H13.
       rewrite <- Reduced_scale in H12.
       rewrite <- Reduced_scale in H14. 
       assert(Reduced ρ1 s x = (/p1 * x3) .* (x2 × (x2) †)).
       rewrite <-Mscale_assoc. rewrite <-H12.
       rewrite Mscale_assoc. rewrite Cinv_l.
       rewrite Mscale_1_l. reflexivity.
       unfold not. intros. injection H15. intros. lra. 
       assert(@Par_Pure_State  (2^(x-s)) (Reduced ρ1 s x)).
       econstructor. exists ((x2 × (x2) †)). 
        assert(0 < (/ p1 * x3) <= 1)%R.
        assert(Cmod (@trace (2^(x-s)) (Reduced ρ1 s x)) =
        Cmod (trace (/ p1 * x3 .* (x2 × (x2) †))) ).
        rewrite H15. reflexivity.
        rewrite Reduced_trace in H16; try auto_wf; try lia. 
        rewrite trace_mult_dist in H16.
        rewrite Cmod_mult in H16. 
        rewrite trace_mult in H16.
        destruct H5. rewrite H17 in H16.
        rewrite trace_I in H16. 
        rewrite Cmod_1 in H16. rewrite Rmult_1_r in H16.
        rewrite <-RtoC_inv in H16.
        rewrite RtoC_mult in H16.
        rewrite Cmod_R in H16. 
        rewrite Rabs_right in H16.
        rewrite <-H16. apply nz_mixed_state_Cmod_1.
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
       assert(Reduced ρ2 s x = (/p2 * x4) .* (x2 × (x2) †)).
       rewrite <-Mscale_assoc. rewrite <-H14.
       rewrite Mscale_assoc. rewrite Cinv_l.
       rewrite Mscale_1_l. reflexivity.
       unfold not. intros. injection H17. intros. lra. 
       assert(@Par_Pure_State  (2^(x-s)) (Reduced ρ2 s x)).
       econstructor. exists ((x2 × (x2) †)). 
        assert(0 < (/ p2 * x4) <= 1)%R.
        assert(Cmod (@trace (2^(x-s)) (Reduced ρ2 s x)) =
        Cmod (trace (/ p2 * x4 .* (x2 × (x2) †))) ).
        rewrite H17. reflexivity.
        rewrite Reduced_trace in H18.
        rewrite trace_mult_dist in H18.
        rewrite Cmod_mult in H18. 
        rewrite trace_mult in H18.
        destruct H5. rewrite H19 in H18.
        rewrite trace_I in H18. 
        rewrite Cmod_1 in H18. rewrite Rmult_1_r in H18.
        rewrite <-RtoC_inv in H18.
        rewrite RtoC_mult in H18.
        rewrite Cmod_R in H18. 
        rewrite Rabs_right in H18.
        rewrite <-H18. apply nz_mixed_state_Cmod_1.
        assumption.  
        assert(0<(/ p2 * x4 ))%R.
        apply Rmult_gt_0_compat.
        apply Rinv_0_lt_compat. intuition.
        intuition. lra. lra. lia.
        apply WF_NZ_Mixed. assumption.
        split. apply H18.
         split. econstructor.
       split. apply H5. reflexivity.
       rewrite <-RtoC_mult. rewrite RtoC_inv. assumption.
       lra. 
       pose H16. pose H18.
      apply  IHNZ_Mixed_State1 in p.
      apply IHNZ_Mixed_State2 in p0.
      destruct p. destruct H19.
      destruct p0. destruct H20.
       destruct H19.
       destruct H20. rewrite H21. rewrite H22.
       pose H21. pose H22.
       apply Reduced_tensor_l in e0; try apply H19; try apply H20; try auto_wf.
       apply Reduced_tensor_l in e1; try apply H19; try apply H20; auto_wf.
       rewrite <-Reduced_L in e0; try auto_wf; try lia. 
       rewrite <-Reduced_L in e1; try auto_wf; try lia. 
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
       destruct H5. rewrite trace_mult in H24.
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
         destruct H5. rewrite trace_mult in H24.
         rewrite H25 in H24. rewrite trace_I in H24.
         injection H24. lra. 
         apply C0_fst_neq. 
         rewrite<- RtoC_inv. rewrite RtoC_mult.
         simpl.
         apply Rmult_integral_contrapositive_currified.
         assert((/ p2)%R > 0%R)%R. 
         apply Rinv_0_lt_compat. lra.
         lra. lra. lra. 
      apply NZ_Mixed_State_aux_is_Mixed_State_aux. assumption.
      apply NZ_Mixed_State_aux_is_Mixed_State_aux. assumption.
      apply NZ_Mixed_State_aux_is_Mixed_State_aux. assumption.
      apply NZ_Mixed_State_aux_is_Mixed_State_aux. assumption.
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
@NZ_Mixed_State (2^(e-s)) q->
@Par_Pure_State (2^(x-s)) (Reduced q s x)->
@trace (2^(e-s)) (q) .* q = @kron (2^(x-s)) (2^(x-s)) (2^(e-x))  (2^(e-x)) (Reduced q s x) 
(Reduced q x e).
Proof. intros q H H0 H1. apply (Odot_Sepear q H H0) in H1.
       destruct H1. destruct H1. 
       destruct H1. 
       pose H2. pose H2.
       apply Reduced_tensor_l in e0.
       rewrite Reduced_L. 
       rewrite e0. 
       apply Reduced_tensor_r in e1.
       rewrite Reduced_R.
       rewrite e1. 
       rewrite Mscale_kron_dist_l.
       rewrite Mscale_kron_dist_r.
       rewrite Mscale_assoc.
       rewrite H2. f_equal.
       
       assert(2^(x-s)*2^(e-x)= 2^(e-s))%nat.
       type_sovle'. destruct H3.
       rewrite Cmult_comm.
       apply trace_kron. apply Nat.pow_nonzero. lia. reflexivity.
       apply WF_NZ_Mixed. assumption.
       intuition. intuition.
       apply WF_NZ_Mixed. assumption.
       intuition.
       apply WF_NZ_Mixed. assumption.
       intuition. intuition.
       apply WF_NZ_Mixed. assumption.
Qed.

Lemma  nz_Mixed_State_aux_to01':forall {n} (ρ : Density n),
NZ_Mixed_State_aux ρ ->
NZ_Mixed_State (( / (trace ρ))%C .* ρ) .
Proof. intros.  
       assert(trace ρ= ((fst (trace ρ)), snd (trace ρ))).
    destruct (trace ρ). reflexivity.
    rewrite H0. 
    assert(/ (fst (trace ρ), snd (trace ρ)) 
    = (( / (Cmod (trace ρ )))%R, 0%R) ).
     rewrite Cmod_snd_0. rewrite nz_mixed_state_trace_real_aux.
     assert(((/ fst (trace ρ))%R, 0%R) = RtoC ((/ fst (trace ρ))%R)).
     reflexivity. rewrite H1.
     rewrite RtoC_inv. f_equal.
     assert((0 < fst (trace ρ))%R).
     apply nz_mixed_state_trace_gt0_aux.
     assumption. lra. 
     assumption.
     apply nz_mixed_state_trace_gt0_aux.
     assumption. apply nz_mixed_state_trace_real_aux.
     assumption. 
     rewrite H1. apply nz_Mixed_State_aux_to01.
     assumption.
Qed. 

     


Lemma WF_qstate_to01{ s e:nat}: forall (q: qstate s e),
WF_qstate q ->
@WF_qstate  s e (/@trace (2^(e-s)) q .* q).
Proof. intros. unfold WF_qstate in *.
      split. apply nz_Mixed_State_aux_to01'.
      apply nz_Mixed_State_aux_to_nz_Mix_State.
      intuition. intuition.
Qed.


Lemma Odot_Sepear''{ s x e:nat}: forall (q: qstate s e),
s<=x/\x<=e ->
@NZ_Mixed_State (2^(e-s)) q->
@Par_Pure_State (2^(x-s)) (Reduced q s x)->
exists (q1:qstate s x) (q2: qstate x e), 
and (@WF_qstate  s x q1 /\ @WF_qstate x e q2) 
(q = @kron (2^(x-s)) (2^(x-s)) (2^(e-x))  (2^(e-x)) q1 q2).
Proof. intros q H H0 H1. assert(@trace (2^(e-s)) (q) .* q = @kron (2^(x-s)) (2^(x-s)) (2^(e-x))  (2^(e-x)) (Reduced q s x) 
(Reduced q x e)).
apply Odot_Sepear'. assumption. assumption. assumption.
exists (/(@trace (2^(e-s)) q) .* (Reduced q s x)).
exists (Reduced q x e).
split. split. rewrite <-(Reduced_trace _ _ _ s x).
apply WF_qstate_to01. 
apply WF_qstate_Reduced.  intuition.
unfold WF_qstate. split.  apply H0.
intuition. intuition. 
apply WF_NZ_Mixed. assumption.
apply (WF_qstate_Reduced s e x e q).
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
apply nz_mixed_state_trace_gt0.
assumption. lra.
Qed.

Lemma big_sum_par_r: forall m n j  a b(f: nat-> Matrix a b),
j<m ->
(forall i :nat, (i / n) < m -> j <> (i / n) -> f i = Zero)->
big_sum f (m * n) = big_sum (fun i=> f (j * n +i)) n .
Proof. induction m; intros. simpl. lia. 
       simpl. rewrite Nat.add_comm. rewrite big_sum_sum'.
       assert(j=m\/ j<>m).
       apply Classical_Prop.classic. 
       destruct H1. subst. 
       assert(big_sum f (m * n)=Zero).
       apply (@big_sum_0_bounded (Matrix a b)).
       intros. apply H0. 
       apply div_lt_upper_bound. lia. rewrite Nat.mul_comm.
       lia. intro. rewrite H2 in H1.
       assert(x / n * n <= x). rewrite Nat.mul_comm.
       apply Nat.mul_div_le. lia. lia. rewrite H1.
       rewrite Mplus_0_l. reflexivity.
       rewrite (IHm _ j a b). 
       assert(big_sum (fun x : nat => f (m * n + x)) n=Zero).
       apply (@big_sum_0_bounded (Matrix a b)). 
       intros. apply H0. 
       rewrite Nat.div_add_l. 
       apply Nat.div_small in H2. rewrite H2. rewrite Nat.add_0_r.
       lia. lia.      rewrite Nat.div_add_l.  
       apply Nat.div_small in H2. rewrite H2. rewrite Nat.add_0_r. lia.
       lia. rewrite H2. rewrite Mplus_0_r. reflexivity. lia. 
       intros. apply H0. lia. lia.     
Qed.

Lemma Odot_Sepear_r{ s x e:nat}: forall (q: qstate s e),
s<=x/\x<=e ->
@NZ_Mixed_State (2^(e-s)) q->
@Par_Pure_State (2^(e-x)) (Reduced q x e)->
exists (q1:qstate s x) (q2: qstate x e), 
and (@WF_Matrix  (2^(x-s))  (2^(x-s)) q1 /\ @WF_Matrix (2^(e-x))  (2^(e-x)) q2) 
(q = @kron (2^(x-s)) (2^(x-s)) (2^(e-x))  (2^(e-x)) q1 q2).
Proof.

intros q Hs. intros H H0. induction H.   
     unfold Par_Pure_State in *.
       destruct H0. destruct H0.
       destruct H0. destruct H2.
       destruct H2. destruct H2.
       rewrite H4 in *. 
       rewrite Reduced_R in *.
       induction H. destruct H1.
       destruct H1. subst.
       rewrite <-R_reduced_scale in *.
       assert(p=x0).
       assert(@trace (2^(e-x)) (p .* R_reduced (x3 × (x3) †) x)=
       trace (x0 .* (x2 × (x2) †))).
       rewrite H3. reflexivity.
       repeat rewrite trace_mult_dist in H4.
       rewrite <-Reduced_R in H4.
       rewrite Reduced_trace in H4.
        rewrite trace_mult in H4. 
        rewrite (trace_mult _ _ x2) in H4. 
       destruct H1. rewrite H6 in H4.
       destruct H2. rewrite H7 in H4.
       rewrite trace_I in H4. repeat rewrite Cmult_1_r in H4.
       injection H4. intuition.
       intuition. destruct H1. auto_wf. intuition.
       destruct H1.  auto_wf. 
       subst.
       assert(((/x0)* x0)%R .* R_reduced (x3 × (x3) †) x 
       = ((/x0)* x0)%R .* (x2 × (x2) †)).
       rewrite <-RtoC_mult. repeat rewrite <-Mscale_assoc.
       rewrite H3. reflexivity.
       rewrite Rinv_l in H4. 
       rewrite Mscale_1_l in H4.
       unfold L_reduced in H4.

       
       (*第一步*)
       assert(forall i : nat, i< (2 ^ (x - s)) ->
       (((@Mmult _ (2^(x-s) * 2^(e-x)) 1 ((⟨ i ∣_ (2^(x - s))) ⊗  I (2 ^ (e - x)))  x3) = Zero) \/ 
       (exists p, and (0<p<=1)%R ((( ⟨ i ∣_ (2^(x - s))) ⊗  I (2 ^ (e - x)) × (x3 × (x3) †)
       × (∣ i ⟩_ (2^(x - s)) ⊗ I (2 ^ (e - x)))) =
       p .* ( x2 × (x2) †))))).
       assert(forall i : nat, i< (2 ^ (x - s)) -> 
       ((@Mmult _ (2^(x-s) * 2^(e-x)) 1 (( ⟨ i ∣_ (2^(x - s))) ⊗  I (2 ^ (e - x)))  x3) = Zero) \/ 
       ((@Mmult _ (2^(x-s) * 2^(e-x)) 1 (( ⟨ i ∣_ (2^(x - s))) ⊗  I (2 ^ (e - x)))  x3) <> Zero)).
       intros. apply Classical_Prop.classic.
       intros. pose (H6 i  H7).
       destruct o.  left. assumption.
       right.
       apply (Mixed_pure_sum (fun i : nat =>
          (⟨ i ∣_ (2^(x - s))) ⊗  I (2 ^ (e - x)) × (x3 × (x3) †)
       ×  (∣ i ⟩_ (2^(x - s)) ⊗ I (2 ^ (e - x)))) (2 ^ (x - s)) ).
        assumption.
       intros.

      
       
       assert( 2^(e-s)= 2^(x-s) * 2^(e-x)).
       type_sovle'. destruct H10.
       rewrite <-Mmult_assoc. 
       rewrite (Mmult_assoc _ ((x3) †) _ ).
       assert(∣ i0 ⟩_ (2^(x - s)) ⊗ I (2 ^ (e - x))=
       adjoint (⟨ i0 ∣_ (2^(x - s)) ⊗ I (2 ^ (e - x)))).
       rewrite kron_adjoint. rewrite id_adjoint_eq.
       rewrite adjoint_involutive. reflexivity.
       rewrite H10.
       assert(2^(x-s) * 2^(e-x) =  2^(e-s)).
       type_sovle'. destruct H11.
       rewrite <- Mmult_adjoint.
       rewrite NZ_Mixed_State_aux_equiv'.
       assert((⟨ i0 ∣_ (2^(x - s)) ⊗ I (2 ^ (e - x))) × x3 = Zero
       \/ (⟨ i0 ∣_ (2^(x - s)) ⊗ I (2 ^ (e - x))) × x3 <> Zero).
       apply Classical_Prop.classic. destruct H11.
       right. rewrite H11. rewrite Mmult_0_l. reflexivity.
       left. rewrite Nat.mul_1_l. 
       apply Vector_nz_Mix_State_aux. destruct H1.
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
       assert(∣ i ⟩_ (2^(x - s)) ⊗ I (2 ^ (e - x))=
       adjoint (⟨ i ∣_ (2^(x - s)) ⊗ I (2 ^ (e - x)))).
       rewrite kron_adjoint. rewrite id_adjoint_eq.
       rewrite adjoint_involutive. reflexivity.
       rewrite H9.
       assert(2^(x-s) * 2^(e-x) =  2^(e-s)).
       type_sovle'. destruct H10.
       rewrite <- Mmult_adjoint. rewrite Nat.mul_1_l. 
       apply Vector_nz_Mix_State_aux. destruct H1. auto_wf.
       assumption.

       (* 第二步*)
       assert(forall i : nat,i< (2 ^ (x - s))-> 
       ((@Mmult _ (2^(x-s) * 2^(e-x)) 1 (⟨ i ∣_ (2^(x - s)) ⊗ I (2 ^ (e - x)))  x3) = Zero) \/
       exists c : C, 
         (and (c<>C0)
          (@Mmult _ (2^(x-s) * 2^(e-x)) 1 (⟨ i ∣_ (2^(x - s)) ⊗ I (2 ^ (e - x)))  x3
         = c .* x2))).
       intros.
       pose (H6 i H7). 
       destruct o. left. apply H8. 
       right.  apply (outer_product_eq' (2 ^ (e - x))).
       destruct H1. 
       assert( 2^(e-s)= 2^(x-s) * 2^(e-x)).
       type_sovle'. destruct H10.
      rewrite mul_1_l.
       auto_wf. destruct H2.  
       auto_wf.  
       destruct H8.  
       exists x1. 
       split. intro. injection H9. lra.
       unfold outer_product.
      remember (((⟨ i ∣_ (2^(x - s)) ⊗ I (2 ^ (e - x))) × x3) ).
      assert ((@adjoint (Nat.pow (S (S O)) (sub e x)) (S O) m)=(m) †).
      rewrite Heqm. f_equal; lia. rewrite H9. 
      rewrite Heqm.  
       rewrite Mmult_adjoint.
       rewrite kron_adjoint.
       rewrite id_adjoint_eq.
       rewrite adjoint_involutive.
       destruct H8. rewrite<-H10. clear H9.
       assert(2^(x-s) * 2^(e-x) = 2^(e-s)).
       type_sovle'. destruct H9.
       remember ((⟨ i ∣_ (2^(x - s)) ⊗ I (2 ^ (e - x)))).
       rewrite <-Mmult_assoc. 
       rewrite Mmult_assoc. 
        f_equal; lia.   
   
      (*第三步*)
       assert(forall i, i < 2 ^ (x - s) ->  
       (@Mmult _ (2^(x-s) * 2^(e-x)) 1 (⟨ i ∣_ (2^(x - s)) ⊗ I (2 ^ (e - x)))  x3)=
       big_sum
       (fun r : nat => x3 (i * 2 ^ (e - x) + r) 0 .* ∣ r ⟩_ (2^(e - x)))
       (2 ^ (e - x))).
       intros.

       rewrite (base_decom x3) at 1.
       assert( 2^(e-s)=2^(x-s) * 2^(e-x)).
       type_sovle'. destruct H9.
       rewrite Mmult_Msum_distr_l. 
       rewrite (big_sum_eq_bounded _ (
              (fun i0 : nat =>
       (x3 i0 0) .* ( ⟨ i ∣_ (2^(x - s)) × (∣ i0/(2^(e-x))  ⟩_ (2^(x - s))) ⊗ 
        (( ∣ i0 mod (2^(e-x))  ⟩_ (2^(e - x))))) )))
        at 1.
        assert( 2^(x-s) * 2^(e-x)= 2^(e-s)).
        type_sovle'. destruct H9. 
        rewrite (big_sum_par_r  (2 ^ (x - s)) (2 ^ (e - x)) i).
        apply big_sum_eq_bounded.
        intros. f_equal.
        lia. 
        assert((i * 2 ^ (e - x) + x1) / 2 ^ (e - x) = i).
        rewrite add_comm.
        rewrite div_add. 
         rewrite div_small.
         rewrite add_0_l. reflexivity. 
         assumption. apply Nat.pow_nonzero.
         lia. 
        assert((i * 2 ^ (e - x) + x1) mod 2 ^ (e - x)= x1).
        rewrite add_comm.
        rewrite mod_add. 
        rewrite mod_small.
        reflexivity.
        assumption. 
        apply Nat.pow_nonzero.
        lia.
        rewrite H10. rewrite H11. rewrite base_inner_1. unfold c_to_Vector1.
        Msimpl.  reflexivity.
        assumption. assumption.
        intros. rewrite base_inner_0. unfold c_to_Vector1.
        Msimpl.  reflexivity. 
        assumption. assumption.  assumption.
       intros.
        rewrite Mscale_mult_dist_r.
        f_equal.
       assert(((x-s)+ (e-x) )=(e-s)).
       lia. destruct H10. rewrite pow_add_r.
       rewrite <-base_kron.
       remember (⟨ i ∣_ (2^(x - s)) ⊗ I (2 ^ (e - x))).
       remember ((∣ x1 / 2 ^ (e - x) ⟩_ (2^(x - s))
       ⊗ ∣ x1 mod 2 ^ (e - x) ⟩_ (2^(e - x)))). 
       assert( (@Mmult (Init.Nat.mul (S O) (Nat.pow (S (S O)) (sub e x)))
       (mul (Nat.pow (S (S O)) (sub x s))
          (Nat.pow (S (S O)) (sub e x))) (S O) m m0) = m × m0).
      f_equal; type_sovle'. 
      rewrite H10.  rewrite Heqm. rewrite Heqm0.
       rewrite kron_mixed_product.
       rewrite Mmult_1_l; auto_wf. reflexivity.
       apply WF_base. 
       apply mod_bound_pos. lia. apply pow_gt_0.   
        destruct H1. assumption. 


       (*第四步*)
       assert(forall i : nat, (i<(2^(x-s)))->
       ((big_sum (fun r=> (x3 (i*(2^(e-x))+ r)%nat 0) .* (Base_vec (2^(e-x)) r) ) (2^(e-x))) = Zero) 
       \/
       exists c: C,
         (and (c<>C0)
          (big_sum (fun r=> (x3 (i*(2^(e-x))+ r)%nat 0) .* (Base_vec (2^(e-x)) r)  ) (2^(e-x))= c .* x2))%type).
       intros. 
       pose (H7 i H9).
       destruct o. left. rewrite <-H8. assumption. assumption. 
       right.
       destruct H10. destruct H10. 
       exists x1.
       split. intuition. rewrite<-H8.
       assumption. assumption. 
       
       (* 第五步*)
      assert(exists i, and (i< 2 ^ (x - s))  ((big_sum
      (fun r : nat => x3 (i * 2 ^ (e - x) + r)%nat 0 .* ∣ r ⟩_ (2^(e - x)))
      (2 ^ (e - x))) <> Zero)).
      assert(big_sum
      (fun i : nat =>
      (⟨ i ∣_ (2^(x - s)) ⊗ I (2 ^ (e - x))) × (x3 × (x3) †)
       × (∣ i ⟩_ (2^(x - s)) ⊗ I (2 ^ (e - x)))) (2 ^ (x - s))<> Zero).
       unfold R_reduced in H4.
       rewrite H4. rewrite Mscale_1_l.
       intro. assert(trace (x2 × (x2) †)=C0).
       rewrite H10. rewrite mul_1_l. apply Zero_trace.
        destruct H2. rewrite trace_mult in H11.
        rewrite H12 in H11. rewrite trace_I in H11.
        injection H11. lra. 
        apply big_sum_not_0 in H10.
        destruct H10. destruct H10.
        assert(2^(x-s) * 2^(e-x) = 2^(e-s)).
        type_sovle'. destruct H12.
        rewrite<- Mmult_assoc in H11.
        assert(⟨ x1 ∣_ (2^(x - s)) ⊗ I (2 ^ (e - x)) × x3 <> Zero).
        intro. rewrite H12 in H11.
        repeat rewrite Mmult_0_l in H11.
        destruct H11. reflexivity.
        exists x1. split. assumption.
        rewrite <-H8. assumption.
        assumption.
        destruct H10.  
       assert(forall j, (j<(2^(x-s)))-> (exists lamda, forall k, 
       k < 2 ^ (e - x) ->
       (x3 (j * (2^(e-x)) + k) 0) = Cmult lamda (x3 (x1 * (2^(e-x))+ k) 0))).
       (* 这里应该选择哪个 不是全0 的i*)
       intros. destruct H10.
       pose (H9 j H11). 
       pose (H9 x1 H10 ). 
       destruct o. exists 0%R.
       intros. 
       rewrite Cmult_0_l. 
       apply (@big_sum_Vec_0 x e ( fun i:nat=> x3 i 0) (fun r:nat => j * 2 ^ (e - x) + r)).
       assumption. assumption.
       destruct o0. 
       rewrite H14 in H12. destruct H12.
       reflexivity.   
        destruct H13.
      destruct H14.
       exists ( x4/  x5)%C. intros. 
       remember (big_sum
       (fun r : nat =>
        x3 (j * 2 ^ (e - x) + r) 0
        .* ∣ r ⟩_ (2^(e - x))) (2 ^ (e - x))).
        remember (big_sum
        (fun r : nat =>
         x3 (x1 * 2 ^ (e - x) + r) 0
         .* ∣ r ⟩_ (2^(e - x))) (2 ^ (e - x))).
       assert(  m k 0 = (( x4 /  x5)%C * m0 k 0)%C).
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
        rewrite (big_sum_unique  (x3 (j* 2 ^ (e - x) + k) 0)) in H16.
        rewrite (big_sum_unique  (x3 (x1* 2 ^ (e - x) + k) 0)) in H16.
        assumption. 
        exists k. split. assumption. 
        split. unfold scale. rewrite base1.
        rewrite Cmult_1_r. 
        reflexivity. reflexivity. 
        intros. unfold scale. rewrite base0.
        rewrite Cmult_0_r. reflexivity.
        assumption.
        exists k. split. assumption.
        split. unfold scale. rewrite base1.
        rewrite Cmult_1_r. 
        reflexivity. reflexivity. 
        intros. unfold scale. rewrite base0.
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
   assert( exists r, and (r < (2 ^ (e - x)) ) (x3 (x1 * 2 ^ (e - x) + r) 0 <> 0%R)).
   destruct H10. apply (@big_sum_not_0 (2^(e-x)) ((fun r : nat => x3 (x1 * 2 ^ (e - x) + r) 0 .* ∣ r ⟩_ (2^(x - s))))
   (2^(e-x))) in H12. destruct H12.
   exists x4. split. intuition. 
   destruct H12. intro. rewrite H14 in H13.
   rewrite Mscale_0_l in H13. destruct H13.
   reflexivity.
    destruct H12.
   
       exists (fun i=> Cdiv (x3 (i * 2 ^ (e - x) + x4) 0 ) (x3 (x1 * 2 ^ (e - x) + x4) 0)).
       exists (fun i=> (x3 (x1 * 2 ^ (e - x) + i ) 0)). 
       intros. 
       remember (z mod 2 ^ (e - x)).
       assert( exists j, z = j * 2 ^ (e - x) + n).
       exists (z / (2^(e-x))).
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
       assert(x5 < 2 ^ (x - s)). 
       rewrite <-H15. 
       apply Nat.div_lt_upper_bound. 
       apply Nat.pow_nonzero. lia.
       rewrite <-Nat.pow_add_r. rewrite Nat.add_comm. assumption.
      pose (H11 x5 H16).
      destruct e0.
      rewrite H17. rewrite H17. 
      rewrite Cdiv_unfold.   
      rewrite <-(Cmult_assoc x6). 
      rewrite Cinv_r. 
      rewrite Cmult_1_r.  reflexivity.
      intuition. intuition.
       rewrite H14 in H15.
       rewrite add_comm in H15.
       rewrite div_add in H15.
       assert(n / 2 ^ (e - x) + x5 - x5 =  x5 -x5).
       rewrite H15. reflexivity.
       rewrite Nat.sub_diag in H18.
        repeat rewrite add_sub in H18.
        apply div_small_iff. apply Nat.pow_nonzero.
        lia. assumption. apply Nat.pow_nonzero. lia.  
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
       
       destruct H0. rewrite Reduced_plus in H0.
       destruct H0. destruct H0. destruct H5.
       destruct H5. destruct H5. rewrite H7 in *.
       assert( exists p, (and (0 < p <= 1)%R  (Reduced (p1 .* ρ1) x e .+ Reduced (p2 .* ρ2) x e =
       p .* (x2 × (x2) †)))).
       exists x0. intuition.
       assert(@NZ_Mixed_State_aux  (2^(e-x)) (Reduced (p1 .* ρ1) x e) ).
       apply nz_Mixed_State_aux_to_nz_Mix_State.
       apply WF_qstate_Reduced. intuition.
       unfold WF_qstate. split.
       apply nz_Mixed_State_scale. assumption.
       lra. lia. 
       assert(@NZ_Mixed_State_aux  (2^(e-x)) (Reduced (p2 .* ρ2) x e)).
       apply nz_Mixed_State_aux_to_nz_Mix_State.
       apply WF_qstate_Reduced. intuition.
       unfold WF_qstate. split. 
       apply nz_Mixed_State_scale. assumption. lra. lia.
       pose H9. pose H10.
       apply (Mixed_pure' (Reduced (p1 .* ρ1) x e) (Reduced (p2 .* ρ2) x  e) x2) in n; try assumption. 
       apply (Mixed_pure' (Reduced (p1 .* ρ1) x e) (Reduced (p2 .* ρ2) x e) x2) in n0; try assumption.
       destruct n. destruct H11.
       destruct n0. destruct H13.
       rewrite <- Reduced_scale in H12.
       rewrite <- Reduced_scale in H14. 
       assert(Reduced ρ1 x e = (/p1 * x3) .* (x2 × (x2) †)).
       rewrite <-Mscale_assoc. rewrite <-H12.
       rewrite Mscale_assoc. rewrite Cinv_l.
       rewrite Mscale_1_l. reflexivity.
       unfold not. intros. injection H15. intros. lra. 
       assert(@Par_Pure_State  (2^(e-x)) (Reduced ρ1 x e)).
       econstructor. exists ((x2 × (x2) †)). 
        assert(0 < (/ p1 * x3) <= 1)%R.
        assert(Cmod (@trace (2^(e-x)) (Reduced ρ1 x e)) =
        Cmod (trace (/ p1 * x3 .* (x2 × (x2) †))) ).
        rewrite H15. reflexivity.
        rewrite Reduced_trace in H16; try auto_wf; try lia. 
        rewrite trace_mult_dist in H16.
        rewrite Cmod_mult in H16. 
        rewrite trace_mult in H16.
        destruct H5. rewrite H17 in H16.
        rewrite trace_I in H16. 
        rewrite Cmod_1 in H16. rewrite Rmult_1_r in H16.
        rewrite <-RtoC_inv in H16.
        rewrite RtoC_mult in H16.
        rewrite Cmod_R in H16. 
        rewrite Rabs_right in H16.
        rewrite <-H16. apply nz_mixed_state_Cmod_1.
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
       assert(Reduced ρ2 x e = (/p2 * x4) .* (x2 × (x2) †)).
       rewrite <-Mscale_assoc. rewrite <-H14.
       rewrite Mscale_assoc. rewrite Cinv_l.
       rewrite Mscale_1_l. reflexivity.
       unfold not. intros. injection H17. intros. lra. 
       assert(@Par_Pure_State  (2^(e-x)) (Reduced ρ2 x e)).
       econstructor. exists ((x2 × (x2) †)). 
        assert(0 < (/ p2 * x4) <= 1)%R.
        assert(Cmod (@trace (2^(e-x)) (Reduced ρ2 x e)) =
        Cmod (trace (/ p2 * x4 .* (x2 × (x2) †))) ).
        rewrite H17. reflexivity.
        rewrite Reduced_trace in H18.
        rewrite trace_mult_dist in H18.
        rewrite Cmod_mult in H18. 
        rewrite trace_mult in H18.
        destruct H5. rewrite H19 in H18.
        rewrite trace_I in H18. 
        rewrite Cmod_1 in H18. rewrite Rmult_1_r in H18.
        rewrite <-RtoC_inv in H18.
        rewrite RtoC_mult in H18.
        rewrite Cmod_R in H18. 
        rewrite Rabs_right in H18.
        rewrite <-H18. apply nz_mixed_state_Cmod_1.
        assumption.  
        assert(0<(/ p2 * x4 ))%R.
        apply Rmult_gt_0_compat.
        apply Rinv_0_lt_compat. intuition.
        intuition. lra. lra. lia.
        apply WF_NZ_Mixed. assumption.
        split. apply H18.
         split. econstructor.
       split. apply H5. reflexivity.
       rewrite <-RtoC_mult. rewrite RtoC_inv. assumption.
       lra. 
       pose H16. pose H18.
      apply  IHNZ_Mixed_State1 in p.
      apply IHNZ_Mixed_State2 in p0.
      destruct p. destruct H19.
      destruct p0. destruct H20.
       destruct H19.
       destruct H20. rewrite H21. rewrite H22.
       pose H21. pose H22.
       apply Reduced_tensor_r in e0; try apply H19; try apply H20; try auto_wf.
       apply Reduced_tensor_r in e1; try apply H19; try apply H20; auto_wf.
       rewrite <-Reduced_R in e0; try auto_wf; try lia. 
       rewrite <-Reduced_R in e1; try auto_wf; try lia. 
       rewrite H15 in e0.
       rewrite H17 in e1.
     
      
       exists ((p1 * /@trace (2^(x-s)) x5 * /p1 * x3) .* x5 .+ 
       (p2 * /@trace (2^(x-s)) x7 * /p2 *  x4) .* x7).
       exists ( (x2 × (x2) †)).
       split. split.  
       apply WF_plus; auto_wf;
       apply WF_scale; intuition. 
       destruct H5. auto_wf. 
       rewrite kron_plus_distr_r.
       repeat rewrite Mscale_kron_dist_l.
       repeat rewrite <-Mscale_kron_dist_r.
       f_equal; type_sovle'.
       rewrite <-Mscale_assoc.
       rewrite <-Mscale_assoc.
       rewrite (Mscale_assoc _ _  (/p1) x3).
       rewrite e0.  rewrite  Mscale_assoc.
       rewrite <-Cmult_assoc.
       rewrite Cinv_l. rewrite Cmult_1_r.
       rewrite Mscale_kron_dist_r. reflexivity.
       intro. rewrite H23 in e0. rewrite Mscale_0_l in e0.
       apply (scale_Zero  (/ p1 * x3)  (x2 × (x2) †) ) in e0.
       assert(trace ( x2 × (x2) † )  =C0).
       rewrite e0. rewrite Zero_trace. reflexivity.
       destruct H5. rewrite trace_mult in H24.
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
       rewrite e1.  repeat rewrite Mscale_kron_dist_r.
       rewrite Mscale_assoc. 
       rewrite <-Cmult_assoc.
        rewrite Cinv_l. rewrite Cmult_1_r.
         reflexivity.
         intro. rewrite H23 in e1. rewrite Mscale_0_l in e1.
         apply (scale_Zero  (/ p2 * x4) ((x2)  × (x2) †) ) in e1.
         assert(trace ( (x2 × (x2) †) ) =C0).
         rewrite e1. rewrite Zero_trace. reflexivity.
         destruct H5. rewrite trace_mult in H24.
         rewrite H25 in H24. rewrite trace_I in H24.
         injection H24. lra. 
         apply C0_fst_neq. 
         rewrite<- RtoC_inv. rewrite RtoC_mult.
         simpl.
         apply Rmult_integral_contrapositive_currified.
         assert((/ p2)%R > 0%R)%R. 
         apply Rinv_0_lt_compat. lra.
         lra. lra. lra.
         apply NZ_Mixed_State_aux_is_Mixed_State_aux. assumption.
         apply NZ_Mixed_State_aux_is_Mixed_State_aux. assumption.
         apply NZ_Mixed_State_aux_is_Mixed_State_aux. assumption.
         apply NZ_Mixed_State_aux_is_Mixed_State_aux. assumption.
Qed.

Lemma Odot_Sepear'_r{ s x e:nat}: forall (q: qstate s e),
s<=x/\x<=e ->
@NZ_Mixed_State (2^(e-s)) q->
@Par_Pure_State (2^(e-x)) (Reduced q x e)->
@trace (2^(e-s)) (q) .* q = @kron (2^(x-s)) (2^(x-s)) (2^(e-x))  (2^(e-x)) (Reduced q s x) 
(Reduced q x e).
Proof. intros q H H0 H1. apply (Odot_Sepear_r q H H0) in H1.
       destruct H1. destruct H1. 
       destruct H1. 
       pose H2. pose H2.
       apply Reduced_tensor_r in e0.
       rewrite Reduced_R. 
       rewrite e0. 
       apply Reduced_tensor_l in e1.
       rewrite Reduced_L.
       rewrite e1. 
       rewrite Mscale_kron_dist_r.
       rewrite Mscale_kron_dist_l.
       rewrite Mscale_assoc.
       rewrite H2. f_equal.
       
       assert(2^(x-s)*2^(e-x)= 2^(e-s))%nat.
       type_sovle'. destruct H3.
       apply trace_kron. apply Nat.pow_nonzero. lia. lia. 
       apply WF_NZ_Mixed. assumption.
       intuition. intuition.
       apply WF_NZ_Mixed. assumption.
       intuition.
       apply WF_NZ_Mixed. assumption.
       intuition. intuition.
       apply WF_NZ_Mixed. assumption.
Qed.

Lemma Odot_Sepear'''{ s x e:nat}: forall (q: qstate s e),
s<=x/\x<=e ->
@NZ_Mixed_State (2^(e-s)) q->
@Par_Pure_State (2^(e-x)) (Reduced q x e)->
exists (q1:qstate s x) (q2: qstate x e), 
and (@WF_qstate  s x q1 /\ @WF_qstate x e q2) 
(q = @kron (2^(x-s)) (2^(x-s)) (2^(e-x))  (2^(e-x)) q1 q2).
Proof.  
intros q H H0 H1.
 assert(@trace (2^(e-s)) (q) .* q = @kron (2^(x-s)) (2^(x-s)) (2^(e-x))  (2^(e-x)) (Reduced q s x) 
(Reduced q x e)).
apply Odot_Sepear'_r. assumption. assumption. assumption.
exists (/(@trace (2^(e-s)) q) .* (Reduced q s x)).
exists (Reduced q x e).
split. split. rewrite <-(Reduced_trace _ _ _ s x).
apply WF_qstate_to01. 
apply WF_qstate_Reduced.  intuition.
unfold WF_qstate. split.  apply H0.
intuition. intuition. 
apply WF_NZ_Mixed. assumption.
apply (WF_qstate_Reduced s e x e q).
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
apply nz_mixed_state_trace_gt0.
assumption. lra.
Qed.


Lemma Par_Pure_State_wedge{ s e: nat}:forall (q:qstate s e) s' x' e',
s<=s'/\ s'<=x'/\ x'<=e' /\ e'<= e ->
WF_qstate q->
@Par_Pure_State (2^(x'-s')) (Reduced q s' x')->
@Par_Pure_State (2^(e'-x')) (Reduced q x' e')->
@Par_Pure_State (2^(e'-s')) (Reduced q s' e').
Proof. intros.
assert((Reduced q s' x') = 
Reduced (Reduced q s' e') s' x').
rewrite  Reduced_assoc.
reflexivity. intuition.
rewrite H3 in H1. 
assert((Reduced q x' e') =
Reduced (Reduced q s' e') x' e'). 
rewrite Reduced_assoc.
reflexivity. intuition.
rewrite H4 in H2. 
remember ((Reduced q s' e')).
assert(@trace (2^(e'-s')) (q0) .* q0 =@kron (2^(x'-s')) (2^(x'-s')) 
(2^(e'-x'))  (2^(e'-x')) (Reduced q0 s' x') (Reduced q0 x' e') ).
apply Odot_Sepear'. intuition.
rewrite Heqq0.
apply WF_qstate_Reduced. intuition.
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
apply nz_mixed_state_trace_gt0.
rewrite Heqq0. apply WF_qstate_Reduced.
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
rewrite <-(Reduced_trace _ _ _  s' x').
rewrite H7. 
rewrite trace_mult_dist.
assert(trace (x1 × (x1) †)= C1).
rewrite trace_mult. 
destruct H6. rewrite H13.
rewrite trace_I.
reflexivity. rewrite H13.
rewrite Cmult_1_r.
rewrite <-RtoC_inv.
rewrite RtoC_mult.
rewrite Rinv_l. rewrite Cmult_1_l. reflexivity.
lra. lra.  intuition.
rewrite Heqq0. unfold Reduced.
apply WF_R_reduced. 
intuition. apply WF_L_reduced.
intuition. apply WF_NZ_Mixed. apply H0.
Qed.

Lemma Odot_Sepear''''{ s x e:nat}: forall (q: qstate s e),
s<=x/\x<=e ->
@NZ_Mixed_State (2^(e-s)) q->
(@Par_Pure_State (2^(x-s)) (Reduced q s x)\/ 
@Par_Pure_State (2^(e-x)) (Reduced q x e)) ->
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
(@Par_Pure_State (2^(x-s)) (Reduced q s x)\/
@Par_Pure_State (2^(e-x)) (Reduced q x e)) ->
/(@trace (2^(e-s)) q) .* q =
 @kron (2^(x-s)) (2^(x-s)) (2^(e-x)) (2^(e-x)) 
(/(@trace (2^(x-s)) ((Reduced q s x))) .* (Reduced q s x))
(/(@trace (2^(e-x)) ((Reduced q x e))) .* (Reduced q x e)).
Proof. intros. destruct H0.
apply (@Odot_Sepear'''' s x e) in H1; try lia; try assumption.  
destruct H1. destruct H1. 
destruct H1. destruct H1.
destruct H1. destruct H4. 
assert(Reduced q s x=(@trace (2^(e-x)) x1) .* x0).
rewrite H3. rewrite Reduced_L; try lia; try auto_wf.
rewrite (Reduced_tensor_l _ x0 x1); try lia; try auto_wf; try reflexivity.
assert(Reduced q x e=(@trace (2^(x-s)) x0) .* x1).
rewrite H3. rewrite Reduced_R; try lia; try auto_wf.
rewrite (Reduced_tensor_r _ x0 x1); try lia; try auto_wf; try reflexivity.
rewrite H7. rewrite H8. 
repeat rewrite trace_mult_dist. rewrite H3.
assert(2^(x-s) * (2^(e-x))= 2^(e-s)). type_sovle'.
destruct H9.  repeat rewrite trace_kron.
repeat rewrite Mscale_assoc. 
rewrite (Cmult_comm (@trace (2^(e-x)) x1)). 
 repeat rewrite Cinv_mult_distr; try apply C0_fst_neq;
 try apply Rgt_neq_0; try apply nz_mixed_state_trace_gt0; try assumption.
 rewrite <- Cmult_assoc. rewrite Cinv_l; 
 try apply C0_fst_neq;
 try apply Rgt_neq_0; try apply nz_mixed_state_trace_gt0; try assumption.
 Csimpl. rewrite (Cmult_comm (/(@trace (2^(x-s)) x0))).
 rewrite <- Cmult_assoc. rewrite Cinv_l; 
 try apply C0_fst_neq;
 try apply Rgt_neq_0; try apply nz_mixed_state_trace_gt0; try assumption.
 Csimpl. 
 repeat rewrite  Mscale_kron_dist_r.
 repeat rewrite  Mscale_kron_dist_l.
 rewrite Mscale_assoc. reflexivity. apply Nat.pow_nonzero. 
  lia.

Qed.


(*-----------------------------------------set of free variables------------------------------*)

Fixpoint Free_QExp'(qs :QExp) := 
match qs with 
|QExp_s s e v => (s, e) 
|QExp_t qs1 qs2 => (min (fst (Free_QExp' qs1)) (fst (Free_QExp' qs2)),
                  max  (snd (Free_QExp' qs1))  (snd (Free_QExp' qs2) ))
end.

Definition option_beq (a b:option (nat * nat)) :=
       match a, b with 
       |None, None =>true
       |None , _ => false  
       |_, None => false
       |Some (x,y), Some (x',y') => (x=?x') && (y=?y') 
       end. 

Definition option_free(a:option (nat*nat)):=
match a with 
|None  => (0, 0)
|Some x => x 
end.


Fixpoint Free_State(F:State_formula): option (nat * nat):=
match F with 
|SPure P => None
|SQuan qs=> Some (Free_QExp' qs) 
|SOdot F1 F2=>if  (option_beq (Free_State F1)  None) 
              then Free_State F2 
              else if (option_beq (Free_State F2)  None)
              then Free_State F1 
              else let a:= option_free (Free_State F1) in let b:=option_free (Free_State F2) in 
              Some (min (fst a) (fst b),
              max  (snd a)  (snd b))
|SAnd F1 F2 => if  (option_beq (Free_State F1)  None) 
              then Free_State F2 
              else if (option_beq (Free_State F2)  None)
              then Free_State F1 
              else let a:= option_free (Free_State F1) in let b:=option_free (Free_State F2) in 
              Some (min (fst a) (fst b),
              max  (snd a)  (snd b))
|SAssn i a F => Free_State F
end.

Fixpoint Considered_QExp (qs:QExp) : Prop :=
match qs with 
|QExp_s s e v => s<e  
|QExp_t qs1 qs2 => Considered_QExp qs1 /\ Considered_QExp qs2 /\ 
              (((snd (Free_QExp' qs1))=(fst (Free_QExp' qs2)))
              \/ ((snd (Free_QExp' qs2))=(fst (Free_QExp' qs1))))
end.


Fixpoint Considered_Formula (F:State_formula) : Prop:=
match F with
| SPure P => True 
| SQuan s => Considered_QExp s
| SOdot F1 F2 =>  if  (option_beq (Free_State F1)  None) 
then Considered_Formula F2 
else if (option_beq (Free_State F2)  None)
then Considered_Formula F1
else   let a:= option_free (Free_State F1) in let b:=option_free (Free_State F2) in 
      ( Considered_Formula F1 /\ Considered_Formula F2 
              /\ (((snd a)=(fst b))
              \/ ((snd b)=(fst a))))
|SAnd F1 F2 =>   if  (option_beq (Free_State F1)  None) 
then Considered_Formula F2 
else if (option_beq (Free_State F2)  None)
then  Considered_Formula F1
else  let a:= option_free (Free_State F1) in let b:=option_free (Free_State F2) in 
                     (Considered_Formula F1 /\ Considered_Formula F2 
              /\  ((((fst a)=(fst b))/\
                     ((snd a)=(snd b)))
                     \/ ((snd a)=(fst b)) 
                    \/ (((snd b)=(fst a)))))
|SAssn i a F => Considered_Formula F
end. 

Lemma  le_min: forall s e, 
s<=e -> min s e= s .
Proof. induction s; intros. simpl. reflexivity.
       destruct e. 
       simpl. lia. 
       simpl. f_equal. apply IHs.
       lia.
Qed.

Lemma  le_max: forall s e, 
s<=e -> max s e= e .
Proof. induction s; intros. simpl. reflexivity.
       destruct e. 
       simpl. lia. 
       simpl. f_equal. apply IHs.
       lia.
Qed.
Lemma min_le: forall s0 e0 s1 e1, 
s0<=e0 /\ e0=s1 /\ s1<=e1 ->
min s0 s1 = s0 /\
max e0 e1= e1.
Proof. intros. split; [apply le_min| apply le_max]; lia. 
Qed.

Lemma Considered_QExp_dom: forall qs,
Considered_QExp qs ->
fst (Free_QExp' qs) < snd (Free_QExp' qs) .
Proof. induction qs; 
simpl. intuition.
simpl; intros.
destruct H. 
destruct H0.
destruct H1.

apply IHqs1  in H.
apply IHqs2 in H0.
assert(min (fst (Free_QExp' qs1))
(fst (Free_QExp' qs2))=(fst (Free_QExp' qs1))/\
max (snd (Free_QExp' qs1))
  (snd (Free_QExp' qs2))=(snd (Free_QExp' qs2))).
apply min_le. intuition.
destruct H2. rewrite H2. rewrite H3.
apply lt_trans with  (snd (Free_QExp' qs1)).
assumption. rewrite H1.
assumption.

apply IHqs1  in H.
apply IHqs2 in H0.
rewrite min_comm.
rewrite max_comm.
assert(min (fst (Free_QExp' qs2))
(fst (Free_QExp' qs1))=(fst (Free_QExp' qs2))/\
max (snd (Free_QExp' qs2))
  (snd (Free_QExp' qs1))=(snd (Free_QExp' qs1))).
apply min_le. intuition.
destruct H2. rewrite H2. rewrite H3.
apply lt_trans with  (snd (Free_QExp' qs2)).
assumption. rewrite H1.
assumption.
Qed.


Lemma option_edc{A: Type}: forall (a b:option A),
 a = b \/ a<> b .
Proof. intros. apply Classical_Prop.classic.
Qed.

Lemma option_eqb_neq(a b:option (nat *nat)):
a <> b <-> option_beq a b = false.
Proof. intros; split; intros; destruct a; destruct b.
       destruct p. destruct p0.   
       simpl.    
       destruct (eq_dec n n1);
       destruct (eq_dec n0 n2).  rewrite e in *. 
       rewrite e0 in *. 
       destruct H. reflexivity.  
       apply Nat.eqb_neq in n3. rewrite n3.
       apply Nat.eqb_eq in e. rewrite e.
       simpl. reflexivity.
       apply Nat.eqb_neq in n3. rewrite n3.
       apply Nat.eqb_eq in e. rewrite e.
       simpl. reflexivity.
       apply Nat.eqb_neq in n3. rewrite n3.
       apply Nat.eqb_neq in n4. rewrite n4.
       reflexivity. 
       destruct p. simpl. reflexivity.
       destruct p. simpl. reflexivity.  
       destruct H. reflexivity.
       destruct p; destruct p0. 
       simpl in *. 
       destruct (eq_dec n n1);
       destruct (eq_dec n0 n2).  
       apply Nat.eqb_eq in e. rewrite e in *.
       apply Nat.eqb_eq in e0. rewrite e0 in *.
       simpl in H. discriminate H.
       intro. injection H0.  intros. subst. destruct n3; reflexivity.
       intro. injection H0.  intros. subst. destruct n3; reflexivity.
       intro. injection H0.  intros. subst. destruct n3; reflexivity.
       intro. discriminate H0. 
       intro. discriminate H0. 
       simpl in H. discriminate H.
       
       
Qed.




Lemma Considered_Formula_dom: forall F,
Considered_Formula F ->
fst (option_free (Free_State F)) <=  snd (option_free (Free_State F)).
Proof. induction F; intros.
       simpl. intuition.
       apply Considered_QExp_dom in H.
       simpl. lia.  

       simpl in H. simpl. 
       destruct (option_edc (Free_State F1) None). 
       rewrite H0 in *. simpl in *. apply IHF2. 
       assumption.
       apply option_eqb_neq in H0. rewrite H0 in *.

       destruct (option_edc (Free_State F2) None).
       rewrite H1 in *. simpl in *. 
       apply IHF1. assumption. 
       apply option_eqb_neq in H1. rewrite H1 in *.

       simpl.
       destruct H.
       destruct H2.
       destruct H3;
       
apply IHF1  in H;
apply IHF2 in H2.
pose (min_le ( (fst (option_free (Free_State F1))))
(snd (option_free (Free_State F1)))
(fst (option_free (Free_State F2)))
  (snd (option_free (Free_State F2)))). 
destruct a. intuition.  rewrite H4. 
rewrite H5. 
apply le_trans with  (snd (option_free (Free_State F1))).
assumption. rewrite H3.
assumption.

rewrite min_comm.
rewrite max_comm.
pose (min_le ( (fst (option_free (Free_State F2))))
(snd (option_free (Free_State F2)))
(fst (option_free (Free_State F1)))
  (snd (option_free (Free_State F1)))). 
destruct a. intuition.
rewrite H4.  rewrite H5. 
apply le_trans with  (snd (option_free (Free_State F2))).
assumption. rewrite H3.
assumption.

simpl in *.
       destruct (option_edc (Free_State F1) None). 
       rewrite H0 in *. simpl in *. apply IHF2. 
       assumption.
       apply option_eqb_neq in H0. rewrite H0 in *.

       destruct (option_edc (Free_State F2) None).
       rewrite H1 in *. simpl in *. 
       apply IHF1. assumption. 
       apply option_eqb_neq in H1. rewrite H1 in *.

simpl.
destruct H.
destruct H2.
destruct H3;

apply IHF1  in H;
apply IHF2 in H2.
destruct H3. rewrite H3. rewrite H4.
rewrite min_id.
rewrite max_id. intuition.

destruct H3;
simpl.
pose (min_le ( (fst (option_free (Free_State F1))))
(snd (option_free (Free_State F1)))
(fst (option_free (Free_State F2)))
  (snd (option_free (Free_State F2)))). 
destruct a. intuition.  rewrite H4. 
rewrite H5. 
apply le_trans with  (snd (option_free (Free_State F1))).
assumption. rewrite H3.
assumption.

rewrite min_comm.
rewrite max_comm.
pose (min_le ( (fst (option_free (Free_State F2))))
(snd (option_free (Free_State F2)))
(fst (option_free (Free_State F1)))
  (snd (option_free (Free_State F1)))). 
destruct a. intuition.
rewrite H4.  rewrite H5. 
apply le_trans with  (snd (option_free (Free_State F2))).
assumption. rewrite H3.
assumption. 

simpl in *. apply IHF. assumption. 
Qed.


(*------------------------------eval_dom---------------------------------------------*)


Lemma QExp_eval_dom{ s e:nat}: forall qs c (q:qstate s e),
QExp_eval qs (c,q) -> s<= fst (Free_QExp' qs) /\ 
fst (Free_QExp' qs) < snd (Free_QExp' qs) /\ snd (Free_QExp' qs) <=e.
Proof. induction qs; intros.
       simpl in *. intuition.
       simpl in *.
       destruct H. destruct H0.
       apply IHqs1 in H0.
       apply IHqs2 in H1.
       split. 
       apply min_glb.
       intuition. intuition.
       split.
       destruct (D.compare (snd (Free_QExp' qs1)) (fst (Free_QExp' qs2))) eqn: E;
       try unfold D.lt in l.
       rewrite min_l; try lia. 
       rewrite max_r; try lia.  
      
       unfold D.eq in e0. lia.
       destruct (D.compare (snd (Free_QExp' qs2)) (fst (Free_QExp' qs1))) eqn: E';
       try unfold D.lt in l0.
       rewrite min_r; try lia. 
       rewrite max_l; try lia.
      
       unfold D.eq in e0. lia.
       apply min_lt_iff.
       left. 
       apply max_lt_iff. left. lia.
       
       apply max_lub_iff.
       intuition.
Qed.


Lemma State_eval_dom{ s e:nat}: forall F c (q:qstate s e),
State_eval F (c,q) ->( (Free_State F)= None )\/ 
let a:= option_free ((Free_State F)) in 
(s<=fst a /\ fst a < snd a /\ snd a <=e).
Proof. induction F; intros.
       simpl in *. left. intuition. 
       simpl in *. right.
       apply QExp_eval_dom with c q.
       assumption.

       destruct H. destruct H0.
       apply IHF1 in H0.
       apply IHF2 in H1.
       destruct H0.
       destruct H1. simpl. left. rewrite H0. simpl. 
       assumption. simpl. right. rewrite H0. simpl. 
       assumption. 

       destruct H1. 

       assert(Free_State F1 <> None). intro. rewrite H2 in *.
       simpl in H0. lia. apply option_eqb_neq in H2. 
       simpl. right. rewrite H1. rewrite H2. simpl. 
       assumption. 

       assert(Free_State F1 <> None). intro. rewrite H2 in *.
       simpl in H0. lia. apply option_eqb_neq in H2. 
       assert(Free_State F2 <> None). intro. rewrite H3 in *.
       simpl in H1. lia. apply option_eqb_neq in H3.
       simpl. right.  rewrite H2. rewrite H3.
       simpl.  split. 
       apply min_glb.
       intuition. intuition.
       split. simpl in *. 
       
       destruct (D.compare (snd (option_free (Free_State F1))) (fst (option_free (Free_State F2)) )) eqn: E;
       try unfold D.lt in l.
       rewrite min_l; try lia. 
       rewrite max_r; try lia.  
      
       unfold D.eq in e0. lia.
       destruct (D.compare (snd (option_free (Free_State F2)) ) (fst (option_free (Free_State F2)) )) eqn: E';
       try unfold D.lt in l0.
       rewrite min_r; try lia. 
       rewrite max_l; try lia.
      
       unfold D.eq in e0. lia.
       apply min_lt_iff.
       left. 
       apply max_lt_iff. left. lia.
       apply max_lub_iff.
       intuition.
       destruct H.
       apply IHF1 in H.
       apply IHF2 in H0.

       destruct H.
       destruct H0; simpl. left. rewrite H.
       simpl. assumption. 
       right. rewrite H.  simpl. 
       assumption. 
       destruct H0. 

       assert(Free_State F1 <> None). intro. rewrite H1 in *.
       simpl in H. lia. apply option_eqb_neq in H1. 
       simpl. right. rewrite H0. rewrite H1. simpl. 
       assumption. 

       assert(Free_State F1 <> None). intro. rewrite H1 in *.
       simpl in H. lia. apply option_eqb_neq in H1. 
       assert(Free_State F2 <> None). intro. rewrite H2 in *.
       simpl in H0. lia. apply option_eqb_neq in H2.
       simpl. right.  rewrite H2. rewrite H1.
       simpl.  split. 
       apply min_glb.
       intuition. intuition.
       split. simpl in *. 
       
       destruct (D.compare (snd (option_free (Free_State F1))) (fst (option_free (Free_State F2)) )) eqn: E;
       try unfold D.lt in l.
       rewrite min_l; try lia. 
       rewrite max_r; try lia.  
      
       unfold D.eq in e0. lia.
       destruct (D.compare (snd (option_free (Free_State F2)) ) (fst (option_free (Free_State F2)) )) eqn: E';
       try unfold D.lt in l0.
       rewrite min_r; try lia. 
       rewrite max_l; try lia.
      
       unfold D.eq in e0. lia.
       apply min_lt_iff.
       left. 
       apply max_lt_iff. left. lia.
       apply max_lub_iff.
       intuition. 

       simpl in *. eapply IHF. apply H.
Qed.


Lemma dstate_eval_dom{ s e:nat}: forall F (mu:list (cstate * qstate s e)),
State_eval_dstate F mu  -> ( (Free_State F)= None )\/ 
let a:= option_free ((Free_State F)) in 
(s<=fst a /\ fst a < snd a /\ snd a <=e).
Proof. induction mu; intros. destruct H.
     inversion H; subst. destruct a. 
     apply State_eval_dom with c q.
     assumption. 
Qed.

(*-------------------------------------------------eval pure-------------------------*)


Lemma QExp_eval_pure: forall qs s e c (q: qstate s e) ,
Considered_QExp qs ->
WF_qstate q->
QExp_eval qs (c, q)->
@Par_Pure_State (2^((snd (Free_QExp' qs))- ((fst (Free_QExp' qs)))))
(@Reduced s e q ((fst (Free_QExp' qs))) (((snd (Free_QExp' qs))))).
Proof. induction qs; intros. unfold Par_Pure_State. 
       simpl in H1. 
       exists ((Cmod (@trace (2^(e0-s0)) q))%R).
       exists (outer_product v v).
       simpl. 
       rewrite <-Reduced_scale in H1.
       unfold outer_product in H1.
       destruct H1. destruct H2.
       destruct H3. destruct H4. 
       split. 
       apply nz_mixed_state_Cmod_1.
       apply H0. split.
       econstructor. split. 
       apply H1. unfold outer_product.
       reflexivity.
       unfold outer_product.
       rewrite <-H5. 
       rewrite Mscale_assoc.
       rewrite RtoC_mult.
       rewrite Rdiv_unfold.
       rewrite Rmult_1_l.
       rewrite Rinv_r. 
       rewrite Mscale_1_l.
       reflexivity. 
       assert((Cmod (@trace (2^(e0-s0)) q) > 0)%R).
       apply nz_mixed_state_Cmod_1.
       apply H0. lra.

       simpl QExp_eval in H1.  
       destruct H1. 
       destruct H2.
       pose H2 as H2'. pose H3 as H3'.
       apply IHqs1 in H2'.
       apply IHqs2 in H3'.
       simpl in H.
       destruct H.
       destruct H4.
       destruct H5.
       simpl.
       assert(min (fst (Free_QExp' qs1))
       (fst (Free_QExp' qs2))=(fst (Free_QExp' qs1))/\
       max (snd (Free_QExp' qs1))
         (snd (Free_QExp' qs2))=(snd (Free_QExp' qs2))).
       apply min_le. split. 
       pose (Considered_QExp_dom qs1 H).
       lia. 
       split. intuition.

       pose (Considered_QExp_dom qs2 H4).
       lia.  
       destruct H6. rewrite H6. rewrite H7.
     apply (Par_Pure_State_wedge) with (snd (Free_QExp' qs1)).
     pose (QExp_eval_dom qs1 c q H2). 
     pose (QExp_eval_dom qs2 c q H3).
     split.  intuition.
    split. pose (Considered_QExp_dom qs1 H). lia. 
     split. rewrite H5. pose (Considered_QExp_dom qs2 H4). lia.
      intuition.  assumption. assumption. 
       rewrite H5. assumption.
      
       simpl.
       rewrite min_comm.
       rewrite max_comm.
       assert(min (fst (Free_QExp' qs2))
       (fst (Free_QExp' qs1))=(fst (Free_QExp' qs2))/\
       max (snd (Free_QExp' qs2))
         (snd (Free_QExp' qs1))=(snd (Free_QExp' qs1))).
       apply min_le. split. 
       pose (Considered_QExp_dom qs2 H4). lia. 
       split. intuition.
       pose (Considered_QExp_dom qs1 H). lia. 
      destruct H6. rewrite H6. rewrite H7.
     apply (Par_Pure_State_wedge) with (snd (Free_QExp' qs2)).
     pose (QExp_eval_dom qs1 c q H2). 
     pose (QExp_eval_dom qs2 c q H3).
     split.  intuition.
    split. pose (Considered_QExp_dom qs1 H). lia. 
     split. rewrite H5. pose (Considered_QExp_dom qs2 H4). lia.
      intuition.  assumption. assumption. 
       rewrite H5. assumption.
        apply H.
        assumption.
        apply H.
        assumption.
Qed.


Lemma State_eval_pure: forall F s e c (q: qstate s e) ,
Considered_Formula F ->
WF_qstate q->
State_eval F (c, q)->
((Free_State F = None) 
\/ @Par_Pure_State (2^((snd (option_free (Free_State F)))- ((fst (option_free (Free_State F))))))
(@Reduced s e q ((fst (option_free (Free_State F)))) (((snd (option_free (Free_State F))))) )).
Proof. induction F; intros.
       simpl. left. reflexivity.
       right. 
       apply QExp_eval_pure with c.
       assumption. assumption.
       assumption.
        
        
       destruct H1. 
       destruct H2.   
       destruct (option_edc (Free_State F1) None).
       simpl in *. rewrite H4 in *. simpl in *.  
       apply IHF2 with c; assumption. 
       
       pose H2 as H2'.  
       apply IHF1 in H2'. 
       destruct H2'. destruct H4. assumption. 
       apply option_eqb_neq in H4. 
       destruct (option_edc (Free_State F2) None).
       simpl in *. rewrite H6 in *. rewrite H4 in *. simpl in *.
       right. assumption. 
       pose H3 as H3'. 
       apply IHF2 in H3'. 
       destruct H3'. destruct H6. assumption.
       apply option_eqb_neq in H6. 
       simpl in *. rewrite H4 in *. rewrite H6 in*.   
       simpl in *.
      
       right. simpl in *.  apply option_eqb_neq in H4.
       apply option_eqb_neq in H6.
       destruct H.
       destruct H8.
       destruct H9.
       simpl.
       pose (min_le ( (fst (option_free (Free_State F1))))
       (snd (option_free (Free_State F1)))
       (fst (option_free (Free_State F2)))
         (snd (option_free (Free_State F2)))).  
       destruct a.  split.
pose (Considered_Formula_dom F1 H). lia. 
split. assumption.
apply Considered_Formula_dom. assumption.
 rewrite H10. rewrite H11.
     apply Par_Pure_State_wedge with (snd (option_free (Free_State F1))).
     pose (State_eval_dom F1 c q H2). 
     destruct o. destruct H4. assumption.
     pose (State_eval_dom F2 c q H3).
     destruct o. destruct H6; assumption. 
     split. intuition. 
     split. 
     apply Considered_Formula_dom. assumption.
     split. 
     rewrite H9. 
     apply Considered_Formula_dom. assumption.
     intuition. assumption. assumption.
     rewrite H9.
     assumption.
       
     simpl.
     rewrite min_comm.
     rewrite max_comm.
     pose (min_le ( (fst (option_free (Free_State F2))))
       (snd (option_free (Free_State F2)))
       (fst (option_free (Free_State F1)))
         (snd (option_free (Free_State F1)))).  
       destruct a.  split.
pose (Considered_Formula_dom F2 H8).  lia. 
split. assumption.
apply Considered_Formula_dom. assumption.
 rewrite H10. rewrite H11.
   apply (Par_Pure_State_wedge) with (snd (option_free (Free_State F2))).
   pose (State_eval_dom F1 c q H2).
     destruct o. destruct H4; assumption. 
     pose (State_eval_dom F2 c q H3).
     destruct o. destruct H6; assumption.  
     split. intuition. 
     split. 
     apply Considered_Formula_dom. assumption.
     split. 
     rewrite H9. 
     apply Considered_Formula_dom. assumption.
     intuition. assumption. assumption.
     rewrite H9.
     assumption. 
       
     apply option_eqb_neq in H6. 
     simpl in *.  rewrite H4 in *.
     rewrite H6 in *. 

        apply H.
        assumption.
        apply option_eqb_neq in H4. 
        simpl in *.  rewrite H4 in *.
        destruct (option_edc (Free_State F2) None).
        rewrite H5 in *. simpl in *.
        apply H.  
        apply option_eqb_neq in H5. rewrite H5 in *.
        apply H.
        assumption.

simpl in H. destruct H1.


destruct (option_edc (Free_State F1) None).
simpl in *. rewrite H3 in *. simpl in *.  
apply IHF2 with c; assumption. 

pose H1 as H1'.  
apply IHF1 in H1'. 
destruct H1'. destruct H3. assumption. 
apply option_eqb_neq in H3. 
destruct (option_edc (Free_State F2) None).
simpl in *. rewrite H5 in *. rewrite H3 in *. simpl in *.
right. assumption. 
pose H2 as H2'. 
apply IHF2 in H2'. 
destruct H2'. destruct H5. assumption.
apply option_eqb_neq in H5. 
simpl in *. rewrite H3 in *. rewrite H5 in*.   
simpl in *.
      
right. simpl in *.  apply option_eqb_neq in H3.
apply option_eqb_neq in H5.
destruct H.
destruct H7.
destruct H8.
destruct H8.
simpl. rewrite H8. rewrite H9.
rewrite min_id. rewrite max_id.
assumption.

destruct H8.
simpl.
       pose (min_le ( (fst (option_free (Free_State F1))))
       (snd (option_free (Free_State F1)))
       (fst (option_free (Free_State F2)))
         (snd (option_free (Free_State F2)))).  
       destruct a.  split.
pose (Considered_Formula_dom F1 H). lia. 
split. assumption.
apply Considered_Formula_dom. assumption.
 rewrite H10. rewrite H9.
     apply Par_Pure_State_wedge with (snd (option_free (Free_State F1))).
     pose (State_eval_dom F1 c q H1). 
     destruct o. destruct H3. assumption.
     pose (State_eval_dom F2 c q H2).
     destruct o. destruct H5; assumption. 
     split. intuition. 
     split. 
     apply Considered_Formula_dom. assumption.
     split. 
     rewrite H8. 
     apply Considered_Formula_dom. assumption.
     intuition. assumption. assumption.
     rewrite H8.
     assumption.
simpl.
rewrite min_comm.
rewrite max_comm.
pose (min_le ( (fst (option_free (Free_State F2))))
  (snd (option_free (Free_State F2)))
  (fst (option_free (Free_State F1)))
    (snd (option_free (Free_State F1)))).  
  destruct a.  split.
pose (Considered_Formula_dom F2 H7).  lia. 
split. assumption.
apply Considered_Formula_dom. assumption.
rewrite H10. rewrite H9.
apply (Par_Pure_State_wedge) with (snd (option_free (Free_State F2))).
pose (State_eval_dom F1 c q H1).
destruct o. destruct H3; assumption. 
pose (State_eval_dom F2 c q H2).
destruct o. destruct H5; assumption.  
split. intuition. 
split. 
apply Considered_Formula_dom. assumption.
split. 
rewrite H8. 
apply Considered_Formula_dom. assumption.
intuition. assumption. assumption.
rewrite H8.
assumption. 
  
apply option_eqb_neq in H5. 
simpl in *.  rewrite H3 in *.
rewrite H5 in *. 

   apply H.
   assumption.
   apply option_eqb_neq in H3. 
   simpl in *.  rewrite H3 in *.
   destruct (option_edc (Free_State F2) None).
   rewrite H4 in *. simpl in *.
   apply H.  
   apply option_eqb_neq in H4. rewrite H4 in *.
   apply H.
   assumption.

   simpl Free_State.  eapply IHF. apply H. 
   assumption. apply H1. 
Qed.


(*--------------------------------dstate_Separ------------------------------------------*)
Inductive q_combin'{s0 e0 s1 e1 s2 e2}: (qstate s0 e0) -> (qstate s1 e1)-> (qstate s2 e2)->Prop:=
|q_combin'': forall q0 q1, e0 = s1-> s0 = s2 -> e1 = e2 -> WF_qstate q0 ->
             WF_qstate q1->
            q_combin' q0 q1 (@kron (2^(e0-s0)) (2^(e0-s0)) (2^(e1-s1))  
            (2^(e1-s1)) q0 q1).

Inductive dstate_Separ{ s e: nat}: (list (cstate *qstate s e)) -> nat -> nat -> nat-> nat-> Prop :=
|dstate_Separ_nil: forall s0 e0 s1 e1,  dstate_Separ nil s0 e0 s1 e1
|dstate_Separ_cons: forall s0 e0 s1 e1 c q mu' (q0_i: nat->qstate s0 e0) (q1_i:nat-> qstate s1 e1) n, 
                    e0 = s1-> s0 = s -> e1 = e ->
  (forall i, (WF_qstate (q0_i i))\/  (q0_i i)= Zero) ->
(forall i, (WF_qstate (q1_i i)) \/ (q1_i i)= Zero)->
(q= big_sum (fun i=>@kron (2^(e0-s0)) (2^(e0-s0))  (2^(e1-s1)) (2^(e1-s1)) (q0_i i ) (q1_i i)) n)->
dstate_Separ mu' s0 e0 s1 e1->
dstate_Separ ((c,q)::mu') s0 e0 s1 e1.

(*------------------mu \modes F => mu is separable--------------------*)
Lemma State_eval_separ_r{s e:nat}: forall F r c (q:qstate s e),
Considered_Formula (F) /\
(r <= e /\ snd (option_free (Free_State F)) <=r /\ fst (option_free (Free_State F)) < snd (option_free (Free_State F)))->
WF_qstate q->
State_eval F (c, q) -> 
exists 
(q1:qstate (fst (option_free (Free_State F))) (snd (option_free (Free_State F))))
(q2:qstate  (snd (option_free (Free_State F))) r), 
(q_combin' q1 q2 (@Reduced s e q  (fst (option_free (Free_State F))) r)).
Proof. intros F r c q H Hw. intros. 
       assert(s<=fst (option_free (Free_State F))). 
       pose (State_eval_dom F c q H0). destruct o.
       rewrite H1 in *. simpl in *. lia. 
        apply H1.  
        remember ((snd (option_free (Free_State F)))) as x.
        remember ((fst (option_free (Free_State F)))) as s'.
        simpl.  
        remember ((Reduced q s' r)).
       assert(exists (q1:qstate s' x) (q2: qstate x r), 
       and (WF_qstate q1 /\ WF_qstate q2)
       (q0 = @kron (2^(x-s')) (2^(x-s')) (2^(r-x))  (2^(r-x)) q1 q2)).
       apply Odot_Sepear''; try lia. 
       rewrite Heqq0. apply WF_qstate_Reduced; try lia. 
       assumption. 
       rewrite Heqq0. rewrite Reduced_assoc; try lia. 
       apply State_eval_pure  in H0. destruct H0.
       subst. rewrite H0 in *. simpl in *.  lia. rewrite Heqs'. rewrite Heqx. apply H0.
      apply H. assumption. 
       destruct H2. destruct H2.
       destruct H2. rewrite H3. 
       exists x0. exists x1.
       econstructor; try reflexivity; try apply H2.
Qed.


Lemma State_eval_separ_l{s e:nat}: forall F l  c (q:qstate s e),
Considered_Formula (F) /\
(s <= l /\ l <= fst (option_free (Free_State F)) /\ fst (option_free (Free_State F)) < snd (option_free (Free_State F)))->
WF_qstate q->
State_eval F (c, q) -> 
exists 
(q1:qstate l (fst (option_free (Free_State F))))
(q2:qstate (fst (option_free (Free_State F))) (snd (option_free (Free_State F)))), 
(q_combin' q1 q2 (@Reduced s e q l (snd (option_free (Free_State F))))).
Proof. intros F l c q H Hw. intros. 
        assert(snd (option_free (Free_State F))<=e). 
        pose (State_eval_dom F c q H0). destruct o.
        rewrite H1 in *. simpl in *. 
        subst. lia. apply H1.  
        remember ((fst (option_free (Free_State F)))) as x.
        remember ((snd (option_free (Free_State F)))) as e'.
        simpl.  
        remember ((Reduced q l e')).
       assert(exists (q1:qstate l x) (q2: qstate x e'), 
       and (WF_qstate q1 /\ WF_qstate q2)
       (q0 = @kron (2^(x-l)) (2^(x-l)) (2^(e'-x))  (2^(e'-x)) q1 q2)).
       apply Odot_Sepear'''; try lia.  
       rewrite Heqq0. apply WF_qstate_Reduced; try lia; try assumption.
       rewrite Heqq0. rewrite Reduced_assoc; try lia. 
       apply State_eval_pure  in H0; try assumption; try apply H. 
       destruct H0. subst. rewrite H0 in *. simpl in *. lia. rewrite Heqx. rewrite Heqe'. apply H0.
       destruct H2. destruct H2.
       destruct H2. rewrite H3. 
       exists x0. exists x1.
       econstructor; try reflexivity; try apply H2.
Qed.


Lemma State_eval_dstate_separ_l{s e:nat}: forall (mu : list (cstate *qstate s e)) F l,
Considered_Formula F /\
(s <= l /\ l <= fst (option_free (Free_State F)) /\ fst (option_free (Free_State F)) < snd (option_free (Free_State F)))->
State_eval_dstate F mu->
WF_dstate_aux mu ->
(dstate_Separ (d_reduced mu l (snd (option_free (Free_State F)))) 
l (fst (option_free (Free_State F))) (fst (option_free (Free_State F))) (snd (option_free (Free_State F)))).
Proof. induction mu; intros. 
      simpl. intuition.
      destruct mu. 
      destruct a. 
      simpl.

      assert(exists (q1:qstate l (fst (option_free (Free_State F)))) 
      (q2:qstate (fst (option_free (Free_State F))) (snd (option_free (Free_State F)))), 
      (q_combin' q1 q2 (@Reduced s e q l (snd (option_free (Free_State F)))))).
      apply State_eval_separ_l with c.
      assumption. inversion_clear  H1. intuition.
      inversion_clear H0. assumption.

      destruct H2. destruct H2.
      inversion H2; subst.
      econstructor; try reflexivity.
      assert((forall i : nat, WF_qstate ((fun i:nat=> x) i) \/  ((fun i:nat=> x) i) = Zero)).
      intuition. apply H8.
      assert(forall i : nat, WF_qstate ((fun i=>x0) i) \/ ((fun i=>x0) i)= Zero).
      intuition.  apply H8.
      apply Logic.eq_trans with 
      (big_sum
      (fun i : nat =>
      (fun _ : nat => x) i ⊗ (fun _ : nat => x0) i) 
      1). simpl. 
      rewrite Mplus_0_l.
      reflexivity. intuition.

      econstructor.
      destruct a. destruct p.

      simpl.
      assert(exists (q1:qstate l (fst (option_free (Free_State F))))
      (q2:qstate (fst (option_free (Free_State F))) (snd (option_free (Free_State F)))), 
      (q_combin' q1 q2 (@Reduced s e q l (snd (option_free (Free_State F)))))).
      apply State_eval_separ_l with c.
      assumption. inversion_clear  H1. intuition.
      inversion_clear H0. assumption. 
      destruct H2. destruct H2. 
      inversion H2; subst.

      econstructor; try assumption.

      assert((forall i : nat, WF_qstate ((fun i:nat=> x) i) \/  ((fun i:nat=> x) i) = Zero)).
      intuition. apply H8.
      assert(forall i : nat, WF_qstate ((fun i=>x0) i) \/ ((fun i=>x0) i)= Zero).
      intuition.  apply H8.
      apply Logic.eq_trans with 
      (big_sum
      (fun i : nat =>
      (fun _ : nat => x) i ⊗ (fun _ : nat => x0) i) 
      1). simpl. 
      rewrite Mplus_0_l.
      reflexivity. intuition.

      apply IHmu.
      assumption.
      inversion_clear H0.
      apply H9.
      inversion_clear H1. assumption.  
Qed.


Lemma State_eval_dstate_separ_r{s e:nat}: forall (mu : list (cstate *qstate s e)) F r,
Considered_Formula F /\
(r <= e /\ snd (option_free (Free_State F)) <=r /\ fst (option_free (Free_State F)) < snd (option_free (Free_State F)))->
State_eval_dstate F mu->
WF_dstate_aux mu ->
(dstate_Separ (d_reduced mu  (fst (option_free (Free_State F))) r) 
(fst (option_free (Free_State F))) (snd (option_free (Free_State F))) (snd (option_free (Free_State F))) r).
Proof. induction mu; intros. 
      simpl. intuition.
      destruct mu. 
      destruct a. 
      simpl.

      assert(exists 
      (q1:qstate (fst (option_free (Free_State F))) (snd (option_free (Free_State F))))
      (q2:qstate  (snd (option_free (Free_State F))) r), 
      (q_combin' q1 q2 (@Reduced s e q  (fst (option_free (Free_State F))) r))).
      apply State_eval_separ_r with c.
      assumption. inversion_clear  H1. intuition.
      inversion_clear H0. assumption.

      destruct H2. destruct H2.
      inversion H2; subst.
      econstructor; try reflexivity.
      assert((forall i : nat, WF_qstate ((fun i:nat=> x) i) \/  ((fun i:nat=> x) i) = Zero)).
      intuition. apply H8.
      assert(forall i : nat, WF_qstate ((fun i=>x0) i) \/ ((fun i=>x0) i)= Zero).
      intuition.  apply H8.
      apply Logic.eq_trans with 
      (big_sum
      (fun i : nat =>
      (fun _ : nat => x) i ⊗ (fun _ : nat => x0) i) 
      1). simpl. 
      rewrite Mplus_0_l.
      reflexivity. intuition.

      econstructor.
      destruct a. destruct p.

      simpl.
      assert(exists 
      (q1:qstate (fst (option_free (Free_State F))) (snd (option_free (Free_State F))))
      (q2:qstate  (snd (option_free (Free_State F))) r), 
      (q_combin' q1 q2 (@Reduced s e q  (fst (option_free (Free_State F))) r))).
      apply State_eval_separ_r with c.
      assumption. inversion_clear  H1. intuition.
      inversion_clear H0. assumption. 
      destruct H2. destruct H2. 
      inversion H2; subst.

      econstructor; try assumption.

      assert((forall i : nat, WF_qstate ((fun i:nat=> x) i) \/  ((fun i:nat=> x) i) = Zero)).
      intuition. apply H8.
      assert(forall i : nat, WF_qstate ((fun i=>x0) i) \/ ((fun i=>x0) i)= Zero).
      intuition.  apply H8.
      apply Logic.eq_trans with 
      (big_sum
      (fun i : nat =>
      (fun _ : nat => x) i ⊗ (fun _ : nat => x0) i) 
      1). simpl. 
      rewrite Mplus_0_l.
      reflexivity. intuition.

      apply IHmu.
      assumption.
      inversion_clear H0.
      apply H9.
      inversion_clear H1. assumption.  
Qed.

(*  ------------------------------mu \models F => mu|_{V} \modesl F -----------*)
Lemma QExp_free_eval{s e:nat}:forall (qs: QExp) (st: state s e) s' e',
s<=s'/\ s'<=e' /\ e'<=e ->
s'<=(fst (Free_QExp' qs)) /\ (snd (Free_QExp' qs))<=e'->
@WF_Matrix (2^(e-s)) (2^(e-s)) (snd st)->
QExp_eval qs st <-> QExp_eval qs (fst st, (Reduced (snd st) s' e')).
Proof. induction qs; split; intros. 
        simpl in *. rewrite Reduced_scale.
        rewrite Reduced_assoc. 
        split. intuition. split. lia.
        split. lia. split. lia. 
        rewrite Reduced_trace. intuition.
        lia. assumption. lia.  
        simpl in *. 
        rewrite Reduced_scale in H2.
        rewrite Reduced_assoc in H2.
        rewrite Reduced_trace in H2.
        split. intuition. 
        split. lia. split. lia. split. lia. 
        intuition. lia. assumption.  lia.
        simpl in H2. 
        simpl. split.  intuition.
        destruct st. simpl in *.
  
        split. 
        apply (IHqs1 (c, q)).  assumption.
        intuition. assumption.
        intuition. 
        apply (IHqs2 (c,q)). assumption.
        intuition. assumption.
        intuition. 
        simpl in *. split.  intuition.
        destruct H2.
        destruct H3.
  
        split.
        apply IHqs1 in H3. 
        assumption. intuition.
        pose (QExp_eval_dom qs1 (fst st) (Reduced (snd st) s' e') H3).
        lia. 
        assumption.
        apply IHqs2 in H4. assumption.
        intuition.
        pose (QExp_eval_dom qs2 (fst st) (Reduced (snd st) s' e') H4).
        lia. 
        assumption. 
Qed.



Lemma min_max_eq: forall x1 x2 y1 y2,
min x1 x2= max y1 y2->
x1<=y1 /\ x2<=y2->
x1=y1 /\ x2 = y2.
Proof. intros. lia. Qed.

Lemma Pure_free_eval'{s e s' e':nat}:forall  (F: State_formula) c (q : qstate s e) (q0: qstate s' e'),
(Free_State F)= None->
State_eval F (c, q) -> 
State_eval F (c, q0).
Proof. induction F;   intros.
       eapply state_eq_Pure with (c, q). 
       reflexivity. apply H0.
       apply QExp_eval_dom in H0.
       unfold Free_State in *. discriminate H.

       simpl in *;
       split. intuition.
       destruct H0. destruct H1.
destruct (option_edc (Free_State F1) None).
split.  apply IHF1 with q; try assumption. 
apply IHF2 with q; try assumption. 
rewrite H3 in *. simpl in *. assumption. 
apply option_eqb_neq in H3. rewrite H3 in *.
destruct (option_edc (Free_State F2) None); try assumption.
rewrite H4 in *. simpl in *. rewrite H in *. simpl in *. discriminate H3.
apply option_eqb_neq in H4. 
rewrite H4 in *. discriminate H.

destruct H0. simpl in H. 
destruct (option_edc (Free_State F1) None).
rewrite H2 in *. simpl in *. 
split. apply IHF1 with q; try assumption. reflexivity. 
apply IHF2 with q; try assumption.  

apply option_eqb_neq in H2. rewrite H2 in *.
destruct (option_edc (Free_State F2) None); try assumption.
rewrite H3 in *. simpl in *. rewrite H in *. simpl in *. discriminate H2.
apply option_eqb_neq in H3. 
rewrite H3 in *. discriminate H.

eapply IHF. apply H. simpl in H0. rewrite (state_eq_aexp _ (c, q)). apply H0.
reflexivity.
Qed. 


(*对于一个连续的而言*)  
Lemma State_free_eval{s e:nat}:forall (F: State_formula) (st: state s e) s' e',
s<=s'/\ s'<=e' /\ e'<=e ->
s'<=(fst (option_free (Free_State F))) /\ (snd (option_free (Free_State F)))<=e' ->
@WF_Matrix (2^(e-s)) (2^(e-s)) (snd st) ->
State_eval F st <-> 
State_eval F (fst st, (Reduced (snd st) s' e')).
Proof. induction F. split; intros. destruct st. 
    eapply state_eq_Pure with (c, q). 
    reflexivity. apply H2.
    destruct st. simpl in *.
    eapply state_eq_Pure with (c, Reduced q s' e'). 
    reflexivity. intuition. destruct st.
    split; intros.
    apply (QExp_free_eval _  (c, q)) .
    intuition. intuition. intuition.
    assumption.
    simpl in *.
    rewrite QExp_free_eval. apply H2. 
    intuition. intuition. intuition.


    intros.
    simpl in *.
    destruct (option_edc (Free_State F1) None). 
    split; intros.
    split. intuition.
    split. destruct st. simpl.  
    apply (@Pure_free_eval' s e) with q; try assumption.
 intuition.  rewrite H2 in *. simpl in *.
    apply IHF2; try assumption. intuition.
    split. intuition. 
    split. 
    destruct st. simpl.  
    apply (@Pure_free_eval' s' e') with (Reduced (snd (c, q)) s' e'); try assumption.
           intuition. rewrite H2 in *.  simpl in *.
    eapply IHF2; try assumption. apply H. assumption.
    intuition. 
    apply option_eqb_neq in H2.  rewrite H2 in *.
    destruct (option_edc (Free_State F2) None).
    rewrite H3 in *. simpl in *.
    split. intros.
    split. intuition.
    split. apply IHF1; try assumption. intuition.
    destruct st. simpl.  
    apply (@Pure_free_eval' s e) with q; try assumption.
 intuition.   
    split. intuition.
    split. eapply IHF1; try assumption. apply H.
    assumption. intuition.
    destruct st. simpl.  
    apply (@Pure_free_eval' s' e') with (Reduced (snd (c, q)) s' e'); try assumption.
           intuition.


           apply option_eqb_neq in H3.  rewrite H3 in *. simpl in *.
    split. intros. 
    simpl in *. split. intuition.
    split. apply IHF1. assumption.
    split.
    apply min_glb_l with (fst (option_free(Free_State F2))).
    intuition.
    eapply max_lub_iff.  rewrite max_comm. apply H0.
    assumption. intuition.
    apply IHF2. assumption.
    split.
    apply min_glb_l with (fst (option_free(Free_State F2))).
    intuition.
    eapply max_lub_iff.   apply H0.
    assumption. intuition.
    split. intuition.
    simpl in *.
    split. eapply IHF1; try assumption. apply H.
    split.
    apply min_glb_l with (fst (option_free(Free_State F2))).
    intuition.
    eapply max_lub_iff.  rewrite max_comm. apply H0.
    intuition.
    eapply IHF2; try assumption. apply H. 
    split.
    apply min_glb_l with (fst (option_free(Free_State F2))).
    intuition.
    eapply max_lub_iff.  apply H0. intuition.
    

    intros.
    simpl in *.
    destruct (option_edc (Free_State F1) None). 
    rewrite H2 in *. simpl in *. 
    split; intros.
    split.
    destruct st. simpl.  
    apply (@Pure_free_eval' s e) with q; try assumption.
 intuition.
    apply IHF2; try assumption. intuition.
    split.
    destruct st. simpl.  
    apply (@Pure_free_eval' s' e') with (Reduced (snd (c, q)) s' e'); try assumption.
           intuition.
    eapply IHF2; try assumption. apply H. assumption.
    intuition.
    destruct (option_edc (Free_State F2) None).
    apply option_eqb_neq in H2. 
    rewrite H2 in *. rewrite H3 in *. simpl in *.
    split. intros.
    split. apply IHF1; try assumption. intuition.
    destruct st. simpl.  
    apply (@Pure_free_eval' s e) with q; try assumption.
 intuition.
    split. eapply IHF1; try assumption. apply H.
    assumption. intuition.
    destruct st. simpl.  
    apply (@Pure_free_eval' s' e') with (Reduced (snd (c, q)) s' e'); try assumption.
           intuition.
           apply option_eqb_neq in H2. 
           rewrite H2 in *.
           apply option_eqb_neq in H3. 
           rewrite H3 in *. simpl in *.
    simpl in *.
    split; intros.
    split.  apply IHF1. assumption.
    split.
    apply min_glb_l with (fst (option_free(Free_State F2))).
    intuition.
    eapply max_lub_iff.  rewrite max_comm. apply H0.
    assumption. intuition.
    apply IHF2. assumption.
    split.
    apply min_glb_l with (fst (option_free(Free_State F2))).
    intuition.
    eapply max_lub_iff.  apply H0.
    assumption. intuition.
    split. eapply IHF1; try assumption. apply H.
    split.
    apply min_glb_l with (fst (option_free(Free_State F2))).
    intuition.
    eapply max_lub_iff.  rewrite max_comm. apply H0.
    intuition.
  
    eapply IHF2; try assumption. apply H. 
    split.
    apply min_glb_l with (fst (option_free(Free_State F2))).
    intuition.
    eapply max_lub_iff.   apply H0.
    intuition.

    intros. destruct st. simpl. rewrite (state_eq_aexp ((c, Reduced q s' e')) (c,q)); try reflexivity.
    eapply IHF; try assumption.
Qed.


Lemma State_dstate_free_eval{s e:nat}:forall  (mu: list (cstate * qstate s e)) (F: State_formula) s' e',
s<=s'/\ s'<=e' /\ e'<=e ->
s'<=(fst (option_free (Free_State F))) /\ (snd (option_free (Free_State F)))<=e' ->
WF_Matrix_dstate mu ->
State_eval_dstate F mu <-> 
State_eval_dstate F (d_reduced mu s' e').
Proof. induction mu; intros. simpl. intuition.
       destruct mu; destruct a. 
       split; intros.
       inversion_clear H2. 
       econstructor.
       apply (State_free_eval _ (c, q)).  
       assumption. assumption. 
       inversion_clear H1. intuition.
       assumption. econstructor.
       
       inversion_clear H2.
       econstructor.
       apply (State_free_eval _ (c, q)) in H3.
       assumption. assumption. assumption.
       inversion_clear H1. intuition.
       econstructor.

       split; intros.
       inversion_clear H2.
       econstructor. 
       apply (State_free_eval _ (c, q)).  
       assumption. assumption. 
       inversion_clear H1. intuition.
       assumption.
       rewrite <-State_eval_dstate_Forall in H4. 
       rewrite (IHmu _ s' e') in H4.
       rewrite <-State_eval_dstate_Forall.
       apply H4. destruct p.  discriminate.
       assumption. assumption. 
       inversion_clear H1. intuition.
       discriminate. 
       
       econstructor. 
       inversion_clear H2.
       apply (State_free_eval _ (c, q)) in H3.  
       assumption. assumption. assumption. 
       inversion_clear H1. intuition.
       destruct p. 
       inversion_clear H2.
       rewrite <-State_eval_dstate_Forall. 
       rewrite (IHmu _ s' e').
       simpl. assumption. assumption.
       assumption.
       inversion_clear H1. intuition.
       discriminate.
Qed.


Lemma Pure_free_dstate{s e s' e':nat}:forall  (F: State_formula)  (mu : list (state s e))  l r,
(Free_State F)= None-> 
State_eval_dstate F mu -> 
State_eval_dstate F (d_reduced mu l r).
Proof. induction mu; intros. simpl in *.  destruct H0.
       destruct a.   inversion_clear H0.  destruct mu.
       simpl in *. econstructor.  
       eapply Pure_free_eval'. assumption. apply H1.
       econstructor. destruct s0.   
       simpl. econstructor.   
       eapply Pure_free_eval'. assumption. apply H1.
       apply IHmu. assumption. assumption.
Qed.  




(*---------------------------------seman_eq-------------------------------------------*)
Lemma Pure_dom: forall F, 
option_beq (Free_State F) None = true ->
fst (option_free (Free_State F)) = snd (option_free (Free_State F)).
Proof.  induction F; simpl. intuition.  induction qs; simpl. intro. 
        discriminate. discriminate.
        destruct (option_beq (Free_State F1) None)  eqn:E. auto. 
        destruct (option_beq (Free_State F2) None) eqn:E1. intros. rewrite E in H.  auto.
        simpl. intros. discriminate. 
        destruct (option_beq (Free_State F1) None)  eqn:E. auto. 
        destruct (option_beq (Free_State F2) None) eqn:E1. intros. rewrite E in H.  auto.
        simpl. intros. discriminate. auto.
Qed.


 


Lemma Reduced_id{s e : nat}: forall (l r : nat) (q : qstate s e),
s<=r->
l=r -> 
r<=e->
@WF_Matrix (2^(e-s)) (2^(e-s)) q->
Reduced q l r = c_to_Vector1 (@trace (2^(e-s)) q).
Proof. intros. rewrite Ptrace_l_r'. rewrite H0. rewrite Nat.sub_diag. simpl.
rewrite <-trace_base. rewrite big_sum_double_sum.  
assert(2 ^ (e - r) * 2 ^ (r - s)=2 ^ (e - s)). type_sovle'.  rewrite H3.
apply big_sum_eq_bounded. intros. Msimpl. f_equal; rewrite mul_1_r. type_sovle'.
f_equal; type_sovle'. rewrite <-H3. admit. apply base_kron. assumption. lia.  
Admitted.

  
Lemma inter_empty:forall x y ,
NSet.Equal x NSet.empty \/ NSet.Equal y NSet.empty->
NSet.Equal (NSet.inter x y) NSet.empty.
Proof. unfold NSet.Equal. intros. 
      destruct H. 
      split. intros. apply H. 
      apply NSet.inter_1 in H0. assumption.
      intros. inversion_clear H0.
      split. intros. apply H. 
      apply NSet.inter_2 in H0. assumption.
      intros. inversion_clear H0.
Qed. 

Lemma smean_odot_eq_P{s e:nat}: forall F1 F2 c (q:qstate s e),
(Free_State F1)= None /\  (Free_State F2)=None ->
WF_qstate q-> 
(State_eval (F1 ⊙ F2) (c, q)) <-> 
exists s1 e1 s2 e2 (q1:qstate s1 e1) (q2:qstate s2 e2), 
((s<=s1 /\ s1<=e1/\e1=s2/\ s2<=e2 /\ e2<=e)  /\ q_combin' q1 q2 (@Reduced s e q  s1 e2)) /\ 
State_eval F1 (c, q1) /\ State_eval F2 (c, q2).
Proof. intros. split; intros. exists s. exists s. exists s. exists s.
assert( NZ_Mixed_State (I (2^(s-s)))).  rewrite <-Mscale_1_l. apply NZ_Pure_S. lra.
rewrite Nat.sub_diag. simpl.
 apply pure_id1.
exists (I (2^(s-s))).   exists (c_to_Vector1 (@trace (2^(e-s)) q)).
split.
 rewrite (Reduced_id s s); try lia; try apply H0; auto_wf.
 assert( I 1= I (2^(s-s))).   rewrite Nat.sub_diag. simpl. reflexivity. split. destruct H0. lia.     
  rewrite <-(@kron_1_l (2^(s-s)) (2^(s-s))). 
  rewrite H3.    econstructor; try reflexivity. 
         split; try lia. assumption. 
         unfold c_to_Vector1.  split; try lia. rewrite H3. 
         apply (@nz_Mixed_State_scale_c  (2 ^ (s - s))). assumption. 
         apply nz_mixed_state_trace_in01. apply H0. 
         apply nz_mixed_state_trace_real. apply H0. 
         unfold c_to_Vector1.   
         rewrite Nat.sub_diag. simpl. 
         apply (@WF_scale 1 1). auto_wf. 
        split.  apply (@Pure_free_eval' s e ) with q. apply H. 
         simpl in H1. apply H1.
        apply (@Pure_free_eval' s e ) with q. apply H.  
        simpl in H1. apply H1. 
destruct H1. destruct H1. destruct H1. destruct H1. destruct H1.
destruct H1.  destruct H1. destruct H1. simpl. split. apply inter_empty.
left. admit.
split. 
apply (@Pure_free_eval' x x0 ) with x3. apply H.  apply H2. subst. 
apply (@Pure_free_eval' x1 x2 ) with x4. apply H.   apply H2. 
Admitted.


Lemma smean_odot_eq_P_l{s e:nat}: forall F1 F2 c (q:qstate s e),
(Free_State F1)= None /\ (fst (option_free (Free_State F2)) < snd (option_free (Free_State F2))) ->
WF_qstate q-> 
(State_eval (F1 ⊙ F2) (c, q)) <-> 
exists s1 e1 s2 e2 (q1:qstate s1 e1) (q2:qstate s2 e2), 
( (s<=s1 /\ s1<=e1/\e1=s2/\ s2<=e2 /\ e2<=e)  /\ q_combin' q1 q2 (@Reduced s e q  s1 e2)) /\ 
State_eval F1 (c, q1) /\ State_eval F2 (c, q2).
Proof. intros. split; intros. 
simpl in H1. destruct H1. destruct H2. 
pose(State_eval_dom F2 c q  H3). destruct o. 
assert(option_beq (( (Free_State F2))) None = true). rewrite H4. reflexivity.
 apply Pure_dom in H5.  lia.  
 destruct H4.  remember (fst (option_free (Free_State F2))) as l. 
 remember (snd (option_free (Free_State F2))) as r. 
exists l. exists l. exists l.  exists r.    
exists (I (2^(l-l))).  exists ((Reduced q l r)). split. split. lia.
assert((Reduced q l r) = @kron _ _ (2^(r-l)) (2^(r-l)) (I (2 ^ (l - l)))  (Reduced q l r)). 
rewrite Nat.sub_diag. simpl.  
 rewrite (@kron_1_l ). reflexivity. apply WF_Reduced. lia. auto_wf. rewrite H6 at 2. 
 econstructor; try reflexivity.  rewrite Nat.sub_diag. simpl.
 econstructor. rewrite <-Mscale_1_l. apply NZ_Pure_S. lra. 
 rewrite Nat.sub_diag. simpl. apply pure_id1. lia. 
 apply WF_qstate_Reduced. lia. assumption. 
 split. apply (@Pure_free_eval' s e ) with q. apply H. assumption. 
 apply (@State_free_eval s e F2 (c,q) l r).  lia. lia. 
 auto_wf. assumption. destruct H1. destruct H1. destruct H1. destruct H1. destruct H1.
 destruct H1.  destruct H1. destruct H1. simpl. split. apply inter_empty. admit.
 split.  apply (@Pure_free_eval' x x0 ) with x3. apply H.  apply H2.
 
  inversion H3; subst. destruct H2. 
  pose(State_eval_dom F2 c x4 H5). destruct o.  
  assert(option_beq (( (Free_State F2))) None = true). rewrite H9. reflexivity.
   apply Pure_dom in H10.  lia. destruct H9.   
 apply (@State_free_eval s e F2 _ x x2).  lia.  lia.    
 auto_wf.  simpl.    rewrite <-H4.    
 rewrite (@State_free_eval x x2 F2 _ x1 x2); try  lia; try auto_wf.   
 simpl. rewrite Reduced_R; try lia.    
 rewrite (Reduced_tensor_r _ x3 x4); try auto_wf; try reflexivity. 
 admit.
 apply WF_kron;type_sovle';  auto_wf. 
 apply WF_kron;type_sovle';  auto_wf. 
Admitted.


Lemma smean_odot_eq_P_r{s e:nat}: forall F1 F2 c (q:qstate s e),
(Free_State F2)= None /\ (fst (option_free (Free_State F1)) < snd (option_free (Free_State F1))) ->
WF_qstate q-> 
(State_eval (F1 ⊙ F2) (c, q)) <-> 
exists s1 e1 s2 e2 (q1:qstate s1 e1) (q2:qstate s2 e2), 
( (s<=s1 /\ s1<=e1/\e1=s2/\ s2<=e2 /\ e2<=e)  /\ q_combin' q1 q2 (@Reduced s e q  s1 e2)) /\ 
State_eval F1 (c, q1) /\ State_eval F2 (c, q2).
Proof. intros. split; intros. 
simpl in H1. destruct H1. destruct H2. 
pose(State_eval_dom F1 c q  H2). destruct o. 
assert(option_beq (( (Free_State F1))) None = true). rewrite H4. reflexivity.
 apply Pure_dom in H5.  lia.  
 destruct H4.  remember (fst (option_free (Free_State F1))) as l. 
 remember (snd (option_free (Free_State F1))) as r. 
exists l. exists r. exists r.  exists r.    
  exists ((Reduced q l r)). exists (I (2^(r-r))). split. split. lia.
assert((Reduced q l r) = @kron (2^(r-l)) (2^(r-l)) _ _  (Reduced q l r) (I (2 ^ (r - r))) ). 
rewrite Nat.sub_diag. simpl.  
 rewrite (@kron_1_r). reflexivity.  rewrite H6 at 2. 
 econstructor; try reflexivity. 
 apply WF_qstate_Reduced. lia. assumption. 
 rewrite Nat.sub_diag. simpl.
 econstructor. rewrite <-Mscale_1_l. apply NZ_Pure_S. lra. 
 rewrite Nat.sub_diag. simpl. apply pure_id1. lia.  
 split. 
 apply (@State_free_eval s e F1 (c,q) l r).  lia. lia. 
 auto_wf. assumption. apply (@Pure_free_eval' s e ) with q. apply H. assumption. 
  destruct H1. destruct H1. destruct H1. destruct H1. destruct H1.
 destruct H1.  destruct H1. destruct H1. simpl. split. apply inter_empty. admit.
 split.   inversion H3; subst. destruct H2. 
 pose(State_eval_dom F1 c x3 H2). destruct o.  
 assert(option_beq (( (Free_State F1))) None = true). rewrite H9. reflexivity.
  apply Pure_dom in H10.  lia. destruct H9.   
apply (@State_free_eval s e F1 _ x x2).  lia.  lia.    
auto_wf.  simpl.    rewrite <-H4.    
rewrite (@State_free_eval x x2 F1 _ x x1); try  lia; try auto_wf.   
simpl. rewrite Reduced_L; try lia.    
rewrite (Reduced_tensor_l _ x3 x4); try auto_wf; try reflexivity. 
admit.
apply WF_kron;type_sovle';  auto_wf. 
apply WF_kron;type_sovle';  auto_wf. 
 apply (@Pure_free_eval' x1 x2 ) with x4. apply H.  apply H2.
Admitted.

Definition F1_lt_F2 F1 F2 := 
(fst (option_free (Free_State F1)) < snd (option_free (Free_State F1)) ->
fst (option_free (Free_State F2)) < snd (option_free (Free_State F2) ) ->
(snd (option_free (Free_State F1)) = (fst (option_free (Free_State F2)))) ) .


Lemma smean_odot_eq{s e:nat}: forall F1 F2 c (q:qstate s e),
Considered_Formula (F1 ⊙ F2) ->
WF_qstate q->
(State_eval (F1 ⊙ F2) (c, q) /\ F1_lt_F2 F1 F2) <-> 
exists s1 e1 s2 e2 
(q1:qstate s1 e1) 
(q2:qstate s2 e2), 
((s<=s1 /\ s1<=e1/\e1=s2/\ s2<=e2 /\ e2<=e) /\ 
q_combin' q1 q2 (@Reduced s e q  s1 e2)) /\ 
State_eval F1 (c, q1) /\ State_eval F2 (c, q2).  
Proof. intros.   split; intros. 
       simpl in H. 
       destruct (option_beq (Free_State F1) None)  eqn:E. 
       destruct (option_beq (Free_State F2) None)  eqn:E1.
       apply smean_odot_eq_P. admit. assumption. apply H1. 
       apply smean_odot_eq_P_l. admit. assumption. apply H1.
       destruct (option_beq (Free_State F2) None)  eqn:E1.
       apply smean_odot_eq_P_r. admit. assumption. apply H1.  

       simpl in H1. destruct H1. destruct H1. destruct H3. 
       pose (@State_eval_dom s e F1 c q H3). 
       pose (@State_eval_dom s e F2 c q H4). 
       
       destruct H. destruct H5.  
       assert(Free_State F1 <> None ). apply option_eqb_neq. assumption. 
       assert(Free_State F2 <> None ). apply option_eqb_neq. assumption.
       
       destruct o. destruct H7. assumption. 
       destruct o0. destruct H8. assumption.  destruct H9.
       destruct H10.

       destruct H6. 
       exists (fst (option_free (Free_State F1))). 
       exists (snd (option_free (Free_State F1))).
       exists (fst (option_free (Free_State F2))). 
       exists (snd (option_free (Free_State F2))).
  
        assert(Considered_Formula F1 /\
        snd (option_free (Free_State F2)) <= e /\
        snd (option_free (Free_State F1)) <= snd (option_free (Free_State F2)) /\
        fst (option_free (Free_State F1)) < snd (option_free (Free_State F1))).
        split. assumption. lia. 
        pose (@State_eval_separ_r s e F1 (snd (option_free (Free_State F2))) c q H13 H0 H3).
        destruct e0. destruct H14. exists x. exists x0.  split. 
        split. lia.   rewrite <-H6 . assumption. 
        inversion H14; subst.  
        symmetry  in H15. pose H15.
        apply Reduced_tensor_l in e0;  try  apply WF_Reduced; try lia; auto_wf. 
        rewrite <-Reduced_L in e0;try  apply WF_Reduced; try lia; auto_wf.
        apply Reduced_tensor_r in H15; try  apply WF_Reduced; try lia; auto_wf.
        rewrite <-Reduced_R in H15; try  apply WF_Reduced; try lia; auto_wf.
        split. 
        remember ((Nat.pow (S (S O)) (Init.Nat.sub
       (@snd nat nat (option_free (Free_State F2)))
       (@snd nat nat (option_free (Free_State F1)))))).
    
        rewrite (s_seman_scale_c _ ( (@trace n x0))).  rewrite <-e0. 
        rewrite Reduced_assoc; try lia. 
        rewrite <-(@State_free_eval s e F1 (c, q) (fst (option_free (Free_State F1)))
        (snd (option_free (Free_State F1)))); try lia. assumption. 
        auto_wf. split. apply nz_mixed_state_trace_gt0. rewrite Heqn. apply H22.
        apply nz_mixed_state_trace_real. rewrite Heqn. apply H22. 
        
        remember ((Nat.pow (S (S O)) (Init.Nat.sub
       (@snd nat nat (option_free (Free_State F1)))
       (@fst nat nat (option_free (Free_State F1)))))).
      
        rewrite (s_seman_scale_c _ ( (@trace n x))). rewrite <-H6.  rewrite <-H15. 
        rewrite Reduced_assoc; try lia.  
        rewrite <-(@State_free_eval s e F2 (c, q) (snd (option_free (Free_State F1)))
        (snd (option_free (Free_State F2)))); try lia. assumption. 
        auto_wf. split. apply nz_mixed_state_trace_gt0. rewrite Heqn. apply H19.
        apply nz_mixed_state_trace_real. rewrite Heqn.  apply H19. 
        
      unfold F1_lt_F2 in *. lia.   

       
        simpl in H.  
        destruct (option_beq (Free_State F1) None)  eqn:E. 
        destruct (option_beq (Free_State F2) None)  eqn:E1.
        split.
        apply smean_odot_eq_P. admit. assumption.  apply H1. 
        destruct H1. destruct H1. destruct H1. destruct H1. destruct H1.
        destruct H1. destruct H1. destruct H2.    
        apply smean_odot_eq_P_r. admit. assumption. apply H1.  
 
        simpl in H1. destruct H1. destruct H1. destruct H3. 
        pose (@State_eval_dom s e F1 c q H3). 
        pose (@State_eval_dom s e F2 c q H4). 
      
       assert(Free_State F1 <> None ). intro. 
       assert(option_beq (Free_State F1) None= true).
       rewrite H5. reflexivity. apply Pure_dom in H6. lia.
       assert(Free_State F2 <> None ). intro. 
       assert(option_beq (Free_State F2) None= true).
       rewrite H6. reflexivity. apply Pure_dom in H7. lia.
  
       destruct (option_beq (Free_State F1) None)  eqn:E.
       apply option_eqb_neq in H5. rewrite E in H5 . discriminate.
       destruct (option_beq (Free_State F2) None)  eqn:E1.
       apply option_eqb_neq in H6. rewrite E1 in H6. discriminate.


       pose (@State_eval_dom x x0 F1 c x3 H2). 
        pose (@State_eval_dom x1 x2 F2 c x4 H3).

       destruct H. destruct H7. 
       destruct o. destruct H5. assumption. 
       destruct o0. destruct H6. assumption.  destruct H9.
       destruct H10. destruct H8.   
        destruct H1.
        inversion H13; subst. 
        simpl. split.   split.  admit.    


       
       split.    
       apply (@State_free_eval s e F1 _ x x2).  lia. lia.   
       auto_wf.  simpl.  rewrite <-H14. 
       rewrite (@State_free_eval x x2 F1 _ x x1); try  lia; try auto_wf.   
       simpl. rewrite Reduced_L; try lia.    
       rewrite (Reduced_tensor_l _ x3 x4); try auto_wf; try reflexivity.
       admit.  
       apply WF_kron;type_sovle';  auto_wf. 
       apply WF_kron;type_sovle';  auto_wf. 
         
       
       apply (@State_free_eval s e F2 _ x x2).  lia. lia.   
       auto_wf.  simpl.  rewrite <-H14. 
       rewrite (@State_free_eval x x2 F2 _ x1 x2); try  lia; try auto_wf.   
       simpl. rewrite Reduced_R; try lia. 
       rewrite (Reduced_tensor_r _ x3 x4); try auto_wf; try reflexivity. 
       admit. 
       apply WF_kron;type_sovle';  auto_wf. 
       apply WF_kron;type_sovle';  auto_wf. 
       lia. lia.   


       

       (*  *)

(* Lemma smean_odot_eq_r{s e:nat}: forall F1 F2 c (q:qstate s e),
Considered_Formula (F1 ⊙ F2) /\
(s<=  fst (option_free (Free_State F1)) /\
snd (option_free (Free_State F1)) = (fst (option_free (Free_State F2)))/\
snd (option_free (Free_State F2)) < e)->
WF_qstate q->
State_eval (F1 ⊙ F2) (c, q) <-> 
exists 
(q1:qstate (fst (option_free (Free_State F1))) (snd (option_free (Free_State F1))))
(q2:qstate  (fst (option_free (Free_State F2))) (snd (option_free (Free_State F2)))), 
(q_combin' q1 q2 (@Reduced s e q  (fst (option_free (Free_State F1))) (snd (option_free (Free_State F2))))) /\ 
State_eval F1 (c, q1) /\ State_eval F2 (c, q2).
Proof. intros.  split; intros. simpl in H1. destruct H1. destruct H2.  destruct H.
       simpl in H. destruct (option_beq (Free_State F1) None) eqn:E.
       apply Pure_dom in E. rewrite E. destruct H4.  destruct H5. rewrite H5.
       destruct (option_beq (Free_State F2) None) eqn:E1.
       apply Pure_dom in E1. rewrite E1. 
       remember ((Nat.pow (S (S O)) (Init.Nat.sub
       (@snd nat nat (option_free (Free_State F2)))
       (@snd nat nat (option_free (Free_State F2)))))).
       exists (I n). exists (c_to_Vector1 (@trace (2^(e-s)) q)). split.
         rewrite (@Reduced_id s e ((snd (option_free (Free_State F2))))); try lia; auto_wf.
         assert(n=1). rewrite Heqn. rewrite Nat.sub_diag.
         simpl. reflexivity.  rewrite <-(@kron_1_l n n ). rewrite <-H7.
          rewrite Heqn.  
           econstructor; try reflexivity. rewrite Nat.sub_diag. simpl.
          econstructor. rewrite <-Mscale_1_l. apply NZ_Pure_S. lra. 
          rewrite Nat.sub_diag. simpl. apply pure_id1. lia. 
         unfold c_to_Vector1.  split.   
         assert( I 1 = I (2
         ^ (snd (option_free (Free_State F2)) - snd (option_free (Free_State F2))))).
         rewrite Nat.sub_diag. simpl. reflexivity. Set Printing All.
         apply (@nz_Mixed_State_scale_c ((2 
         ^ (snd (option_free (Free_State F2)) - snd (option_free (Free_State F2)))))).
         rewrite <-Mscale_1_l. apply NZ_Pure_S. lra. 
         rewrite Nat.sub_diag. simpl. apply pure_id1.  
         apply nz_mixed_state_trace_in01. rewrite<- Heqn.
         rewrite H7.  apply H0. 
         apply nz_mixed_state_trace_real. rewrite<- Heqn.
         rewrite H7.  apply H0. lia.  unfold c_to_Vector1. 
         assert( I 1 = I (n)). rewrite H7. reflexivity. rewrite H8.
         apply (@WF_scale n n). auto_wf. 
        split.  apply (@Pure_free_eval' s e ) with q. admit. assumption. 
        apply (@Pure_free_eval' s e ) with q. admit. assumption.
  
       remember ((Nat.pow (S (S O)) (Init.Nat.sub
       (@fst nat nat (option_free (Free_State F2)))
       (@fst nat nat (option_free (Free_State F2)))))). 
       remember ((Nat.pow (S (S O)) (Init.Nat.sub
       (@snd nat nat (option_free (Free_State F2)))
       (@fst nat nat (option_free (Free_State F2)))))).
       exists (I n).  exists ((Reduced q (fst (option_free (Free_State F2)))
       (snd (option_free (Free_State F2))))).  
       split. assert(n=1). rewrite Heqn. rewrite Nat.sub_diag.
       simpl. reflexivity.  rewrite <-(@kron_1_l n0 n0 ). rewrite <-H7.
        rewrite Heqn. rewrite Heqn0.   
        econstructor; try reflexivity. rewrite Nat.sub_diag. simpl.
        econstructor. rewrite <-Mscale_1_l. apply NZ_Pure_S. lra. 
        rewrite Nat.sub_diag. simpl. apply pure_id1. lia. 
        apply WF_qstate_Reduced. pose(Considered_Formula_dom F2 H). 
       lia. assumption. 
        rewrite Heqn0.  
        apply WF_Reduced. pose(Considered_Formula_dom F2 H). lia. auto_wf.  
        split. apply (@Pure_free_eval' s e ) with q. admit. assumption. 
        apply (@State_free_eval s e F2 (c,q) (fst (option_free (Free_State F2)))
        (snd (option_free (Free_State F2)))). pose(Considered_Formula_dom F2 H). lia. lia.
        auto_wf. assumption.   
        destruct (option_beq (Free_State F2) None) eqn:E1.
       apply Pure_dom in E1. rewrite<-E1. destruct H4. destruct H5. rewrite <-H5.   
       remember ((Nat.pow (S (S O)) (Init.Nat.sub
       (@snd nat nat (option_free (Free_State F1)))
       (@snd nat nat (option_free (Free_State F1)))))). 
       remember ((Nat.pow (S (S O)) (Init.Nat.sub
       (@snd nat nat (option_free (Free_State F1)))
       (@fst nat nat (option_free (Free_State F1)))))).
        exists ((Reduced q (fst (option_free (Free_State F1)))
       (snd (option_free (Free_State F1))))).   exists (I n).
       split. assert(n=1). rewrite Heqn. rewrite Nat.sub_diag.
       simpl. reflexivity.  rewrite <-(@kron_1_r n0 n0 ). rewrite <-H7.
        rewrite Heqn. rewrite Heqn0.   
        econstructor; try reflexivity. 
        apply WF_qstate_Reduced. pose(Considered_Formula_dom F1 H). lia.
        assumption.
        rewrite Nat.sub_diag. simpl.
        econstructor. rewrite <-Mscale_1_l. apply NZ_Pure_S. lra. 
        rewrite Nat.sub_diag. simpl. apply pure_id1. lia.   
        split.
        apply (@State_free_eval s e F1 (c,q) (fst (option_free (Free_State F1)))
        (snd (option_free (Free_State F1)))). pose(Considered_Formula_dom F1 H). lia. lia.
        auto_wf. assumption.   
        eapply Pure_free_eval'. admit. apply H3. 
        destruct H. destruct H5.   
        pose(Considered_Formula_dom F1 H).
        pose(Considered_Formula_dom F2 H5).
        pose(@State_eval_dom s e F1 c q H2). destruct o. rewrite H7 in *.
        simpl in *. discriminate.   
        assert(Considered_Formula F1 /\
        snd (option_free (Free_State F2)) <= e /\
        snd (option_free (Free_State F1)) <= snd (option_free (Free_State F2)) /\
        fst (option_free (Free_State F1)) < snd (option_free (Free_State F1))).
        split. assumption. destruct H7. lia.
        pose (@State_eval_separ_r s e F1 (snd (option_free (Free_State F2))) c q H8 H0 H2).
        destruct e0. destruct H9. exists x. exists x0.  split. 
        destruct H4. destruct H10.
        rewrite <-H10. assumption. 
        inversion H9; subst.  
        symmetry  in H10. pose H10.
        apply Reduced_tensor_l in e0;  try  apply WF_Reduced; try lia; auto_wf. 
        rewrite <-Reduced_L in e0;try  apply WF_Reduced; try lia; auto_wf.
        apply Reduced_tensor_r in H10; try  apply WF_Reduced; try lia; auto_wf.
        rewrite <-Reduced_R in H10; try  apply WF_Reduced; try lia; auto_wf.
        split. 
        remember ((Nat.pow (S (S O)) (Init.Nat.sub
       (@snd nat nat (option_free (Free_State F2)))
       (@snd nat nat (option_free (Free_State F1)))))).
        assert(@trace n x0 = (fst (@trace n x0) , snd (@trace n x0))).
        destruct (@trace n x0). reflexivity. 
        assert(snd (@trace n x0)= 0%R ). apply nz_mixed_state_trace_real.
        rewrite Heqn.  apply H17.  rewrite H16 in H15.  rewrite H15 in e0. 

        rewrite (s_seman_scale _ (fst (@trace n x0))). unfold s_scale. simpl in *. 
        unfold q_scale. unfold RtoC.  rewrite <-e0. 
        rewrite Reduced_assoc; try lia. 
        rewrite <-(@State_free_eval s e F1 (c, q) (fst (option_free (Free_State F1)))
        (snd (option_free (Free_State F1)))); try lia. assumption. 
        auto_wf. apply nz_mixed_state_trace_gt0. rewrite Heqn. apply H17.
        
        remember ((Nat.pow (S (S O)) (Init.Nat.sub
       (@snd nat nat (option_free (Free_State F1)))
       (@fst nat nat (option_free (Free_State F1)))))).
        assert(@trace n x = (fst (@trace n x) , snd (@trace n x))).
        destruct (@trace n x). reflexivity. 
        assert(snd (@trace n x)= 0%R ). apply nz_mixed_state_trace_real. 
        rewrite Heqn. apply H14.   rewrite H16 in H15.  rewrite H15 in H10.
        destruct H4. destruct H18.  

        rewrite (s_seman_scale _ (fst (@trace n x))). unfold s_scale. simpl in *. 
        unfold q_scale. unfold RtoC.  rewrite <-H18.  rewrite <-H10. 
        rewrite Reduced_assoc; try lia.  
        rewrite <-(@State_free_eval s e F2 (c, q) (snd (option_free (Free_State F1)))
        (snd (option_free (Free_State F2)))); try lia. assumption. 
        auto_wf. apply nz_mixed_state_trace_gt0. rewrite Heqn. apply H14.

        destruct H1. destruct H1. destruct H1. 
        inversion H1; subst. 
        destruct H.  simpl in H. 
        simpl. split.  admit.   
        destruct (option_beq (Free_State F1) None) eqn:E. 
        assert((Free_State F1)= None). apply Classical_Prop.NNPP. intro.
        apply option_eqb_neq in H9. rewrite E in H9. discriminate. 
        apply (Pure_free_eval' _ c x q) in H9; try apply H2. split. assumption.
        apply Considered_Formula_dom in H. apply Pure_dom in E.
        destruct H8. destruct H11. 
       apply (@State_free_eval s e F2 _ (fst (option_free (Free_State F1)))
       (snd (option_free (Free_State F2)))).  lia. lia.   
       auto_wf.  simpl.  rewrite <-H3. 
       rewrite (@State_free_eval (fst (option_free (Free_State F1)))
       (snd (option_free (Free_State F2))) F2 _ (fst (option_free (Free_State F2)))
       (snd (option_free (Free_State F2)))); try  lia; try auto_wf.   
       simpl. rewrite Reduced_R; try lia.  rewrite <-H11.  
       rewrite (Reduced_tensor_r _ x x0); try auto_wf; try reflexivity. 

       admit. rewrite H11. auto_wf. 
       apply WF_kron;type_sovle';  auto_wf. try rewrite H11; auto_wf.
       apply WF_kron;type_sovle';  auto_wf. 
       apply WF_kron;type_sovle';  auto_wf.
      
       destruct (option_beq (Free_State F2) None) eqn:E1. 
        assert((Free_State F2)= None). apply Classical_Prop.NNPP. intro.
        apply option_eqb_neq in H9. rewrite E1 in H9. discriminate. 
        apply (Pure_free_eval' _ c x0 q) in H9; try apply H2. split.
        apply Considered_Formula_dom in H. apply Pure_dom in E1.
        destruct H8. destruct H11. 
       apply (@State_free_eval s e F1 _ (fst (option_free (Free_State F1)))
       (snd (option_free (Free_State F2)))).  lia. lia.   
       auto_wf.  simpl.  rewrite <-H3. 
       rewrite (@State_free_eval (fst (option_free (Free_State F1)))
       (snd (option_free (Free_State F2))) F1 _ (fst (option_free (Free_State F1)))
       (snd (option_free (Free_State F1)))); try  lia; try auto_wf.   
       simpl. rewrite Reduced_L; try lia.  rewrite <-H11.  
       rewrite (Reduced_tensor_l _ x x0); try auto_wf; try reflexivity.  
       admit.  rewrite H11. auto_wf. 
       apply WF_kron;type_sovle';  auto_wf. try rewrite H11; auto_wf.
       apply WF_kron;type_sovle';  auto_wf. 
       apply WF_kron;type_sovle';  auto_wf. assumption.
       
       destruct H. destruct H9. 
       apply Considered_Formula_dom in H.    
       apply Considered_Formula_dom in H9. destruct H8. destruct H12.    
       split.    
       apply (@State_free_eval s e F1 _ (fst (option_free (Free_State F1)))
       (snd (option_free (Free_State F2)))).  lia. lia.   
       auto_wf.  simpl.  rewrite <-H3. 
       rewrite (@State_free_eval (fst (option_free (Free_State F1)))
       (snd (option_free (Free_State F2))) F1 _ (fst (option_free (Free_State F1)))
       (snd (option_free (Free_State F1)))); try  lia; try auto_wf.   
       simpl. rewrite Reduced_L; try lia.  rewrite <-H12.  
       rewrite (Reduced_tensor_l _ x x0); try auto_wf; try reflexivity.  
       admit.  rewrite H12. auto_wf. 
       apply WF_kron;type_sovle';  auto_wf. try rewrite H12; auto_wf.
       apply WF_kron;type_sovle';  auto_wf. 
       apply WF_kron;type_sovle';  auto_wf.
       
       apply (@State_free_eval s e F2 _ (fst (option_free (Free_State F1)))
       (snd (option_free (Free_State F2)))).  lia. lia.   
       auto_wf.  simpl.  rewrite <-H3. 
       rewrite (@State_free_eval (fst (option_free (Free_State F1)))
       (snd (option_free (Free_State F2))) F2 _ (fst (option_free (Free_State F2)))
       (snd (option_free (Free_State F2)))); try  lia; try auto_wf.   
       simpl. rewrite Reduced_R; try lia.  rewrite <-H12.  
       rewrite (Reduced_tensor_r _ x x0); try auto_wf; try reflexivity. 
       admit. rewrite H12. auto_wf. 
       apply WF_kron;type_sovle';  auto_wf. try rewrite H12; auto_wf.
       apply WF_kron;type_sovle';  auto_wf. 
       apply WF_kron;type_sovle';  auto_wf.
        *)






