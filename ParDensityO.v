Require Import Psatz.
Require Import Reals.
From Quan Require Export VecSet.
From Quan Require Export Quantum.


Notation Density n := (Matrix n n) (only parsing). 

Definition Classical {n} (ρ : Density n) := forall i j, i <> j -> ρ i j = 0.

Definition Pure_State_Vector {n} (φ : Vector n): Prop := 
   WF_Matrix φ /\ φ† × φ = I  1.

Definition Pure_State {n} (ρ : Density n) : Prop := 
  exists φ,  Pure_State_Vector φ /\ ρ = (φ × φ†). 

Inductive Mixed_State {n} : Matrix n n -> Prop :=
| Pure_S : forall ρ (p:R), (0 < p <= 1)-> Pure_State ρ -> Mixed_State (p.* ρ) 
| Mix_S : forall (p1 p2: R) ρ1 ρ2, 0 < p1 <=1-> 0 < p2 <=1 -> p1+p2<=1
-> Mixed_State ρ1 -> Mixed_State ρ2 ->Mixed_State (p1 .* ρ1 .+ p2 .* ρ2).  

Lemma WF_Pure : forall {n} (ρ : Density n), Pure_State ρ -> WF_Matrix ρ.
Proof. intros. destruct H as [φ [[WFφ IP1] Eρ]]. rewrite Eρ. auto with wf_db. Qed.
#[export] Hint Resolve WF_Pure : wf_db.

Lemma WF_Mixed : forall {n} (ρ : Density n), Mixed_State ρ -> WF_Matrix ρ.
Proof.  induction 1; auto with wf_db. Qed.
#[export] Hint Resolve WF_Mixed : wf_db.

Lemma pure0 : Pure_State ∣0⟩⟨0∣. 
Proof. exists ∣0⟩. intuition. split. auto with wf_db. solve_matrix. Qed.

Lemma pure1 : Pure_State ∣1⟩⟨1∣. 
Proof. exists ∣1⟩. intuition. split. auto with wf_db.
solve_matrix. Qed.

Lemma pure_id1 : Pure_State (I  1).
Proof. exists (I  1). split. split. auto with wf_db. solve_matrix. solve_matrix. Qed.
 
Lemma pure_dim1 : forall (ρ : Square 1), Pure_State ρ -> ρ = I 1.
Proof.
  intros. 
  assert (H' := H).
  apply WF_Pure in H'.
  destruct H as [φ [[WFφ IP1] Eρ]]. 
  apply Minv_flip in IP1; auto with wf_db.
  rewrite Eρ; easy.
Qed.

Local Open Scope C_scope.
Lemma mixed_dim1 : forall (ρ : Square 1), Mixed_State ρ -> exists p, ρ =p .*  I  1.
Proof.
  intros.  
  induction H. 
  + exists p. f_equal. apply pure_dim1; trivial.
  + destruct IHMixed_State1. destruct IHMixed_State2.
    exists (p1*x + p2*x0). rewrite H4, H5.
    prep_matrix_equality.
    lca.
Qed.

Lemma pure_state_vector_unitary_pres : forall {n} (ϕ : Vector n) (U : Square n),
  Pure_State_Vector ϕ -> WF_Unitary U -> Pure_State_Vector (U × ϕ).
Proof. 
  unfold Pure_State_Vector.
  intros n ϕ U [H H0] [H1 H2].
  split; auto with wf_db.
  distribute_adjoint.
  rewrite Mmult_assoc, <- (Mmult_assoc _ U), H2, Mmult_1_l; auto.
Qed.

Lemma mixed_unitary : forall {n} (U ρ : Matrix n n), 
  WF_Unitary U -> Mixed_State ρ -> Mixed_State (super U ρ).
  Proof.
  intros n U ρ H M.
  induction M.
  + unfold super. rewrite Mscale_mult_dist_r.
    rewrite Mscale_mult_dist_l.
    apply Pure_S. intuition.
    apply pure_unitary; trivial.
  + unfold WF_Unitary, super in *.
    rewrite Mmult_plus_distr_l.
    rewrite Mmult_plus_distr_r.
    rewrite 2 Mscale_mult_dist_r.
    rewrite 2 Mscale_mult_dist_l.
    apply Mix_S; trivial.
Qed.


Lemma pure_state_vector_kron : forall {n m} (ϕ : Vector n) (ψ : Vector m),
  Pure_State_Vector ϕ -> Pure_State_Vector ψ -> Pure_State_Vector (ϕ ⊗ ψ).
Proof.
  unfold Pure_State_Vector.
  intros n m ϕ ψ [WFu Pu] [WFv Pv].
  split.
  - apply WF_kron; auto.
  - Msimpl. rewrite Pu, Pv. Msimpl. easy.
Qed.
                              
Lemma pure_state_kron : forall m n (ρ : Square m) (φ : Square n),
  Pure_State ρ -> Pure_State φ -> Pure_State (ρ ⊗ φ).
Proof.
  intros m n ρ φ [u [? Eρ]] [v [? Eφ]].
  exists (u ⊗ v).
  split.
  - apply pure_state_vector_kron; auto.
  - Msimpl. subst. easy.
Qed.

Lemma mixed_state_kron : forall m n (ρ : Square m) (φ : Square n),
  Mixed_State ρ -> Mixed_State φ -> Mixed_State (ρ ⊗ φ).
Proof.
  intros m n ρ φ Mρ Mφ.
  induction Mρ.
  induction Mφ.
  - rewrite Mscale_kron_dist_r. 
    rewrite Mscale_kron_dist_l.
    rewrite Mscale_assoc.
    assert(Cmult (RtoC p0) (RtoC p)=RtoC (p0 * p)).
    unfold RtoC. unfold Cmult. simpl.
     repeat rewrite Rmult_0_r.
    rewrite Rmult_0_l. rewrite Rplus_0_l.
     rewrite Rminus_0_r.
    reflexivity. rewrite H3. apply Pure_S.
    split. 
    apply Rmult_gt_0_compat. intuition. intuition.
    assert(p0 * p <= 1*1). apply Rmult_le_compat.
    intuition. intuition. intuition. intuition.
    intuition. rewrite Rmult_1_r in H4. intuition.
    apply pure_state_kron; easy.
  - rewrite kron_plus_distr_l.
    rewrite 2 Mscale_kron_dist_r.
    apply Mix_S; easy.
  - rewrite kron_plus_distr_r.
    rewrite 2 Mscale_kron_dist_l.
    apply Mix_S; easy.
Qed.



Lemma pure_state_trace_1 : forall {n} (ρ : Density n), Pure_State ρ -> trace ρ = 1.
Proof.
  intros n ρ [u [[WFu Uu] E]]. 
  subst.
  clear -Uu.
  unfold trace.
  unfold Mmult, adjoint in *.
  simpl in *.
  match goal with
    [H : ?f = ?g |- _] => assert (f O O = g O O) by (rewrite <- H; easy)
  end. 
  unfold I in H; simpl in H.
  rewrite <- H.
  apply big_sum_eq.
  apply functional_extensionality.
  intros x.
  rewrite Cplus_0_l, Cmult_comm.
  easy.
Qed.

Lemma mixed_state_diag_in01 : forall {n} (ρ : Density n) i , Mixed_State ρ -> 
                                                        0 <= fst (ρ i i) <= 1.
Proof.
  intros.
  induction H.
  - destruct H0 as [φ [[WFφ IP1] Eρ]].
    destruct (lt_dec i n). 
    2: rewrite Eρ; unfold Mmult, adjoint; simpl; rewrite WFφ; simpl; [lra|lia].
    rewrite Eρ.
    unfold Mmult, adjoint in *.
    simpl in *.
    rewrite Rplus_0_l.
    match goal with
    [H : ?f = ?g |- _] => assert (f O O = g O O) by (rewrite <- H; easy)
    end. 
    unfold I in H. simpl in H. clear IP1.
    match goal with
    [ H : ?x = ?y |- _] => assert (H': fst x = fst y) by (rewrite H; easy); clear H
    end.
    simpl in H'.
    rewrite <- H'.    
    split.
    + unfold Rminus. rewrite <- Ropp_mult_distr_r. rewrite Ropp_involutive.
      rewrite <- Rplus_0_r at 1. rewrite Rmult_0_l. rewrite Ropp_0.
        apply Rplus_le_compat. assert((0*0)%R=0%R). apply Rmult_0_r.
        rewrite<- H0.  apply Rmult_le_compat; try intuition. 
        rewrite <- Rplus_0_r at 1.
        apply Rplus_le_compat;
       apply Rle_0_sqr. intuition.    
    + match goal with 
      [ |- ?x <= fst (big_sum ?f ?m)] => specialize (big_sum_member_le f n) as res
      end.
      simpl in *.
      unfold Rminus in *.
      rewrite <- Ropp_mult_distr_r.
      rewrite Ropp_mult_distr_l.
      rewrite Rmult_0_l. rewrite Ropp_0. rewrite Rplus_0_r.
       rewrite<- (Rmult_1_l (fst (Σ (fun y : nat => (φ y 0%nat) ^* * φ y 0%nat) n))).
       apply Rmult_le_compat. intuition.  
       unfold Rminus. rewrite <- Ropp_mult_distr_l. rewrite Ropp_involutive.
       rewrite <- Rplus_0_r at 1.
       apply Rplus_le_compat; apply Rle_0_sqr. intuition.  
      apply res with (x := i); trivial. 
      intros x.
      unfold Rminus. rewrite <- Ropp_mult_distr_l. rewrite Ropp_involutive.
      rewrite <- Rplus_0_r at 1.
      apply Rplus_le_compat; apply Rle_0_sqr.    
  - simpl.
    repeat rewrite Rmult_0_l.
    repeat rewrite Rminus_0_r.
    split.
    assert (0 <= p1 * fst (ρ1 i i)).
      apply Rmult_le_pos; lra.
    assert (0 <= p2* fst (ρ2 i i)).
      apply Rmult_le_pos; lra.
    lra.
    assert (p1 * fst (ρ1 i i) <= p1)%R. 
      rewrite <- Rmult_1_r.
      apply Rmult_le_compat_l; lra.
    assert (p2 * fst (ρ2 i i) <= p2)%R. 
      rewrite <- Rmult_1_r.
      apply Rmult_le_compat_l; lra.
    lra.
Qed.


Require Import Basic_Supplement.
Lemma mixed_state_trace_gt0: forall {n} (ρ : Density n) , Mixed_State ρ -> 
                                                        0 < fst (trace ρ).
Proof.  
intros n ρ H. 
induction H. 
- rewrite trace_mult_dist. simpl. rewrite Rmult_0_l.
  rewrite Rminus_0_r. apply Rmult_gt_0_compat.
  intuition. rewrite pure_state_trace_1. simpl. intuition.
  intuition.
- rewrite trace_plus_dist. 
 repeat rewrite trace_mult_dist.
 simpl. repeat rewrite Rmult_0_l.
 repeat rewrite Rminus_0_r.
 apply Rplus_lt_0_compat;
 apply Rmult_lt_0_compat; intuition. 
Qed.

Local Open Scope R_scope.
Lemma Rplus_mult_le_1: forall (p1 p2 r1 r2:R),
0 < p1 <=1->
0 < p2 <=1->
p1+p2<=1->
0<r1 <= 1->
0<r2<= 1->
p1 * r1 + p2 * r2<= 1 .
Proof. intros. 
assert(r1<r2\/ r2<=r1).
apply Rlt_or_le.
destruct H4.
apply Rle_trans with ((p1 * r2)%R + (p2 * r2)%R)%R.
apply Rplus_le_compat;
apply Rmult_le_compat;
intuition. 
rewrite <-Rmult_plus_distr_r. 
assert((p1 + p2) * r2 <= 1*1).
apply Rmult_le_compat. 
assert(0<p1 + p2). apply Rplus_lt_0_compat. intuition. intuition.
intuition. intuition. intuition. intuition. 
rewrite Rmult_1_l in H5.
intuition.

apply Rle_trans with (p1 * r1 + p2 * r1 ).
apply Rplus_le_compat;
apply Rmult_le_compat;
intuition. 
rewrite <-Rmult_plus_distr_r. 
assert((p1 + p2) * r1 <= 1*1).
apply Rmult_le_compat. 
assert(0<p1 + p2). apply Rplus_lt_0_compat. intuition. intuition.
intuition. intuition. intuition. intuition. 
rewrite Rmult_1_l in H5.
intuition.
Qed.


Lemma mixed_state_trace_1 : forall {n} (ρ : Density n), Mixed_State ρ ->  fst (trace ρ) <=1.
Proof.
  intros n ρ H. 
  induction H. 
  - rewrite trace_mult_dist. simpl. rewrite Rmult_0_l.
    rewrite Rminus_0_r. assert(p * fst (trace ρ) <= 1 * 1).
    apply Rmult_le_compat. intuition.
    assert(0 < fst (trace ρ)). 
    apply mixed_state_trace_gt0. intuition. 
    assert(ρ=1%R .* ρ). rewrite Mscale_1_l. reflexivity.
    rewrite H. apply Pure_S. lra. intuition. 
    intuition. intuition.  rewrite pure_state_trace_1. simpl. intuition.
     easy. rewrite Rmult_1_r in H1. intuition.
  - rewrite trace_plus_dist.
    rewrite 2 trace_mult_dist.
    simpl. repeat rewrite Rmult_0_l. 
    repeat rewrite Rminus_0_r.
    apply Rplus_mult_le_1; intuition;
    assert(0 < fst (trace ρ2)); 
    apply mixed_state_trace_gt0; intuition. 
 Qed.


Lemma mixed_state_diag_real : forall {n} (ρ : Density n) i , Mixed_State ρ -> 
                                                        snd (ρ i i) = 0.
Proof.
  intros.
  induction H.
  + unfold Pure_State in H. 
  - destruct H0 as [φ [[WFφ IP1] Eρ]].
    rewrite Eρ. 
    simpl. 
    lra.
  + simpl.
    rewrite IHMixed_State1, IHMixed_State2.
    repeat rewrite Rmult_0_r, Rmult_0_l.
    lra.
Qed.

Lemma mixed_state_trace_real : forall {n} (ρ : Density n) , Mixed_State ρ -> 
                                                        snd (trace ρ) = 0.
Proof. intros. unfold trace. apply big_sum_snd_0. intros. apply mixed_state_diag_real.
     intuition.     
Qed.


 Lemma Cmod_snd_0: forall c:C, 0<fst c -> snd c=0 -> Cmod c = fst c .
 Proof. intros. unfold Cmod. rewrite H0. unfold pow. repeat rewrite Rmult_0_l.
      rewrite Rplus_0_r. rewrite Rmult_1_r. apply sqrt_square. intuition. 
 Qed.

 Lemma mixed_state_Cmod_1 : forall {n} (ρ : Density n), Mixed_State ρ ->0<  Cmod (trace ρ) <=1.
 Proof. intros. rewrite Cmod_snd_0. split.
        apply mixed_state_trace_gt0. intuition.
        apply mixed_state_trace_1. intuition.
        apply mixed_state_trace_gt0.  intuition. apply mixed_state_trace_real.
        intuition.
 Qed.



Local Open Scope R_scope.
Lemma mixed_state_Cmod_plus: forall {n} (ρ1  ρ2: Density n), Mixed_State ρ1 -> Mixed_State ρ2->  
Cmod (trace (ρ1 .+ ρ2)) = Cmod (trace ρ1) + Cmod (trace ρ2).
Proof. intros. 
    repeat rewrite Cmod_snd_0;      
    try rewrite trace_plus_dist; 
    simpl; try reflexivity; try apply Rplus_lt_0_compat;
    try apply mixed_state_trace_gt0;
    try intuition; try repeat rewrite mixed_state_trace_real; 
    try intuition.  
Qed.

Lemma RtoC_mult: forall p p0 , Cmult (RtoC p) (RtoC p0)=RtoC (p * p0).
Proof. intros.
unfold RtoC. unfold Cmult. simpl.
repeat rewrite Rmult_0_r.
rewrite Rmult_0_l. rewrite Rplus_0_l.
 rewrite Rminus_0_r.
reflexivity.
Qed.

Lemma Rmult_in01: forall p1 p2,
0 < p1 <=1->
0 < p2 <=1->
0 < p1 * p2 <=1.
Proof. split. apply Rmult_gt_0_compat. intuition. intuition.
        assert(p1 * p2 <= 1*1).
        apply Rmult_le_compat. 
        intuition. intuition. intuition. intuition. 
        rewrite Rmult_1_l in H1. assumption.
Qed.


Lemma Mixed_State_scale: forall n (ρ : Square n) p, Mixed_State ρ ->
0 < p <= 1->
Mixed_State (p .* ρ).
Proof. intros.
       inversion_clear H.
       - rewrite Mscale_assoc.  
       rewrite RtoC_mult. apply Pure_S.
       apply Rmult_in01. intuition. intuition.
       intuition.
      --rewrite Mscale_plus_distr_r.
        repeat rewrite Mscale_assoc.
        repeat rewrite RtoC_mult;
        apply Mix_S; try rewrite <-Rmult_plus_distr_l;
         try apply Rmult_in01;
        try assumption.  split. lra. assumption.
Qed.

(*Mixed_State_aux*)

Inductive Mixed_State_aux {n} : Matrix n n -> Prop :=
|Pure_S_aux : forall ρ (p:R), 0 < p -> Pure_State ρ -> Mixed_State_aux (p.* ρ) 
|Mix_S_aux : forall  ρ1 ρ2, Mixed_State_aux ρ1 -> Mixed_State_aux ρ2 ->Mixed_State_aux (ρ1 .+ ρ2).  

Local Open Scope C_scope.
Lemma  Rplus_le_1:forall (r1 r2:R), r1>0->r1+r2<=1 ->r2<=1 .
Proof. intros. lra.
Qed.


Lemma mixed_state_diag_in01_aux : forall {n} (ρ : Density n) i , Mixed_State_aux ρ -> 
                                                        0 <= fst (ρ i i).
Proof.
  intros.
  induction H.
  - destruct H0 as [φ [[WFφ IP1] Eρ]].
    destruct (lt_dec i n). 
    2: rewrite Eρ; unfold Mmult, adjoint; simpl; rewrite WFφ; simpl; [lra|lia].
    rewrite Eρ.
    unfold Mmult, adjoint in *.
    simpl in *.
    rewrite Rplus_0_l.
    match goal with
    [H : ?f = ?g |- _] => assert (f O O = g O O) by (rewrite <- H; easy)
    end. 
    unfold I in H. simpl in H. clear IP1.
    match goal with
    [ H : ?x = ?y |- _] => assert (H': fst x = fst y) by (rewrite H; easy); clear H
    end.
    simpl in H'. 
    (* rewrite <- H'.    
    split. *)
    + unfold Rminus. rewrite <- Ropp_mult_distr_r. rewrite Ropp_involutive.
      rewrite <- Rplus_0_r at 1. rewrite Rmult_0_l. rewrite Ropp_0.
        apply Rplus_le_compat. assert((0*0)%R=0%R). apply Rmult_0_r.
        rewrite<- H0.  apply Rmult_le_compat; try intuition. 
        rewrite <- Rplus_0_r at 1.
        apply Rplus_le_compat;
       apply Rle_0_sqr. intuition.     
  - simpl. apply Rplus_le_le_0_compat. assumption. assumption.
Qed.




Lemma mixed_state_diag_real_aux : forall {n} (ρ : Density n) i , Mixed_State_aux ρ -> 
                                                        snd (ρ i i) = 0.
Proof.
  intros.
  induction H.
  + unfold Pure_State in H. 
  - destruct H0 as [φ [[WFφ IP1] Eρ]].
    rewrite Eρ.
    simpl. 
    lra.
  + simpl.
    rewrite IHMixed_State_aux1, IHMixed_State_aux2.
    repeat rewrite Rmult_0_r, Rmult_0_l.
    lra.
Qed.



Lemma mixed_state_trace_real_aux : forall {n} (ρ : Density n) , Mixed_State_aux ρ -> 
                                                        snd (trace ρ) = 0.
Proof. intros. unfold trace. apply big_sum_snd_0. intros. apply mixed_state_diag_real_aux.
       intuition.
Qed.


 Lemma mixed_state_trace_gt0_aux: forall {n} (ρ : Density n) , Mixed_State_aux ρ -> 
 0 < fst (trace ρ).
Proof.  
intros n ρ H. 
induction H. 
- rewrite trace_mult_dist. simpl. rewrite Rmult_0_l.
rewrite Rminus_0_r. apply Rmult_gt_0_compat.
intuition. rewrite pure_state_trace_1. simpl. intuition.
intuition.
- rewrite trace_plus_dist. 
repeat rewrite trace_mult_dist.
simpl. repeat rewrite Rmult_0_l.
repeat rewrite Rminus_0_r.
apply Rplus_lt_0_compat; intuition.
Qed.




 
  Lemma mixed_state_Cmod_1_aux : forall {n} (ρ : Density n), Mixed_State_aux ρ ->0<  Cmod (trace ρ).
  Proof. intros. rewrite Cmod_snd_0. 
         apply mixed_state_trace_gt0_aux. intuition.
         apply mixed_state_trace_gt0_aux.  intuition. apply mixed_state_trace_real_aux.
         intuition.
  Qed. 

Local Open Scope R_scope.
  Lemma mixed_state_Cmod_plus_aux: forall {n} (ρ1  ρ2: Density n), Mixed_State_aux ρ1 -> Mixed_State_aux ρ2->  
  Cmod (trace (ρ1 .+ ρ2)) = Cmod (trace ρ1) + Cmod (trace ρ2).
  Proof. intros. 
      repeat rewrite Cmod_snd_0;      
      try rewrite trace_plus_dist; 
      simpl; try reflexivity; try apply Rplus_lt_0_compat;
      try apply mixed_state_trace_gt0_aux;
      try intuition; try repeat rewrite mixed_state_trace_real_aux; 
      try intuition.  
  Qed.
  


 

Lemma mixed_unitary_aux : forall {n} (U ρ : Matrix n n), 
  WF_Unitary U -> Mixed_State_aux ρ -> Mixed_State_aux (super U ρ).
  Proof.
  intros n U ρ H M.
  induction M.
  + unfold super. rewrite Mscale_mult_dist_r.
    rewrite Mscale_mult_dist_l.
    apply Pure_S_aux. intuition.
    apply pure_unitary; trivial.
  + unfold WF_Unitary, super in *.
    rewrite Mmult_plus_distr_l.
    rewrite Mmult_plus_distr_r.
    apply Mix_S_aux; trivial.
Qed.



Lemma  Mixed_State_aux_to01:forall {n} (ρ : Density n),
Mixed_State_aux ρ ->
Mixed_State ((R1 / Cmod (trace ρ))%R .* ρ) .
Proof. intros. induction H.  rewrite Mscale_assoc. 
       rewrite Rdiv_unfold. rewrite trace_mult_dist.
       rewrite Cmod_mult. rewrite Cmod_R. rewrite Rabs_right.
        rewrite pure_state_trace_1. rewrite Cmod_1. 
        rewrite Rmult_1_r. rewrite RtoC_mult.
        rewrite Rmult_assoc.
        rewrite Rinv_l. rewrite Rmult_1_r. 
        apply Pure_S. lra. assumption. lra.
        assumption.  intuition.
        rewrite Mscale_plus_distr_r.  
        assert(ρ1=Cmod (trace ρ1) .* (((R1 / Cmod (trace ρ1))%R) .* ρ1) ).
        rewrite Mscale_assoc. 
         rewrite Rdiv_unfold. 
       rewrite RtoC_mult.  
       rewrite <-Rmult_assoc . 
       rewrite Rmult_comm.  
         rewrite <-Rmult_assoc . 
         rewrite Rinv_l.  
         rewrite Rmult_1_r . 
         rewrite Mscale_1_l. reflexivity.
         assert(Cmod (trace ρ1) >0). apply mixed_state_Cmod_1_aux.
       assumption. lra .
        assert(ρ2=Cmod (trace ρ2) .* (((R1 / Cmod (trace ρ2))%R) .* ρ2) ).
        rewrite Mscale_assoc.
        rewrite Rdiv_unfold. 
        rewrite RtoC_mult.  
        rewrite <-Rmult_assoc . 
        rewrite Rmult_comm.  
          rewrite <-Rmult_assoc . 
          rewrite Rinv_l.  
          rewrite Rmult_1_r . 
          rewrite Mscale_1_l. reflexivity.
          assert(Cmod (trace ρ2) >0). apply mixed_state_Cmod_1_aux.
        assumption. lra . remember ((R1 / Cmod (trace (ρ1 .+ ρ2)))%R).
        rewrite H1. rewrite H2.
         rewrite Mscale_assoc.  
         rewrite (Mscale_assoc _ _ r _ _).
        repeat rewrite RtoC_mult.   
        apply Mix_S. rewrite Heqr. 
        rewrite Rdiv_unfold.  rewrite Rmult_1_l.
        split. apply Rmult_gt_0_compat. apply Rinv_0_lt_compat.
        rewrite mixed_state_Cmod_plus_aux. apply Rplus_lt_0_compat.
        apply mixed_state_Cmod_1_aux. assumption. 
        apply mixed_state_Cmod_1_aux. assumption. assumption. assumption.
        apply mixed_state_Cmod_1_aux. assumption. 
        rewrite Rmult_comm. rewrite <-Rdiv_unfold. 
        apply (Rcomplements.Rdiv_le_1 (Cmod (trace ρ1))). 
        rewrite mixed_state_Cmod_plus_aux. apply Rplus_lt_0_compat.
        apply mixed_state_Cmod_1_aux. assumption. 
        apply mixed_state_Cmod_1_aux. assumption. assumption. assumption.
        rewrite mixed_state_Cmod_plus_aux. 
        assert( Cmod (trace ρ1) +0 <= Cmod (trace ρ1) + Cmod (trace ρ2)).
        apply Rplus_le_compat_l. assert(0<Cmod (trace ρ2) ).
        apply mixed_state_Cmod_1_aux. assumption. lra.
      rewrite Rplus_0_r in H3. assumption.  assumption. assumption.
      rewrite Heqr. 
      rewrite Rdiv_unfold.  rewrite Rmult_1_l.
      split. apply Rmult_gt_0_compat. apply Rinv_0_lt_compat.
      rewrite mixed_state_Cmod_plus_aux. apply Rplus_lt_0_compat.
      apply mixed_state_Cmod_1_aux. assumption. 
      apply mixed_state_Cmod_1_aux. assumption. assumption. assumption.
      apply mixed_state_Cmod_1_aux. assumption. 
      rewrite Rmult_comm. rewrite <-Rdiv_unfold. 
      apply (Rcomplements.Rdiv_le_1 (Cmod (trace ρ2))). 
      rewrite mixed_state_Cmod_plus_aux. apply Rplus_lt_0_compat.
      apply mixed_state_Cmod_1_aux. assumption. 
      apply mixed_state_Cmod_1_aux. assumption. assumption. assumption.
      rewrite mixed_state_Cmod_plus_aux. 
      assert(0+ Cmod (trace ρ2) <= Cmod (trace ρ1) + Cmod (trace ρ2)).
      apply Rplus_le_compat_r. assert(0<Cmod (trace ρ1) ).
      apply mixed_state_Cmod_1_aux. assumption. lra.
    rewrite Rplus_0_l in H3. assumption.  assumption. assumption.
    rewrite <-Rmult_plus_distr_l.
        rewrite Heqr.  rewrite mixed_state_Cmod_plus_aux. 
        rewrite Rdiv_unfold. rewrite Rmult_assoc. 
        rewrite Rinv_l. lra. 
        assert((Cmod (trace ρ1) + Cmod (trace ρ2))%R > 0).
        apply Rplus_lt_0_compat. apply mixed_state_Cmod_1_aux.
        assumption. apply mixed_state_Cmod_1_aux.
        assumption. lra. 
       assumption. assumption. 
       apply IHMixed_State_aux1. apply IHMixed_State_aux2.
Qed.

Lemma Mixed_State_scale_aux: forall n (ρ : Square n) p, Mixed_State_aux ρ ->
0 < p->
Mixed_State_aux (p .* ρ).
Proof. intros.
        induction H.
        - rewrite Mscale_assoc.  
        rewrite RtoC_mult. apply Pure_S_aux.
        apply Rmult_lt_0_compat. intuition. intuition.
        intuition.
      --rewrite Mscale_plus_distr_r. 
        apply Mix_S_aux; intuition.
Qed.

Require Import Reals.
Lemma Mixed_State_aux_to_Mix_State: forall {n} (ρ : Density n), 
(Mixed_State_aux ρ /\ Cmod (trace ρ) <=1) <-> Mixed_State ρ. 
Proof. intros. split; intros. destruct H. induction H. apply Pure_S. 
      rewrite trace_mult_dist in H0. rewrite Cmod_mult in H0.
      rewrite Cmod_R in H0. rewrite Rabs_right in H0.
      split. assumption.  rewrite pure_state_trace_1 in H0.
      rewrite Cmod_1 in H0. rewrite Rmult_1_r in H0. assumption.
      assumption. intuition. assumption. 
      rewrite mixed_state_Cmod_plus_aux  in H0. 
      assert(Mixed_State (Cmod (trace ρ1) .* (((R1 / Cmod (trace ρ1))%R) .* ρ1) .+ 
           Cmod (trace ρ2) .* (((R1/ Cmod (trace ρ2))%R) .* ρ2))).
      apply Mix_S. split. apply mixed_state_Cmod_1_aux. assumption.
      apply Rplus_le_1 with (Cmod (trace ρ2)). apply mixed_state_Cmod_1_aux.
      assumption. rewrite Rplus_comm. assumption. split.
      apply mixed_state_Cmod_1_aux. assumption. 
      apply Rplus_le_1 with (Cmod (trace ρ1)). apply mixed_state_Cmod_1_aux. assumption.
      assumption. assumption.  
      apply Mixed_State_aux_to01. assumption.
      apply Mixed_State_aux_to01. assumption.
      repeat rewrite Rdiv_unfold in H2. 
      repeat rewrite Mscale_assoc in H2. 
      repeat rewrite RtoC_mult in H2. 
      repeat rewrite <-Rmult_assoc in H2. 
       rewrite Rmult_comm in H2. 
        rewrite (Rmult_comm (Cmod (trace ρ2) * R1) _) in H2.
        repeat rewrite <-Rmult_assoc in H2. 
         rewrite Rinv_l in H2.  rewrite Rinv_l in H2. 
        repeat rewrite Rmult_1_r in H2.
        repeat rewrite Mscale_1_l in H2. assumption.
       assert(Cmod (trace ρ2) >0). apply mixed_state_Cmod_1_aux.
       assumption.  lra.  
       assert(Cmod (trace ρ1) >0). apply mixed_state_Cmod_1_aux.
       assumption.  lra.
      assumption. assumption.
      induction H. split. apply Pure_S_aux.  intuition.
      assumption. apply mixed_state_Cmod_1. apply Pure_S.
      assumption. assumption.
      split.  apply Mix_S_aux. apply Mixed_State_scale_aux.
      apply IHMixed_State1. intuition. 
      apply Mixed_State_scale_aux.
      apply IHMixed_State2. intuition.  
      apply mixed_state_Cmod_1. apply Mix_S; intuition.
Qed.


(* Lemma Mixed_pure: forall {n} (ρ1 ρ2: Density n) (φ:Vector n), Mixed_State ρ1-> Mixed_State ρ2 -> 
ρ1 .+  ρ2= φ† × φ -> ρ1= φ† × φ /\ ρ2= φ† × φ.
Proof.
    intros.
    induction H; induction H0.
    --inversion_clear H2. inversion_clear H3.
      destruct H4. destruct H2. rewrite H4 in H1.
      rewrite H5 in H1. destruct H1.
    
Qed. *)
