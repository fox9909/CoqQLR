Require Import Reals.
Require Import Coquelicot.Complex.
Require Import Strings.String.
Require Import Lists.List.
Require Import Coq.Init.Datatypes.
From Coq Require Import Bool.Bool.
From Coq Require Import Lia.
From Coq Require Import Init.Nat.


Require Import Psatz.
Require Import Reals.
From Quan Require Export VecSet.
From Quan Require Export Matrix.
From Quan Require Export Quantum.
From Quan Require Export Complex.
From Quan Require Import Basic.

(*-------------------------------------------------------------------------*)

Notation Density n := (Matrix n n) (only parsing). 

Definition Classical {n} (ρ : Density n) := forall i j, i <> j -> ρ i j = 0.

Definition Pure_State_Vector {n} (φ : Vector n): Prop := 
   WF_Matrix φ /\ φ† × φ = I  1.

Definition Pure_State {n} (ρ : Density n) : Prop := 
  exists φ,  Pure_State_Vector φ /\ ρ = (φ × φ†). 

Inductive Mixed_State {n} : Matrix n n -> Prop :=
| Pure_S : forall ρ (p:R), (0 <= p <= 1)-> Pure_State ρ -> Mixed_State (p.* ρ) 
| Mix_S : forall (p1 p2: R) ρ1 ρ2, 0 <= p1 -> 0 <= p2  -> p1+p2<=1
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

Lemma norm_1_pure_vec{n:nat}:  forall (x:Vector n),
WF_Matrix x -> norm x =1 -> Pure_State_Vector x.
Proof. intros. econstructor. assumption. unfold norm in *. 
       rewrite <-sqrt_1 in H0. apply sqrt_inj in H0. 
       assert( WF_Matrix (I 1)). auto_wf.
       unfold WF_Matrix in *.
       unfold inner_product in H0. unfold I. 
       prep_matrix_equality. destruct x0. destruct y.
       simpl. 
       remember(((x) † × x) 0%nat 0%nat).
       assert(c= (fst c, snd c)). destruct c. reflexivity.
       rewrite H2. assert(C1=(1,0)). reflexivity. rewrite H3.
         f_equal. subst. assumption. subst. 
       unfold adjoint. unfold Mmult. rewrite big_sum_snd_0.
       reflexivity. intros. simpl. lra.
       unfold Mmult.  apply (@big_sum_0_bounded C C_is_monoid).
       intros.   rewrite H. rewrite Cmult_0_r. reflexivity.
       destruct y.  lia. lia.

       destruct y;    simpl in *. 
       unfold Mmult.  apply (@big_sum_0_bounded C C_is_monoid).
       intros. unfold adjoint. simpl.   rewrite H. rewrite Cconj_0. rewrite Cmult_0_l. reflexivity.
        lia. assert((S x0 <? 1) = false). apply Nat.ltb_ge. lia.  
        rewrite H2. simpl. assert((x0 =? y) && false = false).
        destruct (x0=?y); simpl; reflexivity. rewrite H3.
        unfold Mmult.  apply (@big_sum_0_bounded C C_is_monoid).
       intros. unfold adjoint. simpl.   rewrite H. rewrite Cconj_0. rewrite Cmult_0_l. reflexivity.
       lia. 
       apply inner_product_ge_0. lra.  
Qed.

Lemma Pure_State_Vector_base{n:nat}: forall i, 
(i<n)%nat->
Pure_State_Vector (∣ i ⟩_ n).
Proof. intros. apply norm_1_pure_vec. apply WF_base. assumption. 
apply norm_base_1. assumption.
Qed.

Lemma Pure_State_base{n:nat}: forall  i, 
(i<n)%nat-> 
Pure_State (∣ i ⟩_ n × (adjoint (∣ i ⟩_ n))) .
Proof. intros. econstructor. split. apply (Pure_State_Vector_base  i H). reflexivity.  
Qed.

Lemma zero_mixed{n:nat}:   Mixed_State (@Zero (2^n) (2^n)).
Proof. intros. assert(@Zero (2^n) (2^n) = 0%R .* (∣ 0 ⟩_ (2^n) × (adjoint (∣ 0 ⟩_ (2^n))))). rewrite Mscale_0_l. 
reflexivity. intros. rewrite H.  apply Pure_S. lra. apply Pure_State_base. apply pow_gt_0. 
Qed.


Definition NZ_Mixed_State'{n:nat} (ρ:Square n ) := Mixed_State ρ /\  ρ<> Zero .

Inductive NZ_Mixed_State {n} : Matrix n n -> Prop := 
| NZ_Pure_S : forall ρ (p:R), (0 < p <= 1)-> Pure_State ρ -> NZ_Mixed_State (p.* ρ) 
| NZ_Mix_S : forall (p1 p2: R) ρ1 ρ2, 0 < p1 -> 0 < p2  -> p1+p2<=1
-> NZ_Mixed_State ρ1 ->NZ_Mixed_State ρ2 ->NZ_Mixed_State (p1 .* ρ1 .+ p2 .* ρ2).  


Lemma WF_NZ_Mixed : forall {n} (ρ : Density n), NZ_Mixed_State ρ -> WF_Matrix ρ.
Proof.  induction 1; auto with wf_db. Qed.
#[export] Hint Resolve WF_NZ_Mixed : wf_db. 

Lemma Pure_NZ_Mixed{n:nat}: forall ( ρ : Matrix n n),
Pure_State ρ ->
NZ_Mixed_State ρ .
Proof. intros. assert(ρ= C1 .* ρ). rewrite Mscale_1_l. reflexivity.
       rewrite H0. econstructor. intuition. assumption. 
Qed.
#[export] Hint Resolve  Pure_NZ_Mixed: Mixed.



(*Uρ is mixed*)
Lemma pure_state_vector_unitary_pres : forall {n} (ϕ : Vector n) (U : Square n),
  Pure_State_Vector ϕ -> WF_Unitary U -> Pure_State_Vector (U × ϕ).
Proof. 
  unfold Pure_State_Vector.
  intros n ϕ U [H H0] [H1 H2].
  split; auto with wf_db.
  distribute_adjoint.
  rewrite Mmult_assoc, <- (Mmult_assoc _ U), H2, Mmult_1_l; auto.
Qed.

Lemma nz_mixed_unitary : forall {n} (U ρ : Matrix n n), 
  WF_Unitary U -> NZ_Mixed_State ρ -> NZ_Mixed_State (super U ρ).
  Proof.
  intros n U ρ H M.
  induction M.
  + unfold super. rewrite Mscale_mult_dist_r.
    rewrite Mscale_mult_dist_l.
    apply NZ_Pure_S. intuition.
    apply pure_unitary; trivial.
  + unfold WF_Unitary, super in *.
    rewrite Mmult_plus_distr_l.
    rewrite Mmult_plus_distr_r.
    rewrite 2 Mscale_mult_dist_r.
    rewrite 2 Mscale_mult_dist_l.
    apply NZ_Mix_S; trivial.
Qed.

#[export] Hint Resolve  nz_mixed_unitary: Mixed.

(*ρ_1⊗ρ_2 is mixed*)
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
  NZ_Mixed_State ρ -> NZ_Mixed_State φ -> NZ_Mixed_State (ρ ⊗ φ).
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
    reflexivity. rewrite H3. apply NZ_Pure_S.
    split. 
    apply Rmult_gt_0_compat. intuition. intuition.
    assert(p0 * p <= 1*1). apply Rmult_le_compat.
    intuition. intuition. intuition. intuition.
    intuition. rewrite Rmult_1_r in H4. intuition.
    apply pure_state_kron; easy.
  - rewrite kron_plus_distr_l.
    rewrite 2 Mscale_kron_dist_r.
    apply NZ_Mix_S; easy.
  - rewrite kron_plus_distr_r.
    rewrite 2 Mscale_kron_dist_l.
    apply NZ_Mix_S; easy.
Qed.
#[export] Hint Resolve  mixed_state_kron: Mixed.

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
#[export] Hint Resolve Rmult_in01: Rsimpl.
#[export] Hint Resolve RtoC_mult: Rsimpl.

(*p .* ρ is mixed*)
Lemma nz_Mixed_State_scale: forall n (ρ : Square n) p, NZ_Mixed_State ρ ->
0 < p <= 1->
NZ_Mixed_State (p .* ρ).
Proof. intros.
       inversion_clear H.
       - rewrite Mscale_assoc.  
       rewrite RtoC_mult. apply NZ_Pure_S.
       apply Rmult_in01. intuition. intuition.
       intuition.
      -rewrite Mscale_plus_distr_r.
        repeat rewrite Mscale_assoc.
        repeat rewrite RtoC_mult;
        apply NZ_Mix_S; try rewrite <-Rmult_plus_distr_l;
         try apply Rmult_in01;
        try assumption. lra. lra. lra.  
Qed.


Lemma nz_Mixed_State_scale_c: forall n (ρ : Square n) c, 
NZ_Mixed_State ρ ->
0 < fst c <= 1-> 
snd c =0->
NZ_Mixed_State (c .* ρ).
Proof. intros. destruct c. simpl in *. rewrite H1. 
       assert((r, 0) = RtoC r). reflexivity.
       rewrite H2. apply nz_Mixed_State_scale. assumption.
        assumption.
Qed.


(*trace of mixed*)
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

Lemma nz_mixed_state_diag_in01 : forall {n} (ρ : Density n) i , NZ_Mixed_State ρ -> 
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


Lemma nz_mixed_state_trace_gt0: forall {n} (ρ : Density n) , NZ_Mixed_State ρ -> 
                                                        0 < fst (trace ρ).
Proof.  
intros n ρ H. 
induction H. 
- rewrite trace_mult_dist. simpl. rewrite Rmult_0_l.
  rewrite Rminus_0_r. apply Rmult_gt_0_compat. lra.
  rewrite pure_state_trace_1. simpl. intuition.
  intuition.
- rewrite trace_plus_dist. 
 repeat rewrite trace_mult_dist.
 simpl. repeat rewrite Rmult_0_l.
 repeat rewrite Rminus_0_r.
 apply Rplus_lt_0_compat;
 apply Rmult_gt_0_compat; intuition. 
Qed.

Local Open Scope R_scope.
Lemma Rplus_mult_le_1: forall (p1 p2 r1 r2:R),
0 <=p1 <=1->
0 <=p2 <=1->
p1+p2<=1->
0<=r1 <= 1->
0<=r2<= 1->
0<=p1 * r1 + p2 * r2<= 1 .
Proof. intros. 
assert(r1<r2\/ r2<=r1).
apply Rlt_or_le.
destruct H4.
split. apply Rplus_le_le_0_compat;
apply Rmult_le_pos; intuition.
apply Rle_trans with ((p1 * r2)%R + (p2 * r2)%R)%R.
apply Rplus_le_compat;
apply Rmult_le_compat;
intuition. 
rewrite <-Rmult_plus_distr_r. 
assert((p1 + p2) * r2 <= 1*1).
apply Rmult_le_compat. 
 apply Rplus_le_le_0_compat. intuition. intuition.
intuition. intuition. intuition. 
rewrite Rmult_1_l in H5.
intuition.

split. apply Rplus_le_le_0_compat;
apply Rmult_le_pos; intuition.
apply Rle_trans with (p1 * r1 + p2 * r1 ).
apply Rplus_le_compat;
apply Rmult_le_compat;
intuition.  
rewrite <-Rmult_plus_distr_r. 
assert((p1 + p2) * r1 <= 1*1).
apply Rmult_le_compat. 
 apply Rplus_le_le_0_compat. intuition. intuition.
intuition. intuition. intuition.  
rewrite Rmult_1_l in H5.
intuition.
Qed.
#[export] Hint Resolve Rplus_mult_le_1 : Rsimpl.

Lemma Rgt_ge: forall r:R, r>0 -> r>=0 .
Proof. intro. lra.
Qed.

Lemma Rge_le: forall r:R, r>=0 <->0 <=r.
Proof. intro. lra.
Qed.
#[export] Hint Resolve Rgt_ge Rge_le: Rsimpl.

Ltac RSimpl:= auto with Rsimpl.

Lemma nz_mixed_state_trace_1 : forall {n} (ρ : Density n), NZ_Mixed_State ρ ->  fst (trace ρ) <=1.
Proof.
  intros n ρ H. 
  induction H. 
  - rewrite trace_mult_dist. simpl. rewrite Rmult_0_l.
    rewrite Rminus_0_r. assert(p * fst (trace ρ) <= 1 * 1).
    apply Rmult_le_compat. intuition. apply Rge_le. 
    apply Rgt_ge. 
    apply nz_mixed_state_trace_gt0. intuition.  intuition.
     rewrite pure_state_trace_1. simpl. intuition.
     easy.  rewrite Rmult_1_r in H1. intuition.
  - rewrite trace_plus_dist.
    rewrite 2 trace_mult_dist.
    simpl. repeat rewrite Rmult_0_l. 
    repeat rewrite Rminus_0_r.
    apply Rplus_mult_le_1. lra. lra. assumption.
    assert(0 <= fst (trace ρ1)).  
    apply Rge_le. 
    apply Rgt_ge. 
    apply nz_mixed_state_trace_gt0. intuition. lra.
    assert(0 <= fst (trace ρ2)).
    apply Rge_le. 
    apply Rgt_ge. 
    apply nz_mixed_state_trace_gt0. intuition. lra.   
 Qed.


Lemma nz_mixed_state_trace_in01 : forall {n} (ρ : Density n), NZ_Mixed_State ρ ->0<  fst (trace ρ) <=1.
Proof. intros.  split.
       apply nz_mixed_state_trace_gt0. intuition.
       apply nz_mixed_state_trace_1. intuition.
Qed.

Lemma nz_mixed_state_diag_real : forall {n} (ρ : Density n) i , NZ_Mixed_State ρ -> 
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
    rewrite IHNZ_Mixed_State1, IHNZ_Mixed_State2.
    repeat rewrite Rmult_0_r, Rmult_0_l.
    lra.
Qed.

Lemma nz_mixed_state_trace_real : forall {n} (ρ : Density n) , NZ_Mixed_State ρ -> 
                                                        snd (trace ρ) = 0.
Proof. intros. unfold trace. apply big_sum_snd_0. intros. apply nz_mixed_state_diag_real.
       intuition.     
Qed.

Lemma Cmod_snd_0: forall c:C, 0<fst c -> snd c=0 -> Cmod c = fst c .
Proof. intros. unfold Cmod. rewrite H0. unfold pow. repeat rewrite Rmult_0_l.
    rewrite Rplus_0_r. rewrite Rmult_1_r. apply sqrt_square. intuition. 
Qed.

Lemma nz_mixed_state_Cmod_1 : forall {n} (ρ : Density n), NZ_Mixed_State ρ ->0< Cmod (trace ρ) <=1.
Proof. intros. rewrite Cmod_snd_0. split.
      apply nz_mixed_state_trace_gt0. intuition.
      apply nz_mixed_state_trace_1. intuition.
      apply nz_mixed_state_trace_gt0.  intuition. apply nz_mixed_state_trace_real.
      intuition.
Qed.


Local Open Scope R_scope.
Lemma nz_mixed_state_Cmod_plus: forall {n} (ρ1  ρ2: Density n), NZ_Mixed_State ρ1 -> NZ_Mixed_State ρ2->  
Cmod (trace (ρ1 .+ ρ2)) = Cmod (trace ρ1) + Cmod (trace ρ2).
Proof. intros. 
    repeat rewrite Cmod_snd_0;      
    try rewrite trace_plus_dist; 
    simpl; try reflexivity; try apply Rplus_lt_0_compat;
    try apply nz_mixed_state_trace_gt0;
    try intuition; try repeat rewrite nz_mixed_state_trace_real; 
    try intuition.  
Qed.

(*nz_mixed not Zero*)
Lemma big_sum_0_R : forall n,
(Σ (fun _ :nat =>0%R ) n)= 0%R. 
Proof. 
intros.
  induction n.
  - reflexivity.
  - simpl. remember (Σ (fun _ : nat => 0%R) n) as f.
  rewrite IHn.   
  rewrite Cplus_0_r. easy.
Qed.  

Lemma  Zero_trace: forall n, @trace n Zero=C0.
Proof. intros. unfold Zero.  unfold trace.
 apply (big_sum_0_R n). 
Qed.

Lemma Pure_State_Vector_not_Zero{n:nat}:forall (v: Vector n),
Pure_State_Vector v -> v<>Zero .
Proof. intros. destruct H.  intro. rewrite H1 in *.
      rewrite Mmult_0_r in H0. 
      assert(@trace 1 Zero= trace (I 1)).
      rewrite H0. reflexivity.
      rewrite Zero_trace in H2.
      rewrite trace_I in H2.
      injection H2. intuition.
Qed.

Lemma Pure_not_Zero{n:nat}:forall (M: Square n),
Pure_State M -> M<>Zero .
Proof. intros.  intro.     
      assert(@trace n Zero= trace (M)).
      rewrite H0. reflexivity.
      rewrite Zero_trace in H1.
      symmetry in H1. pose H. 
        apply pure_state_trace_1 in p. rewrite p in H1. injection H1.   lra.
Qed.


Lemma NZ_Mixed_not_Zero{n:nat}:forall (M: Square n),
NZ_Mixed_State M -> M<>Zero .
Proof. intros.  intro.  
      assert(@trace n Zero= trace (M)).
      rewrite H0. reflexivity.
      rewrite Zero_trace in H1.
      symmetry in H1. pose H.
        apply nz_mixed_state_trace_gt0 in n0.
        apply nz_mixed_state_trace_real in H.
      destruct (trace M). simpl in *.
      injection H1. intros. rewrite H3 in n0.
      lra.
Qed.


(*equiv*)
Local Open Scope R_scope.
Lemma Mscale_0: forall (m n:nat) (A:Matrix m n) (p: R), 
(p <> 0) /\ (p .* A = Zero) -> A = Zero .
Proof. intros. destruct H.  
assert(((1%R)/p) .* (p .* A ) = Zero).
rewrite H0. rewrite Mscale_0_r. reflexivity.  
rewrite Mscale_assoc in H1.  
rewrite Cdiv_unfold in H1.
assert((/ p * p)%C = 1).
rewrite Cinv_l. reflexivity.
unfold RtoC. unfold not. intros. injection H2. 
intros. intuition.
rewrite <- Cmult_assoc in H1.
rewrite H2 in H1.
rewrite Cmult_1_l in H1.
rewrite Mscale_1_l in H1.
assumption.
Qed.

Local Open Scope R_scope.
Lemma Mscale_not_0:forall (m n:nat) (A:Matrix m n) (p: R), 
(p <> 0)/\ (A<>Zero )-> p.* A <> Zero .
Proof. unfold not. intros. 
intros. assert(A=Zero). apply (Mscale_0 _ _ _ p). 
split. lra.
assumption. apply H in H1. intuition.  
Qed.

Lemma Mscale_not_0':forall (m n:nat) (A:Matrix m n) (p: R), 
p.* A <> Zero -> A<>Zero .
Proof. unfold not.  intros.  rewrite H0 in H.  rewrite Mscale_0_r in H.
intuition. 
Qed.

Lemma NZ_Mixed_State_is_Mixed_State{n:nat} : forall (ρ:Square n ),
NZ_Mixed_State ρ -> Mixed_State ρ.
Proof. intros. induction H. econstructor; try lra. assumption. 
       econstructor; try lra; try assumption.
Qed.  

Lemma Mplus_not_Zero{n:nat}: forall (M1 M2: Matrix n n),
M1 .+ M2 <> Zero -> M1 <> Zero \/ M2 <> Zero .
Proof. intros. apply Classical_Prop.NNPP. intro. apply Classical_Prop.not_or_and in H0.
       destruct H0. apply Classical_Prop.NNPP in H0.
       apply Classical_Prop.NNPP in H1. subst. rewrite Mplus_0_l in *.
       destruct H. reflexivity.  
Qed.


Lemma NZ_Mixed_State_equiv{n:nat} : forall (ρ:Square n ),
NZ_Mixed_State ρ <-> NZ_Mixed_State' ρ.
Proof. intros; split; intros. split. apply NZ_Mixed_State_is_Mixed_State. assumption. 
       apply NZ_Mixed_not_Zero. assumption.
       destruct H.     induction H. econstructor. 
       assert(p<>0). intro. rewrite H2 in *. rewrite Mscale_0_l in *. destruct H0. reflexivity.
       lra. assumption. 
      
       destruct (Req_dec p1 0). subst. Msimpl. rewrite Mscale_0_l in *.
       rewrite Mplus_0_l in *.  assert(p2<>0). intro.
       subst. repeat rewrite Mscale_0_l in *. 
       destruct H0. reflexivity. 
       apply nz_Mixed_State_scale; try lra; try apply IHMixed_State2.
       apply Mscale_not_0' with p2. assumption.

       destruct (Req_dec p2 0). subst. Msimpl. rewrite Mscale_0_l in *.
       rewrite Mplus_0_r in *. 
       apply nz_Mixed_State_scale; try lra; try apply IHMixed_State1.
       apply Mscale_not_0' with p1. assumption.

       apply Mplus_not_Zero in H0. destruct H0.  
       
       assert(ρ2= Zero \/ ~(ρ2= Zero)). 
       apply Classical_Prop.classic. destruct H7. subst. Msimpl.
       apply nz_Mixed_State_scale; try lra; try apply IHMixed_State1.
       apply Mscale_not_0' with p1. assumption.
       econstructor; try lra. apply IHMixed_State1. 
       apply Mscale_not_0' with p1. assumption.
       apply IHMixed_State2. assumption.
       
       assert(ρ1= Zero \/ ~(ρ1= Zero)). 
       apply Classical_Prop.classic. destruct H7. subst. Msimpl.
       apply nz_Mixed_State_scale; try lra; try apply IHMixed_State2.
       apply Mscale_not_0' with p2. assumption.
       econstructor; try lra. apply IHMixed_State1. assumption. 
       apply IHMixed_State2.  apply Mscale_not_0' with p2. assumption.
Qed.

(*----------------------------------Mixed_State_aux-------------------------------------*)

Inductive Mixed_State_aux {n} : Matrix n n -> Prop :=
|Pure_S_aux : forall ρ (p:R), 0 <= p -> Pure_State ρ -> Mixed_State_aux (p.* ρ) 
|Mix_S_aux : forall  ρ1 ρ2, Mixed_State_aux ρ1 -> Mixed_State_aux ρ2 ->Mixed_State_aux (ρ1 .+ ρ2).  

Inductive NZ_Mixed_State_aux {n} : Matrix n n -> Prop :=
|NZ_Pure_S_aux : forall ρ (p:R), 0 < p -> Pure_State ρ -> NZ_Mixed_State_aux (p.* ρ) 
|NZ_Mix_S_aux : forall  ρ1 ρ2, NZ_Mixed_State_aux ρ1 -> NZ_Mixed_State_aux ρ2 ->NZ_Mixed_State_aux (ρ1 .+ ρ2).  

Local Open Scope C_scope.
Lemma  Rplus_le_1:forall (r1 r2:R), r1>0->r1+r2<=1 ->r2<=1 .
Proof. intros. lra.
Qed.

(*p .* ρ and super U ρ *)
Lemma nz_Mixed_State_scale_aux: forall n (ρ : Square n) p, NZ_Mixed_State_aux ρ ->
0 < p->
NZ_Mixed_State_aux (p .* ρ).
Proof. intros.
        induction H.
        - rewrite Mscale_assoc.  
        rewrite RtoC_mult. apply NZ_Pure_S_aux.
        apply Rmult_lt_0_compat. intuition. intuition.
        intuition.
      --rewrite Mscale_plus_distr_r. 
        apply NZ_Mix_S_aux; intuition.
Qed.


Lemma nz_mixed_unitary_aux : forall {n} (U ρ : Matrix n n), 
WF_Unitary U -> NZ_Mixed_State_aux ρ -> NZ_Mixed_State_aux (super U ρ).
Proof.
intros n U ρ H M.
induction M.
+ unfold super. rewrite Mscale_mult_dist_r.
  rewrite Mscale_mult_dist_l.
  apply NZ_Pure_S_aux. intuition.
  apply pure_unitary; trivial.
+ unfold WF_Unitary, super in *.
  rewrite Mmult_plus_distr_l.
  rewrite Mmult_plus_distr_r.
  apply NZ_Mix_S_aux; trivial.
Qed.
#[export] Hint Resolve  nz_mixed_unitary_aux nz_Mixed_State_scale_aux: Mixed.

(*trace*)
Lemma nz_mixed_state_diag_in01_aux : forall {n} (ρ : Density n) i , NZ_Mixed_State_aux ρ -> 
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

Lemma nz_mixed_state_diag_real_aux : forall {n} (ρ : Density n) i , NZ_Mixed_State_aux ρ -> 
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
    rewrite IHNZ_Mixed_State_aux1, IHNZ_Mixed_State_aux2.
    repeat rewrite Rmult_0_r, Rmult_0_l.
    lra.
Qed.



Lemma nz_mixed_state_trace_real_aux : forall {n} (ρ : Density n) , NZ_Mixed_State_aux ρ -> 
                                                        snd (trace ρ) = 0.
Proof. intros. unfold trace. apply big_sum_snd_0. intros. apply nz_mixed_state_diag_real_aux.
       intuition.
Qed.


 Lemma nz_mixed_state_trace_gt0_aux: forall {n} (ρ : Density n) , NZ_Mixed_State_aux ρ -> 
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



Lemma nz_mixed_state_Cmod_1_aux : forall {n} (ρ : Density n), NZ_Mixed_State_aux ρ ->0<  Cmod (trace ρ).
Proof. intros. rewrite Cmod_snd_0. 
        apply nz_mixed_state_trace_gt0_aux. intuition.
        apply nz_mixed_state_trace_gt0_aux.  intuition. apply nz_mixed_state_trace_real_aux.
        intuition.
Qed. 


Local Open Scope R_scope.
Lemma nz_mixed_state_Cmod_plus_aux: forall {n} (ρ1  ρ2: Density n), NZ_Mixed_State_aux ρ1 -> NZ_Mixed_State_aux ρ2->  
Cmod (trace (ρ1 .+ ρ2)) = Cmod (trace ρ1) + Cmod (trace ρ2).
Proof. intros. 
    repeat rewrite Cmod_snd_0;      
    try rewrite trace_plus_dist; 
    simpl; try reflexivity; try apply Rplus_lt_0_compat;
    try apply nz_mixed_state_trace_gt0_aux;
    try intuition; try repeat rewrite nz_mixed_state_trace_real_aux; 
    try intuition.  
Qed.

  
Lemma Rdiv_in_01:forall r1 r2, r1>0 -> r2>0 -> 
r1<=r2->
0<r1/r2<=1.
Proof. intros. split. apply Rdiv_lt_0_compat.
      assumption. lra. 
       rewrite<- Rcomplements.Rdiv_le_1.
      assumption. assumption.
Qed.

(*relation*)
Local Open Scope R_scope.
Lemma Rgt_neq_0: forall r, r>0 -> r<>0.
Proof. intros. lra. Qed.

Lemma normalize_nz_mixed{n}: forall (ρ: Square n),
NZ_Mixed_State_aux ρ -> 
Cmod (trace ρ).* ((/ Cmod (trace ρ))%R .* ρ)=ρ.
Proof. intros. rewrite Mscale_assoc. rewrite RtoC_mult.
      rewrite Rinv_r. Msimpl. reflexivity. 
      apply Rgt_neq_0. apply nz_mixed_state_Cmod_1_aux. assumption.
Qed.


Lemma  nz_Mixed_State_aux_to01:forall {n} (ρ : Density n),
NZ_Mixed_State_aux ρ ->
NZ_Mixed_State ((/ Cmod (trace ρ))%R .* ρ).
Proof. intros. induction H.
      { rewrite Mscale_assoc. 
        rewrite trace_mult_dist.
        rewrite Cmod_mult. rewrite Cmod_R. rewrite Rabs_right.
        rewrite pure_state_trace_1.  rewrite Cmod_1. 
        rewrite Rmult_1_r. rewrite RtoC_mult.
        rewrite Rinv_l. apply NZ_Pure_S. lra. assumption. lra.
        assumption.  intuition. }
      { rewrite Mscale_plus_distr_r. 
        assert(ρ1=Cmod (trace ρ1) .* (((/ Cmod (trace ρ1))%R) .* ρ1) ).
        symmetry. apply normalize_nz_mixed. assumption. 
        assert(ρ2=Cmod (trace ρ2) .* ((( / Cmod (trace ρ2))%R) .* ρ2) ).
        symmetry. apply normalize_nz_mixed. assumption. 
        remember (( / Cmod (trace (ρ1 .+ ρ2)))%R).
        rewrite H1. rewrite H2.
         rewrite Mscale_assoc.  
         rewrite (Mscale_assoc _ _ r _ _).
        repeat rewrite RtoC_mult.   apply NZ_Mix_S. 
         rewrite Heqr.
        rewrite nz_mixed_state_Cmod_plus_aux. 
        rewrite Rmult_comm.
        rewrite <-Rdiv_unfold. apply Rdiv_in_01. 
        apply nz_mixed_state_Cmod_1_aux. assumption. 
         apply Rplus_lt_0_compat;
        apply nz_mixed_state_Cmod_1_aux; assumption. 
        rewrite <-Rplus_0_r at 1. apply Rplus_le_compat_l.
        apply Cmod_ge_0. assumption. assumption.
        rewrite Heqr.
        rewrite nz_mixed_state_Cmod_plus_aux. 
        rewrite Rmult_comm.
        rewrite <-Rdiv_unfold. apply Rdiv_in_01. 
        apply nz_mixed_state_Cmod_1_aux. assumption. 
         apply Rplus_lt_0_compat;
        apply nz_mixed_state_Cmod_1_aux; assumption. 
        rewrite <-Rplus_0_l at 1. apply Rplus_le_compat_r.
        apply Cmod_ge_0. assumption. assumption.
        rewrite <-Rmult_plus_distr_l.
        rewrite Heqr.  rewrite nz_mixed_state_Cmod_plus_aux. 
        rewrite Rinv_l. lra. apply Rgt_neq_0. 
        apply Rplus_lt_0_compat; apply nz_mixed_state_Cmod_1_aux;
        assumption. assumption. assumption.  
       apply IHNZ_Mixed_State_aux1. apply IHNZ_Mixed_State_aux2. }
Qed.
#[export] Hint Resolve  nz_Mixed_State_aux_to01 nz_Mixed_State_scale : Mixed. 

Require Import Reals.
Lemma nz_Mixed_State_aux_to_nz_Mix_State: forall {n} (ρ : Density n), 
(NZ_Mixed_State_aux ρ /\ Cmod (trace ρ) <=1) <-> NZ_Mixed_State ρ. 
Proof. intros. split; intros. destruct H. induction H.
      { apply NZ_Pure_S.  
      rewrite trace_mult_dist in H0. rewrite Cmod_mult in H0.
      rewrite Cmod_R in H0. rewrite Rabs_right in H0.
      split. assumption.  rewrite pure_state_trace_1 in H0.
      rewrite Cmod_1 in H0. rewrite Rmult_1_r in H0. assumption.
      assumption. intuition. assumption. }
      {
      rewrite nz_mixed_state_Cmod_plus_aux  in H0. 
       rewrite <-(normalize_nz_mixed ρ1). 
        rewrite <- (normalize_nz_mixed ρ2).
      apply NZ_Mix_S.  apply nz_mixed_state_Cmod_1_aux. assumption.
      apply nz_mixed_state_Cmod_1_aux. assumption. assumption.
      apply nz_Mixed_State_aux_to01. assumption.
      apply nz_Mixed_State_aux_to01. assumption. 
      assumption. assumption.  assumption. assumption. }

      { induction H. split. apply NZ_Pure_S_aux.  intuition.
      assumption. apply nz_mixed_state_Cmod_1. apply NZ_Pure_S.
      assumption. assumption.
      split.  apply NZ_Mix_S_aux. apply nz_Mixed_State_scale_aux.
      apply IHNZ_Mixed_State1. intuition. 
      apply nz_Mixed_State_scale_aux.
      apply IHNZ_Mixed_State2. intuition.  
      apply nz_mixed_state_Cmod_1. apply NZ_Mix_S; intuition. }
Qed.

Lemma  nz_Mixed_State_aux_to_01':forall {n} (ρ : Density n) p,
NZ_Mixed_State_aux ρ ->
0<p-> Cmod (trace (p .* ρ) )<=1 ->
NZ_Mixed_State (p .* ρ).
Proof. intros. apply nz_Mixed_State_aux_to_nz_Mix_State.
      split. apply nz_Mixed_State_scale_aux.
      assumption. assumption. assumption.
Qed.
#[export] Hint Resolve  nz_Mixed_State_aux_to_nz_Mix_State nz_Mixed_State_scale_c
nz_Mixed_State_aux_to_01': Mixed.


(*equiv*)
Lemma zero_mixed_aux{n:nat}:(0<n)%nat-> Mixed_State_aux (@Zero n n).
Proof. intros. assert(@Zero n n = 0%R .* (∣ 0 ⟩_ n × (adjoint (∣ 0 ⟩_ n)))). rewrite Mscale_0_l. 
reflexivity. intros. rewrite H0.  apply Pure_S_aux. lra. apply Pure_State_base. assumption. 
Qed.

Lemma NZ_Mixed_State_aux_is_Mixed_State_aux{n:nat} : forall (ρ:Square n ),
NZ_Mixed_State_aux ρ -> Mixed_State_aux ρ.
Proof. intros. induction H. econstructor; try lra. assumption. 
       econstructor; try lra; try assumption.
Qed.  

Lemma NZ_Mixed_aux_not_Zero{n:nat}:forall (M: Square n),
NZ_Mixed_State_aux M -> M<>Zero .
Proof. intros.  intro.  
      assert(@trace n Zero= trace (M)).
      rewrite H0. reflexivity.
      rewrite Zero_trace in H1.
      symmetry in H1. pose H.
      apply nz_mixed_state_trace_gt0_aux in n0.
      apply nz_mixed_state_trace_real_aux in H.
      destruct (trace M). simpl in *.
      injection H1. intros. rewrite H3 in n0.
      lra.
Qed.

Lemma NZ_Mixed_State_aux_equiv{n:nat} : forall (ρ:Square n ),
NZ_Mixed_State_aux ρ <-> Mixed_State_aux ρ /\ ρ <> Zero.
Proof. intros; split; intros. split. apply NZ_Mixed_State_aux_is_Mixed_State_aux. assumption. 
       apply NZ_Mixed_aux_not_Zero. assumption.
       destruct H.     induction H. econstructor. 
       assert(p<>0). intro. rewrite H2 in *. rewrite Mscale_0_l in *. destruct H0. reflexivity.
       lra. assumption. 

       apply Mplus_not_Zero in H0. destruct H0.  
       
       assert(ρ2= Zero \/ ~(ρ2= Zero)). 
       apply Classical_Prop.classic. destruct H2. subst. Msimpl.
       apply IHMixed_State_aux1. assumption. 
       econstructor. apply IHMixed_State_aux1. assumption.  
       apply IHMixed_State_aux2. assumption.
       
       assert(ρ1= Zero \/ ~(ρ1= Zero)). 
       apply Classical_Prop.classic. destruct H2. subst. Msimpl.
       apply IHMixed_State_aux2. assumption. 
       econstructor. apply IHMixed_State_aux1. assumption.  
       apply IHMixed_State_aux2. assumption.
Qed. 

Lemma NZ_Mixed_State_aux_equiv'{n:nat} : forall (ρ:Square (2^n) ),
Mixed_State_aux ρ <-> NZ_Mixed_State_aux ρ \/ ρ = Zero.
Proof. intros; split; intros. 
       assert(ρ= Zero \/ ~(ρ= Zero)). 
       apply Classical_Prop.classic. destruct H0. auto. left. 
       apply NZ_Mixed_State_aux_equiv. auto.  
       destruct H. apply NZ_Mixed_State_aux_is_Mixed_State_aux. 
       assumption. rewrite H. apply zero_mixed_aux. apply pow_gt_0. 
Qed.

Lemma mixed_state_Cmod_ge_0_aux : forall {n} (ρ : Density (2^n)), Mixed_State_aux ρ ->0<= Cmod (trace ρ).
Proof. intros. rewrite NZ_Mixed_State_aux_equiv' in H. destruct H. 
      apply nz_mixed_state_Cmod_1_aux in H. lra. rewrite H. rewrite Zero_trace.
      rewrite Cmod_0. lra.
Qed. 

Lemma Mix_stated_plus_aux{n:nat}: forall (q1 q2: Density n),
Mixed_State_aux  q1 ->
Mixed_State_aux  q2 ->
(Mplus q1  q2 <> Zero)->
NZ_Mixed_State_aux  (q1.+ q2).
Proof. intros. 
       apply NZ_Mixed_State_aux_equiv.
       split.
       apply Mix_S_aux; assumption. assumption.
Qed.
(*Vec is Mix_stated_aux*)
Local Open Scope nat_scope.
Lemma Vector_State_snd_0: forall n (x: Vector (n)),
WF_Matrix x-> (snd (((x) † × x) 0%nat 0%nat)= 0)%R.
 Proof.  intros.  simpl. unfold adjoint. unfold Mmult. 
 apply big_sum_snd_0.  intros.  rewrite  Cmult_comm.
 apply Cmult_conj_real.  
Qed.
         

Lemma inner_eq: forall n (x: Vector (n)),
WF_Matrix x->
((x) † × x) = ((norm x) * (norm x))%R .* I 1.
Proof. intros. unfold norm. rewrite sqrt_sqrt. unfold inner_product.
     rewrite <-(matrix_0_0_rev ((x) † × x)) at 1.
      unfold RtoC.  f_equal. 
      destruct (((x) † × x) 0 0)  eqn:E. 
      simpl.  f_equal. assert(r0= snd (((x) † × x) 0 0)).
      rewrite E. simpl. reflexivity. rewrite H0.
     apply Vector_State_snd_0. assumption.
     apply WF_mult.
     apply WF_adjoint. assumption. assumption.   
      apply inner_product_ge_0.
Qed.

Local Open Scope R_scope.
Lemma Vector_nz_Mix_State_aux{n:nat} : forall (x: Vector (n)),
WF_Matrix x-> x <> Zero->
NZ_Mixed_State_aux (x × (x) †).
Proof. intros. assert(x= ( (norm x))%R .* ( (R1 / ( (norm x)))%R .* x )).
          rewrite Mscale_assoc. rewrite Rdiv_unfold.
          rewrite Rmult_1_l. rewrite Cmult_comm. 
          rewrite RtoC_mult. 
          rewrite Rinv_l.
          rewrite Mscale_1_l. reflexivity.
          unfold not. intros.
          apply norm_zero_iff_zero in H1. rewrite H1 in H0.
          destruct H0. reflexivity. assumption.
          rewrite H1. rewrite Mscale_mult_dist_l.
          rewrite Mscale_adj.   rewrite Mscale_mult_dist_r.
          remember ( (norm x)). rewrite Mscale_assoc.
          rewrite Cconj_R. 
          rewrite RtoC_mult. 
          apply NZ_Pure_S_aux. 
          assert(0<=r). rewrite Heqr.
          apply norm_ge_0 . assert(0<r).   destruct H2.  
          assumption. rewrite Heqr in H2. 
          symmetry in H2.
          apply norm_zero_iff_zero in H2. rewrite H2 in H0.
          destruct H0. reflexivity.  
          assumption. apply Rmult_gt_0_compat.
          assumption. assumption.    
          unfold Pure_State. exists (((R1 / r)%R .* x)).
          split. unfold Pure_State_Vector. split. apply WF_scale.
          assumption.
           rewrite Mscale_adj. rewrite Mscale_mult_dist_r.
          rewrite Cconj_R. rewrite Mscale_mult_dist_l.
          rewrite inner_eq. 
          rewrite Heqr.  
          rewrite Rdiv_unfold. rewrite Rmult_1_l.
          repeat rewrite Mscale_assoc. 
          repeat rewrite RtoC_mult. 
          rewrite <-Rmult_assoc . 
          rewrite (Rmult_assoc  _ (/ norm x) _).
          assert((norm x<> 0)%R). 
          unfold not. intros.
          apply norm_zero_iff_zero in H2. rewrite H2 in H0.
          destruct H0. reflexivity. assumption.  
          rewrite Rinv_l. rewrite Rmult_1_r. 
          rewrite  Rinv_l. rewrite Mscale_1_l. reflexivity.
          assumption. assumption. assumption. reflexivity.
Qed.

(*super M ρ is NZ_Mixed_State_aux *)
Lemma nz_mixed_super_aux : forall {m n} (M : Matrix m n) (ρ: Matrix n n), 
WF_Matrix M-> NZ_Mixed_State_aux ρ ->(super M ρ) <> Zero -> NZ_Mixed_State_aux  (super M ρ).
  Proof.
  intros m n M ρ Hw H1 H2.
  induction H1.
  + unfold super. rewrite Mscale_mult_dist_r.
    rewrite Mscale_mult_dist_l.
    apply nz_Mixed_State_scale_aux. 
    destruct H0. destruct H0. rewrite H1.
    rewrite Mmult_assoc. rewrite Mmult_assoc.
     rewrite <-(Mmult_assoc M ). rewrite <-Mmult_adjoint.
     apply Vector_nz_Mix_State_aux.
     destruct H0.  
     auto_wf. rewrite H1 in *. unfold super in H2.
    rewrite Mscale_mult_dist_r in H2.
    rewrite Mscale_mult_dist_l in H2.
    rewrite Mmult_assoc in H2. rewrite Mmult_assoc in H2.
    rewrite <-(Mmult_assoc M ) in H2 .
    rewrite <-Mmult_adjoint in H2.
    intro. rewrite H3 in H2. 
    rewrite Mmult_0_l in H2.
    rewrite Mscale_0_r in H2. destruct H2. reflexivity.
    assumption.
  + unfold  super in *.
    rewrite Mmult_plus_distr_l in *.
    rewrite Mmult_plus_distr_r in *.
    assert(M × ρ1 × (M) †  = Zero \/ M × ρ1 × (M) †  <> Zero).
    apply Classical_Prop.classic.
    assert(M × ρ2 × (M) †  = Zero \/ M × ρ2 × (M) †  <> Zero).
    apply Classical_Prop.classic.
    destruct H. rewrite H in *. destruct H0.
    rewrite H0 in *. 
    rewrite Mplus_0_l in *. destruct H2. reflexivity.
    rewrite Mplus_0_l. apply IHNZ_Mixed_State_aux2.
    assumption. destruct H0.
    rewrite H0. rewrite Mplus_0_r. 
    apply IHNZ_Mixed_State_aux1. assumption.
    apply NZ_Mix_S_aux; trivial.
    apply IHNZ_Mixed_State_aux1. assumption.
    apply IHNZ_Mixed_State_aux2. assumption.
Qed.

(*big_sum NZ_Mixed_State_aux*)
Local Open Scope nat_scope.
Lemma big_sum_not_0{n:nat}:forall (f:nat-> Square n) n0,
(big_sum f n0) <> Zero ->
(exists i:nat, (i<n0)%nat /\   (f i) <> Zero).
Proof. induction n0; intros H0. simpl in *. destruct H0. reflexivity.
      assert(big_sum f n0 = Zero \/ big_sum f n0 <> Zero).
      apply Classical_Prop.classic. destruct H.
      simpl in H0. rewrite H in H0. rewrite Mplus_0_l in H0.
      exists n0. split. lia. assumption.
       assert(exists i : nat, i < n0 /\ f i <> Zero).
       apply IHn0.  assumption. 
       destruct H1. exists x. split. lia. intuition. 
Qed.

Lemma nz_Mixed_State_aux_big_sum{n:nat}:forall (f:nat-> Square (2^n)) n0,
(n0<>0)%nat->
(forall i:nat, (i<n0)%nat ->  Mixed_State_aux (f i))->
(exists i:nat, (i<n0)%nat /\   (f i) <> Zero)->
NZ_Mixed_State_aux (big_sum f n0).
Proof. induction n0; intros. simpl. intuition. 
       simpl. destruct n0.  simpl. rewrite Mplus_0_l.
       destruct H1. destruct H1. assert(x =0)%nat. lia.
       rewrite H3 in H2.   
       assert(Mixed_State_aux (f 0)).
       apply H0. lia. rewrite NZ_Mixed_State_aux_equiv'  in H4. destruct H4. assumption.
       rewrite H4 in H2. destruct H2. reflexivity.
       assert(Mixed_State_aux (f (S n0))). apply H0. lia.
       rewrite NZ_Mixed_State_aux_equiv'  in H2. 
       destruct H2.
        assert (((big_sum f (S n0))= Zero) \/  (big_sum f (S n0)) <> Zero).
     apply Classical_Prop.classic. destruct H3.
     rewrite H3. rewrite Mplus_0_l. assumption.  econstructor.
     apply IHn0; try lia. intros. apply H0. lia.  
     apply big_sum_not_0 in H3. assumption. assumption.   
       rewrite H2. rewrite Mplus_0_r.
       apply IHn0. lia. 
     intros. apply H0. lia.  
     destruct H1.   destruct H1.
     exists x. split. bdestruct (x =? S n0).
     rewrite H4 in *. rewrite H2 in H3. destruct H3. reflexivity.
     lia. assumption. 
Qed. 

(*big_sum_Cmod*)
Lemma  big_sum_Cmod{n:nat}: forall (f:nat-> Square (2^n)) n0,
(forall i:nat, (i<n0)%nat-> Mixed_State_aux (f i))->
Cmod (trace (big_sum f n0)) = 
big_sum (fun i=> Cmod (trace (f i))) n0.
Proof. induction n0.
    { simpl. intros. rewrite Zero_trace. 
     rewrite Cmod_0.  reflexivity. }

    { intros.
    assert((forall i : nat,
    (i < S n0)%nat -> f i = Zero) \/ ~(forall i : nat,
    (i < S n0)%nat ->
    f i = Zero)).
     apply Classical_Prop.classic. destruct H0.
     rewrite big_sum_0_bounded.  rewrite big_sum_0_bounded.
     rewrite Zero_trace. rewrite Cmod_0. reflexivity.
     intros. rewrite H0. rewrite Zero_trace. rewrite Cmod_0. reflexivity.
     lia. apply H0. simpl. 
     bdestruct (n0=?0).

     rewrite H1. simpl. rewrite Mplus_0_l.
     rewrite Rplus_0_l. reflexivity.

     assert((forall i : nat,
     (i <  n0)%nat -> f i = Zero) \/ ~(forall i : nat,
     (i <  n0)%nat ->
     f i = Zero)).
     apply Classical_Prop.classic. destruct H2.
     rewrite big_sum_0_bounded.  rewrite big_sum_0_bounded.
     rewrite Mplus_0_l.
     rewrite Rplus_0_l. reflexivity.
     intros. rewrite H2. rewrite Zero_trace.
     rewrite Cmod_0. reflexivity. lia.
     intros. rewrite H2. reflexivity. lia. 
     assert(f n0 = Zero \/ f n0 <> Zero).
     apply Classical_Prop.classic. 
     destruct H3.

     rewrite H3. 
     rewrite Mplus_0_r. rewrite Zero_trace.
     rewrite Cmod_0. rewrite Rplus_0_r.
     apply IHn0. intros. apply H. lia.     
     rewrite nz_mixed_state_Cmod_plus_aux. f_equal. apply IHn0.
     intros. apply H. lia.
     apply nz_Mixed_State_aux_big_sum. lia. intros. apply H.
     lia. unfold not.  
     apply Classical_Pred_Type.not_all_ex_not in H2.
     destruct H2. exists x. 
     apply Classical_Prop.imply_to_and.
     assumption. apply NZ_Mixed_State_aux_equiv. split. apply H. lia.
     assumption.   }
Qed.

(*----------------------------------------------------------------------------*)
(*Import Lemma*)
Require Import Complex.
Lemma real_gt_0_aux:forall a b c : R, 0 < a -> 0 < b -> a = (b * c)%R -> 0 < c.
Proof. intuition. 
replace c with (a * / b)%R.
apply Rlt_mult_inv_pos; auto.
subst.
replace (b * c * / b)%R with (b * /b * c)%R by lra.
rewrite Rinv_r; try lra. 
Qed.

Lemma Zero_opp{ m n:nat}: forall m n (A B:Matrix m n),
A .+ (Mopp A) = Zero.
Proof. intros. prep_matrix_equality.
       unfold Mplus. unfold Mopp.
       unfold scale. rewrite<-Copp_mult_distr_l.
       rewrite Cmult_1_l.
       rewrite Cplus_opp_r. reflexivity.
Qed.

Lemma scale_Zero{m n:nat}: forall c (M:Matrix m n),
c .* M = Zero -> c<>C0 -> M = Zero.
Proof. intros. unfold scale in H. 
       unfold Zero in *.
      prep_matrix_equality.
      assert((fun x y : nat => c * M x y) x y=
      c * (M x y)). reflexivity.
      assert(c * (M x y)= C0).
      rewrite H in H1. symmetry. assumption. 
      apply Cmult_integral in H2.
      destruct H2. rewrite H2 in H0. destruct H0.
      reflexivity. assumption.
Qed.

Lemma Cauchy_Schwartz_ver1' : forall {n} (u v : Vector n),
WF_Matrix v ->WF_Matrix u->
v<>Zero-> u <> Zero ->
((exists c, c .*  u = v) -> False)->
  (Cmod ⟨u,v⟩)^2 < (fst ⟨u,u⟩) * (fst ⟨v,v⟩).
Proof. intros n u v Hw Hu H01 H02 Hc. intros.  
       - assert (H := CS_key_lemma u v).
         apply real_gt_0_aux in H.
         lra.  assert(0 <=
         fst
           ⟨ ⟨ v, v ⟩ .* u .+ -1 * ⟨ v, u ⟩ .* v,
           ⟨ v, v ⟩ .* u .+ -1 * ⟨ v, u ⟩ .* v ⟩).
           apply inner_product_ge_0.
           assert(fst
           ⟨ ⟨ v, v ⟩ .* u .+ -1 * ⟨ v, u ⟩ .* v,
           ⟨ v, v ⟩ .* u .+ -1 * ⟨ v, u ⟩ .* v ⟩<> 0).
           unfold not. intros.
           rewrite  <-norm_squared in H1.
           rewrite <-Rsqr_pow2 in H1.
         apply Rsqr_0_uniq in H1.
         apply norm_zero_iff_zero in H1.
         assert(⟨ v, v ⟩ .* u .+ -1 * ⟨ v, u ⟩ .* v .+ ⟨ v, u ⟩ .* v = ⟨ v, u ⟩ .* v).
         rewrite H1. rewrite Mplus_0_l. reflexivity.
         rewrite Mplus_assoc in H2.
         rewrite (Mplus_comm _ _  _ (⟨ v, u ⟩ .* v) ) in H2.
         assert(-1 * ⟨ v, u ⟩ .* v= Mopp(⟨ v, u ⟩ .* v)).
         unfold Mopp. rewrite <-Mscale_assoc.  f_equal.
         rewrite <-RtoC_opp. reflexivity. 
        rewrite H3 in H2. rewrite (@Zero_opp n 1) in H2.
        rewrite Mplus_0_r in H2.
        destruct Hc. 
        exists (/ (⟨ v, u ⟩) * (⟨ v, v ⟩)).
        rewrite <-Mscale_assoc. rewrite H2.
        rewrite Mscale_assoc. rewrite Cinv_l.
        rewrite Mscale_1_l. reflexivity.
        unfold not. intros. rewrite H4 in H2.
        rewrite Mscale_0_l in H2.
        apply scale_Zero in H2. rewrite H2 in H02.
        destruct H02. reflexivity.
        unfold not. intros.
        apply inner_product_zero_iff_zero in H5.
        rewrite H5 in H01. destruct H01. reflexivity.
        assumption. intuition.
              auto_wf. lra.
        
       -  destruct(inner_product_ge_0 v). lra.
         rewrite <-norm_squared in H0.
         rewrite <-Rsqr_pow2 in H0.
         symmetry in H0.
         apply Rsqr_0_uniq in H0.
         apply norm_zero_iff_zero in H0.
         rewrite H0 in H01. destruct H01. reflexivity.
         assumption.
Qed.


Lemma Rmult_in01': forall p1 p2,
0 <= p1 <=1->
0 <= p2 <=1->
0 <= p1 * p2 <=1.
Proof. split. assert(0=0*0)%R. rewrite Rmult_0_l. reflexivity.
     rewrite H1. apply Rmult_le_compat. intuition. intuition.
      intuition. intuition.
        assert(p1 * p2 <= 1*1).
        apply Rmult_le_compat. 
        intuition. intuition. intuition. intuition. 
        rewrite Rmult_1_l in H1. assumption.
Qed.

Lemma trace_mult: forall (m n:nat) (A:Matrix m n) (B:Matrix n m),
trace(Mmult A B) =trace (Mmult B A).
Proof. intros. unfold trace. unfold Mmult. 
       rewrite big_sum_swap_order. 
       apply big_sum_eq. apply functional_extensionality.
       intros. apply big_sum_eq. apply functional_extensionality.
       intros.
apply Cmult_comm. 
Qed.

Local Open Scope C_scope.
Lemma trace_Vector: forall (m n:Vector 1), 
 (trace (m × n)) = (trace m) * (trace n).
Proof. intros. unfold trace.  unfold Mmult. 
       simpl. repeat rewrite Cplus_0_l.
       reflexivity.
Qed.

Lemma big_sum_Cconj: forall (f: nat->C) n,
Cconj (big_sum f n)=big_sum (fun x=> Cconj (f x) ) n.
Proof. induction n; simpl. rewrite Cconj_0.
       reflexivity. rewrite Cconj_plus_distr.
       rewrite IHn. reflexivity.
Qed.

Lemma  trace_adj{  n:nat}:forall ( A: Square n),
trace (A)=Cconj (trace (adjoint A)) .
Proof. intros.   unfold trace. unfold adjoint.
rewrite big_sum_Cconj. apply big_sum_eq_bounded. intros.
      rewrite Cconj_involutive. reflexivity.
Qed.

Lemma trace_vector_mult{n}: forall (x x0:Vector n),
Cmod (trace (x × ((x) † × x0 × (x0) †)))=
(Cmod ⟨ x0, x ⟩ * Cmod ⟨ x0, x ⟩)%R.
Proof. intros.  rewrite trace_mult. 
rewrite Mmult_assoc.
rewrite trace_Vector.
rewrite trace_mult.
rewrite trace_adj.
rewrite Cmod_mult.
rewrite  Cmod_Cconj.
rewrite Mmult_adjoint.
rewrite adjoint_involutive.
rewrite trace_mult.
rewrite inner_trace'. reflexivity.
Qed.

Lemma Mixed_State_mult_trace_le_1:forall {n} (ρ1 :Density n),
Mixed_State ρ1->
forall (ρ2: Density n),
Mixed_State ρ2 ->
0<=Cmod (trace (ρ1 × ρ2))<=1.
Proof. intros n ρ1 Hρ1. 
  induction Hρ1.
  intros.  induction H1.
  {
  destruct H0. destruct H2.
  destruct H0. destruct H2.
  rewrite Mscale_mult_dist_l.
  rewrite Mscale_mult_dist_r.
  rewrite Mscale_assoc.
  rewrite trace_mult_dist.
  rewrite H4. rewrite H3.
  rewrite Mmult_assoc.
  rewrite <-(Mmult_assoc (x) †). 
  rewrite <-RtoC_mult. rewrite Cmod_mult.
  rewrite Cmod_R. rewrite Rabs_right. 
  apply Rmult_in01'. apply Rmult_in01'.
    intuition. intuition. rewrite trace_vector_mult.
  assert(Cmod ⟨ x0, x ⟩ * Cmod ⟨ x0, x ⟩= (Cmod ⟨ x0, x ⟩)^2 )%R.
  simpl. rewrite Rmult_1_r. reflexivity.
  rewrite H5. split. apply pow2_ge_0.
  apply Rle_trans with (fst ⟨ x0, x0 ⟩ * fst ⟨ x, x ⟩)%R.
  apply Cauchy_Schwartz_ver1. 
  destruct H0. unfold inner_product. rewrite H6.
  destruct H2. rewrite H7. simpl. rewrite Rmult_1_l. intuition.
  assert(0<=p * p0 ).
  apply Rmult_le_pos. intuition. intuition. lra. }

{ rewrite Mmult_plus_distr_l.
  repeat rewrite Mscale_mult_dist_l.
  repeat rewrite Mscale_mult_dist_r.
  repeat rewrite Mscale_assoc.
  rewrite Cmult_comm.
  rewrite (Cmult_comm _ p2) .
  repeat rewrite<- Mscale_assoc.
  rewrite trace_plus_dist.
  rewrite trace_mult_dist.
  rewrite (trace_mult_dist _ p2).
  split. apply Cmod_ge_0. 
  apply Rle_trans with (Cmod
  (p1 * trace (p .* (ρ × ρ1)))+ Cmod
  (p2 * trace (p .* (ρ × ρ2))))%R.
  apply Cmod_triangle. 
  repeat rewrite Cmod_mult.
  repeat rewrite Cmod_R. repeat rewrite Rabs_right.
  repeat rewrite <-Mscale_mult_dist_l.
  apply Rplus_mult_le_1. lra. lra.
  assumption. intuition. intuition.
  intuition. intuition. }   

  intros. 
  rewrite Mmult_plus_distr_r.
  repeat rewrite Mscale_mult_dist_l.
  rewrite trace_plus_dist.
  repeat rewrite trace_mult_dist.
  split. apply Cmod_ge_0. 
  apply Rle_trans with (Cmod
  (p1 * trace ( (ρ1 × ρ0)))+ Cmod
  (p2 * trace ((ρ2 × ρ0))))%R.
  apply Cmod_triangle. 
  repeat rewrite Cmod_mult.
  repeat rewrite Cmod_R. repeat rewrite Rabs_right.
  repeat rewrite <-Mscale_mult_dist_l.
  apply Rplus_mult_le_1. lra. lra.
  assumption.
  apply IHHρ1_1. assumption.
  apply IHHρ1_2. assumption.
  intuition. intuition.
Qed.

Lemma Rmult_in01'': forall p1 p2,
0 <= p1 <=1->
0 <= p2 <1->
0<=p1 * p2 <1.
Proof.  split. assert(0=0*0)%R. rewrite Rmult_0_l. reflexivity.
        rewrite H1. apply Rmult_le_compat. intuition. intuition.
        intuition. intuition. destruct (Req_dec p1 1).
        rewrite H1. rewrite Rmult_1_l.  lra. 
        assert(p1 * p2 < 1*1).
        apply Rmult_le_0_lt_compat.
        intuition. intuition. lra. intuition. lra. 
Qed.


Lemma Rplus_mult_lt_1: forall (p1 p2 r1 r2:R),
0 <p1 <=1->
0 <p2 <=1->
p1+p2<=1->
0<=r1 < 1->
0<=r2<= 1->
0<=p1 * r1 + p2 * r2< 1 .
Proof. intros. 
assert(r1<r2\/ r2<=r1).
apply Rlt_or_le.
destruct H4.
split. apply Rplus_le_le_0_compat;
apply Rmult_le_pos; intuition.
apply Rlt_le_trans with ((p1 * r2)%R + (p2 * r2)%R)%R.
apply Rplus_lt_compat_r;
apply Rmult_lt_compat_l. 
intuition. assumption. 
rewrite <-Rmult_plus_distr_r. 
assert((p1 + p2) * r2 <= 1*1).
apply Rmult_le_compat. 
 apply Rplus_le_le_0_compat. intuition. intuition.
intuition. intuition. intuition. 
rewrite Rmult_1_l in H5.
intuition.

split. apply Rplus_le_le_0_compat;
apply Rmult_le_pos; intuition.
apply Rle_lt_trans with (p1 * r1 + p2 * r1 )%R.
apply Rplus_le_compat;
apply Rmult_le_compat;
intuition. 
rewrite <-Rmult_plus_distr_r. 
assert(0<=(p1 + p2) * r1 < 1).
apply Rmult_in01''. lra. lra. 
lra. 
Qed.


Lemma nz_Mixed_State_mult_trace_lt_1:forall {n} (ρ1 :Density n),
NZ_Mixed_State ρ1->
forall (ρ2: Density n),
NZ_Mixed_State ρ2 ->
((exists c, c .*  ρ1= ρ2) -> False) ->
Cmod (trace (ρ1 × ρ2))<1.
Proof. intros n ρ1 Hρ1. induction Hρ1.
      {intros.  induction H1.

       {destruct H0. destruct H3.
       destruct H0. destruct H3.
       rewrite Mscale_mult_dist_l.
       rewrite Mscale_mult_dist_r.
       rewrite Mscale_assoc.
       rewrite trace_mult_dist.
       rewrite H4. rewrite H5.
       rewrite Mmult_assoc.
       rewrite <-(Mmult_assoc (x) †).
       destruct (Req_dec p 1). subst. 
       destruct (Req_dec p0 1). subst.
       Csimpl. repeat rewrite Mscale_1_l in *.
      rewrite trace_vector_mult.
      assert(Cmod ⟨ x0, x ⟩ * Cmod ⟨ x0, x ⟩= (Cmod ⟨ x0, x ⟩)^2 )%R.
      simpl.  rewrite Rmult_1_r. reflexivity.  rewrite H4.
      apply Rlt_le_trans with (fst ⟨ x0, x0 ⟩ * fst ⟨ x, x ⟩)%R.
      apply Cauchy_Schwartz_ver1'.
      apply H0. apply H3.  
      apply Pure_State_Vector_not_Zero. assumption.
      apply Pure_State_Vector_not_Zero. assumption.
      intro. destruct H2.  destruct H5. 
      rewrite<-H2. exists (/ (x1* x1 ^*)).
      rewrite Mscale_mult_dist_l.
      rewrite Mscale_adj.
      rewrite Mscale_mult_dist_r.
      rewrite Mscale_assoc.
      rewrite Mscale_assoc.
      rewrite <-Cmult_assoc.
      rewrite Cinv_l. Msimpl. reflexivity.
      rewrite Cmult_comm.
      rewrite <-Cmod_sqr.  rewrite RtoC_pow.
      apply RtoC_neq. rewrite <-Rsqr_pow2. 
      apply Rgt_neq_0. apply Rlt_0_sqr. 
      intro.  apply Cmod_eq_0 in H5. 
      rewrite H5 in H2. rewrite Mscale_0_l in H2.
      destruct H2. apply Pure_State_Vector_not_Zero in H0.
      destruct H0. reflexivity.
      destruct H0. unfold inner_product. rewrite H5.
      destruct H3. rewrite H6. simpl. rewrite Rmult_1_l. intuition.
       assert(p0<1). lra. Csimpl.
       rewrite Cmod_mult. 
       rewrite Cmod_R. rewrite Rabs_right.
       rewrite Rmult_comm.
       apply Rmult_in01''.
       rewrite Mmult_assoc.
       rewrite <-(Mmult_assoc x).
       apply  Mixed_State_mult_trace_le_1.
       apply NZ_Mixed_State_is_Mixed_State.
       apply Pure_NZ_Mixed. econstructor. 
       split. apply H0. reflexivity. 
       apply NZ_Mixed_State_is_Mixed_State.
       apply Pure_NZ_Mixed.
      econstructor. 
       split. apply H3. reflexivity. 
       lra. lra. 
       assert(p<1). lra.
       rewrite Cmod_mult. rewrite Cmod_mult. 
       repeat rewrite Cmod_R. repeat rewrite Rabs_right.
       rewrite Rmult_comm.
       apply Rmult_in01''.
       rewrite Mmult_assoc.
       rewrite <-(Mmult_assoc x).
       apply  Mixed_State_mult_trace_le_1.
       apply NZ_Mixed_State_is_Mixed_State.
       apply Pure_NZ_Mixed. econstructor. 
       split. apply H0. reflexivity. 
       apply NZ_Mixed_State_is_Mixed_State.
       apply Pure_NZ_Mixed. econstructor. 
       split. apply H3. reflexivity. 
       rewrite Rmult_comm. 
       apply  Rmult_in01''.
       lra. lra.  
       lra. lra. } 
       
      { rewrite Mmult_plus_distr_l.
      repeat rewrite Mscale_mult_dist_l.
      repeat rewrite Mscale_mult_dist_r.
      repeat rewrite Mscale_assoc.
      rewrite Cmult_comm.
      rewrite (Cmult_comm _ p2) .
      repeat rewrite<- Mscale_assoc.
      rewrite trace_plus_dist.
      rewrite trace_mult_dist.
      rewrite (trace_mult_dist _ p2).
      apply Rle_lt_trans with (Cmod
      (p1 * trace (p .* (ρ × ρ1)))+ Cmod
      (p2 * trace (p .* (ρ × ρ2))))%R.
      eapply Cmod_triangle. 
      repeat rewrite Cmod_mult.
      repeat rewrite Cmod_R. repeat rewrite Rabs_right.
      repeat rewrite <-Mscale_mult_dist_l.
      assert((exists c : C, c .* (p .* ρ) = ρ1) \/ ~((exists c : C, c .* (p .* ρ) = ρ1))).
      apply Classical_Prop.classic. 
      destruct H5. destruct H5. 
      assert((exists c : C, c .* (p .* ρ) = ρ2) \/ ~((exists c : C, c .* (p .* ρ) = ρ2))).
      apply Classical_Prop.classic. 
      destruct H6. destruct H6.
      destruct H2. exists (x * p1+ x0 * p2).
      rewrite <-H5. rewrite<- H6 .
      rewrite Mscale_plus_distr_l. 
      rewrite Cmult_comm.  rewrite <-Mscale_assoc.
      f_equal.  rewrite Cmult_comm. rewrite <-Mscale_assoc.
      reflexivity.
      rewrite Rplus_comm. 
      apply IHNZ_Mixed_State2 in H6.
      apply Rplus_mult_lt_1; try lra.
      split. apply Cmod_ge_0.
      assumption. 
      apply Mixed_State_mult_trace_le_1.
      apply NZ_Mixed_State_is_Mixed_State.
      apply nz_Mixed_State_scale.  
      apply Pure_NZ_Mixed. assumption.
      assumption. apply NZ_Mixed_State_is_Mixed_State. assumption.
      apply IHNZ_Mixed_State1 in H5.
      apply Rplus_mult_lt_1; try lra.
      split. apply Cmod_ge_0.
      assumption. 
      apply Mixed_State_mult_trace_le_1.
      apply NZ_Mixed_State_is_Mixed_State.
      apply nz_Mixed_State_scale.  
      apply Pure_NZ_Mixed. assumption.
      assumption.  apply NZ_Mixed_State_is_Mixed_State. assumption.
      lra. lra. } }

    {  intros.
      rewrite Mmult_plus_distr_r.
      repeat rewrite Mscale_mult_dist_l.
      rewrite trace_plus_dist.
      repeat rewrite trace_mult_dist.
      apply Rle_lt_trans with (Cmod
    (p1 * trace ( (ρ1 × ρ0)))+ Cmod
    (p2 * trace ((ρ2 × ρ0))))%R.
      eapply Cmod_triangle. 
      repeat rewrite Cmod_mult.
      repeat rewrite Cmod_R. repeat rewrite Rabs_right.
      repeat rewrite <-Mscale_mult_dist_l.
        assert((exists c : C, c .* (ρ1) = ρ0) \/ ~((exists c : C, c .* ( ρ1) = ρ0))).
      apply Classical_Prop.classic. 
      destruct H4. destruct H4. 
      assert((exists c : C, c .* (ρ2) = ρ0) \/ ~((exists c : C, c .* ( ρ2) = ρ0))).
      apply Classical_Prop.classic. 
      destruct H5. destruct H5.
      destruct H3. 
      assert(fst x > 0 /\ snd x= 0). 
      assert(trace (x .* ρ1) = trace ( ρ0)).
      rewrite H4. reflexivity.  
      rewrite trace_mult_dist in H3.
      assert (trace ρ0= (fst (trace ρ0), snd (trace ρ0))).
      destruct (trace ρ0). reflexivity. rewrite H6 in H3.
      assert (trace ρ1= (fst (trace ρ1), snd (trace ρ1))).
      destruct (trace ρ1). reflexivity.  rewrite H7 in H3.
      rewrite nz_mixed_state_trace_real in H3.
      rewrite nz_mixed_state_trace_real in H3.
      destruct x. unfold Cmult in H3.
      simpl in H3.  repeat rewrite Rmult_0_l in H3.
      repeat rewrite Rmult_0_r in H3.
      repeat rewrite Rplus_0_l in H3.
      repeat rewrite Rmult_0_l in H3.
      repeat rewrite Rminus_0_r in H3.
      injection H3. intros. 
      assert(fst (trace ρ0) > 0).
      apply nz_mixed_state_trace_in01.
      assumption.
      assert(fst (trace ρ1) > 0). apply nz_mixed_state_trace_in01.
      assumption.
      split. simpl. assert(r= (fst (trace ρ0)) / (fst (trace ρ1)))%R.
      rewrite <-H9. rewrite Rmult_comm.
      rewrite Rdiv_unfold.
      rewrite Rmult_assoc. rewrite Rmult_comm.
      rewrite Rmult_assoc. rewrite Rinv_l.
      rewrite Rmult_1_r. reflexivity. lra. 
      rewrite H12. apply Rdiv_lt_0_compat.
      assumption. assumption. simpl.
      apply Rmult_integral in H8. destruct H8. assumption. 
      rewrite H8 in H11. lra. assumption. assumption.

      assert(fst x0 > 0 /\ snd x0= 0). 
      assert(trace (x0 .* ρ2) = trace ( ρ0)).
      rewrite H5. reflexivity.  
      rewrite trace_mult_dist in H6.
      assert (trace ρ0= (fst (trace ρ0), snd (trace ρ0))).
      destruct (trace ρ0). reflexivity. rewrite H7 in H6.
      assert (trace ρ2= (fst (trace ρ2), snd (trace ρ2))).
      destruct (trace ρ2). reflexivity.  rewrite H8 in H6.
      rewrite nz_mixed_state_trace_real in H6.
      rewrite nz_mixed_state_trace_real in H6.
      destruct x0. unfold Cmult in H6.
      simpl in H6.  repeat rewrite Rmult_0_l in H6.
      repeat rewrite Rmult_0_r in H6.
      repeat rewrite Rplus_0_l in H6.
      repeat rewrite Rmult_0_l in H6.
      repeat rewrite Rminus_0_r in H6.
      injection H6. intros. 
      assert(fst (trace ρ0) > 0).
      apply nz_mixed_state_trace_in01.
      assumption.
      assert(fst (trace ρ2) > 0). apply nz_mixed_state_trace_in01.
      assumption.
      split. simpl. assert(r= (fst (trace ρ0)) / (fst (trace ρ2)))%R.
      rewrite <-H10. 
      rewrite Rdiv_unfold.
      rewrite Rmult_assoc.  rewrite Rinv_r.
      rewrite Rmult_1_r. reflexivity. lra. 
      rewrite H13. apply Rdiv_lt_0_compat.
      assumption. assumption. simpl.
      apply Rmult_integral in H9. destruct H9. assumption. 
      rewrite H9 in H12. lra. assumption. assumption.
      assert( ρ1 = /x .* ρ0). rewrite<- H4. rewrite Mscale_assoc.
      rewrite Cinv_l. rewrite Mscale_1_l. reflexivity.
      apply C0_fst_neq. lra.  
      assert( ρ2 = /x0 .* ρ0). rewrite<- H5. rewrite Mscale_assoc.
      rewrite Cinv_l. rewrite Mscale_1_l. reflexivity.
      apply C0_fst_neq. lra.
      exists (/(p1 * /x  +  p2/ x0) ). rewrite H7. rewrite H8.
      repeat rewrite Mscale_assoc.
      rewrite <-Mscale_plus_distr_l. 
      rewrite Mscale_assoc. rewrite Cinv_l. 
      rewrite Mscale_1_l. reflexivity.
      apply C0_fst_neq. destruct x. destruct x0. simpl. 
      repeat rewrite Rmult_1_r. repeat rewrite Rmult_0_l.
      repeat rewrite Rminus_0_r.  simpl in H3. simpl in H6.
      destruct H3. destruct H6. rewrite H9. rewrite H10.
      rewrite Rmult_0_l. repeat rewrite Rplus_0_r. repeat rewrite Rdiv_unfold.
      repeat rewrite Rinv_mult.
      rewrite <-(Rmult_assoc r ).  rewrite <-(Rmult_assoc r1 ).
      repeat rewrite Rinv_r. repeat rewrite Rmult_1_l. 
      assert(0<(p1 * / r + p2 * / r1)%R). apply Rplus_lt_0_compat.
      apply Rmult_gt_0_compat. intuition. apply Rinv_0_lt_compat.
      assumption. 
      apply Rmult_gt_0_compat. intuition. apply Rinv_0_lt_compat.
      assumption. lra. lra. lra. 

      rewrite Rplus_comm. 
      apply IHHρ1_2 in H5.
      apply Rplus_mult_lt_1; try lra.
      split. apply Cmod_ge_0.
      assumption. 
      apply Mixed_State_mult_trace_le_1.
      apply NZ_Mixed_State_is_Mixed_State.
      assumption.  apply NZ_Mixed_State_is_Mixed_State. assumption.
       assumption.

      apply IHHρ1_1 in H4.
      apply Rplus_mult_lt_1; try lra.
      split. apply Cmod_ge_0.
      assumption. 
      apply Mixed_State_mult_trace_le_1.
      apply NZ_Mixed_State_is_Mixed_State.
      assumption.  apply NZ_Mixed_State_is_Mixed_State. assumption.
       assumption.
      lra. lra. } 
Qed.


Lemma Mixed_sqrt_trace: forall {n} (ρ1 ρ2: Density n) (p1 p2: R), 
0<p1<=1->
0<p2<=1->
p1+p2<=1->
NZ_Mixed_State ρ1->
NZ_Mixed_State ρ2->
NZ_Mixed_State (p1 .* ρ1 .+ p2 .* ρ2)->
(((exists c, c .*  ρ1= ρ2) -> False))->
Cmod (trace (Mmult (p1 .* ρ1 .+ p2 .* ρ2)  (p1 .* ρ1 .+ p2 .* ρ2)))<1.  
Proof. intros. rewrite Mmult_plus_distr_l.
        repeat rewrite Mmult_plus_distr_r. 
        repeat rewrite trace_plus_dist.
        repeat rewrite Mscale_mult_dist_r.
        repeat rewrite Mscale_mult_dist_l.
        repeat rewrite Mscale_assoc.
        repeat rewrite trace_mult_dist.
        apply Rle_lt_trans with (Cmod
        (p1 * p1 * trace (ρ1 × ρ1) + p1 * p2 * trace (ρ2 × ρ1))+ 
        Cmod
        (p2 * p1 * trace (ρ1 × ρ2) + p2 * p2 * trace (ρ2 × ρ2)))%R.
        apply Cmod_triangle.
      apply Rle_lt_trans with (
      (Cmod ((p1 * p1 * trace (ρ1 × ρ1))) + Cmod (p1 * p2 * trace (ρ2 × ρ1)))+ 
      (Cmod  ((p2 * p1 * trace (ρ1 × ρ2))) + Cmod (p2 * p2 * trace (ρ2 × ρ2))))%R.
        apply Rplus_le_compat;
        apply Cmod_triangle.  
        repeat rewrite<-RtoC_mult.
        repeat rewrite Cmod_mult.
        repeat rewrite Cmod_R. repeat rewrite Rabs_right.
        apply Rlt_le_trans with (p1 * p1 * 1+ p1 * p2 * 1  +
        (p2 * p1 * 1 + p2 * p2 * 1))%R.
         apply Rplus_lt_compat.
         apply Rplus_le_lt_compat.
         apply Rmult_le_compat_l.
         apply Rmult_le_pos; lra.
         apply Mixed_State_mult_trace_le_1;
         apply NZ_Mixed_State_is_Mixed_State;
         assumption. 

         apply Rmult_lt_compat_l.
         apply Rmult_gt_0_compat; lra.
         apply nz_Mixed_State_mult_trace_lt_1; try
         assumption. intros. destruct H5.
         destruct H6. exists (/x).
         rewrite <-H5. rewrite Mscale_assoc.
         rewrite Cinv_l. rewrite Mscale_1_l.
         reflexivity. 
         unfold not. intros. rewrite H6 in H5.
         rewrite Mscale_0_l in H5. 
         apply NZ_Mixed_not_Zero in H2.
         rewrite H5 in H2. destruct H2. reflexivity. 
         apply Rplus_lt_le_compat.
         apply Rmult_lt_compat_l.
         apply Rmult_gt_0_compat; lra.
         apply nz_Mixed_State_mult_trace_lt_1;
          try
         assumption. 


         apply Rmult_le_compat_l.
         apply Rmult_le_pos; lra.
         apply Mixed_State_mult_trace_le_1;
         apply NZ_Mixed_State_is_Mixed_State;
         assumption.
         repeat rewrite Rmult_1_r.
         assert((p1+p2)^2= p1 * p1 + p1 * p2 + (p2 * p1 + p2 * p2))%R.
         simpl. rewrite Rmult_1_r.
         (* repeat rewrite <-RtoC_mult. *)
         rewrite Rmult_plus_distr_r;
         repeat rewrite Rmult_plus_distr_l.
         reflexivity.
         rewrite <-H6. simpl. 
         rewrite Rmult_1_r.
         assert((p1 + p2) * (p1 + p2) <= 1*1).
         apply Rmult_le_compat;
         try apply Rplus_le_le_0_compat; lra.
         lra. 
         assert(0<=p2 * p2).
         apply Rmult_le_pos; lra. lra.
         assert(0<=p2 * p1).
         apply Rmult_le_pos; lra. lra.
         assert(0<=p1 * p2).
         apply Rmult_le_pos; lra. lra.
         assert(0<=p1 * p1).
         apply Rmult_le_pos; lra. lra.
Qed.

Lemma Pure_sqrt_trace: forall {n} (ρ: Density n), 
Pure_State ρ-> (trace (Mmult (ρ)  (ρ)))=1.  
Proof. intros. inversion_clear H.
       destruct H0. inversion_clear H. 
       rewrite H0. rewrite Mmult_assoc. 
       rewrite <-(Mmult_assoc ((x) †)).
       rewrite H2. rewrite Mmult_1_l.
       rewrite<- H0. apply pure_state_trace_1.
       econstructor. split. econstructor.
       apply H1. assumption. assumption.
       apply WF_adjoint. assumption. 
Qed.

Lemma mixed_state_fst_plus_aux: forall {n} (ρ1  ρ2: Density n), 
Mixed_State_aux ρ1 -> Mixed_State_aux ρ2->  
fst (trace (ρ1 .+ ρ2)) = (fst (trace ρ1) + fst (trace ρ2))%R.
Proof. intros.   
    try rewrite trace_plus_dist; 
    simpl; try reflexivity; try apply Rplus_lt_0_compat;
    try apply mixed_state_trace_gt0_aux;
    try intuition; try repeat rewrite mixed_state_trace_real_aux; 
    try intuition.  
Qed.

Lemma solve_1{n}: forall (q1 q2:Square n) c,
NZ_Mixed_State q1->
NZ_Mixed_State q2->
trace (q1)=C1 /\ trace (q2)=C1->
c .* q1 = q2->
c=C1.
Proof. intros.
assert(fst c =1 /\ snd c= 0).  
assert(trace (c .* q1) = trace (q2)). rewrite H2. reflexivity.
rewrite trace_mult_dist in H3.
assert (trace q1= (fst (trace q1), snd (trace q1))).
destruct (trace q1). reflexivity. rewrite H4 in *.
assert (trace q2= (fst (trace q2), snd (trace q2))).
destruct (trace q2). reflexivity. rewrite H5 in *.
 rewrite nz_mixed_state_trace_real in *; try assumption.
 rewrite nz_mixed_state_trace_real in *; try assumption.
destruct c. unfold Cmult in H3. simpl in H3.
  repeat rewrite Rmult_0_r in H3.
 repeat rewrite Rplus_0_l in H3.
  repeat rewrite Rminus_0_r in H3.
 injection H3. intros. destruct H1. injection H1; intros.
 injection H8; intros. rewrite H9 in *. rewrite H10 in *. 
 simpl in *. repeat rewrite Rmult_1_r in *. injection H3; lra.
 destruct c. simpl in H3. destruct H3. subst. reflexivity. 
Qed.

Lemma  nz_Mixed_State_Cmod_trace_trace{n:nat}: forall (q:Square n),
NZ_Mixed_State_aux q->
(RtoC (Cmod (trace q)) = trace  q).
Proof. intros. assert(trace q = (fst (trace q), snd (trace q))).
destruct (trace q). reflexivity. rewrite H0.
rewrite Cmod_snd_0. simpl. rewrite nz_mixed_state_trace_real_aux.
 reflexivity. assumption. simpl. apply nz_mixed_state_trace_gt0_aux.
 assumption. simpl. rewrite nz_mixed_state_trace_real_aux. reflexivity.
 assumption.
Qed.


Lemma nz_normalize_trace{n:nat}:forall (ρ:Square n),
NZ_Mixed_State_aux ρ->
trace ((/ Cmod (trace ρ))%R .* ρ) = C1 .
Proof. intros. rewrite trace_mult_dist.
rewrite RtoC_inv.
 rewrite nz_Mixed_State_Cmod_trace_trace.
 rewrite Cinv_l. reflexivity.
 apply C0_fst_neq.  apply Rgt_neq_0.
 apply nz_mixed_state_trace_gt0_aux. assumption.
 assumption.  apply Rgt_neq_0.
 apply nz_mixed_state_Cmod_1_aux. assumption.
Qed.


Lemma Mixed_pure: forall {n:nat} (ρ1 ρ2: Density n) (φ:Vector n), 
NZ_Mixed_State ρ1 ->
NZ_Mixed_State ρ2 ->
NZ_Mixed_State (ρ1 .+  ρ2)->
Pure_State_Vector φ ->
ρ1 .+  ρ2= φ  × φ†->  
exists (p1 p2:R), 
and (and (0<p1<=1)%R (0<p2<=1)%R)
  (and (ρ1= p1 .* ( φ  × φ† )) (ρ2= p2 .* ( φ  × φ† ))).
Proof. intros. 
    rewrite <-(normalize_nz_mixed ρ1) in H3.  
    rewrite <-(normalize_nz_mixed ρ2) in H3. 
    remember ((( / Cmod (trace ρ1))%R .* ρ1)).
    remember ((( / Cmod (trace ρ2))%R .* ρ2)).
    assert((exists c : C, c .* m = m0) \/ ~(exists c : C, c .* m = m0)).
    apply Classical_Prop.classic.
    destruct H4. destruct H4. 
    assert(x=C1). apply (@solve_1 n  m m0).
    rewrite Heqm. apply nz_Mixed_State_aux_to01;
    apply nz_Mixed_State_aux_to_nz_Mix_State; assumption. 
    rewrite Heqm0.
    apply nz_Mixed_State_aux_to01;
    apply nz_Mixed_State_aux_to_nz_Mix_State; assumption.
    rewrite Heqm. rewrite Heqm0.
     split; apply nz_normalize_trace;
    apply nz_Mixed_State_aux_to_nz_Mix_State; assumption.
    assumption. 
    rewrite <-H4 in *. rewrite H5 in *. clear H5. 
    rewrite Mscale_1_l in *.  
    rewrite <-Mscale_plus_distr_l in H3.
    rewrite <-RtoC_plus in H3.
    remember ((Cmod (trace ρ1) + Cmod (trace ρ2) )%R ).
    rewrite <-H3.
    exists (Cmod (trace ρ1) / r)%R.
    exists (Cmod (trace ρ2)  /r)%R.
    split. split. rewrite Heqr. apply Rdiv_in_01.
    apply nz_mixed_state_Cmod_1. assumption. 
    apply Rplus_lt_0_compat; apply nz_mixed_state_Cmod_1; assumption.
    rewrite <-Rplus_0_r at 1. apply Rplus_le_compat_l.
    apply Cmod_ge_0.  
    rewrite Heqr. apply Rdiv_in_01.
    apply nz_mixed_state_Cmod_1. assumption. 
    apply Rplus_lt_0_compat; apply nz_mixed_state_Cmod_1; assumption.
    rewrite <-Rplus_0_l at 1. apply Rplus_le_compat_r.
    apply Cmod_ge_0. 
    repeat rewrite Rdiv_unfold.  
    repeat rewrite Mscale_assoc.
    repeat rewrite RtoC_mult.
    repeat rewrite <-Cmult_assoc.
    repeat rewrite <-RtoC_mult.
    repeat rewrite Rinv_l. repeat rewrite Rmult_1_r.
    rewrite Heqm at 1. rewrite Heqm0. 
    split; symmetry; apply normalize_nz_mixed;
     apply nz_Mixed_State_aux_to_nz_Mix_State; assumption.
     rewrite Heqr. apply Rgt_neq_0. 
     apply Rplus_lt_0_compat; apply nz_mixed_state_Cmod_1; assumption.

    assert(Cmod (trace (Mmult (Cmod (trace ρ1) .* m .+ Cmod (trace ρ2) .* m0)  (Cmod (trace ρ1) .* m .+ Cmod (trace ρ2) .* m0)))<1).
    apply Mixed_sqrt_trace.  
    apply nz_mixed_state_Cmod_1. assumption.
    apply  nz_mixed_state_Cmod_1. assumption.
    rewrite <-nz_mixed_state_Cmod_plus.
    apply nz_mixed_state_Cmod_1.  assumption.
     assumption.
    assumption.
     rewrite Heqm.
     apply nz_Mixed_State_aux_to01. 
     apply nz_Mixed_State_aux_to_nz_Mix_State. assumption.
     rewrite Heqm0.
     apply nz_Mixed_State_aux_to01. 
     apply nz_Mixed_State_aux_to_nz_Mix_State. assumption.
     rewrite Heqm. rewrite Heqm0.
     repeat rewrite Mscale_assoc. 
     repeat rewrite <-RtoC_mult.
    repeat rewrite Rinv_r. repeat rewrite Mscale_1_l.
     assumption. 
     assert(Cmod (trace ρ2) > 0). apply nz_mixed_state_Cmod_1.
     assumption. lra.
     assert(Cmod (trace ρ1) > 0). apply nz_mixed_state_Cmod_1.
     assumption. lra.
     apply H4.
    assert(trace (Mmult (φ  × φ†)  (φ  × φ†))=1).
    apply Pure_sqrt_trace. econstructor.
    split. apply H2. reflexivity. 
    assert (Cmod (trace (Mmult (Cmod (trace ρ1) .* m  .+ Cmod (trace ρ2) .* m0) (Cmod (trace ρ1) .* m  .+ Cmod (trace ρ2) .* m0)))=
             Cmod (trace (Mmult (φ  × φ†)  (φ  × φ†)))).
    rewrite H3. reflexivity.
    rewrite H6  in H7. 
    rewrite Cmod_1 in H7. 
     lra. apply nz_Mixed_State_aux_to_nz_Mix_State.
      assumption. 
      apply nz_Mixed_State_aux_to_nz_Mix_State.
      assumption. 
Qed.


