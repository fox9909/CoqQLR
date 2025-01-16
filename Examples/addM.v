Require Import Reals.
Require Import Coquelicot.Complex.
Require Import Strings.String.
Require Import Lists.List.


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
From Quan Require Import QState_L.
From Quan Require Import QIMP_L.
From Quan Require Import QAssert_L.
From Quan Require Import Reduced.
From Quan Require Import QRule_Q_L.
From Quan Require Import QRule_E_L.
From Quan Require Import QRule_I_L.
From Quan Require Import QSepar.
From Quan Require Import QFrame.
Import Basic. Import Ceval_Prop.



Lemma Mmult0H: ⟨0∣ × ∣+⟩= / √ 2 .* (I 1).
Proof. solve_matrix. 
Qed.

Lemma Mmult1H: ⟨1∣ × ∣+⟩= / √ 2 .* (I 1).
Proof. solve_matrix. 
Qed.

Lemma MmultH0 : (hadamard) × ∣0⟩ = ∣+⟩. Proof. solve_matrix. Qed.
Lemma H_adjoint: adjoint (hadamard) =hadamard.
Proof. solve_matrix. Qed.

Local Open Scope C_scope.

Lemma MmultH_xplus : adjoint (hadamard) × ∣+⟩ = ∣0⟩. Proof.
assert((hadamard) × ∣0⟩ = ∣+⟩). rewrite MmultH0. reflexivity.
symmetry in H. rewrite H. rewrite <- Mmult_assoc.
assert((hadamard) † × hadamard = I 2).
apply H_unitary. rewrite H0. rewrite Mmult_1_l.
reflexivity. apply WF_qubit0. Qed. 

#[export] Hint Rewrite @Mmult0H @Mmult1H @kron_1_r @MmultH0 @MmultH_xplus using (auto 100 with wf_db): M_db.

Lemma Norm0: (norm ∣0⟩)=1 %R.
Proof. unfold norm. unfold qubit0. simpl.
      rewrite Rmult_1_l. repeat rewrite Rmult_0_r.
      repeat rewrite Rplus_0_l. repeat rewrite Rminus_0_r.
      rewrite Rplus_0_r. simpl.
      rewrite sqrt_1.
     reflexivity.
Qed. 


Lemma Norm1: (norm ∣1⟩)=1 %R.
Proof. unfold norm. unfold qubit0. simpl.
      rewrite Rmult_1_l. repeat rewrite Rmult_0_r.
      repeat rewrite Rplus_0_l. repeat rewrite Rminus_0_r.
      rewrite Rplus_0_l. simpl.
      rewrite sqrt_1.
     reflexivity.
Qed. 


Local Open Scope R_scope.
Lemma Norm_plus01: 
norm( ∣0⟩ .+  ∣1⟩)= √ 2.
Proof. intros. unfold norm. repeat rewrite rewrite_norm.
unfold Mplus. simpl.
autorewrite with R_db.
repeat rewrite Cmod_0. repeat rewrite Rmult_0_l.
repeat  rewrite Rplus_0_r.  repeat rewrite Cmod_1. repeat rewrite Rmult_1_l.
repeat rewrite Rplus_0_l. repeat rewrite sqrt_1.
repeat rewrite Cplus_0_l. repeat rewrite Cplus_0_r.
repeat rewrite Cmod_1. 
 rewrite Rmult_1_l.
reflexivity.
Qed.


Lemma NormH: (norm ∣+⟩)=1 %R.
Proof. unfold "∣+⟩". rewrite norm_scale.
      rewrite Norm_plus01.
      unfold Cmod. simpl.
       autorewrite with R_db.
       rewrite <-Rdiv_unfold.
       repeat rewrite sqrt2_div2.
       rewrite Rdiv_unfold. 
       rewrite <-sqrt2_inv.
       autorewrite with R_db.
       rewrite sqrt2_inv_sqrt2.
       reflexivity.
Qed.


Local Open Scope R_scope.
Lemma big_sum_product_R : forall m n (f g:nat->R), 
  n <> O ->
  big_sum f m * big_sum g n = big_sum (fun x => f (x / n)%nat * g (x mod n)%nat) (m * n). 
Proof. intros. 
induction m; simpl. 
+ rewrite Rmult_0_l; reflexivity. 
+ rewrite Rmult_plus_distr_r.
  rewrite IHm. clear IHm.
  pose (big_sum_mult_l (f m) ( g )). rewrite e.    
  remember ((fun x : nat => f (x / n)%nat * g (x mod n)%nat)) as h.
  replace (big_sum (fun x : nat => f m * g x) n) with
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
    rewrite Nat.add_comm.
    pose (big_sum_sum  (m*n) n h). rewrite e0.
    reflexivity. 
Qed.

Lemma big_sum_ge_0' : forall f n, (forall x, 0 <= (f x)) -> (0 <= (big_sum f n))%R.
Proof.
  intros f n H.
  induction n.
  - simpl. lra. 
  - simpl in *.
    rewrite <- Rplus_0_r at 1.
    apply Rplus_le_compat; easy.
Qed.


Lemma norm_kron{m n:nat}:forall (M: Vector  m) (N : Vector  n),
norm (kron M N) = (norm M) * norm (N).
Proof.
intros. unfold norm. repeat rewrite rewrite_norm.
unfold kron. simpl Nat.div. rewrite Nat.mod_1_r.
rewrite <-sqrt_mult. f_equal. destruct (Nat.eq_dec n 0).
subst. rewrite Nat.mul_0_r. simpl. rewrite Rmult_0_r. reflexivity.
destruct (Nat.eq_dec m 0). 
subst. rewrite Nat.mul_0_l. simpl. rewrite Rmult_0_l. reflexivity.
symmetry.
rewrite big_sum_product_R.  apply big_sum_eq.
apply functional_extensionality. intros.     
repeat rewrite <-Rsqr_pow2.
rewrite <-Rsqr_mult. rewrite Cmod_mult. reflexivity. assumption.
apply big_sum_ge_0'. intros. apply pow2_ge_0. 
apply big_sum_ge_0'. intros. apply pow2_ge_0. 
Qed.
#[export] Hint Rewrite @kron_mixed_product @Norm0 @Norm1 @NormH @norm_kron  @MmultH_xplus using (auto 100 with wf_db): M_db.


(*---------------------------------------addM-----------------------------------------------*)

Local Open Scope com_scope.
Local Open Scope rule_scope.
Local Open Scope assert_scope.
Local Open Scope nat_scope.

Definition v1: nat := 0.
Definition v2: nat := 1. 
Definition v:nat :=2.


Notation "v ' " := (AId v) (at level 0, no associativity): com_scope.


Definition addM : com :=
  <{ [[0 1]] :Q= 0 ;
     [[1 2]] :Q= 0 ; 
     hadamard [[0 1]];
     hadamard [[1 2]];
     v1 :=M [[0 1]];
     v2 :=M [[1 2]];
     v := v1 ' + v2 '}>.

Definition P1 (i:nat):=  BEq (v1 ') i.
Definition P2 (i:nat):= BEq (v2 ') i.
Definition P2_0 (i:nat):Pure_formula :=  (P1 0) /\p (BEq (v2 ') i).
Definition P2_1 (i:nat):Pure_formula  :=  (P1 1) /\p (BEq (v2 ') i).


Ltac seman_sovle:=
  unfold assert_implies;
  intros; 
  rewrite sat_Assert_to_State in *;
   rewrite seman_find in *;
   try match goal with 
   H: WF_dstate ?mu /\ StateMap.this ?mu <> [] /\ 
        (forall x:cstate, d_find x ?mu <> Zero ->?Q)
   |-_ => destruct H as [H11 H12]; destruct H12 as [H21 H22];
   split; try assumption; split; try assumption; intros
   end;
   try  match goal with 
   H1:  forall x:cstate, d_find x ?mu <> Zero ->?Q,
   H2: d_find ?x ?mu <> Zero
   |- _ => apply H1 in H2; clear H1
   end;
   unfold State_eval in *;
   try repeat match goal with 
  H: Pure_eval (?P /\p ?Q) ?st |-_ => destruct H
  end;try repeat match goal with 
  H: _ |- Pure_eval (?P /\p ?Q) ?st => try split end;
  try assumption.


Ltac classic_slove_aux:=
seman_sovle;
unfold Pure_eval in *;
unfold beval in *;
try unfold s_update_cstate;unfold aeval in *;
unfold fst in *; try rewrite c_update_find_eq;
try repeat match goal with 
H : if (?y =? ?x) then True else False 
|- _ => bdestruct (y =? x) end;
try repeat match goal with 
H': c_find ?v2 ?x = ?y 
|-_=>  rewrite H'
end;try match goal with 
H: False |-_ => destruct H end; simpl ; intuition.

    Ltac classic_slove:= 
    repeat (match goal with 
    H: _ |- Forall_two ?f ?F1 ?F2 => 
    econstructor; try (classic_slove_aux);
    try auto with rea_db; try lia; try lia  
    end). 

 Ltac OpLusC_OMerge_sovle x y:=
  eapply implies_trans;
  [apply (rule_POplusC _ x)|
  simpl; eapply implies_trans;
  [apply (rule_POplusC _ y)|
  simpl; eapply implies_trans;
  [apply rule_OMerg; lra| ] ] ].  


Lemma IZR_INR_0:IZR 0= INR 0. Proof. rewrite INR_IZR_INZ. f_equal. Qed .

Ltac implies_trans_solve i y:=
match i with 
|0 => eapply implies_trans; [apply y|]
|S _ =>eapply implies_trans; [| apply y]
end.


Local Open Scope nat_scope.
Lemma correctness_addM:  
{{ BTrue }}
addM 
{{ APro [((1/2)%R, (SPure (BEq (AId v) 1))) ;  ((1/2)%R, SPure (BNeq (AId v) 1))] }}.
Proof.  

(*QInit*)
eapply rule_seq. eapply rule_QInit. simpl sub.  
eapply rule_seq. eapply rule_conseq_l. apply rule_OdotE.
eapply rule_qframe' with (F2:= | ∣ 0 ⟩_ (2) >[ 1, 2]).
unfold Considered_F_c. 
simpl. repeat rewrite <-empty_Empty. intuition. 
split. eapply rule_QInit. split. apply inter_empty. left.
reflexivity. apply Qsys_inter_empty';try lia.  

(*QUnit*)
eapply rule_seq. eapply rule_qframe with (F2:=QExp_s 0 1 ∣+⟩).
unfold Considered_F_c. 
simpl;  rewrite Qsys_inter_empty'; try lia. intuition.
 split. 
eapply rule_conseq_l'. 
eapply rule_QUnit_One; auto_wf; lia. 
unfold U_v. simpl.  rewrite kron_1_l; auto_wf.
rewrite kron_1_r; auto_wf. Msimpl.  apply implies_refl. simpl.
split. apply inter_empty. left.
reflexivity. rewrite Qsys_inter_empty'; try  lia.  

eapply rule_seq.
eapply rule_qframe' with (F2:=QExp_s 1 2 ∣+⟩).
unfold Considered_F_c.
simpl; repeat rewrite<-empty_Empty; rewrite Qsys_inter_empty'; try lia. intuition. 
split; simpl; repeat rewrite<-empty_Empty; try rewrite Qsys_inter_empty'; try lia.
eapply rule_conseq_l'. 
eapply rule_QUnit_One; auto_wf; lia. 
unfold U_v. simpl.  rewrite kron_1_l; auto_wf.
rewrite kron_1_r; auto_wf. Msimpl.  apply implies_refl.
split.  apply inter_empty. left.
reflexivity. lia.  

eapply rule_conseq_l. eapply rule_odotT.
eapply rule_conseq_l. eapply rule_Separ.

(*QMeas_1*)
assert (forall i:nat,(((@Mmult 4 4 1  (@kron 2 2 2 2 (I 1 ⊗ (∣ i ⟩_ (2) × (∣ i ⟩_ (2)) †))
         (I (2))) (∣+⟩ ⊗ ∣+⟩))) ) =
         (I 1 ⊗ (∣ i ⟩_ (2) × (∣ i ⟩_ (2)) †) ⊗ I 2 × (∣+⟩ ⊗ ∣+⟩))). 
reflexivity. 
 
eapply rule_seq. 
eapply rule_conseq_l with ( | ∣+⟩ ⊗ ∣+⟩ >[ 0, 2] /\s big_Sand (fun i : nat => PAssn v1 i (P1 i)) 2).
unfold P1.
simpl. apply rule_ConjE. split. apply rule_PT.
apply rule_Conj_two.  apply Assn_true_P. simpl. unfold not. apply In_empty.
apply rule_Conj_two.  apply Assn_true_P. simpl. unfold not. apply In_empty.
apply rule_PT.
 
eapply rule_QMeas ; try lia; auto_wf.
unfold U_v. simpl.
rewrite (H 0). rewrite (H 1).
Msimpl.   
repeat rewrite Mmult_assoc. Msimpl.
repeat rewrite Mscale_mult_dist_r.
repeat rewrite Mscale_kron_dist_l. 
repeat rewrite Mscale_assoc. Msimpl.
repeat rewrite Nat.mul_1_l . Msimpl.  
rewrite <-RtoC_inv; try ( apply sqrt_neq_0_compat;  lra).
rewrite Cmod_R;  rewrite Rabs_right; try lra.
autorewrite with R_db. 
repeat rewrite <-RtoC_inv. rewrite <-RtoC_mult. 
repeat rewrite <-Rinv_mult_distr_depr; try (apply sqrt2_neq_0;   lra);
try ( apply sqrt_neq_0_compat;  lra).
autorewrite with R_db; try ( apply sqrt_neq_0_compat;  lra).
Msimpl.  


eapply rule_seq. 
eapply rule_sum_pro with (pF1:=([((/ 2)%R, P2_0 0 /\s | ∣0⟩ ⊗ ∣0⟩ >[ 0, 2]);
((/ 2)%R, P2_0 1 /\s | ∣0⟩ ⊗ ∣1⟩ >[ 0, 2])]))
(pF2 := ([((/ 2)%R, P2_1 0 /\s | ∣1⟩ ⊗ ∣0⟩ >[ 0, 2]);
((/ 2)%R,P2_1 1 /\s | ∣1⟩ ⊗ ∣1⟩ >[ 0, 2])]));
simpl.  econstructor. lra. econstructor. lra. econstructor.
econstructor. lra. econstructor. lra. econstructor.
lra.
eapply rule_conseq_l with 
( | ∣0⟩ ⊗ ∣+⟩ >[ 0, 2] /\s big_Sand (fun i : nat => PAssn v2 i (P2_0 i)) 2).
unfold P2_0. unfold P1. simpl.

implies_trans_solve 0 (rule_ConjC);
apply rule_CconjCon; try apply implies_refl; 
apply rule_Conj_two; try apply rule_Conj_two;
try apply rule_PT;
implies_trans_solve 1 (Assn_conj_P);
try implies_trans_solve 1 (SAnd_PAnd_eq);
try apply rule_ConjE; try split; try apply rule_PT; try apply Assn_true_P;
simpl; unfold not; try apply In_empty. intro. apply NSet.union_1 in H0. 
destruct H0. apply NSet.add_3 in H0. eapply In_empty. apply H0.
 discriminate. eapply In_empty. apply H0.  
 intro. apply NSet.union_1 in H0. 
destruct H0. apply NSet.add_3 in H0. eapply In_empty. apply H0.
 discriminate. eapply In_empty. apply H0. 


eapply rule_conseq_r'.
eapply rule_QMeas ; try lia; auto_wf.
unfold U_v. simpl.
assert (forall i:nat,( ((@Mmult 4 4 1  (@kron 4 4 1 1 (I 2 ⊗ (∣ i ⟩_ (2)  × (∣ i ⟩_ (2)) †))
           (I (1))) (∣0⟩ ⊗ ∣+⟩))) ) =
           (I 2 ⊗ (∣ i ⟩_ (2) × (∣ i ⟩_ (2)) †) ⊗ I 1 × (∣0⟩ ⊗ ∣+⟩))).
reflexivity. 
 rewrite (H0 0). rewrite (H0 1). Msimpl.
assert ((
(@Mmult (2*2*1) (2*2*1) (1*1) (I 2 ⊗ ∣1⟩⟨1∣)
      (∣0⟩ ⊗ ∣+⟩)))= (I 2 ⊗ ∣1⟩⟨1∣ × (∣0⟩ ⊗ ∣+⟩)))%R.
      reflexivity. rewrite H1. Msimpl.
      assert ((
        (@Mmult (2*2*1) (2*2*1) (1*1) (I 2 ⊗ ∣0⟩⟨0∣)
              (∣0⟩ ⊗ ∣+⟩)))= (I 2 ⊗ ∣0⟩⟨0∣ × (∣0⟩ ⊗ ∣+⟩)))%R.
              reflexivity. rewrite H2. Msimpl.
repeat rewrite Mmult_assoc. Msimpl.
repeat rewrite Mscale_mult_dist_r.
repeat rewrite Mscale_kron_dist_r. 
repeat rewrite Mscale_assoc. 
Msimpl.  
repeat rewrite Nat.mul_1_l .
Msimpl.  
rewrite <-RtoC_inv; try ( apply sqrt_neq_0_compat;  lra).
rewrite Cmod_R;  rewrite Rabs_right; try lra.
autorewrite with R_db. 
rewrite <-RtoC_mult.
repeat rewrite <-Rinv_mult_distr_depr; try (apply sqrt2_neq_0;   lra);
try ( apply sqrt_neq_0_compat;  lra).
autorewrite with R_db; try ( apply sqrt_neq_0_compat;  lra).
Msimpl.     apply implies_refl. 

rewrite <-sqrt_inv.
apply sqrt_neq_0_compat. apply Rinv_0_lt_compat. lra. 
rewrite <-sqrt_inv. assert((0<=√ (/ 2))%R). apply sqrt_pos. lra.

eapply rule_conseq_l with 
( | ∣1⟩ ⊗ ∣+⟩ >[ 0, 2] /\s big_Sand (fun i : nat => PAssn v2 (ANum i) (P2_1 i)) 2).
simpl.

implies_trans_solve 0 (rule_ConjC);
apply rule_CconjCon; try apply implies_refl; 
apply rule_Conj_two; try apply rule_Conj_two;
try apply rule_PT;
implies_trans_solve 1 (Assn_conj_P);
try implies_trans_solve 1 (SAnd_PAnd_eq);
try apply rule_ConjE; try split; try apply rule_PT; try apply Assn_true_P;
simpl; unfold not; try apply In_empty. intro. apply NSet.union_1 in H0. 
destruct H0. apply NSet.add_3 in H0. eapply In_empty. apply H0.
 discriminate. eapply In_empty. apply H0.
 intro. apply NSet.union_1 in H0. 
destruct H0. apply NSet.add_3 in H0. eapply In_empty. apply H0.
 discriminate. eapply In_empty. apply H0. 
 


eapply rule_conseq_r'.
eapply rule_QMeas ; try lia; auto_wf.
unfold U_v. simpl.
assert (forall i:nat,(
  ((@Mmult 4 4 1  (@kron 4 4 1 1 (I 2 ⊗ (∣ i ⟩_ (2) × (∣ i ⟩_ (2)) †))
           (I (1))) (∣1⟩ ⊗ ∣+⟩))) ) =
           (I 2 ⊗ (∣ i ⟩_ (2) × (∣ i ⟩_ (2)) †) ⊗ I 1 × (∣1⟩ ⊗ ∣+⟩))).
   reflexivity. 
 rewrite (H0 0). rewrite (H0 1). Msimpl.
assert ((
(@Mmult (2*2*1) (2*2*1) (1*1) (I 2 ⊗ ∣1⟩⟨1∣)
      (∣1⟩ ⊗ ∣+⟩)))= (I 2 ⊗ ∣1⟩⟨1∣ × (∣1⟩ ⊗ ∣+⟩)))%R.
      reflexivity. rewrite H1. Msimpl.
      assert ((
        (@Mmult (2*2*1) (2*2*1) (1*1) (I 2 ⊗ ∣0⟩⟨0∣)
              (∣1⟩ ⊗ ∣+⟩)))= (I 2 ⊗ ∣0⟩⟨0∣ × (∣1⟩ ⊗ ∣+⟩)))%R.
              reflexivity. rewrite H2. Msimpl.
repeat rewrite Mmult_assoc. Msimpl.
repeat rewrite Mscale_mult_dist_r.
repeat rewrite Mscale_kron_dist_r. 
repeat rewrite Mscale_assoc. 
Msimpl.  
repeat rewrite Nat.mul_1_l .
Msimpl.  
rewrite <-RtoC_inv; try ( apply sqrt_neq_0_compat;  lra).
rewrite Cmod_R;  rewrite Rabs_right; try lra.
autorewrite with R_db.
rewrite <-RtoC_mult.
repeat rewrite <-Rinv_mult_distr_depr; try (apply sqrt2_neq_0;   lra);
try ( apply sqrt_neq_0_compat;  lra).
autorewrite with R_db; try ( apply sqrt_neq_0_compat;  lra).
Msimpl.  apply implies_refl. 

rewrite <-sqrt_inv.
apply sqrt_neq_0_compat. apply Rinv_0_lt_compat. lra. 
rewrite <-sqrt_inv. assert((0<=√ (/ 2))%R). apply sqrt_pos. lra.

simpl.  
(*add*)
remember ( npro_to_pro_formula   [((((BEq (AId v) 0) /\s (QExp_s 0 2 ((kron ∣0⟩ ∣0⟩))) ))) ; 
                 (((BEq (AId v) 1) /\s (QExp_s 0 2 ((kron ∣0⟩ ∣1⟩))) )) ;
                 (((BEq (AId v) 1) /\s (QExp_s 0 2 ((kron ∣1⟩ ∣0⟩))) )); 
                 (((BEq (AId v) 2) /\s (QExp_s 0 2 ((kron ∣1⟩ ∣1⟩))) ))] [(/4)%R; (/4)%R; (/4)%R; (/4)%R]) as post.
remember ( npro_to_pro_formula  
[P2_0 0 /\s | ∣0⟩ ⊗ ∣0⟩ >[ 0, 2] ; 
(P2_0 1/\s | ∣0⟩ ⊗ ∣1⟩ >[ 0, 2]) ;
(P2_1 0 /\s | ∣1⟩ ⊗ ∣0⟩ >[ 0, 2]); 
(P2_1 1/\s | ∣1⟩ ⊗ ∣1⟩ >[ 0, 2])] [(/ 2 * / 2)%R; (/ 2 * / 2)%R;(/ 2 * / 2)%R; (/ 2 * / 2)%R]) as pre.

eapply rule_conseq with (APro pre) (APro post).
rewrite Heqpre. 
rewrite Heqpost. 
rewrite <-Rinv_mult. assert(2*2=4)%R. lra. rewrite H0.  
eapply rule_sum. econstructor. lra. econstructor.  lra.
econstructor. lra. econstructor.  lra. econstructor.
simpl. reflexivity.

unfold P2_0. unfold P2_1. unfold P1.  

econstructor; try apply Forall_two_cons; 
try apply Forall_two_cons;
try apply Forall_two_cons; try apply Forall_two_nil;
try eapply rule_conseq_l';
try eapply rule_SAssgn;
implies_trans_solve 1 Assn_comm;
implies_trans_solve 1 Assn_conj_F; simpl; try unfold not; try apply In_empty;
implies_trans_solve 1 rule_ConjC;
eapply rule_CconjCon; try apply implies_refl;


classic_slove_aux.

rewrite Heqpre. simpl. apply implies_refl.
(*post*)
rewrite <-(pro_npro_swap post). eapply implies_trans.
eapply rule_OCon with (nF2:=
  [( SPure <{ v ' = 0 }> );
           (SPure <{ v ' = 1 }> );
           (SPure <{ v ' = 1 }>);
           (SPure <{ v ' = 2 }>) ]).  
rewrite pro_to_npro_formula_length.
rewrite get_pro_formula_length. reflexivity.
rewrite Heqpost; simpl; try lia;

classic_slove.
rewrite Heqpost; simpl.
eapply implies_trans.
rewrite <-(pro_npro_swap
([(( / 4)%R, SPure <{ v ' = 0 }>); ((/ 4)%R, SPure <{ v ' = 1 }>);
((/ 4)%R, SPure <{ v ' = 1 }>); (( / 4)%R, SPure <{ v ' = 2 }>)])).
eapply rule_OCon with (nF2:=
  [( SPure  <{ v ' <> 1 }>);
   (SPure <{ v ' =  1 }> );
    (SPure <{ v ' =  1 }> );
   (SPure <{ v ' <>  1 }>) ]); try reflexivity;
try simpl; classic_slove. 
simpl.  OpLusC_OMerge_sovle 2 1.
OpLusC_OMerge_sovle 0 1.
assert(( / 4 +  / 4)%R= (/2)%R).
lra. rewrite H0. 
apply implies_refl. 
apply Rinv_neq_0_compat. 

apply sqrt_neq_0_compat. lra. 
rewrite <-sqrt_inv. assert((0<=√ (/ 2))%R). apply sqrt_pos. lra.
Qed. 

