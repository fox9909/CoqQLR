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
From Quan Require Import ParDensityO.
From Quan Require Import QState.
From Quan Require Import QIMP_L.
From Quan Require Import QAssert.
From Quan Require Import Par_trace.
From Quan Require Import QRule_Q_L.
From Quan Require Import QRule_E_L.
From Quan Require Import QRule_I_L.
From Quan Require Import QSepar.
From Quan Require Import QRule_QFrame.
Import Basic. Import Ceval_Linear.
Local Open Scope com_scope.
Local Open Scope rule_scope.
Local Open Scope assert_scope.
Local Open Scope nat_scope.


Theorem rule_asgn_aux :  forall (F:State_formula) (i:nat) ( a:aexp) 
(s e:nat) (mu : list (cstate * qstate s e)) (mu': list (cstate * qstate s e)),
WF_dstate_aux mu->
ceval_single (<{i := a}>) mu mu' ->
State_eval_dstate (SAssn i a F) mu->
State_eval_dstate F mu'.
Proof. intros P i a s e mu. induction mu; intros; inversion H; subst.
  --simpl in H0. inversion H0; subst. simpl in H1. destruct H1.
  -- destruct mu. inversion H0; subst. inversion_clear H10; subst.
     simpl. econstructor.  simpl in H1. inversion_clear H1.
     assumption. apply Forall_nil.
     destruct a0. inversion_clear H0. 
     apply d_seman_app_aux.
     apply WF_state_dstate_aux.  
     apply WF_state_eq with (c,q). reflexivity.
     assumption. apply WF_ceval with (<{ i := a }>)
      ((p :: mu)). assumption. assumption.
    inversion_clear H1. simpl in H0. simpl.
    econstructor. assumption. apply Forall_nil.
     apply IHmu. intuition. assumption. 
     inversion_clear H1. apply State_eval_dstate_Forall.
     discriminate.  assumption.
Qed. 

Theorem rule_assgn: forall (F:State_formula) (i:nat) ( a:aexp),
             {{SAssn i a F}} i := a {{F}}.
Proof. unfold hoare_triple;
       intros F X a s e (mu,IHmu) (mu', IHmu').
       intros. 
       inversion_clear H; simpl in H2.
       rewrite sat_Assert_to_State in *.
       inversion_clear H0.
       apply sat_F. eapply WF_ceval. apply H1. apply H2. 
       apply rule_asgn_aux with X a mu.
       intuition. intuition. assumption. 
Qed. 

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
    H: _ |- Forall_two.Forall_two ?f ?F1 ?F2 => 
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

Lemma c_update_aeval_eq{s e:nat}: forall i a b c (q:qstate s e),  ~NSet.In i (Free_aexp a) -> 
aeval (c, q) a = aeval (c_update i b c, q) a.
Proof. induction a; intros; simpl in *; [ | | | | | | | | | f_equal];
       try (f_equal;  [rewrite (IHa1 b) | rewrite (IHa2 b)]; try reflexivity;
         intro; destruct H; [apply NSet.union_2| apply NSet.union_3]; 
         assumption); try reflexivity.
      rewrite c_update_find_not. reflexivity.  
      intro. destruct H. apply NSet.add_1. lia. 
       rewrite (IHa1  b). reflexivity. 
       intro. destruct H. apply NSet.union_2. apply NSet.union_2.
       assumption. 
       rewrite (IHa2  b). reflexivity. 
       intro. destruct H. apply NSet.union_2. apply NSet.union_3.
       assumption.
       rewrite (IHa3  b). reflexivity.
       intro. destruct H. apply NSet.union_3.
       assumption.
Qed.

Lemma c_update_beval_eq{s e:nat}: forall i b a c (q:qstate s e),  ~NSet.In i (Free_bexp b) -> 
beval (c, q) b = beval (c_update i a c, q) b.
Proof. induction b; intros; simpl in *; [ | | | f_equal| | f_equal | f_equal|  ];
       try (f_equal; erewrite c_update_aeval_eq; f_equal; 
       intro; destruct H; [apply NSet.union_2| apply NSet.union_3]; 
         assumption); try apply IHb; try assumption;
         try (f_equal; [apply IHb1 | apply IHb2]; 
         intro; destruct H; [apply NSet.union_2| apply NSet.union_3]; 
         assumption ); try reflexivity. 
Qed.

Lemma Assn_true_F: forall i a, ~NSet.In i (Free_aexp a) ->
(BTrue ->> SAssn i a (BEq (i ') a) ).
Proof. rule_solve.  repeat rewrite c_update_find_eq. 
       apply (c_update_aeval_eq _ _ (aeval (x, (d_find x mu)) a) x (d_find x mu) ) in H.
       apply Nat.eqb_eq in H. rewrite H. assumption. 
Qed.


Lemma Assn_true_P: forall i a, ~NSet.In i (Free_aexp a) ->
(BTrue ->> PAssn i a (BEq (AId i) a) ).
Proof. rule_solve.  repeat rewrite c_update_find_eq. 
       apply (c_update_aeval_eq _ _ (aeval (x, (d_find x mu)) a) x (d_find x mu) ) in H.
       apply Nat.eqb_eq in H. rewrite H. assumption. 
Qed.

Lemma  rule_ConjE: forall (F1 F2: State_formula), 
(F2 ->> BTrue) /\ (BTrue ->> F2) ->
F1 ->> F1 /\s F2 .
Proof. unfold assert_implies. intros. apply sat_assert_conj. intuition.
       apply H2. apply rule_PT in H0. assumption.
Qed.

Lemma rule_Conj_two: forall (F1 F2 F: State_formula),
 (F->> F1) ->
 (F ->> F2) ->
(F ->> (F1 /\s F2)).
Proof. unfold assert_implies. intros.   apply sat_assert_conj; split;
       auto.
Qed.


Lemma Assn_conj_P: forall (P1 P2 : Pure_formula) i a,
~NSet.In i ( (Free_pure P1)) ->
P1 /\p PAssn i a P2 ->>
(PAssn i a (P1 /\p P2)). 
Proof. rule_solve.  apply (cstate_eq_P P3 x ); try assumption.
       unfold cstate_eq. intros. destruct (eq_dec j i).
       rewrite e0 in *. destruct H. assumption.
       rewrite c_update_find_not. reflexivity. lia.
Qed.


Lemma Assn_conj_F: forall (F1 F2 : State_formula) i a,
~NSet.In i (fst (Free_state F1)) ->
F1 /\s SAssn i a F2 ->>
(SAssn i a (F1 /\s F2)) . 
Proof. rule_solve.  apply (cstate_eq_F F1 x ); try assumption.
       unfold cstate_eq. intros. destruct (eq_dec j i).
       rewrite e0 in *. destruct H. assumption.
       rewrite c_update_find_not. reflexivity. lia.
Qed.

Lemma Assn_comm:forall i a (F1 F2:State_formula), 
SAssn i a (F1 /\s F2) ->> SAssn i a (F2 /\s F1).
Proof. rule_solve.
  
Qed.


Lemma big_pOplus'_to_pOplus:forall n (p_n : nat -> R) F_n ,
( forall i, i< n -> (0< p_n i)%R)->
big_pOplus' p_n F_n n (big_pOplus p_n F_n n) .
Proof. induction n; intros. simpl. econstructor. 
    simpl. apply big_pOplus_cons. 
    apply Rgt_neq_0. apply H. lia.
    apply IHn. intros. apply H. lia.  
Qed.




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
eapply rule_qframe' with (F2:= | ∣ 0 ⟩_ (1) >[ 1, 2]).
unfold Considered_Formula_F_c.
simpl. intuition. simpl.  
split. eapply rule_QInit. split. apply inter_empty. left.
reflexivity. lia.  

(*QUnit*)
eapply rule_seq. eapply rule_qframe with (F2:=QExp_s 0 1 ∣+⟩).
unfold Considered_Formula_F_c.
simpl. lia. simpl.  split. 
eapply rule_conseq_l'. 
eapply rule_QUnit_One; auto_wf; lia. 
unfold U_v. simpl.  rewrite kron_1_l; auto_wf.
rewrite kron_1_r; auto_wf. Msimpl.  apply implies_refl.
split. apply inter_empty. left.
reflexivity. lia.  

eapply rule_seq.
eapply rule_qframe' with (F2:=QExp_s 1 2 ∣+⟩).
unfold Considered_Formula_F_c.
simpl. lia. simpl.  
split. eapply rule_conseq_l'. 
eapply rule_QUnit_One; auto_wf; lia. 
unfold U_v. simpl.  rewrite kron_1_l; auto_wf.
rewrite kron_1_r; auto_wf. Msimpl.  apply implies_refl.
split. apply inter_empty. left.
reflexivity. lia.  

eapply rule_conseq_l. eapply rule_odotT.
eapply rule_conseq_l. eapply rule_Separ.

(*QMeas_1*)
assert (forall i:nat,(((@Mmult 4 4 1  (@kron 2 2 2 2 (I 1 ⊗ (Vec 2 i × (Vec 2 i) †))
         (I (2))) (∣+⟩ ⊗ ∣+⟩))) ) =
         (I 1 ⊗ (Vec 2 i × (Vec 2 i) †) ⊗ I 2 × (∣+⟩ ⊗ ∣+⟩))). 
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
assert (forall i:nat,( ((@Mmult 4 4 1  (@kron 4 4 1 1 (I 2 ⊗ (Vec 2 i × (Vec 2 i) †))
           (I (1))) (∣0⟩ ⊗ ∣+⟩))) ) =
           (I 2 ⊗ (Vec 2 i × (Vec 2 i) †) ⊗ I 1 × (∣0⟩ ⊗ ∣+⟩))).
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
  ((@Mmult 4 4 1  (@kron 4 4 1 1 (I 2 ⊗ (Vec 2 i × (Vec 2 i) †))
           (I (1))) (∣1⟩ ⊗ ∣+⟩))) ) =
           (I 2 ⊗ (Vec 2 i × (Vec 2 i) †) ⊗ I 1 × (∣1⟩ ⊗ ∣+⟩))).
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

econstructor; try apply Forall_two.Forall_two_cons; 
try apply Forall_two.Forall_two_cons;
try apply Forall_two.Forall_two_cons; try apply Forall_two.Forall_two_nil;
try eapply rule_conseq_l';
try eapply rule_assgn;
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

