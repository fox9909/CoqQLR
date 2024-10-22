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

Definition v_1: nat := 0.
Definition v_2: nat := 1. 
Definition v:nat :=2.

Definition addM : com :=
  <{ (0 1) :Q= 0 ;
     (1 2) :Q= 0 ; 
     QUnit_One 0 1 hadamard;
     QUnit_One 1 2 hadamard;
     v_1 :=M [[0 1]];
     v_2 :=M [[1 2]];
     v :=v_1+v_2 }>.


Definition P1 (i:nat):= BEq v_1  (ANum i).
Definition P2 (i:nat):= BEq v_2  (ANum i).
Definition P2_0 (i:nat):= BAnd (P1 0) (BEq v_2  (ANum i)).
Definition P2_1 (i:nat):= BAnd (P1 1) (BEq v_2  (ANum i)).


Ltac classic_slove_aux:=
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
    |- _ => apply H1 in H2
    end;
    unfold State_eval in *;
    unfold Pure_eval in *;
    unfold beval in *;
    try  match goal with 
 H :?P /\ ?Q
 |- ?P => apply H end ;
    try match goal with 
    H : if (aeval (?x, d_find ?x ?mu) ?v =? aeval (?x, d_find ?x ?mu) (ANum ?y))
        then True else False 
    |- _ => bdestruct (aeval (x, d_find x mu) v =? aeval (x, d_find x mu) (ANum y));    
    [match goal with 
    H':  aeval (x, d_find x mu) ?v =
        aeval (x, d_find x mu) (ANum ?y)
    |-_=>
      rewrite H'; simpl; intuition
    end  | destruct H]
     end.

Ltac classic_slove := 
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
Proof. induction a; intros; simpl in *; 
       try (f_equal; [apply IHa1 | apply IHa2]; 
         intro; destruct H; [apply NSet.union_2| apply NSet.union_3]; 
         assumption). reflexivity.
      rewrite c_update_find_not. reflexivity.  
      intro. destruct H. apply NSet.add_1. lia.
Qed.

Lemma c_update_beval_eq{s e:nat}: forall i b a c (q:qstate s e),  ~NSet.In i (Free_bexp b) -> 
beval (c, q) b = beval (c_update i a c, q) b.
Proof. induction b; intros; simpl in *;  try reflexivity.
       try (f_equal; erewrite c_update_aeval_eq; f_equal; 
       intro; destruct H; [apply NSet.union_2| apply NSet.union_3]; 
         assumption).
        f_equal.  
        try (f_equal; erewrite c_update_aeval_eq; f_equal; 
        intro; destruct H; [apply NSet.union_2| apply NSet.union_3]; 
          assumption). 
          try (f_equal; erewrite c_update_aeval_eq; f_equal; 
       intro; destruct H; [apply NSet.union_2| apply NSet.union_3]; 
         assumption).
         f_equal.
         try (f_equal; erewrite c_update_aeval_eq; f_equal; 
       intro; destruct H; [apply NSet.union_2| apply NSet.union_3]; 
         assumption). f_equal. apply IHb. assumption.
       try (f_equal; [apply IHb1 | apply IHb2]; 
       intro; destruct H; [apply NSet.union_2| apply NSet.union_3]; 
       assumption ).
       try (f_equal; [apply IHb1 | apply IHb2]; 
       intro; destruct H; [apply NSet.union_2| apply NSet.union_3]; 
       assumption ).
Qed.



Lemma Assn_true: forall i a, ~NSet.In i (Free_aexp a) ->
(BTrue ->> Assn_sub_P i a (BEq i a) ).
Proof. rule_solve.  repeat rewrite c_update_find_eq. 
       apply (c_update_aeval_eq _ _ (aeval (x, (d_find x mu)) a) x (d_find x mu) ) in H.
       apply Nat.eqb_eq in H. rewrite H. assumption. 
Qed.

Lemma  rule_ConjE: forall (F1 F2: State_formula), 
(F2 ->> BTrue) /\ (BTrue ->> F2) ->
F1 ->> F1 /\ F2 .
Proof. unfold assert_implies. intros. apply sat_assert_conj. intuition.
       apply H2. apply rule_PT in H0. assumption.
Qed.

Lemma rule_Conj_two: forall (F1 F2 F: State_formula),
 (F->> F1) ->
 (F ->> F2) ->
(F ->> (F1 /\F2)).
Proof. unfold assert_implies. intros.   apply sat_assert_conj; split;
       auto.
Qed.

Lemma Assn_conj: forall (b1 b2 : bexp) i a,
~NSet.In i (Free_bexp b1) ->
b1 /\ Assn_sub_P  i a b2 ->>
(Assn_sub_P i a (BAnd b1 b2)) . 
Proof. rule_solve. destruct (beval (c_update i (aeval (x, d_find x mu) a) x, d_find x mu) b2).
       apply (c_update_beval_eq _ _ (aeval (x, (d_find x mu)) a) x (d_find x mu) ) in H.
       rewrite<- H.  destruct (beval (x, d_find x mu) b1). simpl. auto.
       destruct H4. destruct H5.
Qed.



Lemma big_pOplus'_to_pOplus:forall n (p_n : nat -> R) F_n ,
( forall i, i< n -> (0< p_n i)%R)->
big_pOplus' p_n F_n n (big_pOplus p_n F_n n) .
Proof. induction n; intros. simpl. econstructor. 
    simpl. apply big_pOplus_cons. 
    apply Rgt_neq_0. apply H. lia.
    apply IHn. intros. apply H. lia.  
Qed.
  

Local Open Scope nat_scope.
Lemma correctness_addM:  
{{ BTrue }}
addM 
{{ APro [((1/2)%R, (SPure <{v = ANum 1}>)) ;  ((1/2)%R, (SPure <{v <> ANum 1}>))] }}.
Proof.  

(*QInit*)
eapply rule_seq. eapply rule_QInit. simpl sub.  
eapply rule_seq. eapply rule_conseq_l. apply rule_OdotE.
eapply rule_qframe' with (F2:= | ∣ 0 ⟩_ (1) >[ 1, 2]).
simpl. intuition. simpl. 
split. eapply rule_QInit. split. apply inter_empty. left.
reflexivity. lia.  

(*QUnit*)
eapply rule_seq. eapply rule_qframe with (F2:=QExp_s 0 1 ∣+⟩).
simpl. lia. simpl.  split. 
eapply rule_conseq_l'. 
eapply rule_QUnit_One; auto_wf; lia. 
unfold U_v. simpl.  rewrite kron_1_l; auto_wf.
rewrite kron_1_r; auto_wf. Msimpl.  apply implies_refl.
split. apply inter_empty. left.
reflexivity. lia.  

eapply rule_seq.
eapply rule_qframe' with (F2:=QExp_s 1 2 ∣+⟩).
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
eapply rule_conseq_l with ( | ∣+⟩ ⊗ ∣+⟩ >[ 0, 2] /\ big_Sand (fun i : nat => Assn_sub_P v_1 (ANum i) (P1 i)) 2).
unfold P1.
simpl. apply rule_ConjE. split. apply rule_PT.
apply rule_Conj_two.  apply Assn_true. simpl. unfold not. apply In_empty.
apply rule_Conj_two.  apply Assn_true. simpl. unfold not. apply In_empty.
apply rule_PT.

eapply rule_QMeas ; try lia; auto_wf.
apply big_pOplus'_to_pOplus.  intros. 
unfold U_v.  simpl. rewrite (H i). Msimpl.   
admit.
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
eapply rule_sum_pro with (pF1:=([((/ 2)%R, P2_0 0 /\ | ∣0⟩ ⊗ ∣0⟩ >[ 0, 2]);
((/ 2)%R, P2_0 1 /\ | ∣0⟩ ⊗ ∣1⟩ >[ 0, 2])]))
(pF2 := ([((/ 2)%R, P2_1 0 /\ | ∣1⟩ ⊗ ∣0⟩ >[ 0, 2]);
((/ 2)%R,P2_1 1 /\ | ∣1⟩ ⊗ ∣1⟩ >[ 0, 2])]));
simpl.  econstructor. lra. econstructor. lra. econstructor.
econstructor. lra. econstructor. lra. econstructor.
lra.
eapply rule_conseq_l with 
( | ∣0⟩ ⊗ ∣+⟩ >[ 0, 2] /\ big_Sand (fun i : nat => Assn_sub_P v_2 (ANum i) (P2_0 i)) 2).
unfold P2_0. unfold P1. simpl. eapply implies_trans. apply rule_ConjC.
apply rule_CconjCon. apply implies_refl. 
apply rule_Conj_two. eapply implies_trans'. apply Assn_conj.
admit. apply rule_ConjE. split. apply rule_PT.  apply Assn_true.
admit. 
apply rule_Conj_two. eapply implies_trans'. apply Assn_conj.
admit. apply rule_ConjE. split. apply rule_PT.  apply Assn_true.
admit. apply rule_PT. 

eapply rule_conseq_r'.
eapply rule_QMeas ; try lia; auto_wf.
apply big_pOplus'_to_pOplus.  intros. 
unfold U_v.  simpl. 
admit.
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

admit. admit.

eapply rule_conseq_l with 
( | ∣1⟩ ⊗ ∣+⟩ >[ 0, 2] /\ big_Sand (fun i : nat => Assn_sub_P v_2 (ANum i) (P2_1 i)) 2).
simpl. eapply implies_trans. apply rule_ConjC.
apply rule_CconjCon. apply implies_refl. 
apply rule_Conj_two. eapply implies_trans'. apply Assn_conj.
admit. apply rule_ConjE. split. apply rule_PT.  apply Assn_true.
admit. 
apply rule_Conj_two. eapply implies_trans'. apply Assn_conj.
admit. apply rule_ConjE. split. apply rule_PT.  apply Assn_true.
admit. apply rule_PT. 

eapply rule_conseq_r'.
eapply rule_QMeas ; try lia; auto_wf.
apply big_pOplus'_to_pOplus.  intros. 
unfold U_v.  simpl. 
admit.
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

admit. 
admit. 

simpl.  
(*add*)
remember ( npro_to_pro_formula   [(((<{v= ANum 0}> /\ (QExp_s 0 2 ((kron ∣0⟩ ∣0⟩))) ))) ; 
                 ((<{v = ANum 1}> /\ (QExp_s 0 2 ((kron ∣0⟩ ∣1⟩))) )) ;
                 ((<{v = ANum 1}> /\ (QExp_s 0 2 ((kron ∣1⟩ ∣0⟩))) )); 
                 ((<{v = ANum 2}> /\ (QExp_s 0 2 ((kron ∣1⟩ ∣1⟩))) ))] [(/4)%R; (/4)%R; (/4)%R; (/4)%R]) as post.
remember ( npro_to_pro_formula  
[P2_0 0 /\ | ∣0⟩ ⊗ ∣0⟩ >[ 0, 2] ; 
(P2_0 1/\ | ∣0⟩ ⊗ ∣1⟩ >[ 0, 2]) ;
(P2_1 0 /\ | ∣1⟩ ⊗ ∣0⟩ >[ 0, 2]); 
(P2_1 1/\ | ∣1⟩ ⊗ ∣1⟩ >[ 0, 2])] [(/ 2 * / 2)%R; (/ 2 * / 2)%R;(/ 2 * / 2)%R; (/ 2 * / 2)%R]) as pre.

eapply rule_conseq with (APro pre) (APro post).
rewrite Heqpre. 
rewrite Heqpost. 
rewrite <-Rinv_mult. assert(2*2=4)%R. lra. rewrite H0.  
eapply rule_sum. econstructor. lra. econstructor.  lra.
econstructor. lra. econstructor.  lra. econstructor.
simpl. reflexivity.
econstructor.
eapply rule_conseq_l'.
eapply QRule_Q_L.rule_assgn. 
unfold P2_0. unfold P1.
admit.
econstructor.
eapply rule_conseq_l'.
eapply QRule_Q_L.rule_assgn.
admit.
econstructor.
eapply rule_conseq_l'.
eapply QRule_Q_L.rule_assgn.
admit.
econstructor.
eapply rule_conseq_l'.
eapply QRule_Q_L.rule_assgn.
admit. econstructor.
rewrite Heqpre. simpl. apply implies_refl.
(*post*)
rewrite <-(pro_npro_swap post). eapply implies_trans.
eapply rule_OCon with (nF2:=
  [( SPure <{ v = ANum 0 }> );
           (SPure <{ v = ANum 1 }> );
           (SPure <{ v =  ANum 1 }> );
           (SPure <{ v = ANum 2 }>) ]).  
rewrite pro_to_npro_formula_length.
rewrite get_pro_formula_length. reflexivity.
rewrite Heqpost; simpl; try lia. classic_slove.
rewrite Heqpost; simpl.
eapply implies_trans.
rewrite <-(pro_npro_swap
([(( / 4)%R, SPure <{ v = ANum 0 }>); ((/ 4)%R, SPure <{ v = ANum 1 }>);
((/ 4)%R, SPure <{ v = ANum 1 }>); (( / 4)%R, SPure <{ v = ANum 2 }>)])).
eapply rule_OCon with (nF2:=
  [( SPure <{ v <> ANum 1 }> );
   (SPure <{ v = ANum 1 }> );
    (SPure <{ v = ANum 1 }> );
   (SPure <{ v <> ANum 1 }>) ]); try reflexivity;
try simpl; classic_slove. 
simpl.  OpLusC_OMerge_sovle 2 1.
OpLusC_OMerge_sovle 0 1.
assert(( / 4 +  / 4)%R= (/2)%R).
lra. rewrite H0. 
apply implies_refl. 
apply Rinv_neq_0_compat. 
admit. admit.
Admitted.

