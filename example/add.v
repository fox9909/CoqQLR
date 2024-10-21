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
From Quan Require Import QState_L.
From Quan Require Import QIMP_L.
From Quan Require Import QAssert_L.
From Quan Require Import Par_trace.
From Quan Require Import QRule_Q_L.
From Quan Require Import QRule_E_L.
From Quan Require Import QRule_I_L.
From Quan Require Import QSepar.
From Quan Require Import QRule_QFrame.

Local Open Scope com_scope.







Definition v_1: nat := 0.
Definition v_2: nat := 1. 
Definition v:nat :=2.
Open Scope com_scope.
Local Open Scope nat_scope.
Local Open Scope com_scope.
Definition addM : com :=
  <{ (0 1) :Q= 0 ;
     (1 2) :Q= 0 ; 
     QUnit_One 0 1 hadamard;
     QUnit_One 1 2 hadamard;
     v_1 :=M [[0 1]];
     v_2 :=M [[1 2]];
     v :=v_1+v_2 }>.


Lemma Conj_split_l: forall (F1 F2:State_formula), F1 /\ F2 ->> F1 .
Proof. 
Admitted.
Lemma Conj_split_r: forall (F1 F2:State_formula), F1 /\ F2 ->> F2 .
Proof. 
Admitted.

#[export] Hint Resolve Conj_split_l Conj_split_r: rea_db.

Lemma Mmult0H: ⟨0∣ × ∣+⟩= / √ 2 .* (I 1).
Proof. solve_matrix. 
Qed.


Lemma Mmult1H: ⟨1∣ × ∣+⟩= / √ 2 .* (I 1).
Proof. solve_matrix. 
Qed.

#[export] Hint Rewrite @Mmult0H @Mmult1H @kron_1_r using (auto 100 with wf_db): M_db.


Local Open Scope C_scope.

Lemma MmultH0 : (hadamard) × ∣0⟩ = ∣+⟩. Proof. solve_matrix. Qed.
Lemma H_adjoint: adjoint (hadamard) =hadamard.
Proof. solve_matrix.
Qed.

Lemma MmultH_xplus : adjoint (hadamard) × ∣+⟩ = ∣0⟩. Proof.
assert((hadamard) × ∣0⟩ = ∣+⟩). rewrite MmultH0. reflexivity.
symmetry in H. rewrite H. rewrite <- Mmult_assoc.
assert((hadamard) † × hadamard = I 2).
apply H_unitary. rewrite H0. rewrite Mmult_1_l.
reflexivity. apply WF_qubit0. Qed. 




       Theorem rule_QInit: forall s e,
{{BTrue}} ( s e ) :Q= 0
{{(QExp_s s e  (Vec (2^(e-s)) 0))}}.
Proof. 
unfold hoare_triple.
intros s e s' e' (mu,IHmu) (mu', IHmu').
intros. 
inversion_clear H; simpl in H3.
rewrite sat_Assert_to_State in *.
inversion_clear H0.
apply sat_F. apply H2. intuition.
apply rule_Qinit_aux' with  mu.
intuition. intuition. assumption. 
Qed.






Theorem rule_qframe': forall (F1 F2 F3: State_formula) c,
Considered_Formula F3 ->
({{F1}} c {{F2}}) /\  (NSet.Equal (NSet.inter (fst (Free_state F3)) (fst (MVar c))) (NSet.empty) )
/\ ((option_nat (NSet.max_elt (snd (MVar c)))) <  fst (Free_State F3) \/
snd (Free_State F3) <= ((option_nat (NSet.min_elt (snd (MVar c))))))
->  {{F3 ⊙ F1}} c {{F3 ⊙ F2}}.
Proof. intros.
 eapply rule_conseq. apply rule_qframe.
 apply H. split. apply H0.   apply H0. 
 apply rule_OdotC.
 apply rule_OdotC.
Qed.

Definition P1 (i:nat):= BEq v_1  i.
Definition P2 (i:nat):= BEq v_2  i.
Definition P2_0 (i:nat):= BAnd (P1 0) (BEq v_2  i).
Definition P2_1 (i:nat):= BAnd (P1 1) (BEq v_2  i).

Lemma vector_to_C_refl:forall c, (vector_to_C c) 0 0= c.
Proof. intros. unfold vector_to_C. unfold scale.
       unfold I. simpl. Csimpl .   reflexivity. Qed.

Lemma WF_vec_to_c: forall c, WF_Matrix (vector_to_C c).
Proof. intros. unfold vector_to_C. auto_wf.

Qed.
#[export] Hint Resolve WF_vec_to_c : wf_db.
       

Local Open Scope rule_scope.
Local Open Scope nat_scope.
 Open Scope com_scope.

Lemma npro_pro_inv: forall (pF : list (R* State_formula)) ,
pF = (npro_to_pro_formula (pro_to_npro_formula pF) (get_pro_formula pF)).
Proof. induction pF. simpl. reflexivity.
       destruct a.  
        simpl. f_equal. auto.
Qed.



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




Lemma norm_kron{m n:nat}:forall (M: Vector  m) (N : Vector  n),
norm (kron M N) = (norm M) * norm (N).
Proof.
intros. unfold norm. repeat rewrite rewrite_norm.
unfold kron. simpl Nat.div. rewrite Nat.mod_1_r.
rewrite <-sqrt_mult. f_equal.
Admitted.
#[export] Hint Rewrite @kron_mixed_product @Norm0 @Norm1 @NormH @norm_kron  @MmultH_xplus using (auto 100 with wf_db): M_db.





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



     Ltac classic_slove_aux':= 
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
    match goal with 
    H :?P /\ ?Q
    |- ?P => apply H end . 

Ltac classic_slove := 
    repeat (match goal with 
    H: _ |- Forall_two.Forall_two ?f ?F1 ?F2 => 
    econstructor; try (classic_slove_aux);
    try auto with rea_db; try lia; try lia  
    end). 

   Lemma Vec_qubit0: Vec 2 0= qubit0.
  Proof. unfold Vec. solve_matrix. Qed. 
  Lemma  Vec_qubit1: Vec 2 1= qubit1.
  Proof. unfold Vec. solve_matrix. Qed. 
  #[export] Hint Rewrite @norm_scale @Vec_qubit0 @Vec_qubit1 
   using (auto 100 with wf_db) : M_db.
  

  #[export] Hint Rewrite Rinv_l Rinv_1 : R_db.
    Local Open Scope nat_scope.


 Ltac OpLusC_OMerge_sovle x y:=
  eapply implies_trans;
  [apply (rule_POplusC _ x)|
  simpl; eapply implies_trans;
  [apply (rule_POplusC _ y)|
  simpl; eapply implies_trans;
  [apply rule_OMerg; lra| ] ] ].  



  Lemma big_pOplus'_to_pOplus:forall n (p_n : nat -> R) F_n ,
  ( forall i, i< n -> (0< p_n i)%R)->
   big_pOplus' p_n F_n n (big_pOplus p_n F_n n) .
  Proof. induction n; intros. simpl. econstructor. 
        simpl. apply big_pOplus_cons. 
        apply Rgt_neq_0. apply H. lia.
        apply IHn. intros. apply H. lia.  
    
  Qed.
  
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
simpl. lia. simpl.  
split. 
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

(*QMeas*)
assert (forall i:nat,(
((@Mmult 4 4 1  (@kron 2 2 2 2 (I 1 ⊗ (Vec 2 i × (Vec 2 i) †))
         (I (2))) (∣+⟩ ⊗ ∣+⟩))) ) =
         (I 1 ⊗ (Vec 2 i × (Vec 2 i) †) ⊗ I 2 × (∣+⟩ ⊗ ∣+⟩))).
 reflexivity. 
 

eapply rule_seq. 
eapply rule_conseq_l with ( | ∣+⟩ ⊗ ∣+⟩ >[ 0, 2] /\ big_Sand (fun i : nat => Assn_sub_P v_1 (ANum i) (P1 i)) 2).
simpl.    
admit.

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
repeat rewrite Mscale_assoc. 
Msimpl.
repeat rewrite Nat.mul_1_l .
Msimpl.  
rewrite <-RtoC_inv; try ( apply sqrt_neq_0_compat;  lra).
rewrite Cmod_R;  rewrite Rabs_right; try lra.
autorewrite with R_db.
rewrite RtoC_mult.
repeat rewrite <-Rinv_mult_distr_depr; try (apply sqrt2_neq_0;   lra);
try ( apply sqrt_neq_0_compat;  lra).
autorewrite with R_db; try ( apply sqrt_neq_0_compat;  lra).
Msimpl.  


eapply rule_seq.
eapply rule_sum_pro with (pF1:=([(/ 2, <{ v_1 = 0 && v_2 = 0 }> /\ | ∣0⟩ ⊗ ∣0⟩ >[ 0, 2]);
(/ 2, <{ v_1 = 0 && v_2 = 1 }> /\ | ∣0⟩ ⊗ ∣1⟩ >[ 0, 2])]))
(pF2 := ([(/ 2, <{ v_1 = 1 && v_2 = 0 }> /\ | ∣1⟩ ⊗ ∣0⟩ >[ 0, 2]);
(/ 2,<{ v_1 = 1 && v_2 = 1 }> /\ | ∣1⟩ ⊗ ∣1⟩ >[ 0, 2])]));
simpl.  econstructor. lra. econstructor. lra. econstructor.
econstructor. lra. econstructor. lra. econstructor.
lra.
eapply rule_conseq_l with 
( | ∣0⟩ ⊗ ∣+⟩ >[ 0, 2] /\ big_Sand (fun i : nat => Assn_sub_P v_2 (ANum i) (P2_0 i)) 2).
simpl.
admit.

eapply rule_conseq_r'.
eapply rule_QMeas ; try lia; auto_wf.
apply big_pOplus'_to_pOplus.  intros. 
unfold U_v.  simpl. 
admit.
unfold U_v. simpl.
assert (forall i:nat,(
  ((@Mmult 4 4 1  (@kron 4 4 1 1 (I 2 ⊗ (Vec 2 i × (Vec 2 i) †))
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
rewrite RtoC_mult.
repeat rewrite <-Rinv_mult_distr_depr; try (apply sqrt2_neq_0;   lra);
try ( apply sqrt_neq_0_compat;  lra).
autorewrite with R_db; try ( apply sqrt_neq_0_compat;  lra).
Msimpl.   

unfold P2_0. unfold P1. unfold P2. simpl. apply implies_refl. 

admit. admit.

eapply rule_conseq_l with 
( | ∣1⟩ ⊗ ∣+⟩ >[ 0, 2] /\ big_Sand (fun i : nat => Assn_sub_P v_2 (ANum i) (P2_1 i)) 2).
simpl.
admit.

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
rewrite RtoC_mult.
repeat rewrite <-Rinv_mult_distr_depr; try (apply sqrt2_neq_0;   lra);
try ( apply sqrt_neq_0_compat;  lra).
autorewrite with R_db; try ( apply sqrt_neq_0_compat;  lra).
Msimpl. 


unfold P2_0. unfold P1. unfold P2. simpl. apply implies_refl. 


admit. 
admit. 





simpl.  



(*add*)
remember ( npro_to_pro_formula   [(((<{v= ANum 0}> /\ (QExp_s 0 2 ((kron ∣0⟩ ∣0⟩))) ))) ; 
                 ((<{v = ANum 1}> /\ (QExp_s 0 2 ((kron ∣0⟩ ∣1⟩))) )) ;
                 ((<{v = ANum 1}> /\ (QExp_s 0 2 ((kron ∣1⟩ ∣0⟩))) )); 
                 ((<{v = ANum 2}> /\ (QExp_s 0 2 ((kron ∣1⟩ ∣1⟩))) ))] [(/4)%R; (/4)%R; (/4)%R; (/4)%R]) as post.
                 remember ( npro_to_pro_formula  
                  [ <{ v_1 = 0 && v_2 = 0 }> /\ | ∣0⟩ ⊗ ∣0⟩ >[ 0, 2] ; 
                 (<{ v_1 = 0 && v_2 = 1 }>/\ | ∣0⟩ ⊗ ∣1⟩ >[ 0, 2]) ;
                 (<{ v_1 = 1 && v_2 = 0 }> /\ | ∣1⟩ ⊗ ∣0⟩ >[ 0, 2]); 
                 (<{ v_1 = 1 && v_2 = 1 }> /\ | ∣1⟩ ⊗ ∣1⟩ >[ 0, 2])] [(/ 2 * / 2)%R; (/ 2 * / 2)%R;(/ 2 * / 2)%R; (/ 2 * / 2)%R]) as pre.

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
unfold P1. unfold P2.
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
rewrite (npro_pro_inv post). eapply implies_trans.
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
rewrite (npro_pro_inv
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

