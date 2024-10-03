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


Fixpoint pro_formula_scale (pF: pro_formula ) (p: R): pro_formula:=
  match pF with 
  |[]=>[]
  |(h, F):: pF' => ((p*h)%R, F) :: (pro_formula_scale pF' p)
  end.

Fixpoint pro_formula_linear (pF:list pro_formula ) (p_n: list R): pro_formula:=
  match pF, p_n with 
  |[], [] =>[]
  |[], _ => []
  |_, [] => []
  |F :: pF', h::p' => (pro_formula_scale F h ) ++ (pro_formula_linear pF' p')
  end.



Lemma d_app_empty_r{s e:nat}: forall (mu:dstate s e), 
dstate_eq (d_app  mu (d_empty s e))  mu .
Proof. intros (mu , IHmu).
       unfold d_app. unfold d_empty.
       unfold StateMap.empty .
       unfold StateMap.Raw.empty.
       unfold StateMap.Raw.map2. unfold dstate_eq.
       simpl. apply map2_nil_r.
Qed.

Lemma get_pro_formula_scale: forall pF p,
get_pro_formula (pro_formula_scale pF p) =
map (fun x : R => (p * x)%R) (get_pro_formula pF).
Proof. induction pF;intros; try destruct a; simpl; try reflexivity.
 f_equal; auto. 
Qed.


Lemma get_pro_formula_app:forall pF1 pF2 p1 p2,
(get_pro_formula
  (pro_formula_scale pF1 p1 ++ pro_formula_scale pF2 p2))=
( map (fun x=> (p1* x)%R) (get_pro_formula pF1)) 
 ++(map (fun x=> (p2* x)%R) (get_pro_formula pF2)).
Proof. induction pF1. destruct pF2; intros; simpl.
  -reflexivity.
  -destruct p. simpl. 
   f_equal. apply get_pro_formula_scale.
  - intros. destruct a. simpl. f_equal.
    apply IHpF1.
Qed.

Lemma  big_dapp_app{ s e:nat}: forall (p1 p2: list R) (mu_n1 mu_n2: list (dstate s e)),
length p1= length mu_n1->
length p2= length mu_n2->
dstate_eq (big_dapp (p1 ++ p2) (mu_n1 ++ mu_n2))
(d_app (big_dapp p1 mu_n1) (big_dapp p2 mu_n2) ).
Proof. induction p1; intros. destruct mu_n1. simpl.
       apply dstate_eq_sym .
       apply d_app_empty_l.
       simpl in H.  lia.
       destruct mu_n1. simpl in H. lia.
       simpl. apply dstate_eq_trans with 
       ((d_app (d_scale_not_0 a d)
       (d_app (big_dapp p1 mu_n1) (big_dapp p2 mu_n2)) )) .
       apply d_app_eq. 
       apply dstate_eq_refl.
       apply IHp1. injection H. intuition.
       assumption.
       apply dstate_eq_sym.
       apply d_app_assoc'.
Qed.

Lemma  big_dapp_scale{ s e:nat}: forall  pF1 p1 (mu_n: list (dstate s e)),
length pF1= length mu_n->
dstate_eq (big_dapp (map (fun x : R => (p1 * x)%R) (get_pro_formula pF1)) mu_n)
(d_scale_not_0 p1 (big_dapp (get_pro_formula pF1) mu_n)).
Proof. induction pF1; intros; simpl. 
       destruct mu_n.
       apply dstate_eq_sym.
        apply d_scale_empty'.
        simpl in H. lia.
        destruct mu_n. 
        simpl in H. lia.
        destruct a. simpl.   
        apply dstate_eq_trans with 
        ((d_app (d_scale_not_0 (p1 * r) d)
        (d_scale_not_0 p1 (big_dapp (get_pro_formula pF1) mu_n)))).
        apply d_app_eq.
        apply dstate_eq_refl.
        apply IHpF1. injection H. intuition.
        apply dstate_eq_trans with 
        ((d_app (d_scale_not_0 p1 (d_scale_not_0 r d))
        (d_scale_not_0 p1 (big_dapp (get_pro_formula pF1) mu_n)))).
        apply d_app_eq.
        apply dstate_eq_sym. 
        apply d_scale_assoc'.
        apply dstate_eq_refl.
        apply d_scalar_app_distr'.
       
  
Qed.



Lemma pro_to_npro_formula_scale: forall pF p,
pro_to_npro_formula (pro_formula_scale pF p)=
pro_to_npro_formula pF.
Proof. induction pF; intros; 
try destruct a; simpl; try reflexivity.
f_equal. auto. 
Qed.



Lemma big_and_app{ s e:nat}: forall (nF1 nF2 : npro_formula) (mu_n1 mu_n2:list (dstate s e)),
big_and mu_n1 nF1->
big_and mu_n2 nF2->
big_and (mu_n1 ++ mu_n2) (nF1++nF2) .
Proof. induction nF1; intros.
       destruct mu_n1. simpl.
       assumption.
       inversion_clear H.
       destruct mu_n1.
       inversion_clear H.
       inversion_clear H.
      simpl. auto. 
Qed.

Lemma  Forall_not_0: forall (p_n:list R) p,
Forall (fun x:R => x<>0) p_n->
p<>0->
Forall (fun x : R => (p * x)%R <> 0) p_n. 
Proof. induction p_n; intros; simpl.
       econstructor.
       inversion H; subst.
       econstructor. 
      apply Rmult_integral_contrapositive_currified.
      assumption. 
      assumption. auto. 
Qed.

Lemma  Forall_ge_0: forall (p_n:list R) p,
Forall (fun x:R => 0<=x) p_n->
0<p->
Forall (fun x : R => 0<=(p * x)%R ) p_n. 
Proof. induction p_n; intros; simpl.
       econstructor.
       inversion H; subst.
       econstructor. apply Rmult_le_pos;  lra. auto. 
Qed.







Theorem rule_sum_pro: forall (F1 F2:State_formula ) (pF1 pF2: pro_formula) c (p1 p2: R),
Forall (fun x : R => x <> 0) (get_pro_formula pF1) ->
Forall (fun x : R => x <> 0) (get_pro_formula pF2) ->
              p1<>0 /\ p2<> 0->
              {{F1}} c {{pF1}}->
              {{F2}} c {{pF2}} ->
            {{APro [(p1,F1);(p2,F2)]}} c
            {{pro_formula_linear [pF1; pF2] [p1; p2]}}.
Proof.  unfold hoare_triple. intros F1 F2 pF1 pF2 c p1 p2 HF1 HF2.
intros.  inversion_clear H3. inversion_clear H6.
simpl in *.

 assert(exists (mu_n': list (dstate s e)), 
 and (big_ceval mu_n c mu_n') 
 (dstate_eq mu' (big_dapp [p1;p2] mu_n'))).  
 apply ceval_big_dapp with mu.
 apply big_dapp'_length with mu'0. assumption. 
 apply dstate_eq_trans with mu'0. assumption.
 apply big_dapp_eq with [p1;p2] mu_n. assumption.
 apply big_dapp'_to_app. apply big_dapp'_length with mu'0.
 assumption. econstructor. lra. econstructor. lra.
 econstructor. assumption.
 destruct H6. destruct H6.

  rewrite app_nil_r.  destruct mu_n.
  inversion_clear H3. destruct mu_n. 
  inversion_clear H3. inversion_clear H12.
  destruct mu_n. destruct x. inversion_clear H6.
  destruct x. inversion_clear H6. inversion_clear H12.
  destruct x.  simpl in *. inversion H3; subst.
  inversion H17; subst. inversion H19; subst. clear H19. 
  clear H17. clear H3.
  destruct H8. destruct H8. clear H11. 
  inversion_clear H6. inversion_clear H12. clear H13.

  pose H11. pose H6.
 apply H0 in c0. apply H1 in c1.
 inversion_clear c0. inversion_clear H14.
 inversion_clear c1. inversion_clear H22. 

econstructor. inversion_clear H2. assumption.
econstructor. 
rewrite Forall_app.
admit.
rewrite sum_over_list_app_formula.
admit.
econstructor.
rewrite get_pro_formula_app. 
 assert (big_dapp'
 (map (fun x : R => (p1 * x)%R) (get_pro_formula pF1) ++
   map (fun x : R => (p2 * x)%R) (get_pro_formula pF2)) 
 (mu_n ++ mu_n0) (big_dapp (map (fun x : R => (p1 * x)%R) (get_pro_formula pF1) ++
 map (fun x : R => (p2 * x)%R) (get_pro_formula pF2)) (mu_n ++ mu_n0) ) ).
 apply big_dapp'_to_app.
 repeat rewrite app_length.
 repeat rewrite map_length. 
 f_equal; eapply big_dapp'_length; [apply H15| apply H23].
 apply Forall_app. 
 split; apply Forall_map.
 apply Forall_not_0; intuition.
 apply Forall_not_0; intuition.
  apply H22.
  apply dstate_eq_trans with 
  (d_app (big_dapp (map (fun x : R => (p1 * x)%R) (get_pro_formula pF1)
  ) mu_n )  (big_dapp (map (fun x : R => (p2 * x)%R) (get_pro_formula pF2))
  mu_n0)). 
  apply dstate_eq_trans with 
  ((d_app
  (d_scale_not_0 p1 (big_dapp (get_pro_formula pF1) mu_n))
  (d_scale_not_0 p2 (big_dapp (get_pro_formula pF2) mu_n0)))).
   apply dstate_eq_trans with 
   ((d_app (d_scale_not_0 p1  mu'0)
   (d_scale_not_0 p2 mu'1))).
   apply dstate_eq_trans with 
   ((d_app (d_scale_not_0 p1  d1)
   (d_scale_not_0 p2 d2))).
   apply dstate_eq_trans with 
   ((d_app (d_scale_not_0 p1 d1)
   (d_app (d_scale_not_0 p2 d2) (d_empty s e)))).
  assumption.
  apply d_app_eq. apply dstate_eq_refl.
  apply d_app_empty_r.
  apply d_app_eq;
  apply d_scale_not_0_eq;
  assumption.
  apply d_app_eq;
  apply d_scale_not_0_eq;
  eapply big_dapp_eq;
  [apply H15
  | apply big_dapp'_to_app; [eapply big_dapp'_length; apply H15 | assumption]|
  apply H23 | apply big_dapp'_to_app;
  [eapply big_dapp'_length; apply H23 | assumption] ].
  apply d_app_eq;
  apply dstate_eq_sym;
  apply big_dapp_scale;
  rewrite <-get_pro_formula_length;
  eapply big_dapp'_length; [apply H15| apply H23].
  apply dstate_eq_sym;
  apply big_dapp_app;
  rewrite map_length;
  eapply big_dapp'_length; [apply H15| apply H23].
  rewrite pro_to_npro_formula_app.
  repeat rewrite pro_to_npro_formula_scale.
  apply big_and_app; auto.
  apply Forall_app.
  split. 
  assert(d_trace mu' = d_trace d1).
  inversion_clear H9.
  rewrite (ceval_trace_eq' c _ _ d d1).
  rewrite H22. 
  apply ceval_trace_eq' with c.
  apply WWF_dstate_aux_to_WF_dstate_aux.
  apply H4. assumption.
  inversion_clear H3. 
  apply WWF_dstate_aux_to_WF_dstate_aux.
  assumption. assumption.
  rewrite H22. assumption.
  assert(d_trace mu' = d_trace d2).
  inversion_clear H9. inversion_clear H27.
  rewrite (ceval_trace_eq' c _ _ d0 d2).
  rewrite H9. 
  apply ceval_trace_eq' with c.
  apply WWF_dstate_aux_to_WF_dstate_aux.
  apply H4. assumption.
  inversion_clear H8. 
  apply WWF_dstate_aux_to_WF_dstate_aux.
  assumption. assumption.
  rewrite H22. assumption.
  rewrite sat_Assert_to_State.
  assumption. 
  rewrite sat_Assert_to_State.
  assumption.
  inversion_clear H6. inversion_clear H12.
  inversion_clear H13.
  inversion_clear H3. inversion_clear H12.
  inversion_clear H13.
 Admitted.

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

#[export] Hint Rewrite @Mmult0H @Mmult1H using (auto 100 with wf_db): M_db.


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

Theorem rule_conseq_r' : forall (P Q Q' : Assertion) c,
{{P}} c {{Q'}} ->
(Q'->> Q) ->
      
       {{P}} c {{Q}}.
       Proof. intros. eapply rule_conseq. apply H. 
       apply implies_refl. assumption. Qed.   


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


Theorem rule_conseq_l' : forall (P P' Q : Assertion) c,
           {{P'}} c {{Q}} ->
           (P ->> P') ->
           {{P}} c {{Q}}.
Proof. intros. eapply rule_conseq. apply H. assumption.
apply implies_refl. Qed.



Theorem rule_qframe': forall (F1 F2 F3: State_formula) c,
Considered_Formula (F1 ⊙ F3)->
Considered_Formula (F2 ⊙ F3)->
({{F1}} c {{F2}}) /\  (NSet.Equal (NSet.inter (fst (Free_state F3)) (fst (MVar c))) (NSet.empty) )
/\ (NSet.Subset (snd (MVar c)) (Qsys_to_Set (fst (Free_State F1))  (snd  (Free_State F1)) ) )
->  {{F3 ⊙ F1}} c {{F3 ⊙ F2}}.
Proof. intros.
 eapply rule_conseq. apply rule_qframe.
 apply H. apply H0. apply H1. 
 apply rule_OdotC.
 apply rule_OdotC.
Qed.

Definition P1 (i:nat):= BEq v_1  i.
Definition P2 (i:nat):= BEq v_2  i.

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
    match goal with 
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
    H: _ |- ?P /\ ?Q => 
    split; try (classic_slove_aux);
    try auto with rea_db
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


Lemma correctness_addM:  
{{ BTrue }}
addM 
{{ APro [((1/2)%R, (SPure <{v = ANum 1}>)) ;  ((1/2)%R, (SPure <{v <> ANum 1}>))] }}.
Proof.  

(*QInit*)
eapply rule_seq. eapply rule_QInit. simpl sub.  
eapply rule_seq. eapply rule_conseq_l. apply rule_OdotE.
eapply rule_qframe' with (F2:= | ∣ 0 ⟩_ (1) >[ 1, 2]).
simpl. intuition. simpl. intuition. 
split. eapply rule_QInit. simpl. admit.

(*QUnit*)
eapply rule_seq. eapply rule_qframe with (F2:=QExp_s 0 1 ∣+⟩).
split. simpl. intuition. split. simpl. intuition.
simpl. intuition. simpl. intuition.
split.
eapply rule_conseq_l'. 
eapply rule_QUnit_One; auto_wf; lia. 
unfold U_v. simpl.  rewrite kron_1_l; auto_wf.
rewrite kron_1_r; auto_wf. Msimpl.  apply implies_refl.
 simpl. admit.

eapply rule_seq.
eapply rule_qframe' with (F2:=QExp_s 1 2 ∣+⟩).
simpl. intuition. split. simpl. intuition.
simpl. intuition. 
split. eapply rule_conseq_l'. 
eapply rule_QUnit_One; auto_wf; lia. 
unfold U_v. simpl.  rewrite kron_1_l; auto_wf.
rewrite kron_1_r; auto_wf. Msimpl.  apply implies_refl.
simpl. admit.

eapply rule_conseq_l. eapply rule_odotT.
eapply rule_conseq_l. eapply rule_Separ.

(*QMeas*)
eapply rule_seq. 
eapply rule_conseq_l with ( | ∣+⟩ ⊗ ∣+⟩ >[ 0, 2] /\ big_Sand (fun i : nat => Assn_sub_P v_1 i (P1 i)) 2).
simpl.   
admit. 

eapply rule_QMeas; try lia; auto_wf. 
assert((forall (v1 v2:Vector 2), (@norm 4 
(v1 ⊗ v2) ) = norm (v1 ⊗ v2))). reflexivity.
rewrite H. Msimpl; lra.
simpl. unfold U_v. simpl.
assert (forall i:nat,(
((@Mmult 4 4 1  (@kron 2 2 2 2 (I 1 ⊗ (Vec 2 i × (Vec 2 i) †))
         (I (2))) (∣+⟩ ⊗ ∣+⟩))) ) =
         (I 1 ⊗ (Vec 2 i × (Vec 2 i) †) ⊗ I 2 × (∣+⟩ ⊗ ∣+⟩))).
reflexivity. rewrite (H 0). rewrite (H 1).
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
eapply rule_sum_pro with (pF1:=([(/ 2, P1 0 /\  P2 0 /\ | ∣0⟩ ⊗ ∣0⟩ >[ 0, 2]);
(/ 2, P1 0 /\ P2 1 /\ | ∣0⟩ ⊗ ∣1⟩ >[ 0, 2])]))
(pF2 := ([(/ 2, P1 1 /\ P2 0 /\ | ∣1⟩ ⊗ ∣0⟩ >[ 0, 2]);
(/ 2, P1 1 /\ P2 1 /\ | ∣1⟩ ⊗ ∣1⟩ >[ 0, 2])]));
simpl. admit. admit.  admit.
eapply rule_conseq_l with ( P1 0 /\ | ∣0⟩ ⊗ ∣+⟩ >[ 0, 2] /\ big_Sand (fun i : nat => Assn_sub_P v_2 i (P2 i)) 2).
simpl.   
admit.

admit. 
admit.
simpl.  



(*add*)
remember ( [((1/4)%R, ((<{v= ANum 0}> /\ (QExp_s 0 2 ((kron ∣0⟩ ∣0⟩))) ))) ; 
                 ((1/4)%R, (<{v = ANum 1}> /\ (QExp_s 0 2 ((kron ∣0⟩ ∣1⟩))) )) ;
                 ((1/4)%R, (<{v = ANum 1}> /\ (QExp_s 0 2 ((kron ∣1⟩ ∣0⟩))) )); 
                 ((1/4)%R, (<{v = ANum 2}> /\ (QExp_s 0 2 ((kron ∣1⟩ ∣1⟩))) ))]) as post.
eapply rule_conseq_r' with (APro post). 
admit.


(*post*)
rewrite (npro_pro_inv post). eapply implies_trans.
eapply rule_OCon with (nF2:=
  [( SPure <{ v = ANum 0 }> );
           (SPure <{ v = ANum 1 }> );
           (SPure <{ v =  ANum 1 }> );
           (SPure <{ v = ANum 2 }>) ]).  
rewrite pro_to_npro_formula_length.
rewrite get_pro_formula_length. reflexivity.
rewrite Heqpost; simpl; classic_slove. 
rewrite Heqpost; simpl.
eapply implies_trans.
rewrite (npro_pro_inv
([((1 / 4)%R, SPure <{ v = ANum 0 }>); ((1 / 4)%R, SPure <{ v = ANum 1 }>);
((1 / 4)%R, SPure <{ v = ANum 1 }>); ((1 / 4)%R, SPure <{ v = ANum 2 }>)])).
eapply rule_OCon with (nF2:=
  [( SPure <{ v <> ANum 1 }> );
   (SPure <{ v = ANum 1 }> );
    (SPure <{ v = ANum 1 }> );
   (SPure <{ v <> ANum 1 }>) ]); try reflexivity; try simpl; try classic_slove. 

simpl.  OpLusC_OMerge_sovle 2 1.
OpLusC_OMerge_sovle 0 1.
assert((1 / 4 + 1 / 4)%R= (/2)%R).
lra. rewrite H0. 
apply implies_refl. 
admit. admit.
Admitted.

