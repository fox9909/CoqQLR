Require Import Lists.List.
Require Import Reals.
Require Import Coquelicot.Complex.
Require Import Strings.String.


From Quan Require Import Matrix.
From Quan Require Import Quantum.
From Quan Require Import Basic_Supplement.
From Quan Require Import ParDensityO.
From Quan Require Import QState.
From Quan Require Import QIMP.
From Quan Require Import QAssert.
From Quan Require Import QRule_E.
From Quan Require Import QRule_Q.
From Quan Require Import QRule_I.
From Quan Require Import Basic_Supplement.


Local Open Scope com_scope.
Local Open Scope assert_scope.
Local Open Scope nat_scope.
Local Open Scope matrix_scope.
Local Open Scope rule_scope.


Lemma MmultH0 : (hadamard) × ∣0⟩ = ∣+⟩. Proof. solve_matrix. Qed.
       Lemma H_adjoint: adjoint (hadamard) =hadamard.
       Proof. solve_matrix.
       Qed.

Lemma Had_N: forall n:nat, 
n ⨂ hadamard × ∣ 0 ⟩_ (n) = (C1/ (√ 2) ^ n)%C .* big_sum (fun z=> ∣ z ⟩_ (n)) (2^n).
Proof. intros. 
assert(∣ 0 ⟩_ (n) = n ⨂ qubit0 ).
induction n. simpl. unfold Vec.  
prep_matrix_equality. destruct y; destruct x;
 simpl; try reflexivity.
assert (WF_Matrix (I 1)). apply WF_I.
unfold WF_Matrix in *. rewrite H. reflexivity.
intuition. 
assert( ∣ 0 ⟩_ (S n) =kron  ∣ 0 ⟩_ (n)  ∣0⟩).
intros. prep_matrix_equality. unfold kron.  
destruct y. destruct x.  
simpl.   rewrite Cmult_1_l. reflexivity.
destruct x.
simpl. rewrite Cmult_0_r. reflexivity.
simpl. rewrite divmod_S. simpl.
rewrite Cmult_0_l. reflexivity.
simpl. rewrite divmod_S. simpl. 
 rewrite Cmult_0_l. reflexivity. 
rewrite H. simpl. rewrite IHn. reflexivity.

rewrite H. apply Logic.eq_trans with (n ⨂ hadamard × n ⨂ ∣0⟩).
f_equal. rewrite Nat.pow_1_l. reflexivity.
rewrite kron_n_mult. rewrite MmultH0. 
unfold xbasis_plus. 
rewrite Mscale_kron_n_distr_r.
rewrite <-RtoC_inv. rewrite RtoC_pow.
rewrite <-Rinv_pow_depr. 
f_equal. apply  Nat.pow_1_l. rewrite Cdiv_unfold.
rewrite Cmult_1_l. rewrite RtoC_inv. f_equal. 
f_equal.  rewrite RtoC_pow. reflexivity.
admit. 
induction n.  simpl. rewrite Mplus_0_l.
admit.   simpl (S n ⨂ (∣0⟩ .+ ∣1⟩)).  rewrite IHn.
simpl. rewrite Nat.add_0_r.
rewrite big_sum_sum. 
rewrite kron_plus_distr_l.
   unfold Gplus.  simpl.
   f_equal. admit. admit.
apply Logic.eq_trans with (big_sum (fun z : nat => ∣ z ⟩_ (n) ) (2 ^ n) ⊗ (∣0⟩ )).
f_equal. apply Nat.pow_1_l.
rewrite kron_Msum_distr_r.
apply big_sum_eq_bounded. intros.
admit.
apply Logic.eq_trans with (big_sum (fun z : nat => ∣ z ⟩_ (n) ) (2 ^ n) ⊗ (∣1⟩ )).
f_equal. apply Nat.pow_1_l.
rewrite kron_Msum_distr_r.
apply big_sum_eq_bounded. intros.

prep_matrix_equality. unfold kron. 
unfold Vec. 
simpl. rewrite divmod_0.
destruct y. destruct x0. simpl. 
destruct x. admit. admit.
simpl. 

Admitted.


Lemma pow_0: (2^0=1)%nat. Proof. auto. Qed.
Lemma add_sub_eq: forall n m, n+m-n=m .
Proof. intuition.     
Qed.

Theorem rule_conseq_l' : forall (P P' Q : Assertion) c,
           {{P'}} c {{Q}} ->
           (P ->> P') ->
           {{P}} c {{Q}}.
Proof. intros. eapply rule_conseq. apply H. assumption.
apply implies_refl. Qed.

Theorem rule_qframe': forall (F1 F2 F3: State_formula) c,
         ({{F1}} c {{F2}}) /\  (NSet.inter (fst (Free_state F3)) (fst (MVar c)) =NSet.empty) 
         /\ (NSet.inter (snd (Free_state F3)) (snd (MVar c)) =NSet.empty) 
         ->  {{F3 ⊙ F1}} c {{F3 ⊙ F2}}. Admitted.

         Theorem  rule_odotT: forall s e s' e' u v, 
         (((| v >[ s , e ]) ⊗* (| u >[ s' , e' ])) ->>
         ((| v >[ s , e ])  ⊙ (| u >[ s' , e' ]))) /\
         (((| v >[ s , e ]) ⊙ (| u >[ s' , e' ])) ->>
         ((| v >[ s , e ])  ⊗* (| u >[ s' , e' ]))).
         Proof. split; intros; unfold assert_implies; intros;
         rule_solve.   
         Qed.


 Theorem  rule_Separ':forall s x e u v, 
(( (| v ⊗ u >[ s , e ])) ->>
((| v >[ s , x ]) ⊗* (| u >[ x , e ]))).
Proof.   intros.  unfold assert_implies. 
intros;   rule_solve. simpl.  destruct H0. destruct H3.
admit.
Admitted. 

 Theorem rule_QUnit_One' : forall s' e' s e (U: Square (2^(e'-s'))) (v: Vector (2^(e-s))),
s<=s' /\ e' <=e ->WF_Matrix v->
{{ QExp_s s  e  v }} QUnit_One s' e' U {{ QExp_s s  e  (U_v s' e' s e U v) }}.
Proof. Admitted.

Definition UCtrl_v (s0 e0 s1 e1 s e: nat) (U: nat->Square (2^(e1-s1))) (v: Vector (2^(e-s))) :=
  (big_sum (fun i:nat =>
       (I (2^(s0-s)) ⊗ (∣ i ⟩_ (e0-s0) × ⟨ i ∣_ (e0-s0) ) ⊗ (I (2^(e-e0)))) ×
       (I (2^(s1-s)) ⊗ (U i) ⊗ (I (2^(e-e1))))) (2^(e0 -s0))) × v.

Theorem rule_QUnit_Ctrl' : forall s0 e0 s1 e1 s e (U: nat -> Square (2^(e1-s1))) (v: Vector (2^(e-s))),
s<=s0 /\ e1 <=e ->WF_Matrix v->
{{ QExp_s s  e  v }} QUnit_Ctrl s0 e0 s1 e1 U {{ QExp_s s  e  ( UCtrl_v s0 e0 s1 e1 s e U v) }}.
Proof. Admitted.

Theorem rule_AndC: forall F1 F2:State_formula,
((F1 /\ F2) ->> (F2 /\ F1))/\
((F2 /\ F1) ->> (F1 /\ F2)).
Proof. intros. unfold assert_implies; apply conj;
        intros; rule_solve; simpl;
         destruct H0;
        split; intuition.
Qed.

Theorem rule_AndCon:forall F1 F2 F3 F4:State_formula,
(F1->>F2) -> (F3->>F4) ->
(F1 /\ F3) ->> (F2 /\ F4).
Proof. intros.  unfold assert_implies in *.
intros. rewrite sat_Assert_to_State in *.
inversion_clear H1. econstructor. assumption.
rewrite State_eval_conj in *. split.
assert(sat_Assert mu F2). apply H. 
rewrite sat_Assert_to_State in *. econstructor. 
assumption. intuition. rewrite sat_Assert_to_State in *.
inversion_clear H1. intuition.
assert(sat_Assert mu F4). apply H0. 
rewrite sat_Assert_to_State in *. econstructor. 
assumption. intuition. rewrite sat_Assert_to_State in *.
inversion_clear H1. intuition.
Qed.


Theorem  rule_OCon': forall (nF1 nF2:npro_formula) ,
big_impiles nF1 nF2 
->(nF1->> nF2).
Proof. intros.    unfold assert_implies. intros. 

inversion_clear H0. 
econstructor.  
rewrite<- (big_impiles_length _ _ H). apply H1.
assert((npro_to_pro_formula nF1 p_n) ->> (npro_to_pro_formula nF2 p_n)).
apply rule_OCon. intuition. intuition. apply H0. assumption.
Qed.


Theorem rule_AndE: forall F1 F2:State_formula,
  (F1 /\ F2 ->> F1 ).
Proof. intros. unfold assert_implies;
      intros; rule_solve; simpl;  intuition.     
Qed.

Theorem rule_OdotO': forall (F1 F2:State_formula), 
 ((F1 ⊙ F2) ->> (F1 /\ F2)) .
Proof. intros.  unfold assert_implies.  
       intros; rule_solve; simpl; intuition.
Qed.

Coercion INR : nat >-> R.
Local Open Scope R_scope.



Module HHL.
Definition v:nat:= 0.

Parameter n m:nat .
Parameter A:Square (2^m).
Parameter b:Vector (2^m).
Parameter x:Vector (2^m).
Parameter lamda:nat-> R.
Parameter mu_j:nat-> Vector (2^m).
Parameter b_j:nat-> C.
Parameter c:R.
Parameter U_b:Square (2^m).
Parameter U: Matrix (2^m) (2^m).
Parameter QFT: Matrix (2^n) (2^n).
Parameter t:R. 
Parameter delt:nat->nat.
Hypothesis Hmn:(m<=n)%nat.
Hypothesis HAx: A × x =b.
Hypothesis Hmu_j:forall j, WF_Matrix (mu_j j)/\ norm (mu_j j)=1.
Hypothesis Hx: WF_Matrix x /\ norm x =1.
Hypothesis Hb: WF_Matrix b /\ norm b =1.
Hypothesis HB_decom: big_sum (fun j=>(b_j j) .* (mu_j j)) (2^m)= b.
Hypothesis HA_decom: big_sum (fun j=>(lamda j) .* (mu_j j)) (2^m)= b.
Hypothesis HU_b: WF_Unitary U_b /\ ( U_b × (Vec (2^m) 0) = b).
Hypothesis HU: (WF_Unitary (U) )/\ forall j :nat,  (U) × ( (mu_j j))= (cos ((lamda j) * t), sin ( (lamda j) * t)) .* ( (mu_j j)).
Hypothesis HQFT: WF_Unitary QFT /\ forall k:nat, QFT × (Vec (2 ^ n) k) =
1 / √ 2 ^ n .* (big_sum (fun j : nat => (cos (((2 * PI)/(2^n)) * j * k),  sin (((2 * PI)/(2^n)) * j * k)) .*  Vec (2 ^ n) j) (2 ^ n)).

Hypothesis (Ht: forall j:nat, and (delt j < 2^n)%nat  ((lamda j * t/ (2*PI))*(2^n) = delt j)).
Hypothesis (Hlamda: forall j, lamda j <>0).
Definition  U_f (i:nat):= exp_U U i.
Definition  phi (j:nat):= (lamda j * t) / (2 * PI).
Definition  phi' (j:nat) := ((phi j) * (2^n))%R.

Inductive Vec_R (n :nat) (i:R): Vector (2^n) -> Prop :=
|vec_r:  forall j:nat, and (j<n) (INR j=i)%R -> Vec_R n i (Vec n j).


Definition  U_c (j:nat): Matrix 2 2:=
  match j with 
  | 0 => I 2
  | _ => fun x y => 
          match x, y with 
          |0, 0 => (sqrt (1-(( c^2)/( ( (j))^2))))
          |0, 1 => c/((j))
          |1, 0 => c/( (j))
          |1, 1 => - (sqrt (1-(( c^2)/( (j)^2))))
          | _, _ => C0
          end 
  end.

Lemma HU_c:(forall j, WF_Unitary (U_c j)) /\ ((U_c 0) × (Vec 2 0)) = (Vec 2 0) /\
(forall j:nat, (j<>0)%nat ->(U_c j ) × (Vec 2 0) = (((sqrt (1-(( c^2)/( (j)^2)))) .* (Vec 2 0) .+ (c/((j)) .* Vec 2 1)))).
Proof. split. intros. destruct j. simpl. apply id_unitary.
       unfold WF_Unitary. split.
       unfold WF_Matrix. intros. destruct x0; destruct y.
       intuition. intuition. simpl. destruct y. intuition.
       reflexivity. intuition. simpl. destruct x0. intuition. reflexivity.
       simpl. destruct x0. destruct y. intuition. reflexivity.
       reflexivity. 
       prep_matrix_equality.
       destruct x0; destruct y; 
       unfold Mmult; unfold Σ; 
       unfold adjoint;  
       rewrite Cplus_0_l; 
       simpl; repeat rewrite Cconj_R;
       repeat rewrite RtoC_mult.
        rewrite sqrt_sqrt.
        repeat rewrite Rmult_1_r.
        rewrite <-RtoC_plus.
        unfold I. simpl. f_equal.
       assert(forall r, 1-r+r=1). intuition lra.
       rewrite Rmult_div.
      apply H. admit. admit. admit.
      destruct y.
      repeat rewrite RtoC_mult.
      repeat rewrite <-RtoC_plus.
      unfold I. simpl. 
       rewrite (Rmult_comm _ (c /  (S j)) ).
      assert(forall r1 r2 :R, r1* -r2= -(r1 * r2)).
      intuition lra. rewrite H.
      assert(forall r:R, r+ -r=0). intuition lra.
      rewrite H0. reflexivity.
      repeat rewrite RtoC_mult.
      repeat rewrite Rmult_0_r. 
      unfold I. simpl. rewrite Cplus_0_l. reflexivity.
      destruct x0;  repeat rewrite Cconj_R;
      repeat rewrite RtoC_mult.
      repeat rewrite <-RtoC_plus.
      unfold I. simpl. 
       rewrite (Rmult_comm _ (c / (S j)) ).
      assert(forall r1 r2 :R, r1* -r2= -(r1 * r2)).
      intuition lra. rewrite H.
      assert(forall r:R, r+ -r=0). intuition lra.
      rewrite H0. reflexivity.
      rewrite Rmult_0_l.  
      unfold I. simpl. rewrite Cplus_0_l. rewrite Rmult_0_l.
       reflexivity.
       destruct x0. 
       destruct y. 
       repeat rewrite Cconj_R;
       repeat rewrite RtoC_mult.
       assert(forall r1 r2:R, -r1*-r2= r1*r2).
       intuition lra. rewrite H.
       rewrite sqrt_sqrt.
       repeat rewrite <-RtoC_plus.
       rewrite Rplus_comm. 
       assert(forall r, 1-r+r=1). intuition lra.
       repeat rewrite Rmult_1_r.
       rewrite Rmult_div. unfold I. simpl. f_equal. apply H0.
       admit. admit.  admit.
       repeat rewrite Cconj_R;
      repeat rewrite RtoC_mult.
      repeat rewrite <-RtoC_plus.
      repeat rewrite Rmult_0_r. 
      unfold I. simpl. rewrite Rplus_0_l. reflexivity.
      repeat rewrite Cconj_R;
      repeat rewrite RtoC_mult.
      repeat rewrite Cmult_0_l. 
      unfold I. simpl. destruct y; simpl.
       rewrite Cplus_0_l. reflexivity.
     assert((x0 =? y) && (S (S x0) <? 2) = false).
     admit.
     rewrite H. rewrite Cplus_0_l. reflexivity.
     split. simpl. rewrite Mmult_1_l. reflexivity.
     auto_wf. intros. destruct j. intuition lra.
     prep_matrix_equality.
      destruct x0; destruct y;
     unfold Mmult; 
      unfold Mplus; unfold scale;
      destruct j; simpl;
     repeat rewrite Cmult_0_r;
     repeat rewrite Cplus_0_l; try reflexivity.
  destruct x0. simpl. 
  repeat rewrite Cmult_1_r;
     repeat rewrite Cplus_0_r.
     rewrite Rdiv_unfold. 
     rewrite Cdiv_unfold.
     rewrite <-RtoC_mult.
     simpl. f_equal. rewrite RtoC_inv. reflexivity. intuition.
     simpl. rewrite Cmult_0_l. rewrite Cmult_0_r.
     rewrite Cplus_0_l. reflexivity.
     destruct x0. simpl. rewrite Cplus_0_r.
repeat rewrite Cmult_1_r. 
 rewrite Rdiv_unfold.    rewrite Cdiv_unfold.
 rewrite <-RtoC_mult. f_equal. rewrite RtoC_inv.
 reflexivity. destruct j.    intuition lra.
 assert(S j + 1 + 1= S (S (S j))). intuition lra.
 rewrite H0. admit.
 simpl. rewrite Cmult_0_l. rewrite Cmult_0_r.
 rewrite Cplus_0_l. reflexivity.
Admitted.

Definition  adj_Uf (i:nat) := adjoint (U_f i).

                     
 Local Open Scope nat_scope.                  
Definition HHL :=
    <{ v := 0;
       while  v=0  do 
       QInit 0 n;
       QInit n (n+m);
       QInit (n+m) (n+m+1);
       QUnit_One n (n+m) (U_b);
       QUnit_One 0 n (kron_n n hadamard);
       QUnit_Ctrl 0 n n (n+m) U_f;
       QUnit_One 0 n (adjoint QFT);
       QUnit_Ctrl 0 n (n+m) (n+m+1) (U_c);
       QUnit_One 0 n (QFT);
       QUnit_Ctrl 0 n n (n+m) (adj_Uf);
       QUnit_One 0 n (kron_n n hadamard);
       QMeas v (n+m) (n+m+1)
       end }>.


Lemma Had_N':
U_v 0 n 0 n (n ⨂ hadamard) ∣ 0 ⟩_ n= (1/√ 2 ^ n) .* big_sum (fun z=> ∣ z ⟩_ (n)) (2^n).
Proof. unfold U_v. 
repeat rewrite add_sub_eq. rewrite Nat.sub_0_r.
repeat rewrite Nat.sub_diag. repeat rewrite pow_0.
rewrite kron_1_l. rewrite kron_1_r. rewrite Had_N. reflexivity.
auto_wf.
Qed.

Lemma U_vb:
U_v n (n + m) n (n + m) U_b ∣ 0 ⟩_ (m)=(big_sum (fun j=>(b_j j) .* (mu_j j)) (2^m)).
Proof. unfold U_v. repeat rewrite Nat.sub_diag. repeat rewrite pow_0.
rewrite kron_1_l. rewrite kron_1_r. 
pose HU_b. destruct a. assert(m=n+m-n). lia. destruct H1.  Set Printing All.
 rewrite H0. rewrite HB_decom. reflexivity.
 apply HU_b.
       
Qed.

Lemma  WF_expU{n:nat}: forall (U:Square (2^n)) x0,
WF_Matrix U->
WF_Matrix (exp_U U x0).
Proof. induction x0; simpl; intros. auto_wf.
auto_wf.
Qed.


Lemma U_f': forall (v:Vector (2^n *(2^m))) , 
(UCtrl_v 0 n n (n + m) 0 (n + m) U_f v) =
Mmult (big_sum
(fun i : nat =>
 (∣ i ⟩_ (n) × ⟨ i ∣_ (n)) ⊗ (U_f i)) 
(2 ^ n)) v.
Proof.  intros. unfold UCtrl_v.
repeat rewrite add_sub_eq. repeat rewrite Nat.sub_0_r.
repeat rewrite Nat.sub_diag. repeat rewrite pow_0.
f_equal; type_sovle'; try lia. 
apply big_sum_eq_bounded. intros. 
repeat rewrite kron_1_l. rewrite kron_1_r.
apply Logic.eq_trans with (∣ x0 ⟩_ (n) × ⟨ x0 ∣_ (n) ⊗ I (2 ^ m)
× (I (2 ^ n) ⊗  U_f x0)).
f_equal; type_sovle'; try lia. 
rewrite kron_mixed_product. rewrite Mmult_1_r.
rewrite Mmult_1_l. reflexivity. apply WF_expU.
pose HU. destruct a. apply H0. auto_wf. auto_wf.
Qed .

Definition  P (i:nat): Pure_formula := (BEq v i) .

Lemma simpl_HB: (1 / √ 2 ^ n) .* big_sum (fun z : nat => ∣ z ⟩_ (n)) (2 ^ n)
⊗ big_sum (fun j : nat => b_j j .* mu_j j) (2 ^ m)=
big_sum (fun j : nat => b_j j .* ((1 / √ 2 ^ n) .* big_sum (fun z : nat => ∣ z ⟩_ (n) ⊗ mu_j j ) (2 ^ n)
)) (2 ^ m).
Proof. 
rewrite kron_Msum_distr_l.
apply big_sum_eq_bounded. intros.
rewrite Mscale_kron_dist_r.
rewrite Mscale_kron_dist_l.  f_equal. 
rewrite kron_Msum_distr_r. reflexivity.    
Qed.


Lemma base_inner_0:forall i j :nat,
i<>j->
(⟨ i ∣_ (n) × ∣ j ⟩_ (n))=0 .* I 1 .
Proof.  induction n. simpl. intros. 
destruct i. destruct j. intuition.
     Admitted.


Lemma simpl_expU:forall i j,
U_f i × mu_j j = (cos ((lamda j)* t *i), sin (((lamda j)* t * i))) .* mu_j j.
Proof. intros.  induction i. simpl. rewrite Mmult_1_l.
    rewrite Rmult_0_r. rewrite cos_0. rewrite sin_0.
rewrite Mscale_1_l. reflexivity. pose Hmu_j.
apply a. unfold U_f in *.  simpl exp_U. rewrite Mmult_assoc.
rewrite IHi.
rewrite Mscale_mult_dist_r. pose HU. destruct a.
rewrite H0.
rewrite Mscale_assoc. f_equal.
Admitted.


Lemma simpl_Uf:
UCtrl_v 0 n n (n + m) 0 (n + m) U_f
(big_sum
   (fun j : nat =>
    b_j j
    .* ((1/√ 2 ^ n)
        .* big_sum (fun z : nat => ∣ z ⟩_ (n) ⊗ mu_j j)
             (2 ^ n))) 
   (2 ^ m))= (big_sum
   (fun j : nat =>
    b_j j
    .* ((1/√ 2 ^ n)
        .* big_sum (fun z : nat => (cos (2*PI * (phi j)* z), sin ((2*PI * (phi j)* z))) .* ∣ z ⟩_ (n))
             (2 ^ n)) ⊗ mu_j j ) 
   (2 ^ m)).
Proof. rewrite U_f'. rewrite Mmult_Msum_distr_l.
      apply big_sum_eq_bounded. intros.
      rewrite Mscale_mult_dist_r. 
      rewrite Mscale_kron_dist_l.  f_equal.
      rewrite Mscale_mult_dist_r. 
      rewrite Mscale_kron_dist_l.  f_equal.
      rewrite Mmult_Msum_distr_l.
      rewrite kron_Msum_distr_r.
      apply big_sum_eq_bounded. intros.
      rewrite Mmult_Msum_distr_r.
      rewrite (big_sum_eq_bounded   _ ((fun i : nat =>
      (∣ i ⟩_ (n) × ⟨ i ∣_ (n) × ∣ x1 ⟩_ (n)) ⊗  ((cos (2*PI * (phi x0)* i), sin ((2* PI * (phi x0)* i))) .* mu_j x0)))).
      apply big_sum_unique .
      exists x1. split. assumption. 
      split. rewrite Mmult_assoc. rewrite base_innner.
      rewrite Mmult_1_r.  rewrite Mscale_kron_dist_r.
      rewrite Mscale_kron_dist_l.
      reflexivity.  auto_wf. assumption.
      intros. rewrite Mmult_assoc. rewrite base_inner_0.
      rewrite Mscale_0_l. rewrite Mmult_0_r.
      rewrite kron_0_l. reflexivity. intuition.
      intros.  
      rewrite kron_mixed_product. f_equal.
      rewrite simpl_expU. f_equal. f_equal;
      f_equal; unfold phi; rewrite Rdiv_unfold;
       rewrite (Rmult_comm _ (/ (2 * PI)));
       rewrite <-Rmult_assoc; rewrite Rinv_r;
       try rewrite Rmult_1_l; try reflexivity.
Admitted.

Lemma unitary_trans{n:nat}: forall (U:Square n) (v1 v2:Vector n),
WF_Unitary U->WF_Matrix v1->
U × v1 = v2-> (U) † × v2 = v1 .
Proof. intros. unfold WF_Unitary in H. destruct H.
rewrite <-H1. rewrite <-Mmult_assoc. rewrite H2.
rewrite Mmult_1_l. reflexivity. assumption.
   
Qed.

Lemma simpl_QFT': 
@U_v n (n+m) 0 n 0 (n + m) (QFT) †
       (big_sum
          (fun j : nat =>
           b_j j
           .* ((1/√ 2 ^ n)
               .* big_sum
                    (fun z : nat =>
                     (cos (2 * PI * phi j * z),
                      sin (2 * PI * phi j * z))
                     .* ∣ z ⟩_ (n)) (2 ^ n)) ⊗ 
           mu_j j) (2 ^ m))=
       (big_sum
          (fun j : nat =>
           b_j j
           .* (Vec (2^n) (delt j)) ⊗ 
           mu_j j) (2 ^ m)).
Proof. pose Ht.  unfold U_v. 
repeat rewrite add_sub_eq. repeat rewrite Nat.sub_0_r.
repeat rewrite Nat.sub_diag. repeat rewrite pow_0.
rewrite kron_1_l. assert(2^n=1* 2^n). lia. destruct H.
assert( 2^n * 2^m= 2^(n+m)). type_sovle'. destruct H.
rewrite Mmult_Msum_distr_l. 
apply big_sum_eq_bounded.  intros. 
rewrite Mscale_kron_dist_l.
rewrite Mscale_mult_dist_r.
repeat rewrite Mscale_kron_dist_l.
f_equal. rewrite <-Mscale_kron_dist_l. 
rewrite kron_mixed_product.
rewrite Mmult_1_l. f_equal.
pose HQFT. 
apply unitary_trans. intuition.
apply WF_vec. apply a. 
destruct a0. rewrite H1. 
f_equal.
apply big_sum_eq_bounded. intros.
f_equal. assert(phi' x0 = delt x0). unfold phi'.
unfold phi. apply a.
rewrite <-H3. unfold phi'.
rewrite Rdiv_unfold. repeat rewrite Rmult_assoc.
f_equal; f_equal; f_equal; f_equal;
repeat rewrite <-Rmult_assoc;
rewrite Rmult_comm; repeat rewrite <-Rmult_assoc;
rewrite Rinv_r; try rewrite Rmult_1_l; try lra. 
admit. admit. pose Hmu_j. apply a0. pose HQFT.
destruct a0. apply WF_adjoint. apply H.
Admitted.

Lemma simpl_Uc:
UCtrl_v 0 n (n + m) (n + m + 1) 0 
      (n + m + 1) U_c
      (big_sum
         (fun i : nat =>
          b_j i .* ∣ delt i ⟩_ (n) ⊗ mu_j i ⊗ ∣ 0 ⟩_ (1))
         (2 ^ m))=
         (big_sum
         (fun i : nat =>
          b_j i .* ∣ delt i ⟩_ (n) ⊗ mu_j i ⊗ ((sqrt (1-(( c^2)/( (phi' i)^2)))) .* (Vec 2 0) .+ (c/((phi' i)) .* Vec 2 1)))
         (2 ^ m)).
Proof. pose Ht as H. unfold UCtrl_v. repeat rewrite add_sub_eq. repeat rewrite Nat.sub_0_r.
repeat rewrite Nat.sub_diag. repeat rewrite pow_0.
assert(m+1=n + m + 1 - n). lia. destruct H0.
assert(2^n * 2^m * 2^1=2^(n+m+1)). type_sovle'. destruct H0.
rewrite Mmult_Msum_distr_l. apply big_sum_eq_bounded.
intros. apply Logic.eq_trans with (big_sum
(fun i : nat => (∣  i ⟩_ (n) × ⟨  i ∣_ (n))⊗ I (2^m) ⊗ U_c i )
(2 ^ n) × (b_j x0 .* ∣ delt x0 ⟩_ (n) ⊗ mu_j x0 ⊗ ∣ 0 ⟩_ (1))).
f_equal; rewrite Nat.mul_1_l. rewrite Nat.pow_add_r.
rewrite Nat.mul_assoc. reflexivity. 
apply big_sum_eq_bounded. intros. 
apply Logic.eq_trans with ((∣ x1 ⟩_ (n) × ⟨ x1 ∣_ (n)) ⊗ I (2 ^ m) ⊗ I (2)
× (I (2 ^ n)  ⊗ I (2 ^ m) ⊗  U_c x1)).
rewrite kron_1_l; auto_wf. rewrite kron_1_r;auto_wf.
 rewrite kron_assoc; auto_wf. repeat rewrite id_kron; auto_wf.
 repeat rewrite Nat.pow_add_r. simpl. f_equal;
try (rewrite Nat.mul_assoc; reflexivity).
repeat rewrite kron_mixed_product; auto_wf. repeat rewrite Mmult_1_r; auto_wf.
rewrite Mmult_1_l; auto_wf. reflexivity. admit.
rewrite Mmult_Msum_distr_r. apply big_sum_unique.
exists (delt x0). split. apply H. 
split. repeat rewrite Mscale_kron_dist_l.
rewrite Mscale_mult_dist_r. f_equal.
repeat rewrite kron_mixed_product.  rewrite Mmult_1_l.
rewrite Mmult_assoc. rewrite base_innner.
rewrite Mmult_1_r. f_equal.  
pose HU_c. destruct a.  destruct H2. 
rewrite H3. assert((lamda x0 * t / (2 * PI) * 2 ^ n)%R = delt x0).
apply H. 
rewrite<-H4. unfold phi'. unfold phi. reflexivity.  admit.
admit. apply H. apply Hmu_j. intros.
repeat rewrite Mscale_kron_dist_l.
rewrite Mscale_mult_dist_r. 
repeat rewrite kron_mixed_product.
rewrite Mmult_assoc.  rewrite base_inner_0.
rewrite Mscale_0_l. rewrite Mmult_0_r.
repeat rewrite kron_0_l. rewrite Mscale_0_r. reflexivity.
intuition.
Admitted.

Lemma implies_trans: forall (D D1 D2:Assertion), 
(D->> D1)-> (D1->>D2) 
->(D->>D2).
Proof. unfold assert_implies. intros. auto. Qed.

Lemma implies_trans': forall (D D1 D2:Assertion), 
 (D1->>D2) -> (D->> D1)
->(D->>D2).
Proof.  unfold assert_implies. intros. auto. Qed.


Lemma simpl_QFT: 
@U_v (n-0) (n+m+1-0) 0 n 0 (n + m + 1) QFT
      (big_sum
         (fun i : nat =>
          b_j i .* ∣ delt i ⟩_ (n) ⊗ mu_j i
          ⊗ (√ (1 - c ^ 2 / phi' i ^ 2) .* Vec 2 0 .+ c / phi' i .* Vec 2 1))
         (2 ^ m)) =
         (big_sum
         (fun i : nat =>
          b_j i .* (((1/√ 2 ^ n)
          .* big_sum
               (fun z : nat =>
                (cos (2 * PI * phi i * z),
                 sin (2 * PI * phi i * z))
                .* ∣ z ⟩_ (n)) (2 ^ n))) ⊗ mu_j i
          ⊗ (√ (1 - c ^ 2 / phi' i ^ 2) .* Vec 2 0 .+ c / phi' i .* Vec 2 1))
         (2 ^ m)).
Proof. pose Ht as H. unfold U_v. repeat rewrite add_sub_eq. repeat rewrite Nat.sub_0_r.
repeat rewrite Nat.sub_diag. repeat rewrite pow_0.
rewrite kron_1_l. 
apply Logic.eq_trans with (QFT ⊗ I (2 ^ m) ⊗ I (2^1)
× big_sum
    (fun i : nat =>
     b_j i .* ∣ delt i ⟩_ (n) ⊗ mu_j i
     ⊗ (√ (1 - c ^ 2 / phi' i ^ 2) .* Vec 2 0
        .+ c / phi' i .* Vec 2 1)) (2 ^ m)).
f_equal; type_sovle'. rewrite kron_assoc; auto_wf.
rewrite id_kron.  f_equal; try lia; type_sovle'. f_equal; type_sovle'.
apply HQFT.
rewrite Mmult_Msum_distr_l. 
apply big_sum_eq_bounded.  intros. 
repeat rewrite Mscale_kron_dist_l.
rewrite Mscale_mult_dist_r.
f_equal. 
 rewrite <-Mscale_kron_dist_l. 
repeat rewrite kron_mixed_product.
repeat rewrite Mmult_1_l. f_equal.
rewrite <-Mscale_kron_dist_l. 
f_equal. pose HQFT. destruct a. rewrite H2. 
f_equal. apply big_sum_eq_bounded. intros.
f_equal. assert(phi' x0 = delt x0). apply H.
rewrite <-H4. unfold phi'. rewrite Rdiv_unfold. repeat rewrite Rmult_assoc.
f_equal; f_equal; f_equal; f_equal;
repeat rewrite <-Rmult_assoc;
rewrite Rmult_comm; repeat rewrite <-Rmult_assoc;
rewrite Rinv_r; try rewrite Rmult_1_l; try lra.
admit. admit. auto_wf. apply Hmu_j. apply HQFT. 
Admitted.

Lemma simpl_Uf':
UCtrl_v  0 n n (n + m) 0 (n + m + 1) (adj_Uf)
      (big_sum
         (fun i : nat =>
          b_j i
          .* ((1/√ 2 ^ n)
              .* big_sum
                   (fun z : nat =>
                    (cos (2 * PI * phi i * z), sin (2 * PI * phi i * z))
                    .* ∣ z ⟩_ (n)) (2 ^ n)) ⊗ mu_j i
          ⊗ (√ (1 - c ^ 2 / phi' i ^ 2) .* Vec 2 0 .+ c / phi' i .* Vec 2 1))
         (2 ^ m))= (big_sum
         (fun i : nat =>
          b_j i
          .* ((1/√ 2 ^ n)
              .* big_sum
                   (fun z : nat =>
                     ∣ z ⟩_ (n)) (2 ^ n)) ⊗ mu_j i
          ⊗ (√ (1 - c ^ 2 / phi' i ^ 2) .* Vec 2 0 .+ c / phi' i .* Vec 2 1))
         (2 ^ m)) .
Proof. 
 unfold UCtrl_v.
repeat rewrite add_sub_eq. repeat rewrite Nat.sub_0_r.
repeat rewrite Nat.sub_diag. repeat rewrite pow_0.
apply Logic.eq_trans with (big_sum
(fun i : nat =>
 (∣ i ⟩_ (n) × ⟨ i ∣_ (n)) ⊗ adj_Uf i ⊗ I (2 ^ 1)) 
(2 ^ n)
× big_sum
  (fun i : nat =>
   b_j i
   .* ((1/√ 2 ^ n)
       .* big_sum
            (fun z : nat =>
             (cos (2 * PI * phi i * z),
              sin (2 * PI * phi i * z)) .* 
             ∣ z ⟩_ (n)) (2 ^ n)) ⊗ mu_j i
   ⊗ (√ (1 - c ^ 2 / phi' i ^ 2) .* Vec 2 0
      .+ c / phi' i .* Vec 2 1)) (2 ^ m)).
f_equal. rewrite <-Nat.add_assoc. rewrite Nat.mul_1_l.
rewrite add_sub_eq.   rewrite <-Nat.mul_assoc.
f_equal. simpl. rewrite Nat.pow_add_r. simpl. reflexivity.
type_sovle'. apply big_sum_eq_bounded. intros.
repeat rewrite kron_1_l. repeat rewrite kron_assoc; auto_wf.
eapply Logic.eq_trans with (∣ x0 ⟩_ (n) × ⟨ x0 ∣_ (n)
⊗ I ((2^m * 2^1))
× (I (2 ^ n) ⊗ ( adj_Uf x0 ⊗ I (2 ^ 1)))).
f_equal. admit. admit. type_sovle'. f_equal; type_sovle'; try lia.
f_equal;type_sovle'. 
rewrite kron_mixed_product; auto_wf.  
rewrite Mmult_1_r; auto_wf. rewrite Mmult_1_l; auto_wf.  f_equal.
admit. admit. admit. admit.  
rewrite Mmult_Msum_distr_l. apply big_sum_eq_bounded.
intros. repeat rewrite Mscale_kron_dist_l. 
rewrite Mscale_mult_dist_r. f_equal. 
rewrite Mscale_mult_dist_r. f_equal.
repeat rewrite kron_Msum_distr_r. 
rewrite Mmult_Msum_distr_l. 
apply big_sum_eq_bounded. intros. 
rewrite Mmult_Msum_distr_r. 
apply big_sum_unique .
exists x1. split. assumption. 
split. repeat rewrite kron_mixed_product. f_equal.
rewrite Mscale_mult_dist_r.
rewrite Mscale_kron_dist_l.
rewrite <-Mscale_kron_dist_r. f_equal.
rewrite Mmult_assoc. rewrite base_innner.
rewrite Mmult_1_r. reflexivity.  auto_wf. assumption.
rewrite <-Mscale_mult_dist_r.
assert(adj_Uf x1= (U_f x1)†).
admit. rewrite H1.
apply unitary_trans. admit. admit.
rewrite simpl_expU. f_equal. f_equal;
f_equal; unfold phi; rewrite Rdiv_unfold;
 rewrite (Rmult_comm _ (/ (2 * PI)));
 rewrite <-Rmult_assoc; rewrite Rinv_r;
 try rewrite Rmult_1_l; try reflexivity. admit. admit.
rewrite Mmult_1_l. reflexivity. admit.
intros.  
repeat rewrite kron_mixed_product. f_equal.
rewrite Mscale_mult_dist_r.
rewrite Mscale_kron_dist_l.
rewrite <-Mscale_kron_dist_r. f_equal.
rewrite <-Mscale_mult_dist_r.
rewrite Mmult_assoc. rewrite base_inner_0.
rewrite Mscale_0_l. rewrite Mmult_0_r.
rewrite kron_0_l. rewrite kron_0_l. reflexivity. intuition.
Admitted. 

Lemma kron_n_I : forall n m, n ⨂ I m = I (m ^ n).
Proof.
  intros.
  induction n0; simpl.
  reflexivity.
  rewrite IHn0. 
  rewrite id_kron.
  apply f_equal.
  lia.
Qed.

Lemma kron_n_unitary : forall {m n} (A : Matrix m m),
  WF_Unitary A -> WF_Unitary (n ⨂ A).
Proof.
  intros m n A  [WFA UA].
  unfold WF_Unitary in *.
  split.
  auto with wf_db.
  rewrite kron_n_adjoint.
  rewrite kron_n_mult.
  rewrite UA.
  rewrite kron_n_I. 
  easy. assumption.
Qed.


Lemma simpl_H:
@U_v (n-0) (n+m+1-0) 0 n 0 (n + m + 1) (n ⨂ hadamard)
      (big_sum
         (fun i : nat =>
          b_j i
          .* ((1/√ 2 ^ n)
              .* big_sum (fun z : nat => ∣ z ⟩_ (n))
                   (2 ^ n)) ⊗ mu_j i
          ⊗ (√ (1 - c ^ 2 / phi' i ^ 2) .* Vec 2 0
             .+ c / phi' i .* Vec 2 1)) 
         (2 ^ m))=(big_sum
         (fun i : nat =>
          b_j i
          .* (Vec (2^n) 0) ⊗ mu_j i
          ⊗ (√ (1 - c ^ 2 / phi' i ^ 2) .* Vec 2 0
             .+ c / phi' i .* Vec 2 1)) 
         (2 ^ m))
          .
Proof.  unfold U_v. rewrite <-Nat.add_assoc. repeat rewrite add_sub_eq. rewrite Nat.sub_0_r.
repeat rewrite Nat.sub_diag. repeat rewrite pow_0.
rewrite kron_1_l. 
 apply Logic.eq_trans with 
 (n ⨂ hadamard ⊗ I ( 2 ^ m) ⊗ I 2
 × big_sum
     (fun i : nat =>
      b_j i
      .* ((1/√ 2 ^ n)
          .* big_sum (fun z : nat => ∣ z ⟩_ (n))
               (2 ^ n)) ⊗ mu_j i
      ⊗ (√ (1 - c ^ 2 / phi' i ^ 2) .* Vec 2 0
         .+ c / phi' i .* Vec 2 1)) (2 ^ m)).
         f_equal; repeat rewrite Nat.pow_add_r;
         rewrite Nat.mul_assoc; try reflexivity.
rewrite kron_assoc; auto_wf. f_equal; simpl; try rewrite Nat.sub_0_r;
try rewrite Nat.add_0_r; try lia; rewrite id_kron; reflexivity.
rewrite Mmult_Msum_distr_l.  apply big_sum_eq_bounded.
intros. repeat rewrite kron_mixed_product.
repeat rewrite Mmult_1_l. 
f_equal. f_equal. assert(n ⨂ hadamard= (n ⨂ hadamard) †).
rewrite kron_n_adjoint. f_equal. rewrite  hadamard_sa.
reflexivity. auto_wf. rewrite H0.
apply  unitary_trans. apply kron_n_unitary. apply H_unitary.
apply WF_scale. apply WF_vec. apply pow_gt_0.
rewrite Mscale_mult_dist_r. f_equal. apply Had_N.
auto_wf. apply Hmu_j.  rewrite Nat.sub_0_r. auto_wf. 
Qed.


Theorem correctness_HHL: 
{{BTrue}}
HHL
{{QExp_s n (n+m) x}}.
Proof. unfold HHL. 
       eapply rule_seq.
      *eapply rule_conseq_l'. eapply (rule_assgn (BEq v 0)). admit.
      *eapply rule_conseq. eapply (rule_while BTrue (QExp_s 0 (n+m+1) ((Vec (2^n) 0) ⊗ (x) ⊗ (Vec 2 1)))).
      *eapply rule_seq. eapply rule_conseq_l. apply rule_PT. eapply rule_QInit.  
      *eapply rule_seq. eapply rule_conseq_l. apply rule_OdotE. apply rule_qframe'.
       split. eapply rule_QInit. admit.
      *eapply rule_seq. eapply rule_conseq_l.  apply rule_OdotE.
       apply rule_qframe'.  split. eapply rule_QInit. admit.
       *eapply rule_seq. eapply rule_conseq_l. apply rule_OdotA.
       eapply rule_qframe'. split.  eapply rule_qframe.
       split. eapply rule_QUnit_One'. lia. apply WF_vec. apply pow_gt_0. admit.
       admit.  assert(m=n+m-n). lia. destruct H.  rewrite U_vb. 
      *eapply rule_seq. eapply rule_qframe. split. eapply rule_QUnit_One'.
       lia. apply WF_vec. apply pow_gt_0. admit. assert(n=n-0). lia. destruct H. 
       rewrite Had_N'. 
       *eapply rule_seq. eapply rule_conseq_l. apply rule_OdotA. eapply rule_qframe.
       split. eapply rule_conseq_l. apply rule_odotT. eapply rule_conseq_l.
       apply rule_Separ.
       assert(m=n+m-n). lia. destruct H.
       assert(n=n-0). lia. destruct H.
       rewrite simpl_HB. apply rule_QUnit_Ctrl'. lia. admit. admit.
       rewrite simpl_Uf.
      *eapply rule_seq. apply rule_qframe.
      split. apply rule_QUnit_One'. lia. admit.
      admit. assert(n=n-0). lia. destruct H.
      assert(n+m=n+m-0). lia. destruct H. rewrite simpl_QFT'. 
      *eapply rule_seq. eapply rule_conseq_l. apply rule_odotT. 
      eapply rule_conseq_l. apply rule_Separ. eapply rule_QUnit_Ctrl'. lia.  admit.
      assert(1=n+m+1-(n+m)). lia. destruct H.
      assert(n+m=n+m-0). lia. destruct H.
      assert(2 ^ n * 2 ^ m= 2^(n+m)). type_sovle'. destruct H.
      rewrite kron_Msum_distr_r.
      eapply rule_conseq_l with (P':=| UCtrl_v 0 n (n + m) (n + m + 1) 0 (n + m + 1) U_c
      (big_sum (fun i : nat => b_j i .* ∣ delt i ⟩_ (n) ⊗ mu_j i ⊗ ∣ 0 ⟩_ (1))
        (2 ^ m)) >[ 0, n + m + 1]).
      apply implies_refl.
      rewrite simpl_Uc.
      *eapply rule_seq. apply rule_QUnit_One'. lia. admit.
      rewrite simpl_QFT.
      *eapply rule_seq. eapply rule_QUnit_Ctrl'. lia.  admit.
      rewrite simpl_Uf'.
      *eapply rule_seq. apply rule_QUnit_One'. lia. admit.
      rewrite simpl_H.
      * eapply rule_conseq.
      eapply rule_QMeas with (s:=0) (e:=n+m+1)(P:=P)
      (v:=(big_sum
      (fun i : nat =>b_j i .* (Vec (2^n) 0) ⊗ mu_j i
      ⊗ (√ (1 - c ^ 2 / phi' i ^ 2) .* Vec 2 0
        .+ c / phi' i .* Vec 2 1)) 
      (2 ^ m))).
      lia. admit. admit. rewrite add_sub_eq. unfold P. simpl. admit. 
      rewrite add_sub_eq. unfold P. simpl. 
      eapply implies_trans.  
      eapply  rule_Oplus. simpl.
      eapply rule_OCon'. simpl. split. 
      eapply implies_trans.  apply rule_AndC.
        eapply rule_AndCon. apply rule_PT. apply implies_refl.
        split.  
        eapply implies_trans. apply rule_AndC.
        eapply rule_AndCon. admit. admit. intuition.
        eapply implies_trans.  apply rule_OdotE.
        eapply implies_trans.  apply rule_OdotO.
        eapply implies_trans. apply rule_AndC.
      admit. eapply implies_trans.   
        apply rule_AndE.  
        eapply implies_trans. 
        assert(1=(1 * 1)). lia. destruct H.
        assert(2^(n+m-0)=2 ^ n * 2 ^ m). type_sovle'. destruct H. 
        assert(2^(n+m+1-(n+m))=2). assert(2^1=2). simpl. reflexivity.
        rewrite<- H. rewrite H at 1. f_equal. lia. destruct H.
        eapply rule_Separ'.
        eapply  implies_trans. 
        apply rule_odotT. 
        eapply  implies_trans. 
        eapply rule_OdotO'. 
        eapply  implies_trans. 
        eapply rule_AndE. 
        eapply  implies_trans. 
        assert(2^(n-0)=(2 ^ (n + m + 1 - (n + m))) ^ n).
      rewrite Nat.sub_0_r. f_equal.
      symmetry. assert(2^1=2). simpl. reflexivity.
      rewrite<- H. rewrite H at 1.
      f_equal. apply add_sub_eq. destruct H.
      assert(2^(n+m-n)=(2 ^ (n + m + 1 - (n + m))) ^ m). 
      repeat rewrite add_sub_eq. simpl. reflexivity. destruct H.
      eapply rule_Separ'. 
      eapply  implies_trans. 
      apply rule_odotT.  
      eapply  implies_trans. 
      eapply rule_OdotO'. 
      eapply  implies_trans. 
      apply rule_AndC.  
      eapply rule_AndE. 
      Admitted.
    
End HHL.

Module OF.

Local Open Scope nat_scope.    


Parameter x:nat.
Parameter N:nat.
Parameter r:nat. 
Parameter t:nat.
Parameter L:nat.
Parameter U_plus:Square (2^L).
Parameter U: Square (2^L).
Parameter f: R-> nat.
Parameter QFT: Matrix (2^t) (2^t).

Hypothesis Hr: (x^r mod N) =1. 
Hypothesis HQFT: WF_Unitary QFT /\ forall k:nat, QFT × (Vec (2 ^ t) k) =
1 / √ (2 ^ t) .* (big_sum (fun j : nat => (cos (((2 * PI)/(2^t)) * j * k),  sin (((2 * PI)/(2^t)) * j * k)) .*  Vec (2 ^ t) j) (2 ^ t)).
Hypothesis HU_plus: WF_Unitary U_plus /\ ( U_plus × (Vec (2^L) 0) = (Vec (2^L) 1) ).
Hypothesis HU: WF_Unitary U /\ (forall j:nat, j< N -> U × (Vec (2 ^ L) j) = (Vec (2 ^ t) (x*j mod N))) /\ 
                                (forall j:nat, j>=N -> U × (Vec (2 ^ L) j) = (Vec (2 ^ t) j)).
Definition  U_f (i:nat):= exp_U U i.
Definition  Us (s:nat) := 1 / √ r .* (big_sum (fun k:nat=> (cos (- ((2 * PI)/r) * s * k),  sin (- ((2 * PI)/(r)) * s * k)) .*  Vec (2 ^ L) (x ^ k mod N)) (r) ) .
Definition z:nat := 0.
Definition b:nat := 1.
Definition z':nat:=2 .

Lemma HU_s: 1 / √ r .*  (big_sum (fun s:nat=> Us s) (r) ) =(Vec (2^L) 1).
Proof. Admitted.

Definition b' :=(Nat.modulo (Nat.pow x z) N) .

Definition  P (s:nat): Pure_formula := (BEq z' (s/r * 2^t)) .


Definition OF :=
    <{ z := 1 ;
       b := b' ;
       while  b<>1  do 
       QInit 0 t;
       QInit t (t+L);
       QUnit_One 0 t (kron_n t hadamard);
       QUnit_One t (t+L) (U_plus);
       QUnit_Ctrl 0 t t (t+L) U_f;
       QUnit_One 0 t (adjoint QFT);
       QMeas z' 0 t;
       z := f (z'/2^t);
       b := b'
       end }>.




Lemma  simpl_H_Uplus:
C1 / √ 2 ^ t
    .* big_sum (fun z0 : nat => ∣ z0 ⟩_ (t)) (2 ^ t)
    ⊗ ∣ 1 ⟩_ (L)=
    1 / √ (r *2^t) .*  (big_sum (fun s:nat=>(big_sum (fun j=>(Vec (2^t) j)) (2^t)) ⊗ (Us s)) (r) ).
Proof.  rewrite<-HU_s.
   rewrite Mscale_kron_dist_l.
   rewrite Mscale_kron_dist_r.
   rewrite Mscale_assoc.
   f_equal.
    
Set Printing Coercions.
rewrite RtoC_pow. repeat rewrite <-RtoC_div.
rewrite RtoC_mult. f_equal. 
 rewrite Rmult_div. rewrite Rmult_1_l.
 f_equal.  admit.  admit. admit. admit. admit. admit.
  
   rewrite kron_Msum_distr_l.
   apply big_sum_eq_bounded.
   intros. reflexivity. 
Admitted.


Lemma simpl_expU:forall j s,
U_f j × Us s = (cos ((2*PI/2^t)* j *(s/r * 2^t)), sin ((2*PI/2^t)* j *(s/r * 2^t))) .* Us s.
Proof. intros.  induction j. simpl. rewrite Mmult_1_l.
     rewrite Rmult_0_r. rewrite Rmult_0_l. rewrite cos_0. rewrite sin_0.
rewrite Mscale_1_l. reflexivity. admit.
 unfold U_f in *.  simpl exp_U.
rewrite Mmult_assoc.
rewrite IHj.
rewrite Mscale_mult_dist_r.
pose HU. destruct a. destruct H0.
Admitted.


Lemma U_f': forall (v:Vector (2^t *(2^L))) , 
UCtrl_v 0 t t (t + L) 0 (t + L) U_f v =
Mmult (big_sum
(fun i : nat =>
 (∣ i ⟩_ (t) × ⟨ i ∣_ (t)) ⊗ (U_f i)) 
(2 ^ t)) v.
Proof.  intros. unfold UCtrl_v.
repeat rewrite add_sub_eq. repeat rewrite Nat.sub_0_r.
repeat rewrite Nat.sub_diag. repeat rewrite pow_0.
f_equal; type_sovle'; try lia. 
apply big_sum_eq_bounded. intros. 
repeat rewrite kron_1_l. rewrite kron_1_r.
apply Logic.eq_trans with (∣ x0 ⟩_ (t) × ⟨ x0 ∣_ (t) ⊗ I (2 ^ L)
× (I (2 ^ t) ⊗  U_f x0)).
f_equal; type_sovle'; try lia. 
rewrite kron_mixed_product. rewrite Mmult_1_r.
rewrite Mmult_1_l. reflexivity. admit.
 auto_wf. auto_wf.
Admitted.

Lemma base_inner_0:forall i j :nat,
i<>j->
(⟨ i ∣_ (t) × ∣ j ⟩_ (t))=0 .* I 1 .
Proof.  induction t. simpl. intros. 
destruct i. destruct j. intuition.
     Admitted.

Lemma  simpl_Uf: UCtrl_v 0 t t (t + L) 0 (t + L) U_f
(1 / √ (r * 2 ^ t)
 .* big_sum
      (fun s : nat =>
       big_sum (fun j : nat => ∣ j ⟩_ (t)) (2 ^ t)
       ⊗ Us s) r) =
      (1 / √ (r)
       .* big_sum
            (fun s : nat =>
            (1/ √ (2 ^ t)).* big_sum (fun j : nat =>(cos ((2*PI/2^t)* j *(s/r * 2^t)), sin ((2*PI/2^t)* j *(s/r * 2^t))) .* ∣ j ⟩_ (t)) (2 ^ t)
             ⊗ Us s) r).
Proof.
rewrite U_f'. 
rewrite Mscale_mult_dist_r.
rewrite Mmult_Msum_distr_l.
assert((1 / √ (r * 2 ^ t))%C= (1 / √ r * (1 / √ (2 ^ t)))%C ).
admit. rewrite H. rewrite <-Mscale_assoc.
f_equal. rewrite <-Mscale_Msum_distr_r.
apply big_sum_eq_bounded. intros.
rewrite Mscale_kron_dist_l.  f_equal.
repeat rewrite kron_Msum_distr_r.
rewrite Mmult_Msum_distr_l.
apply big_sum_eq_bounded. intros.
rewrite Mmult_Msum_distr_r.
apply big_sum_unique .
exists x1. split. assumption. 
split. 
apply Logic.eq_trans with ((
(∣ x1 ⟩_ (t) × ⟨ x1 ∣_ (t) × ∣ x1 ⟩_ (t)) ⊗  ((cos ((2*PI/2^t)* x1 *(x0/r * 2^t)), sin ((2*PI/2^t)* x1 *(x0/r * 2^t))) .* Us x0))).
rewrite kron_mixed_product. f_equal.
rewrite simpl_expU. f_equal. 
rewrite Mmult_assoc. rewrite base_innner.
rewrite Mmult_1_r.  rewrite Mscale_kron_dist_r.
rewrite Mscale_kron_dist_l.
reflexivity.  auto_wf. assumption.
intros.
rewrite kron_mixed_product.
rewrite Mmult_assoc. rewrite base_inner_0.
rewrite Mscale_0_l. rewrite Mmult_0_r.
rewrite kron_0_l. reflexivity. intuition.
Admitted.

Lemma unitary_trans{n:nat}: forall (U:Square n) (v1 v2:Vector n),
WF_Unitary U->WF_Matrix v1->
U × v1 = v2-> (U) † × v2 = v1 .
Proof. intros. unfold WF_Unitary in H. destruct H.
rewrite <-H1. rewrite <-Mmult_assoc. rewrite H2.
rewrite Mmult_1_l. reflexivity. assumption.
   
Qed.

Lemma  simpl_QFT': @U_v t (t+L) 0 t 0 (t + L) (QFT) †
(1 / √ r
 .* big_sum
      (fun s : nat =>
       1 / √ (2 ^ t)
       .* big_sum
            (fun j : nat =>
             (cos
                (2 * PI / 2 ^ t * j * (s / r * 2 ^ t)),
              sin
                (2 * PI / 2 ^ t * j * (s / r * 2 ^ t)))
             .* ∣ j ⟩_ (t)) (2 ^ t) ⊗ 
       Us s) r)=
       (1 / √ r
 .* big_sum
      (fun s : nat =>
       (Vec (2^t) (s/r * 2^t)) ⊗ 
       Us s) r) .
Proof. 
 unfold U_v. 
repeat rewrite add_sub_eq. repeat rewrite Nat.sub_0_r.
repeat rewrite Nat.sub_diag. repeat rewrite pow_0.
rewrite kron_1_l. assert(2^t=1* 2^t). lia. destruct H.
assert( 2^t * 2^L= 2^(t+L)). type_sovle'. destruct H.
rewrite Mscale_mult_dist_r. f_equal.
rewrite Mmult_Msum_distr_l. 
apply big_sum_eq_bounded.  intros. 
(* rewrite Mscale_kron_dist_l.
rewrite Mscale_mult_dist_r. *)
(* repeat rewrite Mscale_kron_dist_l.
f_equal. rewrite <-Mscale_kron_dist_l.  *)
rewrite kron_mixed_product.
rewrite Mmult_1_l.
(* rewrite <-Mscale_kron_dist_l. *)
f_equal.
pose HQFT. 
apply unitary_trans. intuition.
apply WF_vec. admit.
destruct a. rewrite H1.  
f_equal. 
apply big_sum_eq_bounded. intros.
f_equal. f_equal; f_equal; f_equal; admit.
admit.
apply WF_adjoint. apply HQFT.
Admitted.


Theorem OF_correctness:   
{{BLe 2 x /\  BLe x (N-1) /\ BEq (Nat.gcd x N) 1 /\ BNeq (N mod 2) 0}} OF {{BEq z r}} .
Proof.  
unfold OF.
eapply rule_seq.
eapply rule_conseq_l'.
eapply rule_assgn with (P:=(BEq z 1)). 
admit.
eapply rule_seq.
eapply rule_conseq_l'.
eapply rule_assgn with (P:=(BAnd (BEq z 1)  ( BEq b (x mod N)))).
admit. 
eapply rule_conseq_l with (P':=( (BNeq z r) /\ (BNeq b 1))).
admit.
eapply rule_conseq.
eapply rule_while with (F0:= (BNeq z r)) (F1:= (BEq z r)).
*eapply rule_seq.
eapply rule_conseq_l.
apply rule_PT.
apply rule_QInit. 
*eapply rule_seq.
eapply rule_conseq_l.
apply rule_OdotE.
eapply rule_qframe'.
split. apply rule_QInit. simpl. admit.
* eapply rule_seq.
eapply rule_qframe.
split. apply rule_QUnit_One'. lia. apply WF_vec. apply pow_gt_0.
simpl. admit. unfold U_v. repeat rewrite Nat.sub_diag. rewrite Nat.sub_0_r. simpl.
rewrite kron_1_l; auto_wf. rewrite kron_1_r; auto_wf. 
rewrite Had_N.  
* eapply rule_seq.
eapply rule_qframe'.
split. apply rule_QUnit_One'. lia. apply WF_vec. apply pow_gt_0.
simpl. admit. unfold U_v. repeat rewrite Nat.sub_diag.
simpl. pose HU_plus. rewrite kron_1_l; auto_wf. rewrite kron_1_r; auto_wf.
destruct a. assert(L=t + L - t). lia. destruct H1.
rewrite H0. 
* eapply rule_seq.
eapply rule_conseq_l.
eapply rule_odotT.
eapply rule_conseq_l.
eapply rule_Separ.
assert(L=t + L - t). lia. destruct H1.
assert(t=t-0). lia. destruct H1.
rewrite simpl_H_Uplus.
eapply rule_QUnit_Ctrl'. lia. admit.
rewrite simpl_Uf.
* eapply rule_seq.
eapply rule_QUnit_One'. lia. admit.
assert(t=t-0). lia. destruct H1.
assert(t+L=t+L-0). lia. destruct H1.
rewrite simpl_QFT'.
* eapply rule_seq. 
eapply rule_conseq_l'.
eapply rule_QMeas with (s:=0) (e:=t+L) (P:=P)
(v:= 1 / √ r .*  (big_sum (fun s:nat=>kron  (Vec (2^t) (s/r * 2^t) ) (Us s)) (r) )). lia.
admit. admit. admit.
*eapply rule_seq. 
eapply rule_conseq_l. 
eapply rule_Oplus. rewrite big_pOplus_get_npro.
eapply rule_conseq_l'.
eapply rule_assgn.
admit. admit.  destruct a.
assert(L=t+L-t). lia. destruct H1.
destruct H. 
apply H.
admit. admit.
Admitted.

Parameter random: nat -> nat -> nat.
Definition y:nat :=3 .
Definition y':nat :=4 .
Definition N2 := (N mod 2).
Definition  b2 :=(BAnd (BEq (z mod 2) 0) (BNeq (x^(z/2) mod N) 1)) .
Definition  b3 :=(BAnd (BNeq y' 1)  (BNeq y' N)) .

Hypothesis Hran: forall i a b, {{BTrue}} i:=random a b {{BLe a i /\ BLe i b}}.

Definition Shor:=
  <{  if BEq N2 0 then
           y:=2
      else  
           x:=random 2 (N-1);
           y:=Nat.gcd x N;
           while BEq y 1 do 
                  OF;
                  if b2 then
                      y':=Nat.gcd (x^(z/2)-1) N;
                      if b3 then 
                          y:=y'
                      else 
                          y:=Nat.gcd (x^(z/2)+1) N
                      end 
                  else 
                       x:=random 2 (N-1);
                       y:=Nat.gcd x N
                  end 
            end 
      end 
  }>.


Theorem rule_while_classic: forall F (b:bexp) (c:com),
         {{F /\ b}} c {{ F}}
      -> {{F}}
         while b do c end
         {{ (F /\ (BNot b)) }}.
Proof. Admitted.

Theorem rule_cond_classic: forall (F1 F2: State_formula) (c1 c2:com) (b:bexp),
        ({{F1 /\ (b)}} c1 {{F2 }} /\ {{F1 /\ ((BNot b) )}} c2 {{F2 }})
     -> ({{F1 }}
        if b then c1 else c2 end
        {{F2}}).
Proof. Admitted.

Theorem rule_qframe': forall (F1 F2 F3: State_formula) c,
         ({{F1}} c {{F2}}) /\  (NSet.inter (fst (Free_state F3)) (fst (MVar c)) =NSet.empty) 
         /\ (NSet.inter (snd (Free_state F3)) (snd (MVar c)) =NSet.empty) 
         ->  {{F3 /\ F1}} c {{F3 /\ F2}}. Admitted.

         Theorem rule_conseq_r' : forall (P Q Q' : Assertion) c,
         {{P}} c {{Q'}} ->
         (Q'->> Q) ->
               
                {{P}} c {{Q}}.
                Proof. intros. eapply rule_conseq. apply H. 
                apply implies_refl. assumption. Qed.   


Theorem Shor_correctness :
{{ BTrue}} Shor {{(BEq (N mod y) 0) /\ (BNeq y' 1) /\ (BNeq y' N)}} .
Proof. unfold Shor. 
eapply rule_cond_classic. split.
{eapply rule_conseq with (P':= (BEq N2 0) /\ (Assn_sub y 2 (BEq y 2)))
(Q':=   ((BEq N2 0)) /\ (BEq y 2)).
eapply rule_qframe'. split. apply rule_assgn.
unfold N2. admit. admit.
unfold N2. unfold assert_implies. intros.
rewrite sat_Assert_to_State in *.
inversion_clear H.  econstructor. intuition.
rewrite State_eval_conj in *. }
{ eapply rule_seq with (Q:= (BLe 2 x /\ BLe x (N-1)) /\ Assn_sub y (Nat.gcd x N) (BEq y (Nat.gcd x N))).

  {eapply rule_conseq_r with (Q':= BLe 2 x /\ BLe x (N-1)). admit.
   eapply rule_conseq.
   apply Hran. apply rule_AndE. apply implies_refl. }
  eapply rule_seq.
 {eapply rule_qframe'. split.  
  apply rule_assgn.  simpl. admit. }

  eapply rule_conseq_l with (P':=  (BEq (N mod y) 0) /\ (BNeq y N)).
  admit.
  eapply rule_conseq_r'.
  eapply rule_while_classic. 
  eapply rule_seq.  
  eapply rule_conseq_l'.  
  apply OF_correctness. admit.
  apply rule_cond_classic. split.
  eapply rule_seq. 
  eapply rule_conseq_l'.
  apply rule_assgn with (P:= (BEq y' (Nat.gcd (x ^ (z / 2) - 1) N))).
  admit.
  eapply rule_conseq_l with (P':= (BEq (N mod y') 0) ).
  admit.
  eapply rule_conseq_r with (Q':= (BEq (N mod y) 0) /\ (BNeq y 1) /\ (BNeq y N)).
  admit.
  apply rule_cond_classic.
  split. unfold b3. admit.
  unfold b3. 
    eapply rule_conseq.
    apply rule_assgn with (P:= (BEq y (Nat.gcd (x ^ (z / 2) - 1) N))).
    admit. admit. 
    eapply rule_seq with (Q:= (BLe 2 x /\ BLe x (N-1)) /\ Assn_sub y (Nat.gcd x N) (BEq y (Nat.gcd x N))).
    eapply rule_conseq_r with (Q':= BLe 2 x /\ BLe x (N-1)). admit.
   eapply rule_conseq.
   apply Hran. admit. apply implies_refl.
   eapply rule_conseq_r'. 
   eapply rule_qframe'. split.  
  apply rule_assgn.  simpl. admit. admit.
  admit.
Admitted.

End OF.
