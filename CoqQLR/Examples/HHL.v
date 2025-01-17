Require Import Lists.List.
Require Import Reals.
Require Import Coquelicot.Complex.
Require Import Strings.String.


From Quan Require Import Matrix.
From Quan Require Import Quantum.
From Quan Require Import Basic.
From Quan Require Import Mixed_State.
From Quan Require Import QState_L.
From Quan Require Import Reduced.
From Quan Require Import QIMP_L.
From Quan Require Import Ceval_Prop.
From Quan Require Import QAssert_L.
From Quan Require Import QRule_E_L.
From Quan Require Import QRule_Q_L.
From Quan Require Import QRule_I_L.
From Quan Require Import QSepar.
From Quan Require Import QFrame.
From Quan Require Import addM.

Local Open Scope com_scope.
Local Open Scope assert_scope.
Local Open Scope nat_scope.
Local Open Scope matrix_scope.
Local Open Scope rule_scope.

Lemma pow_0: (2^0=1)%nat. Proof. auto. Qed.
Lemma add_sub_eq: forall n m, n+m-n=m .
Proof. intuition.     
Qed.

Lemma kron_n_I : forall n m, n ⨂ I m = I (m ^ n).
Proof.
  intros.
  induction n; simpl.
  reflexivity.
  rewrite IHn. 
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



Lemma n_kron: forall n, ∣ 0 ⟩_ (2^n) = n ⨂ qubit0.
Proof.
induction n. simpl. unfold Base_vec.  
prep_matrix_equality. destruct y; destruct x;
 simpl; try reflexivity.
assert (WF_Matrix (I 1)). apply WF_I.
unfold WF_Matrix in *. rewrite H. reflexivity.
intuition. rewrite kron_n_assoc. rewrite <-IHn.
rewrite <-base_qubit0.
rewrite Nat.pow_1_l.
rewrite (qubit0_base_kron n 0). f_equal. f_equal. lia.
apply pow_gt_0. auto_wf.
Qed.

Lemma Had_N: forall n:nat, 
n ⨂ hadamard × ∣ 0 ⟩_ ((2^n)) = (/ (√ 2) ^ n)%C .* big_sum (fun z=> ∣ z ⟩_ ((2^n))) (2^n).
Proof. intros. 
rewrite n_kron. apply Logic.eq_trans with (n ⨂ hadamard × n ⨂ ∣0⟩).
f_equal. rewrite Nat.pow_1_l. reflexivity.
rewrite kron_n_mult. rewrite MmultH0. 
unfold xbasis_plus. 
rewrite Mscale_kron_n_distr_r. 
rewrite <-RtoC_inv. rewrite RtoC_pow.
rewrite <-Rinv_pow_depr. 
f_equal. apply  Nat.pow_1_l.  rewrite RtoC_inv. f_equal.
rewrite RtoC_pow.
f_equal. apply Rgt_neq_0. 
apply pow_lt.   apply sqrt_lt_R0. lra.

induction n.  simpl. rewrite Mplus_0_l.
rewrite base_I. reflexivity.
 rewrite kron_n_assoc.  rewrite IHn.
simpl. rewrite Nat.add_0_r.
rewrite big_sum_sum. 
rewrite kron_plus_distr_r.
unfold Gplus.  simpl.
f_equal. lia.   rewrite Nat.pow_1_l. simpl. reflexivity. 
apply Logic.eq_trans with (∣0⟩ ⊗ big_sum (fun z : nat => ∣ z ⟩_ (2^n) ) (2 ^ n)).
f_equal. apply Nat.pow_1_l.
rewrite kron_Msum_distr_l.
apply big_sum_eq_bounded. intros.
rewrite <-base_qubit0.
rewrite qubit0_base_kron. reflexivity. assumption.
apply Logic.eq_trans with (∣1⟩ ⊗ big_sum (fun z : nat => ∣ z ⟩_ (2^n) ) (2 ^ n) ).
f_equal. apply Nat.pow_1_l.
rewrite kron_Msum_distr_l.
apply big_sum_eq_bounded. intros.
rewrite <-base_qubit1.
rewrite qubit1_base_kron. rewrite (Nat.add_comm x). reflexivity. assumption.
auto_wf. apply sqrt_neq_0_compat. lra. 
apply sqrt_neq_0_compat. lra. 
Qed.


Coercion INR : nat >-> R.
Local Open Scope R_scope.
Module HHL.

Definition v:nat:= 0.
Parameter n m:nat .
Parameter A:Square (2^m).
Parameter b:Vector (2^m).
Parameter x:Vector (2^m).
Parameter v_n:nat-> Vector (2^m).
Parameter lamda_n:nat-> R.
Parameter b_n:nat-> C.
Parameter c:R.
Parameter U_b:Square (2^m).
Parameter U: Square (2^m).
Parameter QFT: Square (2^n) .
Parameter t:R. 
Parameter delt_n:nat->nat.

Hypothesis Hmn: ( (n>0)%nat /\ (m>0)%nat).
Hypothesis HA: WF_Matrix A .
Hypothesis Hb: WF_Matrix b /\ norm b =1.
Hypothesis Hv_n:forall j, WF_Matrix (v_n j) /\ norm (v_n j)=1.
Hypothesis (Hlamda: forall j, lamda_n j <> 0).
Hypothesis HB_decom: big_sum (fun j=>(b_n j) .* (v_n j)) (2^m)= b.
Hypothesis HA_decom: big_sum (fun j=>(lamda_n j) .* Mmult (v_n j) (adjoint (v_n j))) (2^m)= A.
Hypothesis Hx:WF_Matrix x /\ x=(big_sum (fun i : nat => b_n i / lamda_n i .* v_n i) (2 ^ m))%R /\ norm x =1.

Hypothesis Hc: c> 0 /\ forall j:nat, Rabs (c / j) <= 1.
Hypothesis Ht': t>0.

Hypothesis HU_b: WF_Unitary U_b /\ ( U_b × (Base_vec (2^m) 0) = b).
Hypothesis HU: (WF_Unitary (U) )/\ forall j :nat,  (U) × ( (v_n j))= (cos ((lamda_n j) * t), sin ( (lamda_n j) * t)) .* ( (v_n j)).
Hypothesis HQFT: WF_Unitary QFT /\ forall k:nat, QFT × (∣ k ⟩_ (2^n)) =
/ √ 2 ^ n .* (big_sum (fun j : nat => (cos (((2 * PI)/(2^n)) * j * k),  sin (((2 * PI)/(2^n)) * j * k)) .*  (∣ j ⟩_ (2^n))) (2 ^ n)).

Hypothesis (Ht: forall j:nat, and (delt_n j < 2^n)%nat  ((lamda_n j * t/ (2*PI))*(2^n) = delt_n j)).

Definition  U_f (i:nat):= exp_U U i.
Definition  phi (j:nat):= (lamda_n j * t) / (2 * PI).
Definition  phi' (j:nat) := ((phi j) * (2^n))%R.
Definition  adj_Uf (i:nat) := adjoint (U_f i).

Definition  U_c (j:nat): Matrix 2 2:=
  match j with 
  | 0 => I 2
  | _ => fun x y => 
          match x, y with 
          |0, 0 => (sqrt (1-(( c^2)/( ( (j))^2))))
          |0, 1 => c/((j))
          |1, 0 => c/((j))
          |1, 1 => - (sqrt (1-(( c^2)/( (j)^2))))
          | _, _ => C0
          end 
end.

Lemma Rabs_le_1: forall r:R, 
Rabs r <=1 -> r^2 <=1 .
Proof. intros. assert(1=1^2). simpl. repeat rewrite Rmult_1_r. reflexivity.
       rewrite H0. repeat rewrite <-Rsqr_pow2. 
      apply Rsqr_le_abs_1. rewrite Rabs_R1. assumption. 
Qed.


Local Open Scope nat_scope.
Lemma HU_c:(forall j, WF_Unitary (U_c j)) /\ ((U_c 0) × (∣ 0 ⟩_ (2))) = (∣ 0 ⟩_ (2)) /\
(forall j:nat, (j<>0)%nat ->(U_c j) × (∣ 0 ⟩_ (2)) = 
(((sqrt (1-(( c^2)/( (j)^2)))) .* (∣ 0 ⟩_ (2)) .+ (c/((j)) .* (∣ 1 ⟩_ (2)))))).
Proof. split. intros. destruct j. simpl. apply id_unitary.
       unfold WF_Unitary. split.
       unfold WF_Matrix. intros. destruct x0; destruct y. lia. 
       destruct y; try lia. simpl. reflexivity. 
       destruct x0; try lia. reflexivity. 
       destruct x0; try lia. destruct y; try lia. intuition. reflexivity.
       
       prep_matrix_equality.
       destruct x0; destruct y;
       unfold Mmult; unfold Σ;
       unfold adjoint;  
       rewrite Cplus_0_l;
       unfold U_c; repeat rewrite Cconj_R;
       repeat rewrite RtoC_mult;  
       remember ((INR (S j))); 
       try remember ((INR (S x0)));
       try remember ((INR (S y))); simpl;
       repeat rewrite Rmult_1_r;
       try repeat rewrite sqrt_sqrt.
    
       (*0,0*)
       try rewrite <-RtoC_plus.
       unfold I. simpl.  f_equal.
       assert(forall r, 1-r+r=1)%R. intuition lra.
       repeat rewrite Rmult_div. apply H. 
       rewrite Heqr.  apply not_0_INR. lia. 
       rewrite Heqr.  apply not_0_INR. lia. 
       rewrite<- Rcomplements.Rminus_le_0.  
       rewrite <-Rmult_div. rewrite Rmult_pow. apply Rabs_le_1.
       rewrite Heqr. apply Hc.
       rewrite Heqr.  apply not_0_INR. lia.
       rewrite Heqr.  apply not_0_INR. lia.     
      
       (*0,1*)
       destruct y.
       repeat rewrite RtoC_mult.
       repeat rewrite <-RtoC_plus.
       unfold I. simpl. 
       rewrite (Rmult_comm _ (c / r) ).
       rewrite Ropp_mult_distr_r_reverse. 
       rewrite Rplus_opp_r.  reflexivity. 
       repeat rewrite RtoC_mult.
       repeat rewrite Rmult_0_r.  
       unfold I. simpl. rewrite Cplus_0_l. reflexivity.

       (*1,0*)
      destruct x0;  repeat rewrite Cconj_R;
      repeat rewrite RtoC_mult.
      repeat rewrite <-RtoC_plus.
      unfold I. simpl. 
      rewrite (Rmult_comm _ (c / r) ).
      rewrite Ropp_mult_distr_r_reverse. 
      rewrite Rplus_opp_r.  reflexivity. 
      repeat rewrite Rmult_0_l.   rewrite Cplus_0_l.  
       unfold I. simpl. reflexivity.

      (*1,1*)
       destruct x0. 
       destruct y.  
       repeat rewrite Cconj_R;
       repeat rewrite RtoC_mult.
       rewrite Rmult_opp_opp. 
       rewrite sqrt_sqrt. 
       repeat rewrite <-RtoC_plus.
       rewrite Rplus_comm.  
       assert(forall r, 1-r+r=1)%R. intuition lra.
       rewrite Rmult_div. unfold I. simpl. f_equal. apply H.
       rewrite Heqr.  apply not_0_INR. lia.
       rewrite Heqr.  apply not_0_INR. lia.  
       rewrite<- Rcomplements.Rminus_le_0.  
       rewrite <-Rmult_div. rewrite Rmult_pow. apply Rabs_le_1.
       rewrite Heqr. apply Hc.
       rewrite Heqr.  apply not_0_INR. lia.   
       rewrite Heqr.  apply not_0_INR. lia. 
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
      assert((S (S x0) <? 2)=false). rewrite Nat.ltb_ge. lia.
      rewrite H. bdestruct ((x0 =? y)); simpl; rewrite Cplus_0_l; reflexivity.


    split. simpl. rewrite Mmult_1_l. reflexivity.
    auto_wf. intros. destruct j. intuition lra.
    prep_matrix_equality. 
    destruct x0; destruct y;
    unfold Mmult; 
    unfold Mplus; unfold scale;
    destruct j;  simpl;
    repeat rewrite Cmult_0_r;
    repeat rewrite Cplus_0_l; try reflexivity;
    try remember ((match j with
    | 0%nat => 1
    | S _ => j + 1
    end)%R).
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
    reflexivity.  rewrite Rplus_comm.   
    assert( r= S j). rewrite Heqr. simpl. reflexivity. 
    rewrite H0. rewrite <-S_O_plus_INR. 
    apply not_0_INR. lia.    
    simpl. rewrite Cmult_0_l. rewrite Cmult_0_r.
    rewrite Cplus_0_l. reflexivity.
Qed.




           
Local Open Scope nat_scope.     
Local Open Scope com_scope.   


Definition HHL :=
    <{ v := 0;
       while  v ' = 0  do 
       [[ 0 n ]] :Q= 0;
       [[ n (n+m) ]] :Q= 0;
       [[ (n+m) (n+m+1) ]] :Q= 0;
       U_b [[ n (n+m) ]];
       (n ⨂ hadamard) [[ 0 n ]];
       U_f [[ 0 n ]] [[n (n+m)]];
       (adjoint QFT) [[0 n]];
       U_c [[0 n]] [[ (n+m) (n+m+1) ]];
       QFT [[0 n]];
       (adj_Uf) [[ 0 n ]] [[n (n+m)]];
       (n ⨂ hadamard) [[ 0 n ]];
        v :=M [[ (n+m) (n+m+1) ]]
       end }>.

Ltac type_sovle:= 
  try repeat rewrite add_sub_eq; 
  try repeat rewrite Nat.sub_0_r;
  try repeat rewrite Nat.sub_diag;
  try repeat rewrite pow_0;
  try (f_equal; type_sovle'; try lia );
  try apply big_sum_eq_bounded; try intros;
  try rewrite kron_1_l; try rewrite kron_1_r.

Lemma Had_N':
U_v 0 n 0 n (n ⨂ hadamard) ∣ 0 ⟩_ (2^n)= (/√ 2 ^ n) .* big_sum (fun z=> ∣ z ⟩_ (2^n)) (2^n).
Proof. unfold U_v. type_sovle. rewrite Had_N. reflexivity. auto_wf.
Qed.

Lemma U_vb:
U_v n (n + m) n (n + m) U_b ∣ 0 ⟩_ (2^m)=(big_sum (fun j=>(b_n j) .* (v_n j)) (2^m)).
Proof. unfold U_v. type_sovle.  pose HU_b. destruct a. 
rewrite H0.  rewrite HB_decom. reflexivity. apply HU_b.  
Qed.

Lemma  WF_expU{n:nat}: forall (U:Square (2^n)) x0,
WF_Matrix U->
WF_Matrix (exp_U U x0).
Proof. induction x0; simpl; intros. auto_wf.
auto_wf.
Qed.


Lemma U_f': forall (v:Vector (2^n *(2^m))) , 
(UCtrl_v 0 n n (n + m) 0 (n + m) U_f v) =
Mmult (big_sum (fun i : nat => (∣ i ⟩_ (2^n) × ⟨ i ∣_ (2^n)) ⊗ (U_f i))  (2 ^ n)) v.
Proof.  intros. unfold UCtrl_v. type_sovle.  
apply Logic.eq_trans with (∣ x0 ⟩_ (2^n) × ⟨ x0 ∣_ (2^n) ⊗ I (2 ^ m)
× (I (2 ^ n) ⊗  U_f x0)). 
f_equal; type_sovle'; try lia. 
rewrite kron_mixed_product. rewrite Mmult_1_r.
rewrite Mmult_1_l. reflexivity. apply WF_expU.
pose HU. destruct a. apply H0. auto_wf. auto_wf.
Qed .


Definition  P (i:nat): Pure_formula := (BEq v ' ( i)) .

Lemma simpl_HB: (/ √ 2 ^ n) .* big_sum (fun z : nat => ∣ z ⟩_ (2^n)) (2 ^ n)
⊗ big_sum (fun j : nat => b_n j .* v_n j) (2 ^ m)=
big_sum (fun j : nat => b_n j .* (( / √ 2 ^ n) .* big_sum (fun z : nat => ∣ z ⟩_ (2^n) ⊗ v_n j ) (2 ^ n)
)) (2 ^ m).
Proof.  
rewrite kron_Msum_distr_l.
apply big_sum_eq_bounded. intros.
rewrite Mscale_kron_dist_r.
rewrite Mscale_kron_dist_l.  f_equal. 
rewrite kron_Msum_distr_r. reflexivity.    
Qed.

Lemma simpl_expU:forall i j,
U_f i × v_n j = (cos ((lamda_n j)* t *i), sin (((lamda_n j)* t * i))) .* v_n j.
Proof. intros.  induction i. simpl.
       rewrite Mmult_1_l. rewrite Rmult_0_r. rewrite cos_0. rewrite sin_0.
       rewrite Mscale_1_l. reflexivity. pose Hv_n. apply a.
       unfold U_f in *.  simpl exp_U. rewrite Mmult_assoc.
       rewrite IHi. rewrite Mscale_mult_dist_r.
       pose HU. destruct a. rewrite H0.
       rewrite Mscale_assoc. f_equal. 
       remember (lamda_n j * t)%R. 
       rewrite S_O_plus_INR. rewrite Rplus_comm.  rewrite Rmult_plus_distr_l.
       rewrite cos_plus. rewrite sin_plus.
       rewrite Rmult_1_r. unfold Cmult. simpl.
       f_equal. rewrite Rplus_comm.  reflexivity.  
Qed.


Lemma simpl_Uf:
UCtrl_v 0 n n (n + m) 0 (n + m) U_f
(big_sum (fun j : nat =>  b_n j  .* ((/√ 2 ^ n) .* big_sum (fun z : nat => ∣ z ⟩_ (2^n) ⊗ v_n j)  (2 ^ n))) (2 ^ m))
= (big_sum (fun j : nat =>  b_n j .* ((/√ 2 ^ n) .* big_sum (fun z : nat => (cos (2*PI * (phi j)* z), sin ((2*PI * (phi j)* z))) .* ∣ z ⟩_ (2^n)) 
(2 ^ n)) ⊗ v_n j )  (2 ^ m)).
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
      (∣ i ⟩_ (2^n) × ⟨ i ∣_ (2^n) × ∣ x1 ⟩_ (2^n)) ⊗  ((cos (2*PI * (phi x0)* i), sin ((2* PI * (phi x0)* i))) .* v_n x0)))).
      apply big_sum_unique .
      exists x1. split. assumption. 
      split. rewrite Mmult_assoc. rewrite base_inner_1. unfold c_to_Vector1.
      Msimpl. rewrite Mscale_kron_dist_r.
      rewrite Mscale_kron_dist_l.
      reflexivity. assumption.
      intros. rewrite Mmult_assoc. rewrite base_inner_0; try assumption.
      unfold c_to_Vector1. Msimpl.  reflexivity. lia. 
      intros.  
      rewrite kron_mixed_product. f_equal.
      rewrite simpl_expU. f_equal. f_equal;
      f_equal; unfold phi; rewrite Rdiv_unfold;
       rewrite (Rmult_comm _ (/ (2 * PI)));
       rewrite <-Rmult_assoc; rewrite Rinv_r;
       try rewrite Rmult_1_l; try reflexivity.
       apply Rmult_integral_contrapositive_currified.
       lra. apply PI_neq0. 
       apply Rmult_integral_contrapositive_currified.
       lra. apply PI_neq0.
Qed.

Lemma unitary_trans{n:nat}: forall (U:Square n) (v1 v2:Vector n),
WF_Unitary U->WF_Matrix v1->
U × v1 = v2-> (U) † × v2 = v1 .
Proof. intros. unfold WF_Unitary in H. destruct H.
rewrite <-H1. rewrite <-Mmult_assoc. rewrite H2.
rewrite Mmult_1_l. reflexivity. assumption.
Qed.

Lemma simpl_QFT': 
@U_v n (n+m) 0 n 0 (n + m) (QFT) † 
(big_sum (fun j : nat => b_n j.* ((/√ 2 ^ n) .* big_sum (fun z : nat =>
 (cos (2 * PI * phi j * z),  sin (2 * PI * phi j * z)).* ∣ z ⟩_ (2^n)) (2 ^ n)) ⊗ v_n j) (2 ^ m))
=(big_sum (fun j : nat => b_n j .* (Base_vec (2^n) (delt_n j)) ⊗  v_n j) (2 ^ m)).
Proof. pose Ht.  unfold U_v. type_sovle. 
assert(2^n=1* 2^n). lia. destruct H.
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
apply WF_base. apply a. 
destruct a0. rewrite H1. 
f_equal.
apply big_sum_eq_bounded. intros.
f_equal. assert(phi' x0 = delt_n x0). unfold phi'.
unfold phi. apply a.
rewrite <-H3. unfold phi'.
rewrite Rdiv_unfold. repeat rewrite Rmult_assoc.
f_equal; f_equal; f_equal; f_equal;
repeat rewrite <-Rmult_assoc;
rewrite Rmult_comm; repeat rewrite <-Rmult_assoc;
rewrite Rinv_r; try rewrite Rmult_1_l; try lra.
rewrite pow_IZR.  apply not_0_IZR. lia. 
rewrite pow_IZR.  apply not_0_IZR. lia.
pose Hv_n. apply a0. pose HQFT.
destruct a0. apply WF_adjoint. apply H.
Qed.

Lemma simpl_Uc:
UCtrl_v 0 n (n + m) (n + m + 1) 0 (n + m + 1) U_c 
(big_sum (fun i : nat =>  b_n i .* ∣ delt_n i ⟩_ (2^n) ⊗ v_n i ⊗ ∣ 0 ⟩_ (2)) (2 ^ m))=
 (big_sum (fun i : nat =>  b_n i .* ∣ delt_n i ⟩_ (2^n) ⊗ v_n i ⊗
((sqrt (1-(( c^2)/( (phi' i)^2)))) .* (∣ 0 ⟩_ (2)) .+ (c/((phi' i)) .* (∣ 1 ⟩_ (2))))) (2 ^ m)).
Proof. pose Ht as H. unfold UCtrl_v. type_sovle. 
assert(m+1=n + m + 1 - n). lia. destruct H0.
assert(2^n * 2^m * 2^1=2^(n+m+1)). type_sovle'. destruct H0.
rewrite Mmult_Msum_distr_l. apply big_sum_eq_bounded.
intros. apply Logic.eq_trans with (big_sum
(fun i : nat => (∣  i ⟩_ (2^n) × ⟨  i ∣_ (2^n))⊗ I (2^m) ⊗ U_c i )
(2 ^ n) × (b_n x0 .* ∣ delt_n x0 ⟩_ (2^n) ⊗ v_n x0 ⊗ ∣ 0 ⟩_ (2))).
f_equal; rewrite Nat.mul_1_l. rewrite Nat.pow_add_r.
rewrite Nat.mul_assoc. reflexivity. 
apply big_sum_eq_bounded. intros. 
apply Logic.eq_trans with ((∣ x1 ⟩_ (2^n) × ⟨ x1 ∣_ (2^n)) ⊗ I (2 ^ m) ⊗ I (2)
× (I (2 ^ n)  ⊗ I (2 ^ m) ⊗  U_c x1)).   
rewrite kron_1_l; auto_wf. rewrite kron_1_r;auto_wf.
 rewrite kron_assoc; auto_wf. repeat rewrite id_kron; auto_wf.
 repeat rewrite Nat.pow_add_r. simpl. f_equal;
try (rewrite Nat.mul_assoc; reflexivity).
repeat rewrite kron_mixed_product; auto_wf. repeat rewrite Mmult_1_r; auto_wf.
rewrite Mmult_1_l; auto_wf. reflexivity. pose HU_c. 
destruct a. apply H2.  
rewrite Mmult_Msum_distr_r. apply big_sum_unique.
exists (delt_n x0). split. apply H. 
split. repeat rewrite Mscale_kron_dist_l.
rewrite Mscale_mult_dist_r. f_equal.
repeat rewrite kron_mixed_product.  rewrite Mmult_1_l.
rewrite Mmult_assoc. rewrite base_inner_1. unfold c_to_Vector1. 
Msimpl. f_equal.   
assert((lamda_n x0 * t / (2 * PI) * 2 ^ n)%R = delt_n x0). apply H. 
pose HU_c.  destruct a.  destruct H3. rewrite <-base_qubit0.  rewrite <-base_qubit1.  
rewrite H4. rewrite<-H1. unfold phi'. unfold phi. reflexivity.
apply INR_not_0. 
rewrite <-H1. apply Rmult_integral_contrapositive_currified.
rewrite Rdiv_unfold. apply Rmult_integral_contrapositive_currified.
apply Rmult_integral_contrapositive_currified. apply Hlamda.
pose Ht'. apply Rgt_neq_0.  lra.  
apply Rgt_neq_0. apply Rinv_0_lt_compat. apply Rmult_lt_0_compat.
lra.  apply PI_RGT_0. rewrite pow_IZR.  apply not_0_IZR. lia.
apply WF_base. apply H.  apply H. apply Hv_n. intros.
repeat rewrite Mscale_kron_dist_l.
rewrite Mscale_mult_dist_r. 
repeat rewrite kron_mixed_product.
rewrite Mmult_assoc.  rewrite base_inner_0. unfold c_to_Vector1.
Msimpl. reflexivity.
intuition. assumption.
apply H.
Qed. 


Lemma simpl_QFT: 
@U_v (n-0) (n+m+1-0) 0 n 0 (n + m + 1) QFT (big_sum (fun i : nat => b_n i .* ∣ delt_n i ⟩_ (2^n) ⊗ v_n i
⊗ (√ (1 - c ^ 2 / phi' i ^ 2) .* ∣ 0 ⟩_ (2).+ c / phi' i .* ∣ 1 ⟩_ (2))) (2 ^ m)) =
(big_sum (fun i : nat => b_n i .* (((/√ 2 ^ n) .* 
big_sum  (fun z : nat => (cos (2 * PI * phi i * z),  sin (2 * PI * phi i * z)) .* ∣ z ⟩_ (2^n)) (2 ^ n))) ⊗ v_n i
          ⊗ (√ (1 - c ^ 2 / phi' i ^ 2) .* ∣ 0 ⟩_ (2) .+ c / phi' i .* ∣ 1 ⟩_ (2)))
         (2 ^ m)).
Proof. pose Ht as H. unfold U_v. type_sovle. 
apply Logic.eq_trans with (QFT ⊗ I (2 ^ m) ⊗ I (2^1)
× big_sum (fun i : nat => b_n i .* ∣ delt_n i ⟩_ (2^n) ⊗ v_n i
⊗ (√ (1 - c ^ 2 / phi' i ^ 2) .* ∣ 0 ⟩_ (2) .+ c / phi' i .* ∣ 1 ⟩_ (2))) (2 ^ m)).
f_equal; type_sovle'. rewrite kron_assoc; auto_wf.
rewrite id_kron.  f_equal; try lia; type_sovle'. f_equal; type_sovle'.
apply HQFT. rewrite Mmult_Msum_distr_l. 
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
f_equal. assert(phi' x0 = delt_n x0). apply H.
rewrite <-H4. unfold phi'. rewrite Rdiv_unfold. repeat rewrite Rmult_assoc.
f_equal; f_equal; f_equal; f_equal;
repeat rewrite <-Rmult_assoc;
rewrite Rmult_comm; repeat rewrite <-Rmult_assoc;
rewrite Rinv_r; try rewrite Rmult_1_l; try lra.
rewrite pow_IZR.  apply not_0_IZR. lia.
rewrite pow_IZR.  apply not_0_IZR. lia.
assert(0< 2^1). simpl. lia.  auto_wf.
apply Hv_n. apply HQFT. 
Qed.


#[export] Hint Resolve WF_expU : wf_db.
#[export] Hint Resolve WF_adjoint : wf_db.

Lemma  WF_Unitary_expU{n:nat}: forall (U:Square (2^n)) x0,
WF_Unitary U->
WF_Unitary (exp_U U x0).
Proof. induction x0; simpl; intros. apply id_unitary. 
apply Mmult_unitary. apply H. apply IHx0. assumption.
Qed. 


Lemma simpl_Uf':
UCtrl_v 0 n n (n + m) 0 (n + m + 1) adj_Uf 
(big_sum (fun i : nat =>  b_n i  .* ( / √ 2 ^ n
 .* big_sum (fun z : nat =>  (cos (2 * PI * phi i * z), sin (2 * PI * phi i * z)) .*   ∣ z ⟩_ (2^n)) (2 ^ n)) ⊗ v_n i
              ⊗ (√ (1 - c ^ 2 / phi' i ^ 2) .* ∣ 0 ⟩_ (2)
                 .+ c / phi' i .* ∣ 1 ⟩_ (2))) (2 ^ m))
  = (big_sum (fun i : nat => b_n i .* ((/√ 2 ^ n)  .* big_sum (fun z : nat => ∣ z ⟩_ (2^n)) (2 ^ n)) ⊗ v_n i
          ⊗ (√ (1 - c ^ 2 / phi' i ^ 2) .* ∣ 0 ⟩_ (2) .+ c / phi' i .* ∣ 1 ⟩_ (2)))
         (2 ^ m)) .
Proof. pose HU.  destruct a. 
 unfold UCtrl_v. type_sovle.
apply Logic.eq_trans with (big_sum
(fun i : nat =>
 (∣ i ⟩_ (2^n) × ⟨ i ∣_ (2^n)) ⊗ adj_Uf i ⊗ I (2 ^ 1)) 
(2 ^ n)
× big_sum (fun i : nat => b_n i .* ((/√ 2 ^ n)
 .* big_sum (fun z : nat => (cos (2 * PI * phi i * z),
                    sin (2 * PI * phi i * z)) .* 
             ∣ z ⟩_ (2^n)) (2 ^ n)) ⊗ v_n i
   ⊗ (√ (1 - c ^ 2 / phi' i ^ 2) .* Base_vec 2 0
      .+ c / phi' i .* Base_vec 2 1)) (2 ^ m)).
f_equal. rewrite <-Nat.add_assoc. rewrite Nat.mul_1_l.
rewrite add_sub_eq.   rewrite <-Nat.mul_assoc.
f_equal. simpl. rewrite Nat.pow_add_r. simpl. reflexivity.
type_sovle'. apply big_sum_eq_bounded. intros.
repeat rewrite kron_1_l. repeat rewrite kron_assoc; auto_wf.
eapply Logic.eq_trans with (∣ x0 ⟩_ (2^n) × ⟨ x0 ∣_ (2^n)
⊗ I ((2^m * 2^1))
× (I (2 ^ n) ⊗ ( adj_Uf x0 ⊗ I (2 ^ 1)))).
f_equal.  simpl. type_sovle. rewrite <-Nat.add_assoc.
rewrite add_sub_eq. rewrite Nat.pow_add_r. simpl. reflexivity.
rewrite <-Nat.add_assoc. rewrite Nat.mul_1_l.
rewrite add_sub_eq.  f_equal. simpl. rewrite Nat.pow_add_r. simpl. reflexivity.
type_sovle'  . f_equal; type_sovle'; try lia.
f_equal;type_sovle'. 
rewrite kron_mixed_product; auto_wf.  
rewrite Mmult_1_r; auto_wf. rewrite Mmult_1_l; auto_wf.  f_equal. 
apply WF_kron; type_sovle'; auto_wf. 
auto_wf. apply WF_adjoint. apply WF_expU. apply H.  
apply WF_adjoint. apply WF_expU. apply H.  
apply WF_adjoint. apply WF_expU. apply H.  
auto_wf.   
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
rewrite Mmult_assoc. rewrite base_inner_1. unfold c_to_Vector1.
Msimpl. reflexivity.   assumption.
rewrite <-Mscale_mult_dist_r.
unfold adj_Uf. 
apply unitary_trans. unfold U_f. apply WF_Unitary_expU. assumption.   apply Hv_n. 
rewrite simpl_expU. f_equal. f_equal;
f_equal; unfold phi; rewrite Rdiv_unfold;
 rewrite (Rmult_comm _ (/ (2 * PI)));
 rewrite <-Rmult_assoc; rewrite Rinv_r;
 try rewrite Rmult_1_l; try reflexivity.
 apply Rmult_integral_contrapositive_currified. lra.
 apply PI_neq0.
 apply Rmult_integral_contrapositive_currified. lra.
 apply PI_neq0.
rewrite Mmult_1_l. reflexivity. auto_wf. 
intros.  
repeat rewrite kron_mixed_product. f_equal.
rewrite Mscale_mult_dist_r.
rewrite Mscale_kron_dist_l.
rewrite <-Mscale_kron_dist_r. f_equal.
rewrite <-Mscale_mult_dist_r.
rewrite Mmult_assoc. rewrite base_inner_0. unfold c_to_Vector1.
rewrite Mscale_0_l. rewrite Mmult_0_r.
rewrite kron_0_l. rewrite kron_0_l. reflexivity. intuition.
assumption. assumption.
Qed. 


Lemma simpl_H:
@U_v (n-0) (n+m+1-0) 0 n 0 (n + m + 1) (n ⨂ hadamard) (big_sum
 (fun i : nat =>  b_n i  .* ((/√ 2 ^ n) .* big_sum (fun z : nat => ∣ z ⟩_ (2^n)) (2 ^ n)) ⊗ v_n i
    ⊗ (√ (1 - c ^ 2 / phi' i ^ 2) .* ∣ 0 ⟩_ (2) .+ c / phi' i .* ∣ 1 ⟩_ (2))) (2 ^ m))
=(big_sum (fun i : nat =>  b_n i .* (∣ 0 ⟩_ (2^n)) ⊗ v_n i ⊗ (√ (1 - c ^ 2 / phi' i ^ 2) .* ∣ 0 ⟩_ (2)    .+ c / phi' i .* ∣ 1 ⟩_ (2)))  (2 ^ m))  .
Proof.  unfold U_v. rewrite <-Nat.add_assoc. type_sovle. 
 apply Logic.eq_trans with 
 (n ⨂ hadamard ⊗ I ( 2 ^ m) ⊗ I 2
 × big_sum
     (fun i : nat =>
      b_n i
      .* ((/√ 2 ^ n)
          .* big_sum (fun z : nat => ∣ z ⟩_ (2^n))
               (2 ^ n)) ⊗ v_n i
      ⊗ (√ (1 - c ^ 2 / phi' i ^ 2) .* Base_vec 2 0
         .+ c / phi' i .* Base_vec 2 1)) (2 ^ m)).
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
apply WF_scale. apply WF_base. apply pow_gt_0.
rewrite Mscale_mult_dist_r. f_equal. apply Had_N.
auto_wf. apply Hv_n.   auto_wf. 
Qed.

Lemma Qsys_to_Set_not_empty:forall s e, 
s<e-> ~ (NSet.Equal (Qsys_to_Set s e) (NSet.empty)).
Proof. intros.  unfold NSet.Equal. intro.
       eapply In_empty. apply H0. apply (In_Qsys e s s); lia.
Qed.



Lemma simpl_QMeas:((/
norm
  (@U_v (S O) (Nat.sub (Init.Nat.add (Init.Nat.add n m) (S O)) O) (n + m) (n + m + 1) 0 (n + m + 1)(Base_vec 2 1 × (Base_vec 2 1) †)
     (@big_sum (Matrix
        (Init.Nat.mul (Init.Nat.mul (Nat.pow (S (S O)) n) (Nat.pow (S (S O)) m)) 
           (S (S O))) (S O)) _ 
        (fun i : nat =>
        @kron (Init.Nat.mul (Nat.pow (S (S O)) n) (Nat.pow (S (S O)) m)) (S O) (S (S O)) (S O) (b_n i .* ∣ 0 ⟩_ (2^n) ⊗ v_n i)
          (√ (1 - c * (c * 1) / (phi' i * (phi' i * 1))) .* Base_vec 2 0 .+ c / phi' i .* Base_vec 2 1))
        (2 ^ m))))%R
.* @U_v (S O) (Nat.sub (Init.Nat.add (Init.Nat.add n m) (S O)) O) (n + m) (n + m + 1) 0 (n + m + 1) (Base_vec 2 1 × (Base_vec 2 1) †)
    (@big_sum
    (Matrix (Init.Nat.mul (Init.Nat.mul (Nat.pow (S (S O)) n) (Nat.pow (S (S O)) m))
          (S (S O))) (S O)) _
       (fun i : nat =>
       @kron (Init.Nat.mul (Nat.pow (S (S O)) n) (Nat.pow (S (S O)) m)) (S O) (S (S O)) (S O)
       (b_n i .* ∣ 0 ⟩_ (2^n) ⊗ v_n i)
         (√ (1 - c * (c * 1) / (phi' i * (phi' i * 1))) .* Base_vec 2 0 .+ c / phi' i .* Base_vec 2 1)) 
       (2 ^ m)))= ∣ 0 ⟩_ (2^n) ⊗ x ⊗ Base_vec 2 1 .
Proof. 
unfold U_v. type_sovle. pose Hmn. 
assert((2 ^ (n + m) * 2 ^ 1)= (2 ^ n * 2 ^ m * 2)). simpl. rewrite Nat.pow_add_r. reflexivity. 
destruct H.  assert(2 ^ (n + m) * 2 ^ 1 = 2 ^ (n + m + 1)). rewrite <-Nat.pow_add_r. reflexivity.
destruct H. rewrite Mmult_Msum_distr_l.
rewrite (big_sum_eq_bounded _  
((fun i : nat => (b_n i .* ∣ 0 ⟩_ (2^n) ⊗ v_n i ⊗ (c / phi' i .* Base_vec 2 1))) )). 
unfold phi'. unfold phi.
rewrite (big_sum_eq_bounded _ 
((fun i : nat => (((c * (2 * PI)  / ( 2 ^ n* t)))%R.* (∣ 0 ⟩_ (2^n) ⊗ ((b_n i/ lamda_n i ) .* v_n i) ⊗ ( Base_vec 2 1)))) )). 
assert((2 ^ (n + m) * 2 ^ 1)= (2 ^ n * 2 ^ m * 2)). simpl. rewrite Nat.pow_add_r. reflexivity.
destruct H. 
         
rewrite Mscale_Msum_distr_r.  rewrite norm_scale. 
assert(2^n*2^m=2^(n+m)). type_sovle'. destruct H.
assert(2=2^1). simpl. reflexivity. destruct H. 
rewrite <-kron_Msum_distr_r.  rewrite <-kron_Msum_distr_l. 

rewrite Cmod_R. rewrite Rabs_right.   repeat rewrite norm_kron.
repeat rewrite norm_base_1.  rewrite Rmult_1_r. rewrite Rmult_1_l. 
rewrite Rinv_mult_distr_depr.  rewrite Mscale_assoc. rewrite RtoC_mult. 
rewrite Rmult_assoc. rewrite Rmult_comm. rewrite Rmult_assoc.
rewrite Rinv_r. rewrite Rmult_1_r. 
rewrite <-Mscale_kron_dist_l.  rewrite <-Mscale_kron_dist_r.
f_equal. f_equal.
pose Hx. destruct a0. destruct H0.
 rewrite H0 in *. rewrite H1.
rewrite Rinv_1.
rewrite Mscale_1_l. reflexivity.    
apply Rgt_neq_0. apply Rdiv_lt_0_compat.
apply Rmult_gt_0_compat.  apply Hc.
apply Rmult_gt_0_compat. lra. apply PI_RGT_0.
apply Rmult_gt_0_compat. apply pow_lt. lra.
apply Ht'.   
apply Rgt_neq_0. apply Rdiv_lt_0_compat.
apply Rmult_gt_0_compat.  apply Hc.
apply Rmult_gt_0_compat. lra. apply PI_RGT_0.
apply Rmult_gt_0_compat. apply pow_lt. lra.
apply Ht'.   
pose Hx. destruct a0. destruct H0.
 rewrite H0 in *. rewrite H1. lra.  

simpl. lia. apply pow_gt_0.
assert ((c * (2 * PI) / (2 ^ n * t) > 0)%R).
apply Rdiv_lt_0_compat.
apply Rmult_gt_0_compat. apply Hc.
apply Rmult_gt_0_compat. lra. apply PI_RGT_0.
apply Rmult_gt_0_compat. apply pow_lt. lra.
apply Ht'. lra.    


intros. repeat rewrite Mscale_kron_dist_r.  repeat rewrite Mscale_kron_dist_l.
repeat rewrite Mscale_assoc. f_equal.   repeat rewrite Rdiv_unfold.

 repeat rewrite Cdiv_unfold.
 repeat rewrite <-RtoC_inv; try apply Hlamda; 
  repeat rewrite Rinv_mult_distr_depr; 
  try lra; try apply Hlamda; try apply Rinv_neq_0_compat; try apply PI_neq0;
   try apply Rmult_integral_contrapositive; try split;
   try apply Rinv_neq_0_compat;
   try apply Hlamda; try apply PI_neq0;
   try apply Rmult_integral_contrapositive; try split;
   try apply Rinv_neq_0_compat;
   try apply Hlamda; try apply PI_neq0; try lra;
   try apply Rmult_integral_contrapositive; try split;
   try apply Rinv_neq_0_compat;
   try apply Hlamda; try apply PI_neq0; try lra; 
   try apply pow_nonzero; try lra ; try apply Rgt_neq_0; try apply Ht'.
  rewrite Rinv_inv. rewrite Rinv_inv.
  repeat rewrite <-RtoC_mult.  
  repeat rewrite <-Cmult_assoc. 
f_equal. rewrite Cmult_comm.  repeat rewrite Cmult_assoc.
f_equal. f_equal.   
repeat rewrite <-Cmult_assoc. 
rewrite Cmult_comm. 
repeat rewrite Cmult_assoc. reflexivity. 


intros.
remember ((√ (1 - c * (c * 1) / (phi' x0 * (phi' x0 * 1))) .* Base_vec 2 0 .+ c / phi' x0 .* Base_vec 2 1)).
assert(2^n*2^m=2^(n+m)). type_sovle'. destruct H0. rewrite <-id_kron.
assert(2=2^1). simpl. reflexivity. destruct H0. 
apply eq_trans with (I (2 ^ n) ⊗ I (2 ^ m) ⊗ (Base_vec 2 1 × (Base_vec 2 1) †) × (b_n x0 .* ∣ 0 ⟩_ (2^n) ⊗ v_n x0 ⊗ m0)).
f_equal. repeat  rewrite kron_mixed_product. rewrite Heqm0. Msimpl.
f_equal. f_equal.  rewrite Mmult_plus_distr_l;
repeat rewrite Mscale_mult_dist_r.  repeat rewrite Mmult_assoc. 
repeat rewrite <-base_qubit0. rewrite<- base_qubit1.
assert((Base_vec 2 1) † × Base_vec 2 0=(Base_vec (2^1) 1) † × (Base_vec (2^1) 0)). reflexivity. rewrite H0.
assert((Base_vec 2 1) † × Base_vec 2 1=(Base_vec (2^1) 1) † × (Base_vec (2^1) 1)). reflexivity. rewrite H1.
rewrite base_inner_1. rewrite base_inner_0. unfold c_to_Vector1. Msimpl.  reflexivity.
lia. simpl. lia. simpl. lia. simpl. lia. apply Hv_n. assert(0<2^n). apply pow_gt_0.
auto_wf. 
Qed.

Lemma Qsys_union: forall (s x e:nat), 
s< x < e->
NSet.Equal ((NSet.union (Qsys_to_Set s x) (Qsys_to_Set x e))) 
((Qsys_to_Set s e)).
Proof. unfold NSet.Equal. intros. split; intros. 
        apply NSet.union_1 in H0. destruct H0;
        apply In_Qsys in H0; try lia;
        apply In_Qsys; try lia.
        assert(a<x0\/ ~(a<x0)). apply Classical_Prop.classic.
        destruct H1.
        apply NSet.union_2.
        apply In_Qsys in H0; try lia;
        apply In_Qsys; try lia.
        apply NSet.union_3.
        apply In_Qsys in H0; try lia;
        apply In_Qsys; try lia.
Qed.



Theorem correctness_HHL: {{BTrue}} HHL {{QExp_s n (n+m) x}}. 
Proof. 
    unfold HHL.  pose Hmn. assert( n<(n+m)). lia. 
    pose (Qsys_to_Set_min_max 0 n ). destruct a0. lia. 
    pose (Qsys_to_Set_min_max n (n+m) H). destruct a0.
    pose (Qsys_to_Set_min_max (n+m) (n+m+1) ). destruct a0. lia.

      eapply rule_seq.
    {eapply rule_conseq_l'. eapply (rule_SAssgn (BEq v ' ( 0))). apply Assn_true_F. simpl. unfold not.  apply (In_empty v). } 
      eapply rule_conseq. 
    {eapply (rule_while BTrue (QExp_s 0 (n+m+1) ((Base_vec (2^n) 0) ⊗ (x) ⊗ (Base_vec 2 1)))).
        eapply rule_seq.
      {eapply rule_conseq_l. apply rule_PT. eapply rule_QInit. }  
        eapply rule_seq.
      {eapply rule_conseq_l. apply rule_OdotE.
       apply rule_qframe'; [ | split; try eapply rule_QInit].
      unfold Considered_F_c.
      simpl. rewrite H2. rewrite H3. 
      rewrite Nat.sub_add; try lia.  
      split. try reflexivity. split;  try lia. rewrite <-empty_Empty.
      intuition. 
        
       simpl. rewrite Qsys_inter_empty'; try lia. 
       split. apply inter_empty. left. reflexivity. left. lia.   
       } 
        eapply rule_seq.
      {eapply rule_conseq_l.  apply rule_OdotE. 
      apply rule_qframe'; [ | split; try eapply rule_QInit].
      unfold Considered_F_c. simpl. 
      rewrite H4. rewrite H5. rewrite Nat.sub_add; try lia. 
      split; try reflexivity. split. lia.
       rewrite <-empty_Empty. intuition. 
       simpl.  split. apply inter_empty. right. reflexivity.
       rewrite Qsys_union; try lia.   rewrite Qsys_inter_empty'; try lia. 
       }
        eapply rule_seq.
      {eapply rule_conseq_l. apply rule_OdotA.
       eapply rule_qframe'; 
       [ | split; [eapply rule_qframe; [| split; try eapply rule_QUnit_One' ] | ] ].
       unfold Considered_F_c. simpl.  rewrite H2. rewrite H3.
       rewrite Nat.sub_add; try lia. split; try reflexivity. split; try  lia.
       rewrite Qsys_union; try lia.  rewrite Qsys_inter_empty'; try lia. 
       unfold Considered_F_c. simpl.  rewrite H2. rewrite H3.
       rewrite Nat.sub_add; try lia. split; try reflexivity. split; try  lia.
        rewrite Qsys_inter_empty'; try lia. lia.  
       simpl.  split. apply inter_empty. left. reflexivity.
       rewrite Qsys_inter_empty'; try lia.  simpl. 
       split. apply inter_empty. left. reflexivity.
       rewrite Qsys_inter_empty'; try lia.   }
        assert(m=n+m-n). lia. destruct H6.  rewrite U_vb. 
        eapply rule_seq.
      {eapply rule_qframe;[|split; try eapply rule_QUnit_One'].
       unfold Considered_F_c.   
       simpl.   rewrite H0. rewrite H1.
       rewrite Nat.sub_add; try lia. split; try reflexivity. split; try  lia.
         rewrite Qsys_inter_empty'; try lia. lia.   
       simpl.  split. apply inter_empty. left. apply union_empty.
       split; reflexivity. 
       rewrite Qsys_union; try lia.  rewrite Qsys_inter_empty'; try lia. 
       } 
        assert(n=n-0). lia. destruct H6. rewrite Had_N'. 
        eapply rule_seq.
      {eapply rule_conseq_l. apply rule_OdotA.
       eapply rule_qframe;
       [ |split; [eapply rule_conseq_l; [apply rule_odotT | eapply rule_conseq_l;
       [apply rule_Separ | assert(m=n+m-n); try lia; destruct H6;
       assert(n=n-0); try lia; destruct H6;
       rewrite simpl_HB; apply rule_QUnit_Ctrl ] ] | ] ].
       unfold Considered_F_c.  simpl.
       split. destruct a.   
       pose (Qsys_to_Set_not_empty 0 n H6). 
       pose (Qsys_to_Set_not_empty n (n+m) H).
       pose (max_union (Qsys_to_Set 0 n)
       (Qsys_to_Set n (n + m))). destruct a. destruct H9.
       rewrite H10; try assumption. 
       pose (min_union (Qsys_to_Set 0 n)
       (Qsys_to_Set n (n + m))). destruct a. destruct H12.
       rewrite H13; try assumption.
       rewrite H0.  rewrite H1.  rewrite H2. rewrite H3. 
        rewrite max_r; try lia.  
        rewrite (Nat.sub_add  1 (n+m)); try lia. simpl.
        rewrite Qsys_union; try lia. reflexivity. 
      split. lia.  rewrite Qsys_union; try lia.
      rewrite Qsys_inter_empty'; try lia.   lia.     
      simpl. split. apply inter_empty. left. reflexivity. 
      rewrite Qsys_union; try lia. rewrite Qsys_inter_empty'; try lia.   } 
       rewrite simpl_Uf. eapply rule_seq.
      {apply rule_qframe;[|split; try eapply rule_QUnit_One'].
      unfold Considered_F_c. simpl.
      rewrite H0. rewrite H1. rewrite Nat.sub_add; try lia.
      rewrite Qsys_inter_empty'; try lia. split; try reflexivity; try lia.   
       lia. simpl.  
      split. apply inter_empty. left. reflexivity. 
      rewrite Qsys_inter_empty'; try lia.  } 
       assert(n=n-0). lia. destruct H6. assert(n+m=n+m-0). lia.
      destruct H6. rewrite simpl_QFT'. eapply rule_seq.
      {eapply rule_conseq_l. apply rule_odotT. 
      eapply rule_conseq_l. apply rule_Separ. eapply rule_QUnit_Ctrl. lia. }
      assert(1=n+m+1-(n+m)). lia. destruct H6.
      assert(n+m=n+m-0). lia. destruct H6.
      assert(2 ^ n * 2 ^ m= 2^(n+m)). type_sovle'. destruct H6.
      rewrite kron_Msum_distr_r.
      eapply rule_conseq_l with (P':=| UCtrl_v 0 n (n + m) (n + m + 1) 0 (n + m + 1) U_c
      (big_sum (fun i : nat => b_n i .* ∣ delt_n i ⟩_ (2^n) ⊗ v_n i ⊗ ∣ 0 ⟩_ (2))
        (2 ^ m)) >[ 0, n + m + 1]).
      apply implies_refl. rewrite simpl_Uc. eapply rule_seq.
     {apply rule_QUnit_One'. lia. }  rewrite simpl_QFT. eapply rule_seq.
     {eapply rule_QUnit_Ctrl. lia. }  rewrite simpl_Uf'. eapply rule_seq.
     {apply rule_QUnit_One'. lia. } rewrite simpl_H.
     {eapply rule_conseq. eapply rule_QMeas with (s:=0) (e:=n+m+1)(P:=P).  lia. 
       rewrite add_sub_eq. unfold P. simpl. 
      apply rule_Conj_two. apply implies_refl.
      implies_trans_solve 0 rule_PT.  
      apply rule_Conj_two; try apply rule_Conj_two;try apply rule_PT; try apply Assn_true_P;
       unfold not; simpl;  apply In_empty.
      rewrite add_sub_eq. unfold P. simpl. 
      eapply implies_trans.  
      eapply  rule_Oplus. simpl.
      eapply rule_OCon'. simpl. econstructor.
      implies_trans_solve 0 rule_ConjC.
        eapply rule_CconjCon. apply rule_PT. apply implies_refl.
       econstructor.  implies_trans_solve 0 rule_ConjC.
        eapply rule_CconjCon.     rewrite simpl_QMeas.
    apply implies_refl.
        classic_slove_aux. econstructor. } }
  { implies_trans_solve 0 rule_OdotE.
    implies_trans_solve  0 rule_OdotO.
    implies_trans_solve  0 SAnd_PAnd_eq.
    implies_trans_solve 0 rule_ConjC.



unfold assert_implies. intros.
rewrite sat_Assert_to_State in *.
econstructor. 
assert(Datatypes.length [1%R;0%R] =
Datatypes.length
[<{ true }> /\s <{ (v) ' = 0 }>;
   (| ∣ 0 ⟩_ (2^n) ⊗ x ⊗ Base_vec 2 1 >[ 0, n + m + 1]) /\s
   <{ ~ (v) ' = 0 }>] ). reflexivity.
apply H7. simpl. 
remember ((SQuan (QExp_s 0 ((n+m)+1) (@kron (2^n*2^m) 1 2 1 (@kron (2^n) (S O) (2^m) (S O) (∣ 0 ⟩_ (2^n)) x) (Base_vec 2 1))))).
assert([(1%R, <{ true }> /\s <{ (v) ' = 0 }>);
(0%R, s0 /\s <{ ~ (v) ' = 0 }>)]=
swap_list [(0%R, s0 /\s <{ ~ (v) ' = 0 }>); (1%R, <{ true }> /\s <{ (v) ' = 0 }>)] 0 ).
reflexivity. rewrite H7. apply rule_POplusC. apply sat_Pro_State'.
rewrite sat_Assert_to_State. assumption. }
  { implies_trans_solve 0 rule_Conj_split_l.    
     assert(1=(1 * 1)). lia. destruct H6.
    assert(2^(n+m-0)=2 ^ n * 2 ^ m). type_sovle'. destruct H6. 
    assert(2^(n+m+1-(n+m))=2). assert(2^1=2). simpl. reflexivity.
    rewrite<- H6. rewrite H6 at 1. f_equal. lia. destruct H6.
    implies_trans_solve 0 rule_Separ'. lia. apply Pure_State_Vector_base. type_sovle. simpl. lia. 
    type_sovle.
    assert(2 ^ n * 2 ^ m=2^(n+m)). type_sovle'. destruct H6. 
    apply pure_state_vector_kron. apply Pure_State_Vector_base. apply pow_gt_0.
     apply norm_1_pure_vec; try apply Hx.
   

     implies_trans_solve 0 rule_odotT.
     implies_trans_solve 0 rule_OdotO'.  
      implies_trans_solve 0 rule_Conj_split_l. 
      assert(2^(n-0)=(2 ^ (n + m + 1 - (n + m))) ^ n).
    rewrite Nat.sub_0_r. f_equal.
    symmetry. assert(2^1=2). simpl. reflexivity.
    rewrite<- H6. rewrite H6 at 1.
    f_equal. apply add_sub_eq. destruct H6.
    assert(2^(n+m-n)=(2 ^ (n + m + 1 - (n + m))) ^ m). 
    repeat rewrite add_sub_eq. simpl. reflexivity. destruct H6.
    implies_trans_solve 0  rule_Separ'. lia. 
    rewrite add_sub_eq.  apply norm_1_pure_vec; try apply Hx.
   apply Pure_State_Vector_base. apply pow_gt_0.
    implies_trans_solve 0 rule_odotT. 
    implies_trans_solve 0 rule_OdotO'. 
    implies_trans_solve 0 rule_ConjC.   
    eapply rule_Conj_split_l.  }
Qed.
    
End HHL. 

