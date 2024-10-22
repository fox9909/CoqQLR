Require Import Lists.List.
Require Import Reals.
Require Import Coquelicot.Complex.
Require Import Strings.String.


From Quan Require Import Matrix.
From Quan Require Import Quantum.
From Quan Require Import ParDensityO.
From Quan Require Import QState_L.
From Quan Require Import Par_trace.
From Quan Require Import QIMP_L.
From Quan Require Import QAssert_L.
From Quan Require Import QRule_E_L.
From Quan Require Import QRule_Q_L.
From Quan Require Import QRule_I_L.
From Quan Require Import QSepar.
From Quan Require Import QRule_QFrame.
From Quan Require Import add.


Local Open Scope com_scope.
Local Open Scope assert_scope.
Local Open Scope nat_scope.
Local Open Scope matrix_scope.
Local Open Scope rule_scope.

Lemma pow_0: (2^0=1)%nat. Proof. auto. Qed.
Lemma add_sub_eq: forall n m, n+m-n=m .
Proof. intuition.     
Qed.

From Quan Require Import Forall_two.
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
(forall j:nat, (j<>0)%nat ->(U_c j ) × (Vec 2 0) = 
(((sqrt (1-(( c^2)/( (j)^2)))) .* (Vec 2 0) .+ (c/((j)) .* Vec 2 1)))).
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
      apply H.  destruct j. lra.  admit. admit.
       admit.
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
      split. rewrite Mmult_assoc. rewrite Vec_inner_1.
      rewrite Mmult_1_r.  rewrite Mscale_kron_dist_r.
      rewrite Mscale_kron_dist_l.
      reflexivity.  auto_wf. assumption.
      intros. rewrite Mmult_assoc. rewrite Vec_inner_0; try assumption.
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
rewrite Mmult_assoc. rewrite Vec_inner_1.
rewrite Mmult_1_r. f_equal.  
pose HU_c. destruct a.  destruct H2. 
rewrite H3. assert((lamda x0 * t / (2 * PI) * 2 ^ n)%R = delt x0).
apply H. 
rewrite<-H4. unfold phi'. unfold phi. reflexivity.
admit.
admit. apply H. apply Hmu_j. intros.
repeat rewrite Mscale_kron_dist_l.
rewrite Mscale_mult_dist_r. 
repeat rewrite kron_mixed_product.
rewrite Mmult_assoc.  rewrite Vec_inner_0.
rewrite Mscale_0_l. rewrite Mmult_0_r.
repeat rewrite kron_0_l. rewrite Mscale_0_r. reflexivity.
intuition.
Admitted.




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
f_equal.  simpl. admit. admit. type_sovle'. f_equal; type_sovle'; try lia.
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
rewrite Mmult_assoc. rewrite Vec_inner_1.
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
rewrite Mmult_assoc. rewrite Vec_inner_0.
rewrite Mscale_0_l. rewrite Mmult_0_r.
rewrite kron_0_l. rewrite kron_0_l. reflexivity. intuition.
Admitted. 

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
      simpl. admit. 
       split. eapply rule_QInit. simpl.
       split. apply inter_empty. left. reflexivity. admit.
      *eapply rule_seq. eapply rule_conseq_l.  apply rule_OdotE.
       apply rule_qframe'. 
        admit. 
       split. eapply rule_QInit. simpl.
       split. apply inter_empty. left. apply union_empty.
       split; reflexivity.  admit.
       *eapply rule_seq. eapply rule_conseq_l. apply rule_OdotA.
       eapply rule_qframe'.
       admit.

        split.  eapply rule_qframe. simpl. lia. 
       split. eapply rule_QUnit_One'. lia. 
       simpl. 
       split. apply inter_empty. left. reflexivity.  admit.
       simpl. 
       split. apply inter_empty. left. reflexivity.  admit.
        assert(m=n+m-n). lia. destruct H.  rewrite U_vb. 
      *eapply rule_seq. eapply rule_qframe. admit. 
      split. eapply rule_QUnit_One'.
       lia. 
       simpl. 
       split. apply inter_empty. left. apply union_empty.
       split; reflexivity.  admit.  assert(n=n-0). lia. destruct H. 
       rewrite Had_N'. 
       *eapply rule_seq. eapply rule_conseq_l. apply rule_OdotA. eapply rule_qframe.
       admit.
       split. eapply rule_conseq_l. apply rule_odotT. eapply rule_conseq_l.
       apply rule_Separ.
       assert(m=n+m-n). lia. destruct H.
       assert(n=n-0). lia. destruct H.
       rewrite simpl_HB. apply rule_QUnit_Ctrl'. lia.
        admit. 
       rewrite simpl_Uf.
      *eapply rule_seq. apply rule_qframe.
      admit.
      split. apply rule_QUnit_One'. lia. admit.
       assert(n=n-0). lia. destruct H.
      assert(n+m=n+m-0). lia. destruct H. rewrite simpl_QFT'. 
      *eapply rule_seq. eapply rule_conseq_l. apply rule_odotT. 
      eapply rule_conseq_l. apply rule_Separ. eapply rule_QUnit_Ctrl'. lia.
      assert(1=n+m+1-(n+m)). lia. destruct H.
      assert(n+m=n+m-0). lia. destruct H.
      assert(2 ^ n * 2 ^ m= 2^(n+m)). type_sovle'. destruct H.
      rewrite kron_Msum_distr_r.
      eapply rule_conseq_l with (P':=| UCtrl_v 0 n (n + m) (n + m + 1) 0 (n + m + 1) U_c
      (big_sum (fun i : nat => b_j i .* ∣ delt i ⟩_ (n) ⊗ mu_j i ⊗ ∣ 0 ⟩_ (1))
        (2 ^ m)) >[ 0, n + m + 1]).
      apply implies_refl.
      rewrite simpl_Uc.
      *eapply rule_seq. apply rule_QUnit_One'. lia. 
      rewrite simpl_QFT.
      *eapply rule_seq. eapply rule_QUnit_Ctrl'. lia. 
      rewrite simpl_Uf'.
      *eapply rule_seq. apply rule_QUnit_One'. lia. 
      rewrite simpl_H.
      * eapply rule_conseq.
      eapply rule_QMeas with (s:=0) (e:=n+m+1)(P:=P)
      (v:=(big_sum
      (fun i : nat =>b_j i .* (Vec (2^n) 0) ⊗ mu_j i
      ⊗ (√ (1 - c ^ 2 / phi' i ^ 2) .* Vec 2 0
        .+ c / phi' i .* Vec 2 1)) 
      (2 ^ m))).
      lia. apply big_pOplus'_to_pOplus. 
       admit.  rewrite add_sub_eq. unfold P. simpl. admit. 
      rewrite add_sub_eq. unfold P. simpl. 
      eapply implies_trans.  
      eapply  rule_Oplus. simpl.
      eapply rule_OCon'. simpl. econstructor.
      eapply implies_trans.  apply rule_AndC.
        eapply rule_AndCon. apply rule_PT. apply implies_refl.
       econstructor. 
        eapply implies_trans. apply rule_AndC.
        eapply rule_AndCon. admit. admit. econstructor.
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
        eapply rule_Separ'. lia. 
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
      eapply rule_Separ'. lia. 
      eapply  implies_trans. 
      apply rule_odotT.  
      eapply  implies_trans. 
      eapply rule_OdotO'. 
      eapply  implies_trans. 
      apply rule_AndC.  
      eapply rule_AndE. 
      Admitted.
    
End HHL. 

