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




Module HHL.

Local Open Scope com_scope.
Local Open Scope assert_scope.
Local Open Scope nat_scope.
Local Open Scope matrix_scope.
Local Open Scope rule_scope.

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



 Theorem rule_QUnit_One' : forall s' e' s e (U: Square (2^(e'-s'))) (v: Vector (2^(e-s))),
s<=s' /\ e' <=e ->WF_Matrix v->
{{ QExp_s s  e  v }} QUnit_One s' e' U {{ QExp_s s  e  (U_v s' e' s e U v) }}.
Proof. Admitted.

Definition UCtrl_v (s0 e0 s1 e1 s e: nat) (U: Square (2^(e1-s1))) (v: Vector (2^(e-s))) :=
  (big_sum (fun i:nat =>
       (I (2^(s0-s)) ⊗ (∣ i ⟩_ (e0-s0) × ⟨ i ∣_ (e0-s0) ) ⊗ (I (2^(e-e0)))) ×
       (I (2^(s1-s)) ⊗ (exp_U U i) ⊗ (I (2^(e-e1))))) (2^(e0 -s0))) × v.

Theorem rule_QUnit_Ctrl' : forall s0 e0 s1 e1 s e (U: Square (2^(e1-s1))) (v: Vector (2^(e-s))),
s<=s0 /\ e1 <=e ->WF_Matrix v->
{{ QExp_s s  e  v }} QUnit_Ctrl s0 e0 s1 e1 U {{ QExp_s s  e  ( UCtrl_v s0 e0 s1 e1 s e U v) }}.
Proof. Admitted.

Coercion INR : nat >-> R.
Local Open Scope R_scope.

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
Parameter U_f:Matrix (2^m) (2^m).
Parameter QFT: Matrix (2^n) (2^n).
Parameter U_c: (Matrix (2^n * 2^ 1)) ( (2^n * 2^ 1)).
Parameter t:R. 
Hypothesis Hmn:(m<=n)%nat.
Hypothesis HAx: A × x =b.
Hypothesis Hmu_j:forall j, norm (mu_j j)=1.

Hypothesis Hb_j:forall j, norm (mu_j j)=1.
Hypothesis Hb: norm b =1.
Hypothesis HB_decom: big_sum (fun j=>(b_j j) .* (mu_j j)) (2^m)= b.
Hypothesis HA_decom: big_sum (fun j=>(lamda j) .* (mu_j j)) (2^m)= b.
Hypothesis HU_b: WF_Unitary U_b /\ ( U_b × (Vec (2^m) 0) = b).

Definition  phi (j:nat) := (lamda j * t)/ (2 * PI).
Definition  phi' (j:nat) := ((phi j) * (2^n))%R.

Hypothesis HU_c: WF_Unitary U_c /\ (U_c × (Vec (2^n) 0 ⊗ Vec 2 0)) = (Vec (2^n) 0 ⊗ Vec 2 0) /\
                          (forall j:nat, U_c × (Vec (2^n) j ⊗ Vec 2 1) = (Vec (2^n) j ⊗ ((sqrt (1-(( c^2)/( (phi' j)^2)))) .* (Vec 2 0) .+ (c/((phi' j)) .* Vec 2 1)))).
Hypothesis HU_f: forall j:nat, U_f × ( (mu_j j))= (cos ((lamda j) * t), sin ( (lamda j) * t)) .* ( (mu_j j)).
Hypothesis HQFT: forall k:nat, QFT × (Vec (2 ^ n) k) =
1 / √ 2 ^ n .* (big_sum (fun j : nat => (cos (((2 * PI)/(2^n)) * j * k),  sin (((2 * PI)/(2^n)) * j * k)) .*  Vec (2 ^ n) j) (2 ^ n)).

                     
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
       QUnit_Ctrl 0 n n (n+m) (adjoint U_f);
       QUnit_One 0 n (kron_n n hadamard);
       QMeas v (n+m) (n+m+1)
       end }>.

Lemma Had_N: 
n ⨂ hadamard × ∣ 0 ⟩_ (n) = (1/(2^n))%nat .* big_sum (fun z=> ∣ z ⟩_ (n)) (2^n).
Proof. Admitted.

Lemma Had_N':
U_v 0 n 0 n (n ⨂ hadamard) ∣ 0 ⟩_ n= (1/(2^n))%nat .* big_sum (fun z=> ∣ z ⟩_ (n)) (2^n).
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

Lemma U_f': forall (v:Vector (2^n *(2^m))), (UCtrl_v 0 n n (n + m) 0 (n + m) U_f v) =
Mmult (big_sum
(fun i : nat =>
 (∣ i ⟩_ (n) × ⟨ i ∣_ (n)) ⊗ (exp_U U_f i)) 
(2 ^ n)) v.
Proof.  intros. unfold UCtrl_v.
repeat rewrite add_sub_eq. repeat rewrite Nat.sub_0_r.
repeat rewrite Nat.sub_diag. repeat rewrite pow_0.
f_equal; type_sovle'; try lia. 
apply big_sum_eq_bounded. intros. 
repeat rewrite kron_1_l. rewrite kron_1_r.
apply Logic.eq_trans with (∣ x0 ⟩_ (n) × ⟨ x0 ∣_ (n) ⊗ I (2 ^ m)
× (I (2 ^ n) ⊗ exp_U U_f x0)).
f_equal; type_sovle'; try lia. 
rewrite kron_mixed_product. rewrite Mmult_1_r.
rewrite Mmult_1_l. reflexivity. Admitted  .

Definition  P (i:nat): Pure_formula := (BEq v i) .

Lemma simpl_HB: (1 / 2 ^ n)%nat .* big_sum (fun z : nat => ∣ z ⟩_ (n)) (2 ^ n)
⊗ big_sum (fun j : nat => b_j j .* mu_j j) (2 ^ m)=
big_sum (fun j : nat => b_j j .* ((1 / 2 ^ n)%nat .* big_sum (fun z : nat => ∣ z ⟩_ (n) ⊗ mu_j j ) (2 ^ n)
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
Proof. induction i. induction j. intuition. Admitted.


Lemma simpl_expU:forall i j,
exp_U U_f i × mu_j j = (cos ((lamda j)* t *i), sin (((lamda j)* t * i))) .* mu_j j.
Proof. intros.  induction i. simpl. rewrite Mmult_1_l.
    rewrite Rmult_0_r. rewrite cos_0. rewrite sin_0.
rewrite Mscale_1_l. reflexivity.
admit. simpl exp_U. rewrite Mmult_assoc. rewrite IHi.
rewrite Mscale_mult_dist_r. rewrite HU_f.
rewrite Mscale_assoc. f_equal.
Search ((cos i, sin i) * (cos i, sin i)).
Admitted.


Lemma simpl_Uf:
UCtrl_v 0 n n (n + m) 0 (n + m) U_f
(big_sum
   (fun j : nat =>
    b_j j
    .* ((1 / 2 ^ n)%nat
        .* big_sum (fun z : nat => ∣ z ⟩_ (n) ⊗ mu_j j)
             (2 ^ n))) 
   (2 ^ m))= (big_sum
   (fun j : nat =>
    b_j j
    .* ((1 / 2 ^ n)%nat
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


Lemma simpl_QFT:
@U_v n (n+m) 0 n 0 (n + m) (QFT) †
       (big_sum
          (fun j : nat =>
           b_j j
           .* ((1 / 2 ^ n)%nat
               .* big_sum
                    (fun z : nat =>
                     (cos (2 * PI * phi j * z),
                      sin (2 * PI * phi j * z))
                     .* ∣ z ⟩_ (n)) (2 ^ n)) ⊗ 
           mu_j j) (2 ^ m))=
       (big_sum
          (fun j : nat =>
           b_j j
           .* (Vec (2^n) j) ⊗ 
           mu_j j) (2 ^ m)).
Proof. unfold U_v. 
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
Admitted.

Lemma simpl_Uc:
UCtrl_v 0 n (n + m) (n + m + 1) 0 
      (n + m + 1) U_c
      (big_sum
         (fun i : nat =>
          b_j i .* ∣ i ⟩_ (n) ⊗ mu_j i ⊗ ∣ 0 ⟩_ (1))
         (2 ^ m))=
         (big_sum
         (fun i : nat =>
          b_j i .* ∣ i ⟩_ (n) ⊗ mu_j i ⊗ ((sqrt (1-(( c^2)/( (phi' i)^2)))) .* (Vec 2 0) .+ (c/((phi' i)) .* Vec 2 1)))
         (2 ^ m)).
Proof. unfold UCtrl_v. repeat rewrite add_sub_eq. repeat rewrite Nat.sub_0_r.
repeat rewrite Nat.sub_diag. repeat rewrite pow_0.
assert(m+1=n + m + 1 - n). lia. destruct H.
assert(2^n * 2^m * 2^1=2^(n+m+1)). type_sovle'. destruct H.
rewrite Mmult_Msum_distr_l. apply big_sum_eq_bounded.
Admitted.

Lemma implies_trans: forall (D D1 D2:Assertion), 
(D->> D1)
/\ (D1->>D2) 
->(D->>D2).
Proof. Admitted.

Theorem correctness_HHL: 
{{BTrue}}
HHL
{{QExp_s n m x}}.
Proof. unfold HHL. 
       eapply rule_seq.
      *eapply rule_conseq_l'. 
       eapply (rule_assgn (BEq v 0)).
       admit.
      *eapply rule_conseq.
       eapply (rule_while BTrue (QExp_s 0 (n+m+1) ((Vec (2^n) 0) ⊗ (x) ⊗ (Vec 2 1)))).
      *eapply rule_seq.
       eapply rule_conseq_l.
       apply rule_PT.
       eapply rule_QInit.  
      *eapply rule_seq.
       eapply rule_conseq_l.
       apply rule_OdotE.
       apply rule_qframe'.
       split. eapply rule_QInit. admit.
      *eapply rule_seq.
       eapply rule_conseq_l.
       apply rule_OdotE.
       apply rule_qframe'.
       split. eapply rule_QInit. admit.
       *eapply rule_seq.
       eapply rule_conseq_l.
       apply rule_OdotA.
       eapply rule_qframe'.
       split.  eapply rule_qframe.
       split. eapply rule_QUnit_One'. lia. apply WF_vec. apply pow_gt_0. admit.
       admit.  assert(m=n+m-n). lia. destruct H.
       rewrite U_vb. 
      *eapply rule_seq.
       eapply rule_qframe. 
       split. eapply rule_QUnit_One'. lia. apply WF_vec. apply pow_gt_0. admit.
       assert(n=n-0). lia. destruct H. 
       rewrite Had_N'. 
       *eapply rule_seq.
       eapply rule_conseq_l.
       apply rule_OdotA.
       eapply rule_qframe.
       split. eapply rule_conseq_l.
       apply rule_odotT. 
       eapply rule_conseq_l.
       apply rule_Separ.
       assert(m=n+m-n). lia. destruct H.
       assert(n=n-0). lia. destruct H.
       rewrite simpl_HB. 
       apply rule_QUnit_Ctrl'. lia. admit. admit.
       rewrite simpl_Uf.
*eapply rule_seq.
apply rule_qframe.
split. apply rule_QUnit_One'. lia. admit.
admit. assert(n=n-0). lia. destruct H.
assert(n+m=n+m-0). lia. destruct H.
 rewrite simpl_QFT. 
*eapply rule_seq. 
eapply rule_conseq_l.
apply rule_odotT. 
eapply rule_conseq_l.
apply rule_Separ.
eapply rule_QUnit_Ctrl'. lia.  admit.
assert(1=n+m+1-(n+m)). lia. destruct H.
assert(n+m=n+m-0). lia. destruct H.
assert(2 ^ n * 2 ^ m= 2^(n+m)). type_sovle'. destruct H.
rewrite kron_Msum_distr_r.
*eapply rule_seq.
apply rule_QUnit_One'. lia. admit.
*eapply rule_seq. 
eapply rule_QUnit_Ctrl'. lia.  admit.
*eapply rule_seq. 
apply rule_QUnit_One'. lia. admit.
*
eapply rule_conseq.
eapply rule_QMeas with (s:=0) (e:=n+m+1)(P:=P) (v:=((big_sum (fun j:nat=> ∣ 0 ⟩_ (n) ⊗ (Vec (2^m) j) ⊗ (((sqrt (1-(( c^2)/( (phi' j)^2)))) .* (Vec 2 0) .+ (c/((phi' j)) .* Vec 2 1)))) 2))).
lia. admit. admit. admit. simpl. 
rewrite add_sub_eq.  assert(2^1=2). auto. rewrite H.
simpl.
eapply implies_trans. split.
apply rule_Oplus. simpl.

       rewrite U_f'.
      
       assert(m=n+m-n). lia. destruct H.
       rewrite U_vb.
       rewrite Mscale_kron_dist_l. 
       rewrite kron_Msum_distr_l. 
       assert(big_sum
       (fun i : nat => big_sum (fun z : nat => ∣ z ⟩_ (n))
       (2 ^ n) ⊗ (b_j i .* mu_j i))
       (2 ^ m)= (big_sum
       (fun i : nat => b_j i .*
        ((big_sum (fun z : nat => ∣ z ⟩_ (n) ⊗ ( mu_j i) )
          (2 ^ n)))) 
       (2 ^ m))). apply big_sum_eq_bounded. intros.  
       rewrite Mscale_kron_dist_r. rewrite kron_Msum_distr_r. reflexivity.
       rewrite H. rewrite Mscale_mult_dist_r.
       rewrite Mmult_Msum_distr_l.
       assert(big_sum
       (fun i : nat =>
        big_sum
          (fun i0 : nat =>
           ∣ i0 ⟩_ (n) × ⟨ i0 ∣_ (n) ⊗ exp_U U_f i0)
          (2 ^ n)
        × (b_j i
           .* big_sum
                (fun z : nat => ∣ z ⟩_ (n) ⊗ mu_j i)
                (2 ^ n))) (2 ^ m)= 
       big_sum
          (fun i : nat =>
          (b_j i
          .* ( (big_sum
                (fun z : nat => ∣ z ⟩_ (n) ⊗ ((exp_U U_f i) × (mu_j i)))
                (2 ^ n))))) 
          (2 ^ m)). 
          apply big_sum_eq_bounded. intros.
          admit. rewrite H0.
       
       *eapply rule_seq.
       apply rule_qframe.
       split. apply rule_QUnit_One'. lia. admit.
       admit. 
       *eapply rule_seq.
       eapply rule_conseq_l.
       apply rule_odotT. 
       eapply rule_conseq_l.
       apply rule_Separ. 
       eapply rule_QUnit_Ctrl'. lia.  admit.
       *eapply rule_seq.
       apply rule_QUnit_One'. lia. admit.
       *eapply rule_seq. 
       eapply rule_QUnit_Ctrl'. lia.  admit.
       *eapply rule_seq. 
       apply rule_QUnit_One'. lia. admit.
       *
       eapply rule_conseq.
       eapply rule_QMeas with (s:=0) (e:=n+m+1)(P:=P) (v:=((big_sum (fun j:nat=> ∣ 0 ⟩_ (n) ⊗ (Vec (2^m) j) ⊗ (((sqrt (1-(( c^2)/( (phi' j)^2)))) .* (Vec 2 0) .+ (c/((phi' j)) .* Vec 2 1)))) (2^m)))).
       lia. admit. admit. admit.
        simpl. 
 
    
End HHL.

