Require Import Lists.List.
Require Import Psatz ZArith Znumtheory.
Require Import Reals.
Require Import Coquelicot.Complex.
Require Import Strings.String.

From Quan Require Import QuantumLib.Prelim.
From Quan Require Import Matrix.
From Quan Require Import Quantum.
From Quan Require Import Basic.
From Quan Require Import ParDensityO.
From Quan Require Import QState.
From Quan Require Import Par_trace.
From Quan Require Import QIMP_L.
From Quan Require Import Ceval_Linear.
From Quan Require Import QAssert.
From Quan Require Import QRule_E_L.
From Quan Require Import QRule_Q_L.
From Quan Require Import QRule_I_L.
From Quan Require Import QSepar.
From Quan Require Import QRule_QFrame.
From Quan Require Import Forall_two.
From Quan Require Import add.
From Quan Require Import HHL.
From Quan Require Import ContFrac.


Local Open Scope com_scope.
Local Open Scope assert_scope.
Local Open Scope nat_scope.
Local Open Scope matrix_scope.
Local Open Scope rule_scope.  

Require Import Arith.



Module Type Param.
Parameter x:nat.
Parameter N:nat. 
Parameter r:nat. 
Hypothesis Hr: x ^ r mod N =1 /\ (forall j, x ^ j mod N =1 -> r<=j).
Hypothesis H: r>0 /\ 2 <= x <= N-1.
Definition z:nat := 0.
End Param.

Module OF (p: Param).

Definition x := p.x.
Definition N := p.N.
Definition z := p.z.
Definition r := p.r.

Parameter t:nat.
Parameter L:nat.
Parameter U_plus:Square (2^L).
Parameter U: Square (2^L).
Parameter f: R-> nat.
Parameter QFT: Square (2^t).
Parameter delt_n:nat->nat.


Hypothesis HtL: and (t>0)%nat (L>0)%nat.
Hypothesis HNL:  (N < (2^L))%nat. 
Hypothesis HU_plus: WF_Unitary U_plus /\ ( U_plus × (∣ 0 ⟩_ L) = (∣ 1 ⟩_ L)).
Hypothesis HU: WF_Unitary U /\ (forall j:nat, j< N -> U × (Vec (2 ^ L) j) = (Vec (2 ^ L) (x * j mod N))) /\ 
                               (forall j:nat, j>=N /\ j<(2^L)-> U × (Vec (2 ^ L) j) = (Vec (2 ^ L) j)).
Hypothesis HQFT: WF_Unitary QFT /\ forall k:nat, QFT × (∣ k ⟩_ t) =
/ √ 2 ^ t .* (big_sum (fun j : nat => (cos (((2 * PI)/(2^t)) * j * k)%R,  sin (((2 * PI)/(2^t)) * j * k)%R) .*  (∣ j ⟩_ t)) (2 ^ t)).
Hypothesis (Ht: forall s:nat,  s < r-> exists j, j < (2^t) /\ ((( s / r) * 2^t)%R =  j)).


Definition  H := p.H .
Definition  Hr := p.Hr .
Definition  U_f (i:nat):= exp_U U i.
Definition  Us (s:nat):=  / √ r .* (big_sum (fun k:nat=> (cos (- ((2 * PI)) * (s /r) * k)%R,  sin (- ((2 * PI)) * ( s / r) * k)%R) .*  Vec (2 ^ L) (x ^ k mod N)) (r) ) .
Definition  b:nat := 1.
Definition  z':nat:=2 .
Definition  b' := (AMod (APow x z ') (N)) .
Definition  P (i:nat): Pure_formula := (BEq z' ' i%nat).
Definition  P' (s:nat): Pure_formula := (BEq z' ' (s * 2 ^ t / r)%nat).




Local Open Scope nat_scope.
Definition OF :=
    <{ z :=  1 ;
       b := b' ;
       while  b '<> 1  do 
       [[ 0 t ]] :Q= 0;
       [[ t (t+L) ]]:Q= 0;
       (t ⨂ hadamard) [[ 0 t ]];
       U_plus [[t (t + L)]];
       U_f [[0 t]] [[t (t + L)]];
       (adjoint QFT) [[ 0 t ]];
       z' :=M [[ 0 t ]];
       z  := (Afun CFq (CF_bound (2^t)) z' ' ((2^t)));
       b := b'
       end }>. 

Local Open Scope R_scope.



Lemma sum_pro: forall n (q:C), 
q<>C1->
big_sum (fun s=>Cpow q s) n = ((C1-(Cpow q n))/(C1-q))%C.
Proof. induction n; intros. simpl.  rewrite Cminus_diag; try reflexivity.
       rewrite Cdiv_unfold. Csimpl. reflexivity.
       simpl. rewrite IHn; try assumption. 
       assert((Cpow q n)=(C1 - q)*(Cpow q n)/(C1 - q))%C.
       rewrite Cdiv_unfold. rewrite Cmult_comm. rewrite Cmult_assoc.
       rewrite Cinv_l; Csimpl; try reflexivity.
       intro. apply Cminus_eq_0 in H1. destruct H0. rewrite H1. reflexivity.
       rewrite H1 at 2.
       repeat rewrite Cdiv_unfold.
       rewrite <-Cmult_plus_distr_r. 
       f_equal. repeat rewrite Cminus_unfold.
       rewrite Cmult_plus_distr_r.  rewrite Cplus_assoc.
       Csimpl. rewrite <-(Cplus_assoc C1 _ _ ).
       rewrite (Cplus_comm _ (Cpow q n)). rewrite <-Cminus_unfold.
       rewrite Cminus_diag; try reflexivity. rewrite Cplus_0_r.
       rewrite Copp_mult_distr_l.
       reflexivity.
Qed.

Lemma cons_sin_plus_mult: forall i j, 
(cos (i + j ), sin (i +j ))=((cos i, sin i) * (cos j , sin j))%C.
Proof. intros. rewrite cos_plus. rewrite sin_plus. 
       unfold Cmult. simpl. f_equal. rewrite Rplus_comm.
       reflexivity.
Qed.

Lemma cons_sin_pow: forall i n, 
Cpow (cos (i), sin (i)) n=((cos (i*n), sin (i*n)))%C.
Proof. induction n; intros. simpl. rewrite Rmult_0_r. rewrite cos_0.
        rewrite sin_0. reflexivity. 
        simpl Cpow. rewrite IHn.
        rewrite <-cons_sin_plus_mult.
        rewrite S_INR. rewrite Rmult_plus_distr_l.
        rewrite Rmult_1_r. rewrite Rplus_comm. reflexivity.
Qed.



Lemma times_1_n: forall n,
times_n C1 n = n.
Proof. induction n; intros. reflexivity.
        rewrite S_INR. simpl. 
       rewrite IHn. rewrite Rplus_comm. 
       rewrite RtoC_plus. reflexivity.
Qed.



Lemma  CF_out_divide: forall s,
(s<r)%nat->
CFq (CF_bound (2^t)) (s*2^t /r ) (2^t) =  (r / (Nat.gcd s r))%nat .
Proof. intros. pose H. apply Legendre_rational_bound with (s/ (Nat.gcd s r))%nat.
       apply Nat.div_str_pos. split.  
       assert(Nat.gcd s r <> 0)%nat. intro. 
       apply Nat.gcd_eq_0 in H1. destruct H1. unfold r in *. lia.
       lia. pose(Nat.gcd_divide_r s r). apply Nat.divide_pos_le in d. lia. 
       unfold r. lia. apply  Nat.div_lt_upper_bound. unfold r. lia. 
       apply Nat.mul_lt_mono_pos_r. apply pow_gt_0. lia.
       apply Rabs_eq_0. 
       apply Rminus_diag_eq. 
       apply eq_trans with (s/r). pose (Ht s H0). destruct e. 
       rewrite Rdiv_unfold in H1. destruct H1. 
       rewrite Rmult_assoc in H2.  rewrite (Rmult_comm (/ r) ) in H2.
       rewrite <-Rmult_assoc in H2.  
       rewrite <-(div_INR (s*2^t) _ x0). rewrite mult_INR. rewrite pow_INR.
       repeat rewrite Rdiv_unfold. repeat rewrite Rmult_assoc. f_equal.
       rewrite Rmult_comm. rewrite Rmult_assoc. rewrite Rinv_l. rewrite Rmult_1_r. 
       reflexivity. apply pow_nonzero. rewrite IZR_INR_0. 
       intro.  apply INR_eq in H3. lia.  unfold r. lia. 
       rewrite mult_INR. rewrite pow_INR. rewrite <-H2. 
       reflexivity. pose (Nat.gcd_divide s r). destruct a0. 
       unfold Nat.divide in *. destruct H1. destruct H2.
       assert( INR s = INR ((x0 * Nat.gcd s r)%nat) ). 
       rewrite H1 at 1. reflexivity. rewrite mult_INR in H3. 
       assert( INR r = INR ((x1 * Nat.gcd s r)%nat) ). 
       rewrite H2 at 1. reflexivity. rewrite mult_INR in H4. 
       rewrite H1  at 2. rewrite H2 at 4.  
       rewrite  Nat.div_mul. rewrite Nat.div_mul. 
       rewrite H3. rewrite H4.  rewrite Rdiv_unfold at 1. 
       rewrite (Rmult_comm x1).  rewrite Rinv_mult_distr_depr.
       rewrite Rmult_assoc. rewrite <-(Rmult_assoc _ _ (/x1)).
       rewrite Rinv_r. rewrite Rmult_1_l. reflexivity. 
       intro. rewrite IZR_INR_0 in H5.  apply INR_eq in H5.
       rewrite Nat.gcd_eq_0 in H5. destruct H5. unfold r in *. lia.
       intro. rewrite IZR_INR_0 in H5.  apply INR_eq in H5.
       rewrite Nat.gcd_eq_0 in H5. destruct H5. unfold r in *. lia.
       intro. rewrite IZR_INR_0 in H5.  apply INR_eq in H5.
       rewrite H5 in H2. rewrite Nat.mul_0_l in H2. unfold r in *. lia.
       intro. 
       rewrite Nat.gcd_eq_0 in H5. destruct H5. unfold r in *. lia.
       intro. 
       rewrite Nat.gcd_eq_0 in H5. destruct H5. unfold r in *. lia.
       
        rewrite Nat2Z.inj_div.  rewrite Nat2Z.inj_div. 
       apply Zis_gcd_rel_prime. unfold r . lia. 
       lia.  assert(Z.of_nat (Nat.gcd s r)= (Z.gcd s r) ).
       apply inj_gcd. rewrite H1.  
       apply Zgcd_is_gcd.

Qed.
Local Open Scope nat_scope.
Lemma HU_s: 
  / √ r .*  (big_sum (fun s:nat=> Us s) (r) ) =(∣ 1 ⟩_ (L)).
Proof. pose H. assert(0<r)%R. rewrite IZR_INR_0. 
      apply lt_INR. apply a. 
      assert(0<x)%R. rewrite IZR_INR_0. 
      apply lt_INR. unfold x. lia. pose Hr.  
      unfold Us. rewrite Mscale_Msum_distr_r. rewrite Mscale_assoc. 
       rewrite big_sum_swap_order. 
       rewrite (big_sum_eq_bounded _ ((fun i : nat =>
       (@big_sum C _ (fun j : nat =>
          (cos (- (2 * PI) * (j / r) * i), sin (- (2 * PI) * (j / r) * i))) r)
          .* ∣ x ^ i mod N ⟩_ (L)))).
        rewrite (big_sum_unique  (r .* ∣ x ^ r mod N ⟩_ (L) )).
        repeat rewrite Mscale_assoc.
        assert(√ r<>0).  
        apply sqrt_neq_0_compat; try assumption.
        rewrite <-RtoC_inv; try assumption. 
        rewrite RtoC_mult. 
        rewrite <-Rinv_mult_distr_depr; try assumption.
        rewrite sqrt_sqrt. rewrite RtoC_mult. 
        rewrite Rinv_l. Msimpl. destruct a0. unfold x.
        unfold r. unfold N.    rewrite H3.
        reflexivity. apply Rgt_neq_0. assumption. lra. 
        exists 0. split. apply H. 
        split. f_equal. 
        rewrite (@big_sum_eq_bounded  C C_is_monoid _ (fun j=>1%R)).  
        rewrite big_sum_constant. apply times_1_n. 
        intros. rewrite Rmult_0_r. rewrite cos_0. 
        rewrite sin_0. reflexivity. 
        destruct a0. unfold x.
        unfold r. unfold N.  rewrite H2. simpl. 
        rewrite Nat.mod_small. reflexivity. unfold N. lia.  
        intros. 
        rewrite (@big_sum_eq_bounded  C C_is_monoid 
        _ (fun j : nat =>
        Cpow (cos (- (2 * PI) * (x' / r) ),
         sin (- (2 * PI) * (x' / r) )) j)).
        rewrite sum_pro. rewrite cons_sin_pow. 
        repeat rewrite Rdiv_unfold. 
        rewrite <-Rmult_assoc. rewrite Rmult_assoc.
        rewrite Rinv_l.
          rewrite Rmult_1_r. rewrite Cdiv_unfold.  
        rewrite <-Ropp_mult_distr_l. 
        rewrite cos_neg. rewrite sin_neg. 
        rewrite Rmult_assoc. rewrite (Rmult_comm PI ).
        rewrite <-Rmult_assoc.
         rewrite <-(Rplus_0_l (2 * x' * PI)). rewrite cos_period.
         rewrite sin_period. rewrite cos_0. rewrite sin_0.
        rewrite Ropp_0. rewrite Cminus_diag; try reflexivity.
        Csimpl. Msimpl. reflexivity. apply Rgt_neq_0. lra. 
        intro. injection H4; intros.  assert(0<x')%R.  
        rewrite IZR_INR_0. apply lt_INR. lia.  
        rewrite <-Ropp_mult_distr_l in H6. 
        rewrite cos_neg in H6.
        assert((x' / r) <=1/2 \/ ~((x' / r) <=1/2))%R. 
        apply Classical_Prop.classic. destruct H8.
        rewrite <-cos_0 in H6. apply cos_inj in H6.
        assert((2 * PI * (x' / r))<>0)%R.  
        apply Rmult_integral_contrapositive. split.
        apply Rmult_integral_contrapositive. split; try lra.
        apply PI_neq0.  apply Rgt_neq_0.
        apply Rdiv_lt_0_compat; try lra . destruct H9; try assumption. 
        split. apply Rmult_le_pos. apply Rmult_le_pos.
        lra.  pose PI_RGT_0. lra.  
        rewrite Rdiv_unfold. apply Rmult_le_pos; try lra. 
        pose (Rinv_0_lt_compat r H0). lra.  
        rewrite Rmult_assoc. rewrite Rmult_comm. rewrite Rmult_assoc.
        rewrite <-Rmult_1_r.
         apply Rmult_le_compat_l.  pose PI_RGT_0. lra.
         lra.  pose PI_RGT_0. lra.   
        rewrite <-cos_2PI in H4. 
        assert((x' / r > 1 / 2)%R). lra. 
        assert((x' / r) <1)%R. 
        apply (Rcomplements.Rdiv_lt_1 x' r). lra. 
        apply lt_INR. assumption. 
         apply (Rmult_lt_compat_l  (2*PI)%R) in H10. 
        apply cos_increasing_1 in H10; try lra.  rewrite Rmult_1_r in H10.
        rewrite <-cos_2PI in H6.
        lra. rewrite Rmult_comm. rewrite <-Rmult_assoc.
        rewrite <-Rmult_1_l at 1. apply Rmult_le_compat_r; try lra. 
        pose (PI_RGT_0). lra.  rewrite Rmult_1_r. rewrite <-Rmult_1_l at 1.
        apply Rmult_le_compat_r; try lra. 
        pose (PI_RGT_0). lra. apply Rmult_gt_0_compat; try lra.
        apply PI_RGT_0.         
         intros. rewrite cons_sin_pow.
          repeat rewrite Rdiv_unfold. 
          repeat rewrite Rmult_assoc. 
          rewrite (Rmult_comm x0). rewrite (Rmult_comm x').
          repeat rewrite Rmult_assoc. rewrite (Rmult_comm x').
          reflexivity.  
        intros. rewrite Mscale_Msum_distr_l. reflexivity.
Qed.



Lemma  simpl_H_Uplus: 
/ √ 2 ^ t .* big_sum (fun z0 : nat => ∣ z0 ⟩_ (t)) (2 ^ t) ⊗ ∣ 1 ⟩_ (L)
= / √ (r *2^t) .*  (big_sum (fun s:nat=>(big_sum (fun j=>(Vec (2^t) j)) (2^t)) ⊗ (Us s)) (r) ).
Proof. intros.   rewrite<- HU_s. pose H.  
   rewrite Mscale_kron_dist_l.
   rewrite Mscale_kron_dist_r.
   rewrite Mscale_assoc.
   f_equal. repeat rewrite RtoC_pow; repeat rewrite <-RtoC_inv;
   try rewrite RtoC_mult; try apply sqrt_neq_0_compat;
   try apply pow_nonzero; try apply  Rmult_gt_0_compat; 
   try apply pow_lt; try apply sqrt2_neq_0; try lra; try rewrite IZR_INR_0;
   try apply lt_INR; try apply a. 
   rewrite <-Rinv_mult.  f_equal. f_equal. rewrite sqrt_mult_alt. rewrite Rmult_comm.
   f_equal. rewrite sqrt_pow; try lra. try rewrite IZR_INR_0.
   apply le_INR. lia.    
   rewrite kron_Msum_distr_l. 
   apply big_sum_eq_bounded.
   intros. reflexivity. 
Qed.



Lemma WF_Us: forall s, WF_Matrix (Us s) .
Proof.  unfold Us. intros.  pose HNL. pose (H). assert(forall i,  x^i mod N < 2^(L)).
        intros. apply Nat.lt_trans with (N).
        apply  Nat.mod_upper_bound. unfold N.  lia.  lia. auto_wf.    
Qed.

#[export] Hint Resolve WF_Us:wf_db.

Lemma big_sum_move_r:forall {G : Type} `{Monoid G} `{H0 : Comm_Group G} (f: nat-> G) n, 
f(0)=f(n)->
big_sum f n= big_sum (fun i=> f (i+1)) n.
Proof.  induction n;  intros. simpl. reflexivity.
       rewrite <-big_sum_extend_l. 
       simpl. rewrite H4.
        rewrite Gplus_comm.  rewrite S_add_1.
        f_equal. apply big_sum_eq. 
        apply functional_extensionality.
        intros. rewrite S_add_1. reflexivity.
Qed.


Lemma simpl_U_Us: forall s,
U × Us s = (cos ((2*PI )*(s/r )), sin ((2*PI) *(s/r))) .* Us s.
Proof. intros. pose HU. pose HNL. pose H. unfold Us. rewrite Mscale_mult_dist_r.
       rewrite Mscale_assoc. rewrite Cmult_comm.
       rewrite <-Mscale_assoc. f_equal. 
       rewrite Mmult_Msum_distr_l. 
       rewrite <-Mscale_Msum_distr_r.
       rewrite (big_sum_eq_bounded _ 
       ((fun i : nat =>  ((cos (- (2 * PI ) * (s / r) * (i))%R, sin (- (2 * PI ) * (s / r) * (i))%R)) .* ∣ x ^ (i+1) mod N ⟩_ (L)))).
       rewrite (big_sum_eq_bounded ((fun i : nat =>
       (cos (2 * PI * (s / r)), sin (2 * PI * (s / r))) .* ((cos (- (2 * PI) * (s / r) * i),
            sin (- (2 * PI) * (s / r) * i)).* ∣ x ^ i mod N ⟩_ (L)))) 
       ((fun i : nat =>  ((cos (-(2 * PI ) * (s / r) * (i-1%nat)), sin (-(2 * PI) * (s / r) * (i-1%nat))) .* ∣ x ^ i mod N ⟩_ (L))))).
       rewrite (big_sum_move_r ((fun i : nat =>
       (cos (- (2 * PI) * (s / r) * (i - 1%nat)),
        sin (- (2 * PI) * (s / r) * (i - 1%nat)))
       .* ∣ x ^ i mod N ⟩_ (L)))).  apply big_sum_eq_bounded.
       intros.    rewrite plus_INR. rewrite Rminus_unfold.
       rewrite Rplus_assoc. rewrite Rplus_opp_r. rewrite Rplus_0_r.
       reflexivity. 
      repeat rewrite Rminus_unfold. repeat rewrite Rmult_plus_distr_l.
       repeat rewrite cons_sin_plus_mult.  
       f_equal. f_equal. rewrite Rmult_0_r. rewrite cos_0. rewrite sin_0.
       repeat rewrite <-Ropp_mult_distr_l. rewrite cos_neg.
       rewrite sin_neg. rewrite Rdiv_unfold. rewrite Rmult_assoc.
       rewrite (Rmult_assoc s). rewrite Rinv_l. 
       rewrite Rmult_1_r. rewrite <-(Rplus_0_l ((2 * PI * s))).
       rewrite Rmult_assoc. rewrite (Rmult_comm PI).
       rewrite <-Rmult_assoc.
       rewrite cos_period. rewrite sin_period. 
       rewrite cos_0. rewrite sin_0. rewrite Ropp_0. reflexivity.
       apply Rgt_neq_0. rewrite IZR_INR_0. apply lt_INR. unfold r.
       lia.  pose Hr.  destruct a1. unfold x. unfold r. unfold N.
       simpl. rewrite H0. rewrite Nat.mod_small. reflexivity. lia.     
       intros. rewrite Mscale_assoc. f_equal. 
       rewrite<-cons_sin_plus_mult.  f_equal; f_equal;
       repeat rewrite <-Ropp_mult_distr_l;
       repeat rewrite Ropp_mult_distr_r;
       rewrite<- (Rmult_1_r (2 * PI * (s / r))) at 1;
       rewrite <-Rmult_plus_distr_l; f_equal;
       rewrite Rminus_unfold; rewrite Ropp_plus_distr; 
       rewrite Ropp_involutive; rewrite Rplus_comm; reflexivity.
       intros. 
       destruct a.  destruct H2. 
       rewrite Mscale_mult_dist_r. 
       f_equal. rewrite H2. 
       rewrite Nat.mul_comm.
       rewrite Nat.mul_mod_idemp_l; try unfold N; try lia. 
       f_equal. f_equal. rewrite Nat.pow_add_r. simpl.
       rewrite Nat.mul_1_r. reflexivity.  
       apply Nat.mod_upper_bound. unfold N. lia.   
Qed.


Lemma simpl_expU: forall j s,
U_f j × Us s = (cos ((2*PI/2^t)* j *(s/r * 2^t)), sin ((2*PI/2^t)* j *(s/r * 2^t))) .* Us s.
Proof. intros.  induction j. simpl. rewrite Mmult_1_l.
     rewrite Rmult_0_r. rewrite Rmult_0_l. rewrite cos_0. rewrite sin_0.
rewrite Mscale_1_l. reflexivity.  simpl. auto_wf.  
 unfold U_f in *.  simpl exp_U.
rewrite Mmult_assoc.
rewrite IHj.
rewrite Mscale_mult_dist_r. pose HU.
destruct a.   rewrite simpl_U_Us.
rewrite Mscale_assoc. f_equal.
assert(2 * PI * (s / r) =(2 * PI / 2 ^ t) * (s / r * 2^t) )%R.
repeat rewrite Rdiv_unfold. repeat rewrite Rmult_assoc.  
f_equal. f_equal. rewrite (Rmult_comm (/ 2 ^ t) _). 
repeat rewrite Rmult_assoc. f_equal. rewrite Rinv_r.
rewrite Rmult_1_r. reflexivity. apply pow_nonzero. lra.
rewrite H2.
rewrite <-cons_sin_plus_mult.  rewrite S_O_plus_INR. 
rewrite (Rplus_comm 1%nat j).  
rewrite Rmult_plus_distr_l. rewrite Rmult_plus_distr_r. 
 rewrite Rmult_1_r. reflexivity.
Qed.

Lemma  WF_expU{n:nat}: forall (U:Square (2^n)) x0,
WF_Matrix U->
WF_Matrix (exp_U U x0).
Proof. induction x0; simpl; intros. auto_wf.
auto_wf.
Qed.
#[export] Hint Resolve WF_expU : wf_db.

Ltac type_sovle:= 
  try repeat rewrite add_sub_eq; 
  try repeat rewrite Nat.sub_0_r;
  try repeat rewrite Nat.sub_diag;
  try repeat rewrite pow_0;
  try (f_equal; type_sovle'; try lia );
  try apply big_sum_eq_bounded; try intros;
  Msimpl.

Lemma U_f': forall (v:Vector (2^t *(2^L))) , 
UCtrl_v 0 t t (t + L) 0 (t + L) U_f v =
Mmult (big_sum (fun i : nat =>
 (∣ i ⟩_ (t) × ⟨ i ∣_ (t)) ⊗ (U_f i)) (2 ^ t)) v.
Proof.  intros. unfold UCtrl_v. pose HU. type_sovle.
apply Logic.eq_trans with (∣ x0 ⟩_ (t) × ⟨ x0 ∣_ (t) ⊗ I (2 ^ L)
× (I (2 ^ t) ⊗  U_f x0)). f_equal; type_sovle'; try lia. 
rewrite kron_mixed_product; Msimpl; try reflexivity.
unfold U_f. apply WF_expU. apply a. 
Qed.


Lemma  simpl_Uf: 
UCtrl_v 0 t t (t + L) 0 (t + L) U_f
( / √ (r * 2 ^ t)
 .* big_sum (fun s : nat => big_sum (fun j : nat => ∣ j ⟩_ (t)) (2 ^ t) ⊗ Us s) r) =
( / √ (r) .* big_sum (fun s : nat => (/ √ (2 ^ t)).*  big_sum (fun j : nat =>(cos ((2*PI/2^t)* j *(s/r * 2^t)), 
sin ((2*PI/2^t)* j *(s/r * 2^t))) .* ∣ j ⟩_ (t)) (2 ^ t)⊗ Us s) r).
Proof. intros. rewrite U_f'. pose H.  
rewrite Mscale_mult_dist_r.
rewrite Mmult_Msum_distr_l.  rewrite<- RtoC_inv;
try apply sqrt_neq_0_compat; try apply Rmult_gt_0_compat; 
try apply pow_lt; try lra; try rewrite IZR_INR_0;
try apply lt_INR; try apply a. 
rewrite <-sqrt_inv. rewrite Rinv_mult. rewrite sqrt_mult_alt;
try rewrite <-RtoC_mult. repeat rewrite sqrt_inv. 
repeat rewrite RtoC_inv; try apply sqrt_neq_0_compat;
try apply pow_lt; try lra; try rewrite IZR_INR_0; try apply lt_INR; 
try apply le_INR; try apply a.    
rewrite <-Mscale_assoc. f_equal.  rewrite <-Mscale_Msum_distr_r.
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
rewrite Mmult_assoc. rewrite Vec_inner_1. unfold c_to_Vector1.
Msimpl. rewrite Mscale_kron_dist_r.
rewrite Mscale_kron_dist_l.
reflexivity. assumption.  
intros.
rewrite kron_mixed_product.
rewrite Mmult_assoc. rewrite Vec_inner_0. unfold  c_to_Vector1.
Msimpl. reflexivity.   intuition. assumption. assumption.
assert(0</r)%R. apply Rinv_0_lt_compat. rewrite IZR_INR_0. 
apply lt_INR. apply a. lra.
Qed.

Lemma unitary_trans{n:nat}: forall (U:Square n) (v1 v2:Vector n),
WF_Unitary U->WF_Matrix v1->
U × v1 = v2-> (U) † × v2 = v1 .
Proof. intros. unfold WF_Unitary in H0. destruct H0.
rewrite <-H2. rewrite <-Mmult_assoc. rewrite H3.
rewrite Mmult_1_l. reflexivity. assumption.
Qed.




Lemma  simpl_QFT': 
@U_v t (t+L) 0 t 0 (t + L) (QFT) †
(/ √ r .* big_sum (fun s : nat =>  / √ (2 ^ t) .* big_sum  (fun j : nat =>
             (cos (2 * PI / 2 ^ t * j * (s / r * 2 ^ t)), sin (2 * PI / 2 ^ t * j * (s / r * 2 ^ t))) 
             .* ∣ j ⟩_ (t)) (2 ^ t) ⊗ Us s) r)
 =( / √ r .* big_sum  (fun s : nat =>   (Vec (2^t) (s * (2^t) / r )) ⊗  Us s) r).
Proof. 
unfold U_v. type_sovle. pose H.
assert(2^t=1* 2^t). lia. destruct H0.
assert( 2^t * 2^L= 2^(t+L)). type_sovle'. destruct H0.
rewrite Mscale_mult_dist_r. f_equal.
rewrite Mmult_Msum_distr_l. 
apply big_sum_eq_bounded.  intros. 
rewrite kron_mixed_product. Msimpl.
f_equal. pose HQFT. 
apply unitary_trans. intuition.
apply WF_vec. apply Nat.div_lt_upper_bound. unfold r. lia.
apply Nat.mul_lt_mono_pos_r. apply pow_gt_0.  assumption. 
destruct a0. rewrite H2.  
f_equal. repeat rewrite RtoC_pow. repeat rewrite <-RtoC_inv. 
f_equal. f_equal.  rewrite sqrt_pow. reflexivity. lra.
apply sqrt_neq_0_compat. apply pow_lt. lra. 
apply pow_nonzero. apply sqrt2_neq_0.
apply big_sum_eq_bounded. intros.
f_equal. f_equal; f_equal; f_equal;
pose (Ht x0); destruct e; try assumption;
destruct H4;
unfold Rdiv in *; try rewrite Rmult_assoc in *; 
rewrite (Rmult_comm _ (2^t)) in *; 
rewrite <-Rmult_assoc in *;
rewrite <-Rdiv_unfold in *;
assert(INR(Init.Nat.mul x0 (Nat.pow (S (S O)) t))=
(Rmult (INR x0) (pow (IZR (Zpos (xO xH))) t)));
try rewrite  mult_INR; try f_equal; try     
rewrite pow_INR;  
f_equal; rewrite <-H6 in *;
rewrite (div_INR _ _  x2); try reflexivity;
unfold r; try lia; try assumption.  
apply WF_adjoint. apply HQFT.
Qed.


Lemma Had_N: forall n:nat, 
n ⨂ hadamard × ∣ 0 ⟩_ (n) = (/ (√ 2) ^ n)%C .* big_sum (fun z=> ∣ z ⟩_ (n)) (2^n).
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
rewrite Vec_I. reflexivity.
 rewrite kron_n_assoc.  rewrite IHn.
simpl. rewrite Nat.add_0_r.
rewrite big_sum_sum. 
rewrite kron_plus_distr_r.
unfold Gplus.  simpl.
f_equal. lia.   rewrite Nat.pow_1_l. simpl. reflexivity. 
apply Logic.eq_trans with (∣0⟩ ⊗ big_sum (fun z : nat => ∣ z ⟩_ (n) ) (2 ^ n)).
f_equal. apply Nat.pow_1_l.
rewrite kron_Msum_distr_l.
apply big_sum_eq_bounded. intros.
rewrite <-Vec_qubit0.
rewrite qubit0_Vec_kron. reflexivity. assumption.
apply Logic.eq_trans with (∣1⟩ ⊗ big_sum (fun z : nat => ∣ z ⟩_ (n) ) (2 ^ n) ).
f_equal. apply Nat.pow_1_l.
rewrite kron_Msum_distr_l.
apply big_sum_eq_bounded. intros.
rewrite <-Vec_qubit1.
rewrite qubit1_Vec_kron. rewrite (Nat.add_comm x0). reflexivity. assumption.
auto_wf. apply sqrt_neq_0_compat. lra. 
apply sqrt_neq_0_compat. lra. 
Qed.


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

Theorem rule_Dassgn: forall (D:Assertion) (i:nat) ( a:aexp),
             {{Assn_sub i a D}} i := a {{D}}.
Proof. unfold hoare_triple;
       intros F X a s e (mu,IHmu) (mu', IHmu').
       intros. 
       inversion_clear H0; simpl in H3.
       apply ceval_single_1 in H3.
       apply sat_Assert_dstate_eq with 
       ({|
        StateMap.this := d_update_cstate_aux X a mu;
        StateMap.sorted := d_update_cstate_sorted X a mu IHmu
      |}).
       unfold dstate_eq. simpl. intuition. 
       inversion_clear H1. unfold d_update_cstate in H0.
       simpl in H0. assumption.
Qed.


Lemma Assn_impl:forall i a D1 D2,
D1 ->> D2 ->
Assn_sub i a D1 ->> Assn_sub i a D2 .
Proof. intros. unfold assert_implies in *. intros.
inversion_clear H1.
econstructor. assumption. 
apply H0. assumption.   
Qed.


Lemma app_fix_2{s e:nat} : forall c (q:qstate s e) i a (mu:list (cstate * qstate s e)),
((fix map2_aux (m' : StateMap.Raw.t (qstate s e)) :
        StateMap.Raw.t (qstate s e) :=
      match m' with
      | [] => [(c_update i (aeval (c, q) a) c, q)]
      | p :: l' =>
          let (k', e') := p in
          match
            Cstate_as_OT.compare (c_update i (aeval (c, q) a) c) k'
          with
          | OrderedType.LT _ =>
              (c_update i (aeval (c, q) a) c, q)
              :: StateMap.Raw.map2_r option_app m'
          | OrderedType.EQ _ =>
              (c_update i (aeval (c, q) a) c, q_plus q e')
              :: StateMap.Raw.map2_r option_app l'
          | OrderedType.GT _ => (k', e') :: map2_aux l'
          end
      end) (d_update_cstate_aux i a mu))=
 StateMap.Raw.map2  option_app  ([(c_update i (aeval (c, q) a) c, q)]) (d_update_cstate_aux i a mu)     .
Proof. intros. reflexivity. 
       
Qed.


Lemma Assn_true: forall i a D, ~NSet.In i (Free_aexp a) ->
(D ->> Assn_sub i a (BEq (i ') a)).
Proof. unfold assert_implies. intros.
apply WF_sat_Assert in H1. destruct H1.
econstructor. assumption.
rewrite sat_Assert_to_State.  
econstructor. apply WF_d_update_cstate. assumption.
destruct mu as (mu, IHmu). simpl in *.
induction mu. destruct H1. reflexivity.

destruct a0. 
assert(State_eval <{ (i) ' = a }> (c_update i (aeval (c, q) a) c, q)).
simpl.  rewrite c_update_find_eq. 
rewrite <-(c_update_aeval_eq i _  ((aeval (c, q) a))).
assert(aeval (c, q) a = aeval (c, q) a).
reflexivity. apply Nat.eqb_eq in H3. rewrite H3.
auto. assumption. 

destruct mu. econstructor. assumption. econstructor.
remember (p :: mu).
simpl.  rewrite app_fix_2. apply d_seman_app_aux. 
apply WF_state_dstate_aux. 
apply WF_state_eq with (c,q). reflexivity.
inversion_clear H2. assumption.
apply WF_d_update_cstate. inversion_clear H2.
assumption.  econstructor. assumption. econstructor.

subst.
inversion_clear IHmu. apply (IHmu0  H4).
discriminate. inversion_clear H2. assumption.
Qed.

Lemma BTrue_true{s e:nat}: forall (mu:dstate s e),
WF_dstate mu /\ (StateMap.this mu <> [])->
sat_State mu <{ true }> .
Proof. intros. econstructor. apply H0.  
destruct mu as [mu IHmu]. 
induction mu; simpl in *. destruct H0. 
destruct H1. reflexivity. destruct mu. 
econstructor.  auto. econstructor.
econstructor.  auto. destruct H0.
inversion_clear IHmu. 
simpl in IHmu0. eapply IHmu0 with H2. 
split. 
inversion_clear H0. apply H5.
discriminate.
Qed.


Lemma rule_DT: forall D,
D->> <{ true }> .
Proof. unfold assert_implies. intros. rewrite sat_Assert_to_State in *.
apply BTrue_true.  apply WF_sat_Assert in H0. split; apply H0.
Qed.


Lemma Big_Sand_forall{s e:nat}: forall (mu:dstate s e) (f:nat-> State_formula) n,
(forall i,  sat_Assert mu (f i))->
sat_Assert mu (big_Sand f n).
Proof. induction n; intros. simpl. rewrite sat_Assert_to_State in *.
apply BTrue_true. pose(H0 1). 
apply WF_sat_Assert in s0.
split; apply s0.
simpl. apply sat_assert_conj. 
split. 
apply H0. apply IHn. assumption.
Qed.

Lemma big_Sand_Assn_true: forall a D n, 
(forall i:nat, ~NSet.In a (Free_aexp i)) ->
D ->> big_Sand (fun i : nat => PAssn a i (BEq (a ') i)) n.
Proof. unfold assert_implies. intros.  
apply Big_Sand_forall.
intros. apply Assn_true_P.
apply H0. 
eapply rule_DT. apply H1.
Qed.

Lemma fun_to_list_inv{A:Type}: forall(mu_n:list A)  (a: A)  (default: A),
fun_to_list (fun i : nat => match i with
                            | 0 => a
                            | S m => nth m mu_n default
                            end) (Datatypes.length mu_n) ++
[match Datatypes.length mu_n with
 | 0 => a
 | S m => nth m mu_n default
 end] = a :: fun_to_list (fun i : nat => nth i mu_n default) (Datatypes.length mu_n) .
Proof. intros. 
induction (Datatypes.length mu_n). simpl. reflexivity.
simpl. rewrite IHn. reflexivity. 
Qed.


Lemma n_th_fun_to_list_inv{A:Type}: forall (mu_n:list A) (default: A),
(fun_to_list (fun i : nat => nth i mu_n default) (length (mu_n)))=mu_n.
Proof. induction mu_n; intros; simpl in *. reflexivity.
      rewrite <-(IHmu_n default) at 3. apply fun_to_list_inv. 
Qed.


Lemma Forall_two_nth{A B : Type}: forall  (P : A -> B -> Prop) 
(f : list A) (g : list  B) (fdefault:A) (gdefault:B),
Forall_two P f g <-> 
((length f) = (length g) /\ forall i, i< (length f) -> P (nth i f  fdefault) 
(nth i g gdefault)) .
Proof. induction f0; destruct g; intros; simpl in *. split; intros. split; lia. econstructor.
       split; intros. inversion_clear H0. lia.
       split; intros.   
       inversion_clear H0. lia.
       split; intros.  inversion_clear H0. split. apply Forall_two_length_eq in H2.
       rewrite H2. reflexivity.   
       intros. destruct i. assumption. apply IHf0. assumption. lia.
       destruct H0.  econstructor.  apply (H1 0). lia.
       rewrite (IHf0 _ fdefault gdefault). split. injection H0. auto.
       intros. pose( H1 ( S i)). simpl in p.  apply p. lia.      
Qed.


Lemma fst_nth_big_pOplus: forall n p_n F_n i, 
i<n->
fst (nth i (big_pOplus p_n F_n n) ((1%R, SPure (PBexp <{BTrue}>))))%R = p_n i.
Proof. induction n; intros. lia. simpl. 
       assert(i=n \/ i<> n). apply Classical_Prop.classic.
       destruct H1. rewrite H1. 
       rewrite app_nth2; rewrite  big_pOplus_length.  
       rewrite Nat.sub_diag. simpl. reflexivity. lia. 
       rewrite app_nth1; try rewrite  big_pOplus_length.
       apply IHn. lia. lia.    
Qed.


Lemma snd_nth_big_pOplus: forall n p_n F_n i, 
i<n->
snd (nth i (big_pOplus p_n F_n n) ((1%R, SPure (PBexp <{BTrue}>))))%R = F_n i.
Proof. induction n; intros. lia. simpl. 
       assert(i=n \/ i<> n). apply Classical_Prop.classic.
       destruct H1. rewrite H1. 
       rewrite app_nth2; rewrite  big_pOplus_length.  
       rewrite Nat.sub_diag. simpl. reflexivity. lia. 
       rewrite app_nth1; try rewrite  big_pOplus_length.
       apply IHn. lia. lia.    
Qed.



Lemma big_pOplus_sat'{s e:nat}: forall n (p_n:nat-> R) (F_n:nat-> State_formula) (mu_n:nat-> (dstate s e)) mu,
sat_Pro mu (big_pOplus p_n F_n n)->
(exists (mu_n:nat-> (dstate s e)) mu',
 big_dapp' (fun_to_list p_n n) (fun_to_list mu_n n) mu' 
/\ dstate_eq mu mu' 
/\(forall i, i<n -> (0<(p_n i))%R -> sat_State (mu_n i) (F_n i) /\ d_trace (mu_n i) = d_trace mu)).
Proof. intros.  inversion_clear H0.  exists (fun i=> nth  i (mu_n0) (d_empty s e)).
      rewrite big_pOplus_get_pro in *.
      assert( n= length mu_n0). 
      rewrite <-(fun_to_list_length  p_n n). eapply big_dapp'_length. apply H1.
      exists mu'.  split. 
      rewrite H0.
      rewrite n_th_fun_to_list_inv. rewrite <-H0. assumption. 
       split. assumption.
      intros. rewrite H0 in H4.  
      eapply (Forall_two_nth _ mu_n0  (big_pOplus p_n F_n n) (d_empty s e) ((1%R, SPure (PBexp <{BTrue}>)))) in H3; try apply H4.
      destruct H3. pose(H6 i H4).
      rewrite fst_nth_big_pOplus in a; try lia.  
      rewrite snd_nth_big_pOplus in a;try lia.
      apply a. assumption.
Qed.


Lemma big_pOplus_get_npro: forall  (f : nat -> R) (g : nat -> State_formula) (n_0 : nat),
  pro_to_npro_formula (big_pOplus f g n_0) = big_Oplus g n_0.
  Proof. induction n_0. simpl. reflexivity.
         simpl. rewrite pro_to_npro_formula_app.  rewrite IHn_0. 
         simpl. intuition.
  Qed. 

Fixpoint  list_to_fun{A:Type} (mu: list A) (default: A):  nat-> A:= 
  match mu with 
  |[]=> (fun i:nat => default)
  |a::mu=> (fun i:nat => if i=?0 then a else ((list_to_fun mu default) i))
  end.

Lemma big_dapp'_out_empty{s e:nat}: forall  (p_n:list R) (mu_n:list (dstate s e)) (mu:dstate s e),
(Forall (fun i => ( i = 0%R)%R) p_n)->
big_dapp' p_n mu_n mu->
dstate_eq mu (d_empty s e).
Proof. induction p_n;destruct mu_n; intros; simpl in *. inversion_clear H1. reflexivity.
     inversion_clear H1.  
     inversion H1;subst.
         inversion H1; subst. inversion_clear H0.
          pose (IHp_n _ _ H3 H8). 
          apply dstate_eq_trans with ((d_app r0 (d_empty s e))).
          apply d_app_eq. reflexivity. assumption.
          inversion H7; subst.  
          apply d_app_empty_l.
          lra.
Qed.


Lemma map_1_1: forall n2 f0,
(forall i j : nat, i < n2 -> j < n2 -> i < j -> f0 i < f0 j)->
(forall i : nat, i < n2 -> f0 i < n2)->
(forall i, i< n2-> f0 i =i) .
Proof. induction n2; intros. lia. destruct n2. 
       assert( i=0).  lia. subst. pose(H1 0 H2).  lia.  
       assert((forall i j : nat, i < S n2 -> j <S n2 -> i < j -> f0 i < f0 j)).
       intros. apply H0; try lia.
       assert(forall i : nat, i < S n2 -> f0 i < S n2).
       intros. assert(f0 i0 <> S n2).  intro.  
       apply H0 in H4; try lia.  rewrite H5 in H4. 
       assert( f0 (S n2) < S (S n2)). apply H1. lia. lia.  
       assert( f0 i0 < S (S n2)). apply H1. lia. lia.   
       pose(IHn2 f0 H3 H4). 
       assert( i=S n2\/ ~(i=S n2)). 
       apply Classical_Prop.classic.
       destruct H5.      subst. 
       assert( f0 (S n2) < S (S n2)). apply H1. lia.
       assert( f0 (S n2-1) <f0 (S n2)). apply H0; try lia.
       assert(f0 (S n2-1) = (S n2-1)). apply e. lia. 
       lia. apply e. lia.  
Qed.

Import Classical_Prop.
Lemma le_n2_n1: forall n1 n2 f0  (p_n:nat->R), 
 S n1 >=n2->
 (forall i j : nat, i < n2 -> j < n2 -> i < j -> f0 i < f0 j)->
 (forall i : nat, i <  S n1 -> (exists s : nat, s < n2 /\ f0 s = i) -> p_n i <> 0)->
 (forall i : nat, i < n2 -> f0 i < S n1)->
 p_n (n1) =0->
 S n1>n2 .
Proof. intros. assert (~(S n1=n2)). intro. subst.  
       assert ( forall i, i < S n1 -> f0 i = i).
       apply map_1_1; try assumption.  
       pose( H2 n1). destruct n; try lia; try assumption.
       exists n1. split. lia. apply H5. lia.
       lia.         
Qed.



Lemma big_dapp'_app{s e:nat}:forall (p1 p2 : list R) (mu_n1 mu_n2 : list (dstate s e)) mu1 mu2 mu3,
big_dapp' p1 mu_n1 mu1->
big_dapp' p2 mu_n2 mu2->
big_dapp' (p1++p2) (mu_n1++mu_n2) mu3->
dstate_eq mu3 (d_app mu1 mu2).
Proof. induction p1; destruct mu_n1;  intros. simpl in *. 
       inversion_clear H0. 
       eapply dstate_eq_trans with mu2. 
       eapply big_dapp_eq. apply H2. apply H1.
       apply dstate_eq_sym. apply d_app_empty_l.
       inversion_clear H0. inversion_clear H0.
       simpl in *. 
       inversion H0; subst. 
       inversion H2; subst. 
       eapply IHp1 in H11; try apply H9; try apply H1.
       apply dstate_eq_trans with (d_app r0 (d_app d0 mu2)).
       apply d_app_eq. 
       eapply d_scale_eq; try apply H8; try apply H10.
       reflexivity. assumption. apply dstate_eq_sym.
       apply d_app_assoc'.
Qed.


  Lemma r111{s e:nat}: forall n1 n2 (x0:nat-> (dstate s e)) (x1 x2:dstate s e) (p_n:nat->R) f ,
   n1>=n2 ->
  (forall i j, i<n2-> j<n2-> i<j -> f i < f j ) ->
  (forall i, i<n1-> (exists s, s<n2 /\ f s = i) -> p_n i <>0 )->
  (forall i, i<n1-> ~(exists s, s < n2 /\ f s = i) -> p_n i =0 )->
  ((forall i, i<n2 -> f i < n1))->
  big_dapp' (fun_to_list p_n n1) (fun_to_list x0 n1) x1->
  big_dapp' (fun_to_list (fun i : nat => p_n (f i)) n2) (fun_to_list (fun i : nat => x0 (f i)) n2) x2->
  dstate_eq x1 x2.
  Proof. induction n1; intros. 
         destruct n2; intros; simpl in *. 
         eapply big_dapp_eq; try apply H5; try apply H6.  try lia.
         simpl in H5.  assert(p_n n1=0 \/ p_n n1<>0).
         apply Classical_Prop.classic. 
         destruct H7.
         assert(S n1 > n2). apply le_n2_n1 with f0 p_n; try assumption.
         pose(big_dapp_exsist (fun_to_list p_n n1) (fun_to_list x0 n1)). 
         destruct e0.  repeat rewrite fun_to_list_length. 
         reflexivity. 
         apply dstate_eq_trans with x3. 
         pose(big_dapp_exsist [0%R] [x0 n1]). destruct e0. 
         repeat rewrite fun_to_list_length. 
         reflexivity. rewrite H7 in *.
         assert(dstate_eq x1 (d_app x3 x4)).
         eapply big_dapp'_app; try apply H9; try apply H10; try apply H5.
         inversion H10; subst. inversion H18; subst. 
         inversion H17; subst. 
         apply dstate_eq_trans with ((d_app x3 (d_app (d_empty s e) (d_empty s e)))).
         assumption.  
         apply dstate_eq_trans with ((d_app x3 ((d_empty s e) ))).
         apply d_app_eq. reflexivity. apply d_app_empty_l.
         apply d_app_empty_r. lra.  
         
         apply IHn1 with n2 x0 p_n f0; try assumption. lia. 
         intros. apply H2. lia. assumption. 
         intros. apply H3. lia. assumption. 
         simpl in *. rewrite H7 in *. 
         intros. assert(f0 i <> n1). 
         intro. pose(H2 n1). destruct n. lia. 
         exists i. auto. assumption. apply H4 in H10. 
         lia. 

         destruct n2. pose (H3 n1). destruct H7. 
         apply e0. lia.    apply Classical_Pred_Type.all_not_not_ex.
         intros. apply Classical_Prop.or_not_and. left. lia. 
         simpl in *.

         assert(f0 n2 <S n1). apply H4. lia.
         assert((exists s : nat, s < S n2 /\ f0 s = n1)).
         apply Classical_Prop.NNPP. intro. apply H3 in H9. 
         destruct H7. assumption. lia. 
         destruct H9.   
         assert( ~(f0 n2<n1)). intro. destruct H9.
         rewrite <-H11 in H10. 
         assert(~(n2=x3)). intro. subst. lia.
         assert(~(x3<n2)). intro. apply H1 in H13; try lia. 
         assert(n2<x3). lia. lia.   
         assert(f0 n2=n1). lia.  rewrite H11 in *.
         pose (big_dapp_exsist (fun_to_list p_n n1 ) (fun_to_list x0 n1 )).
         destruct e0. repeat rewrite fun_to_list_length. 
         reflexivity. 
         pose (big_dapp_exsist (fun_to_list (fun i : nat => p_n (f0 i)) n2) 
         (fun_to_list (fun i : nat => x0 (f0 i) ) n2)). 
         destruct e0. repeat rewrite fun_to_list_length. 
         reflexivity. 
         assert( dstate_eq x4 x5). 
         apply (IHn1 n2 x0 _ _ p_n f0); try lia; try assumption.
         intros. apply H1. lia. lia. assumption.
         intros. apply H2. lia. destruct H15. 
         exists x6. split. lia. apply H15. 
         intros. apply H3. lia.
         assert(forall n:nat, ~ (n <  n2 /\ f0 n = i)).
         apply Classical_Pred_Type.not_ex_all_not . apply H15.
         apply   Classical_Pred_Type.all_not_not_ex.
         intros. apply Classical_Prop.or_not_and. 
         pose (H16 n).   apply Classical_Prop.not_and_or in n0. 
         destruct n0. assert(n=n2\/ n<> n2). apply Classical_Prop.classic.
         destruct H18. right. rewrite H18. rewrite H11. lia.   left. lia.
         right. assumption.    
         intros. rewrite <-H11. apply H1; try lia.
         pose(big_dapp_exsist [p_n n1] [x0 n1]). destruct e0. 
         repeat rewrite fun_to_list_length. 
         reflexivity. 
         assert( dstate_eq x1 (d_app x4 x6)). eapply big_dapp'_app;
         try apply H12; try apply H15; try apply H5.
         assert( dstate_eq x2 (d_app x5 x6)). eapply big_dapp'_app;
         try apply H6; try apply H15; try apply H13.
         eapply dstate_eq_trans. apply H16. 
         apply dstate_eq_sym. eapply dstate_eq_trans. apply H17.
         apply d_app_eq; try apply dstate_eq_sym; try assumption; try reflexivity.
Qed.


  

  Lemma big_Oplus_solve:  forall (p_n:nat->R) F_n n1 n2 f , 
  n1>=n2 ->
  (forall i j, i<n2-> j<n2-> i<j -> f i < f j ) ->
  (forall i, i<n1-> (exists s, s<n2 /\ f s = i) -> p_n i <>0 )->
  (forall i, i<n1-> ~(exists s, s < n2 /\ f s = i) -> p_n i =0 )->
  ((forall i, i<n2 -> f i < n1))->
  distribution_formula (big_pOplus (fun i : nat => p_n (f i)) (fun i : nat => F_n (f i)) n2)->
  big_pOplus p_n F_n n1->>
  big_pOplus (fun i=> p_n (f i)) (fun i=> F_n (f i)) n2.
  Proof. intros. unfold assert_implies. intros. 
         inversion_clear H6. apply big_pOplus_sat' in H9. 
         destruct H9. destruct H6. destruct H6. 
         destruct H9. econstructor. assumption. assumption.
         pose(big_dapp_exsist (fun_to_list (fun i : nat => p_n (f0 i)) n2) 
         (fun_to_list (fun i : nat => x0 (f0 i)) n2)).
         destruct e0. repeat rewrite fun_to_list_length. reflexivity.
         eapply big_pOplus_sat. 
         apply H11. 
         apply dstate_eq_trans with x1. assumption.
         apply r111 with n1 n2 x0 p_n f0; try assumption. 
         intros. 
         split. 
         apply H10; try assumption. apply H4. assumption.
         apply H10; try assumption. apply H4. assumption.
         auto.
Qed.

Lemma big_dapp_eq_bound{s e:nat}: forall p_n q_n (mu_n: list (dstate s e)) mu,
Forall_two (fun i j: R=> i=j) p_n q_n->
big_dapp' p_n mu_n mu->
big_dapp' q_n mu_n mu .
Proof. induction p_n; intros; destruct mu_n; destruct q_n; inversion_clear H1; try econstructor;
        try inversion_clear H0. rewrite H1 in *. assumption. auto.
Qed.


Lemma big_pOplus_p_eq_bound: forall p_n q_n F_n n,
(forall i, i< n -> p_n i= q_n i)->
(big_pOplus p_n  F_n n->> big_pOplus q_n F_n n).
Proof. intros. unfold assert_implies. intros. inversion_clear H1.
        inversion_clear H4. econstructor. assumption.
        inversion_clear H3. econstructor.
        rewrite big_pOplus_get_pro in *.
        rewrite  <-Forall_fun_to_list in *. intros. rewrite<- H0; try assumption.
        apply H4. assumption. 
        rewrite sum_over_list_big_pOplus in *. 
        rewrite (big_sum_eq_bounded _ p_n); try assumption. 
        intros. symmetry. apply H0. assumption.   
        econstructor. rewrite big_pOplus_get_pro in *.
        apply (big_dapp_eq_bound  _ (fun_to_list q_n n)) in H1.
        apply H1. apply Forall_two_forall. assumption.
        assumption.  
        rewrite (Forall_two_nth  _ _ _ (d_empty s e) (1%R, SPure (PBexp <{BTrue}>))).
        rewrite (Forall_two_nth  _ _ _ (d_empty s e) (1%R, SPure (PBexp <{BTrue}>))) in H6.
        destruct H6. split. rewrite big_pOplus_length in *. assumption.
        rewrite big_pOplus_length in *.
        intros.  pose( H6 i H7). split; 
        try rewrite snd_nth_big_pOplus in *;
        try rewrite fst_nth_big_pOplus in *; try lia; 
        try apply a; try rewrite H0; try lia; try assumption. 
Qed.

Lemma rule_OCon''_aux:forall (s e:nat) (pF1 pF2:pro_formula) (mu_n:list (dstate s e)) 
(P:(dstate s e)-> (R* State_formula)->Prop) (Q:State_formula->State_formula->Prop), 
(forall (i :dstate s e) (j k:R*State_formula), ((fst j)=(fst k))->
(P i j) -> Q (snd j) (snd k)->(P i k))->
(get_pro_formula pF1 = get_pro_formula pF2)->
(Forall_two Q (pro_to_npro_formula pF1) (pro_to_npro_formula pF2) )->
(Forall_two P mu_n pF1 )->
Forall_two P  mu_n pF2.
Proof. induction pF1; intros; destruct pF2; simpl in *.
inversion_clear H3. econstructor. inversion_clear H2.
inversion_clear H2. inversion_clear H3. inversion_clear H2. 
econstructor. apply H0 with a; try assumption. injection H1. auto. 
eapply IHpF1. apply H0. injection H1. auto. auto. auto.
Qed.



Theorem  rule_OCon'': forall (pF1 pF2:pro_formula),
(get_pro_formula pF1 = get_pro_formula pF2)->
(Forall_two (fun (f_i g_i: State_formula) => f_i ->> g_i) (pro_to_npro_formula pF1) (pro_to_npro_formula pF2))->
(pF1 ->> pF2).
Proof. intros.    unfold assert_implies. intros. 
inversion_clear H2. inversion_clear H5.
econstructor. intuition. inversion_clear H4.
econstructor; rewrite <-H0; assumption.  
econstructor. rewrite<-H0. apply H2. assumption. 
eapply rule_OCon''_aux with (P:=(fun (mu_i : dstate s e)
(pF_i : R * State_formula) => (0 < fst pF_i)%R -> sat_State mu_i (snd pF_i) /\ d_trace mu_i = d_trace mu)) 
(Q:=(fun f_i g_i : State_formula => f_i ->> g_i)). 
intros. destruct H8.  rewrite H5. assumption.
split.  rewrite <-sat_Assert_to_State. apply H9.   
rewrite sat_Assert_to_State. assumption. assumption.
apply H0.  assumption. assumption.  
Qed.

Lemma fun_to_list_big_Oplus_eq: forall n F_n,
fun_to_list F_n n = big_Oplus F_n n.
Proof. induction n; intros; simpl; try f_equal; auto.
Qed.

Lemma norm_vec_1: forall n x, (x<2^n) ->norm (Vec (2^n) x)=1 .
Proof. intros.  unfold norm.   rewrite <-inner_trace'. rewrite Vec_inner_1.
       unfold c_to_Vector1. Msimpl. 
       rewrite trace_I. simpl. rewrite sqrt_1. reflexivity. assumption.
Qed.

(* Lemma Cmult_pow: forall c , 
c * c= c² .
Proof.
  
Qed. *)

Lemma s_r_t_relation: forall i, 
i< r -> i*(2^t) /r < (2^t).
Proof. intros. pose H.  
apply Nat.div_lt_upper_bound. unfold r. lia.
apply Nat.mul_lt_mono_pos_r. apply pow_gt_0.
assumption.   
Qed.

Lemma i_j_le: forall i j, 
i< r-> j<r->
i< j -> i*(2^t) /r < j*(2^t) /r.
Proof. intros. apply INR_lt. pose Ht.  pose H.
pose (e  i H0). pose (e j H1). 
destruct e0. destruct e1. 
unfold Rdiv in *. rewrite (Rmult_comm  _ (/r)) in H3.
rewrite (Rmult_comm  _ (/r)) in H4. 
rewrite Rmult_assoc in H3.
rewrite Rmult_assoc in H4.
rewrite (Rmult_comm   (/r)) in H3.
rewrite (Rmult_comm  (/r)) in H4.
destruct H3. destruct H4.
rewrite <-(div_INR _ _ x0).
rewrite <-(div_INR _ _ x1). unfold Rdiv.
apply Rmult_lt_compat_r. apply Rinv_0_lt_compat.
rewrite IZR_INR_0.
apply lt_INR. unfold r. lia.  
 apply lt_INR. apply Nat.mul_lt_mono_pos_r.
apply pow_gt_0. assumption. unfold r. lia.
unfold Rdiv in *.
rewrite <-H6. f_equal. rewrite mult_INR. f_equal.
rewrite pow_INR. f_equal. unfold r. lia.
unfold Rdiv in *.
rewrite <-H5. f_equal. rewrite mult_INR. f_equal.
rewrite pow_INR. f_equal. 
Qed.

Lemma i_j_neq: forall i j, 
i< r-> j<r->
i<> j -> i*(2^t) /r <> j*(2^t) /r.
Proof. intros. intro. 
assert(INR (i * 2 ^ t / r) = INR (j * 2 ^ t / r )).
rewrite H3. reflexivity. 
pose Ht.  pose H.
pose (e  i H0). pose (e j H1). 
destruct e0. destruct e1. 
unfold Rdiv in *.
 rewrite (Rmult_comm  _ (/r)) in H5.
rewrite (Rmult_comm  _ (/r)) in H6. 
rewrite Rmult_assoc in H5.
rewrite Rmult_assoc in H6.
rewrite (Rmult_comm   (/r)) in H5.
rewrite (Rmult_comm  (/r)) in H6.
destruct H5. destruct H6.
rewrite <-(div_INR _ _ x0) in H4.
rewrite <-(div_INR _ _ x1) in H4.
unfold Rdiv in *. 
apply Rmult_eq_reg_r in H4.
apply INR_eq in H4.  
apply Nat.mul_cancel_r in H4. 
lia. lia. apply Rinv_neq_0_compat.
 rewrite IZR_INR_0. unfold r. intro.  apply INR_eq in H9.
 lia. lia.   
unfold Rdiv in *.
rewrite <-H8. f_equal. rewrite mult_INR. f_equal.
rewrite pow_INR. f_equal. unfold r. lia.
unfold Rdiv in *.
rewrite <-H7. f_equal. rewrite mult_INR. f_equal.
rewrite pow_INR. f_equal. 
Qed.

Lemma mod_eq_1: forall a b c ,
c<>0->
a>=b -> a mod c= b mod c ->
exists m:nat, a= m*c +b.
Proof. intros.  rewrite Nat.mod_eq in H2; try lia.
  rewrite Nat.mod_eq in H2; try lia. 
exists (a/c - b0/c).
rewrite Nat.mul_sub_distr_r.
rewrite Nat.mul_comm.  
rewrite (Nat.mul_comm _ c).
apply repad_lemma2 in H2; try apply Nat.mul_div_le; try lia.  
rewrite H2 at 2. 
rewrite Nat.add_assoc.
rewrite Nat.add_sub_assoc; try try apply Nat.mul_div_le; try lia.  
Qed.

Lemma divide_pow_l: forall a b c,  b<>0->
 Nat.divide (a) (c)-> Nat.divide (a) (c^b).
 Proof. induction b0; intros. simpl. lia. 
        assert(b0=0\/b0<>0). 
       apply Classical_Prop.classic. destruct H2. subst.
       simpl. rewrite Nat.mul_1_r. assumption.
       simpl. apply Nat.divide_mul_r. apply IHb0; assumption.
Qed.

Lemma divide_pow_r: forall b a c, 
 a>1->b<>0->
 Nat.divide (a) (c^b) ->(exists y, y <>1 /\ Nat.divide y c /\ (Nat.divide a y \/ Nat.divide y a)).
Proof. induction b0; intros; simpl. lia.
       assert(b0=0\/b0<>0). 
       apply Classical_Prop.classic. destruct H3.
       subst. simpl in *. rewrite Nat.mul_1_r in *. 
       exists a.  intuition. 
       simpl in *.  
       assert(Nat.divide a c \/ ~(Nat.divide a c)).
       apply Classical_Prop.classic. destruct H4.  
       exists a. intuition.  
       assert(Nat.gcd a c =1 \/ ~(Nat.gcd a c =1)).
       apply Classical_Prop.classic. 
       destruct H5. 
       apply (Nat.gauss _ _ (c^b0)) in H5. 
       apply IHb0; try assumption. assumption. 
       exists (Nat.gcd a c).  
       split. assumption. split. apply Nat.gcd_divide_r. right. 
       apply Nat.gcd_divide_l.
Qed.

Lemma divide_trans: forall a b c, Nat.divide a b ->
Nat.divide b c-> Nat.divide a c.
Proof. intros.
unfold Nat.divide in *. destruct H0.
destruct H1. 
exists (x0*x1). rewrite H1. rewrite H0.
rewrite Nat.mul_assoc. rewrite (Nat.mul_comm x1 x0). reflexivity.
Qed.


Lemma gcd_pow: forall a b c, 
a>1/\ c<>0->
Nat.gcd a c=1-> Nat.gcd (a^b) c=1.
Proof. induction b0; intros; simpl. reflexivity.
       pose H1. apply IHb0 in e. 
       apply Classical_Prop.NNPP.
       intro. 
       remember ((Nat.gcd (a * a ^ b0) c)).
       pose(Nat.gcd_divide_r (a * a ^ b0) c ).
       pose(Nat.gcd_divide_l (a * a ^ b0) c ). 
       rewrite <-Heqn in *. 
       assert(a*a^b0= a^(1+b0)). simpl. reflexivity.
       rewrite H3 in *. 
       apply divide_pow_r in d0.  destruct d0.   
       destruct H4. destruct H5. destruct H6.
       assert(Nat.divide n  a). apply divide_trans with x0; try assumption.
        assert(Nat.divide n (Nat.gcd a c)).
         apply(Nat.gcd_divide_iff). split; assumption.
         rewrite H1 in *. 
         apply Nat.divide_pos_le in H8.  assert(n=0). lia.
         rewrite H9 in *. apply Nat.divide_0_l in H7. lia. lia.
        assert(Nat.divide x0 c).
        apply divide_trans with n; try assumption. 
        assert(Nat.divide x0 (Nat.gcd a c)).
         apply(Nat.gcd_divide_iff). split; assumption.
         rewrite H1 in *. 
         apply Nat.divide_pos_le in H8.  assert(x0=0).  lia.  
         rewrite H9 in *. apply Nat.divide_0_l in H5. lia. lia. 
         assert(n<>0). intro. rewrite H4 in *. 
         apply Nat.divide_0_l in d. lia. lia. lia. lia.   
Qed.


Lemma  norm_Us: forall i, i< r -> Nat.gcd x N =1-> norm (Us i) =1 .
Proof. 
intros. unfold Us. pose H.
rewrite norm_scale.
unfold norm. rewrite <-inner_trace' . 
rewrite Msum_adjoint. rewrite Mmult_Msum_distr_l. 
rewrite big_sum_trace.  
rewrite (big_sum_eq_bounded _ (fun i0 : nat =>
 ( Cmult ((cos (- (2 * PI) * (i / r) * i0),
    sin (- (2 * PI) * (i / r) * i0))^*)  (cos (- (2 * PI) * (i / r) * i0),
    sin (- (2 * PI) * (i / r) * i0)) ))).
 rewrite (big_sum_eq_bounded _ (fun i0 : nat => C1)).
 rewrite big_sum_constant. rewrite times_1_n. simpl. 
rewrite Cmod_inv. rewrite Cmod_R. rewrite Rabs_right. 
simpl. rewrite Rinv_l. reflexivity.
apply sqrt_neq_0_compat.  unfold r.
rewrite IZR_INR_0.   apply lt_INR. lia. 
apply Rgt_ge. apply sqrt_lt_R0. unfold r.
rewrite IZR_INR_0.   apply lt_INR. lia.
apply RtoC_neq.
apply sqrt_neq_0_compat.  unfold r.
rewrite IZR_INR_0.   apply lt_INR. lia. 
intros. rewrite <-Cmod_sqr. unfold Cmod. simpl fst. simpl snd.
repeat rewrite <-Rsqr_pow2. rewrite Rplus_comm. rewrite sin2_cos2.
simpl. Csimpl. rewrite RtoC_mult. rewrite sqrt_sqrt. reflexivity.
lra.  intros. rewrite Mmult_Msum_distr_r.  rewrite big_sum_trace.
erewrite (@big_sum_unique C C_is_monoid _ ). reflexivity.
exists x0. split. assumption. rewrite Mscale_mult_dist_r.
rewrite Mscale_adj.
repeat rewrite Mscale_mult_dist_l.
rewrite Vec_inner_1. unfold c_to_Vector1. split.  
Msimpl. rewrite Mscale_assoc. rewrite trace_mult_dist.
rewrite trace_I. Csimpl. rewrite Cmult_comm. reflexivity.
intros.  rewrite Mscale_mult_dist_r.
rewrite Mscale_adj.
repeat rewrite Mscale_mult_dist_l.
rewrite Vec_inner_0. unfold c_to_Vector1.
Msimpl. rewrite Zero_trace. reflexivity. 
intro.
assert(x'>=x0\/ ~(x'>=x0)).
apply Classical_Prop.classic. 
destruct H6.  
apply mod_eq_1 in H5. destruct H5.
assert(x^(x'-x0)=x^x' / x^x0). 
rewrite Nat.pow_sub_r. reflexivity. unfold x.  lia. lia.   
assert(x^x'/ (x^x0) mod N =1). 
rewrite H5. rewrite Nat.add_comm.
rewrite <-(Nat.mul_1_l (x ^ x0)) at 1.
rewrite Nat.div_add_l. 
 assert(x1 * N / x ^ x0= ((x1 / x^(x0)) * N)).
 rewrite Nat.mul_comm.
 rewrite Nat.divide_div_mul_exact.
 rewrite Nat.mul_comm. reflexivity.
 apply Nat.pow_nonzero. unfold x. lia.
 assert(Nat.divide (x ^ x0) (x1*N)).
 apply (Nat.divide_add_cancel_r _ (x^x0)).
 apply Nat.divide_refl. rewrite Nat.add_comm. 
 rewrite <-H5.  
 rewrite <-Nat.mod_divide.
 rewrite Nat.mod_divides. 
 exists (x ^ (x' - x0)). rewrite <-Nat.pow_add_r.
 f_equal. lia.  
 unfold x. apply Nat.pow_nonzero.    lia.
 unfold x. apply Nat.pow_nonzero.    lia.
 rewrite Nat.mul_comm in H8. 
 apply Nat.gauss in H8. assumption.
 apply gcd_pow. unfold x. unfold N. lia. assumption. 
rewrite H8. 
rewrite Nat.mod_add. rewrite Nat.mod_small. reflexivity.
unfold N. lia. unfold N. lia. 
unfold x. apply Nat.pow_nonzero.    lia.
rewrite<- H7 in H8. 
pose Hr. destruct a0. apply H10 in H8. 
unfold r in *. lia. unfold N. lia.
apply Nat.pow_le_mono_r. unfold x. lia. lia.
symmetry in H5.
apply mod_eq_1 in H5. destruct H5.
assert(x^(x0-x')=x^x0 / x^x'). 
rewrite Nat.pow_sub_r. reflexivity. unfold x.  lia. lia.   
assert(x^x0/ (x^x') mod N =1). 
rewrite H5. rewrite Nat.add_comm.
rewrite <-(Nat.mul_1_l (x ^ x')) at 1.
rewrite Nat.div_add_l. 
 assert(x1 * N / x ^ x'= ((x1 / x^(x')) * N)).
 rewrite Nat.mul_comm.
 rewrite Nat.divide_div_mul_exact.
 rewrite Nat.mul_comm. reflexivity.
 apply Nat.pow_nonzero. unfold x. lia.
 assert(Nat.divide (x ^ x') (x1*N)).
 apply (Nat.divide_add_cancel_r _ (x^x')).
 apply Nat.divide_refl. rewrite Nat.add_comm. 
 rewrite <-H5.  
 rewrite <-Nat.mod_divide.
 rewrite Nat.mod_divides. 
 exists (x ^ (x0 - x')). rewrite <-Nat.pow_add_r.
 f_equal. lia.  
 unfold x. apply Nat.pow_nonzero.    lia.
 unfold x. apply Nat.pow_nonzero.    lia.
 rewrite Nat.mul_comm in H8. 
 apply Nat.gauss in H8. assumption.
 apply gcd_pow. unfold x. unfold N. lia. assumption.  
rewrite H8. 
rewrite Nat.mod_add. rewrite Nat.mod_small. reflexivity.
unfold N. lia. unfold N. lia. 
unfold x. apply Nat.pow_nonzero.    lia.
rewrite<- H7 in H8. 
pose Hr. destruct a0. apply H10 in H8. 
unfold r in *. lia. unfold N. lia.
apply Nat.pow_le_mono_r. unfold x. lia. lia.
apply Nat.lt_trans with (N).
apply Nat.mod_upper_bound. unfold N . lia.
pose HNL. lia.         
apply Nat.lt_trans with (N).
apply Nat.mod_upper_bound. unfold N . lia.
pose HNL. lia.
apply Nat.lt_trans with (N).
apply Nat.mod_upper_bound. unfold N . lia.
pose HNL. lia.    
Qed.

Lemma times_n_R: forall (r:R) (n:nat), 
times_n r n = Rmult r n.
Proof. induction n; intros. simpl. rewrite Rmult_0_r. reflexivity.
       simpl times_n. 
        rewrite IHn. rewrite S_O_plus_INR. rewrite Rmult_plus_distr_l.
        rewrite Rmult_1_r. reflexivity.
Qed.


  Lemma big_Oplus_solve': 
  Nat.gcd x N = 1 ->
  big_pOplus
  (fun i : nat =>
   (norm
      (@U_v (Nat.sub t O)
      (Nat.sub (Init.Nat.add t L) 0) 0 t 0 (t + L) (∣ i ⟩_ (t - 0) × ⟨ i ∣_ (t - 0))
         (/ √ r .* big_sum (fun s : nat => ∣ s * 2 ^ t / r ⟩_ (t) ⊗ Us s) r)) ^ 2)%R)
  (fun i : nat =>
   P i /\s
   (| (/
       norm
         (@U_v (Nat.sub t O)
         (Nat.sub (Init.Nat.add t L) 0) 0 t 0 (t + L) (∣ i ⟩_ (t - 0) × ⟨ i ∣_ (t - 0))
            (/ √ r .* big_sum (fun s : nat => ∣ s * 2 ^ t / r ⟩_ (t) ⊗ Us s) r)))%R
      .* @U_v (Nat.sub t O)
      (Nat.sub (Init.Nat.add t L) 0) 0 t 0 (t + L) (∣ i ⟩_ (t - 0) × ⟨ i ∣_ (t - 0))
           (/ √ r .* big_sum (fun s : nat => ∣ s * 2 ^ t / r ⟩_ (t) ⊗ Us s) r) >[ 0, t + L])) 
  (2 ^ (t - 0)) ->> big_pOplus (fun _ : nat => (/ r)%R) (fun s : nat => P' s) r .
Proof.   pose Hr. pose HtL. pose H. 
         assert(forall i j x0, ∣ i ⟩_ (t) × ⟨ i ∣_ (t) ⊗ I (2 ^ L) × (∣ j ⟩_ (t) ⊗ Us x0)=
         (@Mmult ((2^t) * ((2^L))) ((2^t) * ((2^L)))  1 
         (∣ i ⟩_ (t) × ⟨ i ∣_ (t) ⊗ I (2 ^ L)) (∣ j ⟩_ (t) ⊗ Us x0) ) ).
         reflexivity. intros.  

         assert(forall i, i< r->(norm
         (@U_v t (Init.Nat.add t L) 0 t 0 (t + L)  (∣ i * 2 ^ t / r ⟩_ (t) × ⟨ i * 2 ^ t / r ∣_ (t))
         (/ √ r .* big_sum (fun s : nat => ∣ s * 2 ^ t / r ⟩_ (t) ⊗ Us s) r)))= (/ √ r)%R).
         intros. unfold U_v. type_sovle. 
         rewrite <-Mscale_Msum_distr_r.
         repeat rewrite Nat.mul_1_l.
         rewrite Mmult_Msum_distr_l. 
         rewrite (@big_sum_unique (Matrix ((2^t) * ((2^L))) 1) (M_is_monoid ((2^t) * ((2^L))) 1) (/ √ r .* (∣ i * 2 ^ t / r ⟩_ (t) ⊗ Us i)) 
          ). 
          assert(2^(t)* 2^L= 2^(t+L)). type_sovle'. destruct H3.
          rewrite norm_scale.
          rewrite norm_kron. rewrite norm_vec_1. rewrite norm_Us. rewrite Rmult_1_r. rewrite Rmult_1_r.
          rewrite Cmod_inv.  rewrite Cmod_R. rewrite Rabs_right. reflexivity.
          apply Rgt_ge. apply sqrt_lt_R0. unfold r.
          rewrite IZR_INR_0.   apply lt_INR. lia. apply RtoC_neq.  apply sqrt_neq_0_compat. unfold r.
          rewrite IZR_INR_0.   apply lt_INR. lia. assumption. assumption.  
          apply s_r_t_relation. assumption.

         exists i.  
         split. assumption.  split.
         rewrite Mscale_mult_dist_r. rewrite <-H0. 
         rewrite kron_mixed_product. Msimpl.  rewrite Mmult_assoc. rewrite Vec_inner_1.
         unfold c_to_Vector1. Msimpl.  reflexivity. apply WF_vec.
            apply s_r_t_relation. assumption.
            apply s_r_t_relation. assumption.
         intros. rewrite Mscale_mult_dist_r. rewrite <-H0.  
         rewrite kron_mixed_product. Msimpl.  rewrite Mmult_assoc. rewrite Vec_inner_0.
         unfold c_to_Vector1. Msimpl. reflexivity. apply i_j_neq; try assumption.
         apply s_r_t_relation. assumption.   apply s_r_t_relation. assumption. 
         apply WF_mult; try apply WF_adjoint;
         apply WF_vec.   apply s_r_t_relation. assumption. 
         apply s_r_t_relation. assumption.
         
         eapply implies_trans. type_sovle. 
         eapply (big_Oplus_solve _ _ _ r  (fun s=> (s * 2^t/r))).  admit.
         intros. apply i_j_le; try assumption.  
         intros. destruct H4. destruct H4. rewrite<-H5. rewrite Nat.sub_0_r in H2.  
         rewrite (H2 x0). apply Rgt_neq_0. rewrite <-Rsqr_pow2. apply Rlt_0_sqr.
         apply Rinv_neq_0_compat. apply sqrt_neq_0_compat.  unfold r.
         rewrite IZR_INR_0.   apply lt_INR. lia.  assumption. 

         intros. unfold U_v. type_sovle. 
         rewrite <-Mscale_Msum_distr_r.
         repeat rewrite Nat.mul_1_l.
         rewrite Mmult_Msum_distr_l. 
         rewrite big_sum_0_bounded. simpl. rewrite Rmult_1_r. 
         apply Rmult_eq_0_compat_l.
         apply norm_zero_iff_zero; try reflexivity. 
         assert(2^(t)* 2^L= 2^(t+L)). type_sovle'. destruct H5. auto_wf.
         
         intros. rewrite Mscale_mult_dist_r. rewrite <-H0. 
         rewrite kron_mixed_product. Msimpl.  rewrite Mmult_assoc. rewrite Vec_inner_0.
         unfold c_to_Vector1. Msimpl. reflexivity.  
         intro. destruct H4. exists x0. split. assumption. auto. assumption.
         apply s_r_t_relation. assumption.  
         intros.   apply s_r_t_relation. assumption. 

         simpl.
         econstructor. try rewrite big_pOplus_get_pro. 
         apply Forall_fun_to_list. intros. apply pow2_ge_0.
         rewrite sum_over_list_big_pOplus.   
         rewrite (@big_sum_eq_bounded R (R_is_monoid) _ (fun i:nat => (/r)%R)).
         rewrite big_sum_constant. rewrite times_n_R. rewrite Rinv_l. reflexivity. 
         apply not_0_INR. unfold r. lia.  
         intros. rewrite Nat.sub_0_r in H2.   rewrite H2. rewrite Rmult_1_r. 
         rewrite <-Rinv_mult_distr_depr. rewrite sqrt_sqrt. reflexivity.   unfold r.
         rewrite IZR_INR_0.   apply le_INR. lia. apply sqrt_neq_0_compat.
         rewrite IZR_INR_0.   apply lt_INR. lia.
         apply sqrt_neq_0_compat. rewrite IZR_INR_0.   apply lt_INR. lia.
         assumption. 
         

          unfold P. unfold P'.  eapply implies_trans.
          eapply (big_pOplus_p_eq_bound _ (fun _ : nat => (/ r)%R)).
          intros. rewrite Nat.sub_0_r in H2.   rewrite (H2 i).  
          rewrite<- Rsqr_pow2. rewrite Rsqr_inv_depr. rewrite Rsqr_pow2.
          simpl. rewrite Rmult_1_r.  rewrite sqrt_sqrt. reflexivity.   unfold r.
         rewrite IZR_INR_0.   apply le_INR. lia. apply sqrt_neq_0_compat.
         rewrite IZR_INR_0.   apply lt_INR. lia.   assumption. 
          apply rule_OCon''. repeat  rewrite big_pOplus_get_pro. reflexivity.
          repeat rewrite big_pOplus_get_npro. repeat rewrite <-fun_to_list_big_Oplus_eq.
          apply Forall_two_forall. intros. apply rule_Conj_split_l.
Admitted.

Fixpoint d_update_cstate_list{ s e:nat} i a (mu_n:list (dstate s e)) :=
  match mu_n with 
  | nil => [] 
  |mu::mu_n' => (d_update_cstate i a mu) :: (d_update_cstate_list  i a mu_n')
  end. 

Lemma d_update_cstate_empty{s e:nat}: forall i a, 
dstate_eq  (d_update_cstate i a (d_empty s e)) (d_empty s e).
Proof. unfold dstate_eq. intros. simpl in *. reflexivity.
  
Qed.


Lemma d_update_cstate_map2_aux{s e:nat}: forall i a (mu1 mu2:list (state s e)), 
 (d_update_cstate_aux i a (StateMap.Raw.map2 option_app mu1  mu2)) =
 ( StateMap.Raw.map2 option_app (d_update_cstate_aux i a mu1 ) 
(d_update_cstate_aux i a mu2 )).
Proof.  induction mu1; intros . simpl in *.
repeat rewrite map2_r_refl. reflexivity. destruct a0.   
induction mu2.  repeat rewrite map2_nil_r.  reflexivity.
destruct a0. simpl. 
destruct (Cstate_as_OT.compare c c0). simpl.
rewrite app_fix_2. rewrite app_fix_2. rewrite app_fix_2.   
rewrite IHmu1.  remember ([(c_update i (aeval (c, q) a) c, q)]).  
remember ((d_update_cstate_aux i a mu1)).
remember ([(c_update i (aeval (c0, q0) a) c0, q0)]). 
simpl. rewrite app_fix_2. rewrite <-Heql2.  
remember ((d_update_cstate_aux i a mu2)).
remember ((StateMap.Raw.map2 option_app l2 l3)).
rewrite map2_assoc. reflexivity.
simpl. rewrite app_fix_2. rewrite app_fix_2. rewrite app_fix_2.
rewrite IHmu1.   rewrite map2_assoc. rewrite map2_assoc.  
remember ((d_update_cstate_aux i a mu1)).
remember ((d_update_cstate_aux i a mu2)). f_equal.  
rewrite <-map2_assoc.  rewrite (map2_comm l ). 
rewrite map2_assoc. f_equal.  
unfold Cstate_as_OT.eq in e0.
rewrite e0.
simpl. rewrite (state_eq_aexp ((c0, q) ) ((c0, q0) )); try reflexivity.
MC.elim_comp. 
rewrite (state_eq_aexp _  ((c0, q0) )); try reflexivity. 
simpl. 
rewrite app_fix_2.  rewrite app_fix_2. rewrite app_fix_2.    
rewrite app_fix. unfold state in IHmu2.  
rewrite IHmu2. simpl d_update_cstate_aux. 
rewrite app_fix_2.   
rewrite map2_assoc. rewrite map2_assoc. 
 rewrite (map2_comm 
([(c_update i (aeval (c0, q0) a) c0, q0)])). 
rewrite <-map2_assoc.  rewrite <-map2_assoc.
rewrite <-map2_assoc.
f_equal.    rewrite map2_assoc. rewrite map2_assoc.
rewrite (map2_comm ([(c_update i (aeval (c0, q0) a) c0, q0)])).
reflexivity. 
Qed.

Lemma d_update_cstate_dapp{s e:nat}: forall i a (mu1 mu2:dstate s e), 
dstate_eq  (d_update_cstate i a (d_app mu1 mu2)) (d_app (d_update_cstate i a mu1 )
(d_update_cstate i a mu2 )).
Proof. intros i a (mu1, IHmu1)  (mu2, IHmu2). unfold dstate_eq. unfold d_app. unfold  StateMap.map2.
simpl StateMap.this. apply d_update_cstate_map2_aux. 
Qed.


Lemma map_update{s e:nat}: forall i a (r:R) (mu1 :list (state s e)),
StateMap.Raw.map (fun x0 : qstate s e => q_scale r x0)
(d_update_cstate_aux i a mu1) = 
d_update_cstate_aux i a (StateMap.Raw.map (fun x0 : qstate s e => q_scale r x0) mu1).
Proof. induction mu1. simpl. reflexivity. destruct a0.  
      simpl.  rewrite app_fix_2. rewrite app_fix_2.   
      pose (@map_map2_distr s e ([(c_update i (aeval (c, q) a) c, q)]) 
      ((d_update_cstate_aux i a mu1)) r0).  
      unfold q_scale in *.  unfold qstate in *. 
      rewrite <-e0. simpl StateMap.Raw.map. f_equal. 
      rewrite (state_eq_aexp _  ((c, r0.*q) )); try reflexivity. 
      rewrite IHmu1. reflexivity.
Qed.   

Lemma d_scale_not_0_update{s e:nat}: forall i a r (mu1 :dstate s e),
dstate_eq (d_scale_not_0 r (d_update_cstate i a mu1))
  (d_update_cstate i a (d_scale_not_0 r mu1)).
Proof. intros i a r (mu1, IHmu1). unfold dstate_eq. simpl in *.
    apply map_update.
Qed. 


Lemma d_scale_update{s e:nat}: forall i a r (mu1 mu2 mu3:dstate s e),
d_scale r mu1 mu2->
d_scale r (d_update_cstate i a mu1) mu3->
dstate_eq mu3 (d_update_cstate i a mu2).
Proof. intros. inversion H0; subst. inversion_clear H0. inversion_clear H1. 
apply dstate_eq_sym. apply d_update_cstate_empty. lra. lra.
inversion H1; subst. lra.  apply d_scale_not_0_update.
Qed.

  
Lemma big_dapp'_update{s e:nat}: forall p_n (mu_n:list (dstate s e)) mu1 mu2 i a, 
big_dapp' p_n mu_n mu1->
big_dapp' p_n (d_update_cstate_list i a mu_n) mu2->
dstate_eq mu2 (d_update_cstate i a mu1).
Proof. induction p_n; intros. inversion_clear H0. inversion_clear H1.
       apply dstate_eq_sym. apply d_update_cstate_empty.
       inversion H0; subst. inversion H1; subst.  
       eapply dstate_eq_trans with (d_app (d_update_cstate i a0 r0) (d_update_cstate i a0 d)); try  
       apply dstate_eq_sym; try
       apply d_update_cstate_dapp. 
       apply d_app_eq. apply dstate_eq_sym. eapply d_scale_update.
       apply H4. apply H9. 
       apply dstate_eq_sym.
       eapply IHp_n. apply H7. assumption.
Qed.

Lemma d_update_cstate_length{s e:nat}: forall i a (mu_n:list (dstate s e)),
length (d_update_cstate_list i a mu_n) = length mu_n.
Proof. intros. induction mu_n. simpl. reflexivity. simpl. f_equal. auto.
  
Qed.


Lemma d_update_cstate_eq{s e:nat}: forall i a (mu1 mu2: (dstate s e)),
dstate_eq mu1 mu2->
dstate_eq (d_update_cstate i a mu1) (d_update_cstate i a mu2).
Proof. intros i a (mu1, IHmu1) (mu2, IHmu2). unfold dstate_eq. unfold d_update_cstate. simpl. 
intros. subst.  auto. 
Qed.

Lemma snd_nth_npro_to_pro_formula: forall nF p_n i,
length nF=length p_n->
(snd (nth i (npro_to_pro_formula nF p_n) (1%R, SPure (PBexp <{BTrue}>))))=
nth i nF <{true}>.
Proof. induction nF; intros. simpl. destruct p_n. simpl. destruct i. simpl. reflexivity. 
reflexivity. simpl. destruct i; reflexivity.
 destruct p_n. simpl in *. lia.   simpl. destruct i. reflexivity.
 rewrite IHnF. reflexivity. injection H0. auto.     
Qed.


Lemma fst_nth_npro_to_pro_formula: forall nF p_n i,
length nF=length p_n->
(fst (nth i (npro_to_pro_formula nF p_n) (1%R, SPure (PBexp <{BTrue}>))))=
nth i p_n (1%R).
Proof. induction nF; intros. simpl. destruct p_n. simpl. destruct i. simpl. reflexivity. 
reflexivity. simpl in *. lia. 
 destruct p_n. simpl in *. lia.   simpl. destruct i. reflexivity.
 rewrite IHnF. reflexivity. injection H0. auto.     
Qed.


Lemma Assn_sub_Plus_aux:forall (s e:nat) (pF1 pF2:pro_formula) (mu_n:list (dstate s e)) v a 
(P:(dstate s e)-> (R*State_formula)->Prop) (Q:State_formula->State_formula->Prop), 
(forall (i :dstate s e) (j k:R*State_formula), ((fst j)=(fst k))-> 
(P i j) -> Q (snd j) (snd k)->(P (d_update_cstate v a i) k))->
(get_pro_formula pF1 = get_pro_formula pF2)->
(Forall_two Q (pro_to_npro_formula pF1) (pro_to_npro_formula pF2) )->
(Forall_two P mu_n pF1 )->
Forall_two P (d_update_cstate_list v a mu_n) pF2.
Proof. induction pF1; intros; destruct pF2; simpl in *.
inversion_clear H3. econstructor. inversion_clear H2.
inversion_clear H2. inversion_clear H3. inversion_clear H2. 
econstructor. apply H0 with a; try assumption. injection H1. auto. 
eapply IHpF1. apply H0. injection H1. auto. auto. auto.
Qed.

Lemma d_trace_update'{s e:nat}: forall  (mu: (dstate s e)) i a,
WWF_dstate mu->
d_trace (d_update_cstate i a mu)=
d_trace mu.
Proof. intros (mu, IHmu). unfold WWF_dstate.  unfold d_trace. unfold d_update_cstate. simpl. intros.
      apply d_trace_update. assumption. 
Qed.


Lemma State_eval_Assn{s e:nat}: forall (mu:list (state s e)) i a F,
WF_dstate_aux mu->
State_eval_dstate  (SAssn i a F)  mu->
State_eval_dstate F (d_update_cstate_aux i a mu) .
Proof. induction mu; intros. inversion_clear H1. 
inversion_clear H1. simpl in H2. destruct a.
destruct mu. simpl in *. econstructor. assumption. econstructor.
inversion_clear H0. remember (s0 :: mu).    
simpl. rewrite app_fix_2.  apply d_seman_app_aux.
apply WF_state_dstate_aux. apply WF_state_eq with (c,q).
reflexivity.  assumption.  apply WF_d_update_cstate.  assumption. 
econstructor. simpl in H2. assumption. econstructor.
apply IHmu.  assumption.   
subst. apply State_eval_dstate_Forall. discriminate.
assumption.
Qed.


Lemma sat_Assn{s e:nat}: forall (mu:dstate s e) i a F,
sat_State mu (SAssn i a F) ->
sat_State (d_update_cstate i a mu) F.
Proof. intros (mu,IHmu) i a F. intros. inversion_clear H0. 
econstructor. apply WF_d_update_cstate. assumption.
simpl in *. apply State_eval_Assn. assumption. assumption.
Qed.



Lemma Assn_sub_Plus: forall (nF1 nF2: npro_formula) i a,
Forall_two (fun (F1 F2: State_formula) => F1 ->> SAssn i a F2) nF1 nF2->
((ANpro nF1)->> Assn_sub i a (ANpro nF2)). 
Proof. intros. unfold assert_implies. intros. inversion_clear H1. 
inversion_clear H3. inversion_clear H5. rewrite get_pro_formula_p_n in H3; 
try symmetry; try assumption. 
econstructor. assumption. econstructor. erewrite <-(Forall_two_length_eq _ _ nF2); try apply H0. apply H2. 
simpl in *. econstructor. apply WF_d_update_cstate. assumption.
symmetry in H2.
inversion_clear H4. econstructor; rewrite get_pro_formula_p_n in * ;try assumption.
erewrite <-(Forall_two_length_eq _ _ nF2); try apply H0. apply H2.
erewrite <-(Forall_two_length_eq _ _ nF2); try apply H0. apply H2.  
pose(big_dapp_exsist p_n (d_update_cstate_list i a mu_n)) .
symmetry in H2.
destruct e0. rewrite d_update_cstate_length. eapply big_dapp'_length. apply H3. 
econstructor. simpl in *. rewrite get_pro_formula_p_n in *. apply H5. 
erewrite <-(Forall_two_length_eq _ _ nF2); try apply H0.  apply H2.  
apply dstate_eq_trans with (d_update_cstate i a mu'). 
apply d_update_cstate_eq. assumption.  
apply dstate_eq_sym. eapply  big_dapp'_update. 
apply H3. assumption.
apply Assn_sub_Plus_aux with (pF1:=(npro_to_pro_formula nF1 p_n)) (Q:=(fun F1 F2 : State_formula => F1 ->> SAssn i a F2)).
intros. destruct H9. rewrite H8. assumption. split.
 unfold assert_implies in H10. 
pose (H10 s e i0). repeat rewrite sat_Assert_to_State in s0.
apply sat_Assn. apply s0. assumption. 
rewrite d_trace_update'. assumption. 
apply WWF_dstate_aux_to_WF_dstate_aux. eapply WF_sat_State. apply H9. 
apply get_pro_formula_eq; try assumption.
erewrite <-(Forall_two_length_eq _ _ nF2); try apply H0. assumption.
rewrite pro_npro_inv; try assumption. rewrite pro_npro_inv. assumption.
erewrite <-(Forall_two_length_eq _ _ nF2); try apply H0. assumption.
rewrite d_trace_update'. assumption. 
apply WWF_dstate_aux_to_WF_dstate_aux.
assumption.
Qed.

Lemma rule_OCon_Oplus: forall (nF1 nF2 nF1' nF2': npro_formula),
(nF1 ->>  nF1')->
(nF2 ->>  nF2') ->
(ANpro (nF1 ++ nF2) ->>  ANpro (nF1' ++ nF2')) .
Proof. Admitted.


Lemma big_Oplus_to_formula: forall n (F_n:nat-> State_formula) (F:State_formula),
0<n-> 
(forall i, i < n -> F_n i ->> F) ->
 big_Oplus F_n n ->> F. 
Proof.  induction n;  unfold assert_implies;  intros; simpl in *. lia.
        destruct (Nat.eq_dec n 0). subst. simpl in *. 
        apply (H1 0). lia. assumption.     
        apply (@sat_NPro_State' s e mu ).
        assert([F;F] = [F] ++ [F]). simpl. reflexivity.
        rewrite H3.
        apply (rule_OCon_Oplus (big_Oplus F_n n) ([F_n n])).
        apply IHn. lia. 
        intros. unfold assert_implies.  apply H1. lia.
         unfold assert_implies. apply H1. lia. 
         assumption. 
Qed.


Ltac not_In_solve:=
  simpl; intro; try repeat match goal with 
H:NSet.In ?b (NSet.union ?c1 ?c2)|-_ => apply NSet.union_1 in H;
destruct H end;
try match goal with 
H:NSet.In ?b (NSet.add ?a (NSet.empty)) |-_ => apply NSet.add_3 in H;
try discriminate end;
try match goal with 
H:NSet.In ?b NSet.empty |- _ => eapply In_empty; apply H end.

Theorem OF_correctness: 
{{BEq ((Nat.gcd x N)) 1 }} OF {{BEq z ' r}}.
Proof.
       pose HtL. pose H. pose Hr. 
       pose (Qsys_to_Set_min_max t (t+L)). destruct a2; try lia.
       pose (Qsys_to_Set_min_max 0 t). destruct a2; try lia.   

       unfold OF. 
       eapply rule_seq.
       eapply rule_conseq_l; try eapply rule_assgn with (F:=(BEq z ' 1)).
       implies_trans_solve 0 rule_PT; try apply Assn_true_F; not_In_solve.

       eapply rule_seq.
       eapply rule_conseq_l; try eapply rule_assgn with (F:=( (BEq z ' 1) /\s ( BEq b ' (AMod ( APow x  (z '))  N )))).
       implies_trans_solve 1 Assn_conj_F; try eapply rule_Conj_two; try apply implies_refl.
       implies_trans_solve 0  rule_PT;  unfold b'; apply Assn_true_F. 
       not_In_solve.  not_In_solve.  

       eapply rule_conseq_l with (P':=( (BLt z ' r /\p (BNeq b ' 1)))).

       assert(1<>r). unfold r. 
       intro. rewrite <-H4 in *. simpl in *.  destruct a1.
       rewrite Nat.mod_small in H5; try rewrite Nat.mul_1_r in *; try lra.
       rewrite H5 in *. lia. lia. assert(1<r). unfold r in *. lia.     

      seman_sovle; destruct H6; unfold Pure_eval in *;
      unfold beval in *; unfold aeval in *; unfold fst in *; 
      bdestruct (c_find z x0 =? 1).   
      try rewrite H8.
      try apply Nat.ltb_lt in H5; try rewrite H5;  try auto.
      destruct H6.  
      bdestruct(c_find b x0 =? x ^ c_find z x0 mod N).
      rewrite H9.  rewrite H8. simpl. rewrite Nat.mul_1_r.

      rewrite Nat.mod_small. bdestruct (x=?1). 
      pose H. unfold x in H10. lia. auto. pose H. unfold x.
      unfold N. lia. destruct H7. destruct H6.

      eapply rule_conseq.
      eapply rule_while with (F0:= (BLt z ' r))  (F1:=  (BEq z ' r)).

     *eapply rule_seq. eapply rule_conseq_l;try apply rule_QInit; apply rule_PT.

     *eapply rule_seq. eapply rule_conseq_l. apply rule_OdotE.
      eapply rule_qframe'; [|split; try apply rule_QInit].
      unfold Considered_Formula_F_c; simpl; intuition.
      split. apply inter_empty. left. reflexivity.
      simpl. right.  rewrite H0. lia. 

      *eapply rule_seq.
      eapply rule_qframe; simpl; [|split; try apply rule_QUnit_One'].
      unfold Considered_Formula_F_c; simpl. intuition. lia.  
      split. apply inter_empty. left. reflexivity.
      left.  rewrite H3.  lia.  
      unfold U_v; repeat rewrite Nat.sub_diag; rewrite Nat.sub_0_r; simpl;
      rewrite kron_1_l; auto_wf; rewrite kron_1_r; auto_wf; rewrite Had_N.

      *eapply rule_seq.
      eapply rule_qframe'; simpl; [|split; try apply rule_QUnit_One'].
      unfold Considered_Formula_F_c ; simpl. intuition. lia.  
      split. apply inter_empty. left. reflexivity.
      right. rewrite H0; lia.  
      pose HU_plus. destruct a2. assert(L=t + L - t). lia. 
      unfold U_v; repeat rewrite Nat.sub_diag;
      simpl; rewrite kron_1_l; auto_wf; try rewrite kron_1_r; auto_wf; destruct H6; try rewrite H5.

      *eapply rule_seq.  
      eapply rule_conseq_l. eapply rule_odotT.
      eapply rule_conseq_l. eapply rule_Separ.
      assert(L=t + L - t). lia. destruct H6.
      assert(t=t-0). lia. destruct H6.
      rewrite simpl_H_Uplus.
      eapply rule_QUnit_Ctrl; try lia.  rewrite simpl_Uf.

      * eapply rule_seq.
      eapply rule_QUnit_One'; try lia. 
      assert(t=t-0). lia. destruct H6.
      assert(t+L=t+L-0). lia. destruct H6.
      rewrite simpl_QFT'.

      * eapply rule_seq. 
      eapply rule_conseq_l'.
      eapply rule_QMeas with (s:=0) (e:=t+L) (P:=P); try lia.
      apply rule_Conj_two. 
      apply implies_refl. implies_trans_solve 0  rule_PT.
      rewrite Nat.sub_0_r. unfold P.    
      apply big_Sand_Assn_true.   
      intros. simpl. unfold not. apply In_empty.

      *eapply rule_seq. 
      eapply rule_conseq_l  with (big_pOplus (fun i:nat=>(/  r)%R ) (fun s:nat=> P' s) r).
      eapply big_Oplus_solve'. admit.
      eapply rule_conseq_l .  eapply rule_Oplus. rewrite big_pOplus_get_npro. 
      unfold P'.
      eapply rule_conseq_l with 
      (Assn_sub z (Afun CFq (CF_bound (2 ^ t)) (z') ' (2 ^ t))
      (ANpro [ SPure ((BLt (z) '  r )) ; SPure (BEq (z) ' r)])).
      apply implies_trans with (Assn_sub z (Afun CFq (CF_bound (2 ^ t)) (z') ' (2 ^ t)) 
      (big_Oplus (fun s : nat => <{ (z) ' =  r / (AGcd s r) }>) r)).
      apply Assn_sub_Plus. rewrite <-fun_to_list_big_Oplus_eq. 
      rewrite <-fun_to_list_big_Oplus_eq.  apply Forall_two_forall.
      intros. seman_sovle. unfold Pure_eval in *. unfold beval in *. 
      unfold aeval in *. unfold s_update_cstate. unfold fst in *.
      bdestruct (c_find z' x0 =? j * 2 ^ t / r).  
      rewrite H8. rewrite c_update_find_eq. 
      pose (CF_out_divide j H6). rewrite <-Nat.eqb_eq in e0.
      rewrite e0. auto. destruct H7. 
      apply Assn_impl. apply implies_trans with 
      (POr (<{ (z) ' < r }>) (<{ (z) ' = r }>)). 
      apply big_Oplus_to_formula. unfold r. lia. 
      intros. seman_sovle.   unfold Pure_eval in *. unfold beval in *. 
      unfold aeval in *. unfold s_update_cstate. unfold fst in *.
      bdestruct (c_find z x0 =? r / Nat.gcd i r).
      rewrite H8. assert(r / Nat.gcd i r < r \/ r / Nat.gcd i r = r).

      admit. destruct H9. left. apply Nat.ltb_lt in H9. 
      rewrite H9. auto. right. apply Nat.eqb_eq in H9. rewrite H9. auto.
      destruct H7.  
      admit.  

      apply rule_Dassgn.
      eapply rule_conseq_l'. apply rule_Dassgn. 
      unfold b'.  simpl. apply Assn_sub_Plus. econstructor. 

      eapply implies_trans with (<{  (z) ' < r }> /\s (SAssn b <{ x ^ (z) ' % N }> <{ (b) ' <> 1 }>)).
      apply rule_Conj_two. apply implies_refl.
      rule_solve. intros. apply H8 in H16.
      unfold State_eval in *.  unfold Pure_eval in *.
      unfold beval in *. unfold aeval in *. unfold fst in *.
      unfold s_update_cstate.  rewrite c_update_find_eq.
      bdestruct (c_find z x0 <? r).   
      bdestruct (x ^ c_find z x0 mod N =? 1).
      pose Hr. destruct a. unfold x in *. unfold N in *. unfold r in *. 
      apply H20 in H18. lia.  auto. simpl in *. destruct H16.

      apply Assn_conj_F. simpl.

      not_In_solve.

      econstructor. 

      eapply implies_trans with (<{  (z) ' = r }> /\s (SAssn b <{ x ^ (z) ' % N }> <{ ~ (b) ' <> 1 }>)).
      apply rule_Conj_two. apply implies_refl.
      rule_solve. intros. apply H8 in H16.
      unfold State_eval in *.  unfold Pure_eval in *.
      unfold beval in *. unfold aeval in *. unfold fst in *.
      unfold s_update_cstate.  rewrite c_update_find_eq.
      bdestruct (c_find z x0 =? r).   
      bdestruct (x ^ c_find z x0 mod N =? 1). auto. 
      rewrite H17 in H18. 
      pose Hr. destruct a. unfold x in *. unfold N in *. unfold r in *. lia.
      destruct H16.  

      apply Assn_conj_F. simpl.

      not_In_solve.

      econstructor.

      assert(L=t+L-t). lia. destruct H6.    apply H4. 

      implies_trans_solve 0 SAnd_PAnd_eq. 
      unfold assert_implies; intros;
      apply sat_NPro_State; assumption.

      apply rule_Conj_split_l. 
Admitted.
End OF.


