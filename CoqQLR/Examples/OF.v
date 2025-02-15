Require Import Lists.List.
Require Import Psatz ZArith Znumtheory.
Require Import Reals.
Require Import Coquelicot.Complex.
Require Import Strings.String.

From Quan Require Import QuantumLib.Prelim.
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
From Quan Require Import HHL.
From Quan Require Import ContFrac.


Local Open Scope com_scope.
Local Open Scope assert_scope.
Local Open Scope nat_scope.
Local Open Scope matrix_scope.
Local Open Scope rule_scope.  

Require Import Arith.


Module ContFrac.

Local Open Scope R_scope.

Lemma Legendre_rational_bound :
forall a b p q : nat,
       (0 < q)%nat ->
       (a < b)%nat ->
       Rabs (a / b - p / q) =0 ->
       rel_prime p q ->
       CFq (CF_bound b) a b = q.
Proof. intros. pose(Legendre_rational' a b p q). 
       destruct e; try assumption. rewrite H1. apply Rdiv_lt_0_compat; try lra.
       apply Rmult_gt_0_compat; try lra. apply pow_lt.
       rewrite IZR_INR_0.
       apply lt_INR. assumption. 
       assert(CF_bound b= (CF_bound b) - x + x)%nat.
       rewrite Nat.sub_add; try lia.
       rewrite H4. destruct H3. destruct H5.
       rewrite (nthmodseq_0_CFq (CF_bound b - x) x a b); try assumption.
       pose (CF_converge'). 
       apply Classical_Prop.NNPP. 
       intro. 
       assert((forall i : nat,
       (i < x)%nat ->
       nthcfexp i a b <> 0%nat)).
       intros.
       apply (nthmodseq_not_0_nthcfexp_not_0 (x-i) i x);try lia.
       pose H8.
       apply e in n; try lia. 
       
       rewrite H6 in n. rewrite H5 in n.
       apply Rcomplements.Rabs_eq_0 in H1.
       assert( a / b * q - p =0).  
       apply Rminus_diag_uniq in H1.
       rewrite H1. apply Rminus_diag_eq.
       rewrite Rdiv_unfold. rewrite Rmult_assoc.
       rewrite Rinv_l. rewrite Rmult_1_r. reflexivity.
       apply Rgt_neq_0. rewrite IZR_INR_0.
       apply lt_INR. 
       lia.  
       rewrite H9 in n. 
       assert(IZR (signflip (S x)) <> 0).
       intro. pose (signflip_abs (S x)). 
       apply eq_IZR_R0 in H10. rewrite H10 in e0.
       lia.  
       
     
       assert( IZR (signflip (S x)) *
       (nthmodseq x a b /
        (nthmodseq (S x) a b * q +
         nthmodseq x a b * CFq (S x) a b)) <>0).
         apply Rmult_integral_contrapositive.
         split. assumption. rewrite Rdiv_unfold. 
         apply Rmult_integral_contrapositive. 
         split. rewrite IZR_INR_0. 
         intro. 
        
         apply INR_eq in H11. destruct H7. assumption.
        apply Rinv_neq_0_compat. 
        apply Rgt_neq_0.  rewrite <-Rplus_0_l.
        apply Rplus_le_lt_compat.
        apply Rmult_le_pos. rewrite IZR_INR_0. 
        apply le_INR. lia. rewrite IZR_INR_0.
        apply le_INR. lia.   
        apply Rmult_gt_0_compat. 
        rewrite IZR_INR_0.
        apply lt_INR. lia.
        rewrite IZR_INR_0. 
        apply lt_INR. 
        apply Nat.lt_le_trans with q. lia.
        rewrite <-H6. 
        assert( S x = x+1)%nat.
        rewrite S_add_1. reflexivity. 
        rewrite H11. rewrite Nat.add_comm. 
        apply CFq_inc. lia. 
        destruct H11. lra. 
Qed.

Lemma Rabs_eq_0: forall a, 
 a=0%R -> Rabs a= 0%R .
Proof. intros. rewrite H. apply Rabs_R0. 
Qed.


Lemma real_div_mul : forall x y z : R,
  y <> 0%R ->
  (x / y = z)%R ->
  (x = z * y)%R.
Proof.
  intros x y z Hneq Heq.
  rewrite <-Heq. rewrite Rdiv_unfold.
  rewrite Rmult_assoc. rewrite Rinv_l. 
  rewrite (Rmult_1_r). reflexivity.
  assumption.
Qed.

Lemma div_INR: forall (x y z:nat), 
(y<>0%nat)->
(Rdiv (INR x)  (INR y)) =z ->
(Rdiv (INR x)  (INR y)) =INR (x/y).
Proof. intros. simpl. rewrite H0.
apply real_div_mul in H0.
rewrite <-mult_INR in H0.
apply INR_eq in H0. rewrite H0. 
rewrite Nat.div_mul. reflexivity.
assumption. 
apply not_0_INR. assumption.
Qed.


Lemma Z_of_nat_mod : forall m n : nat,
  (n <> 0 )%nat->
  Z.of_nat (Nat.modulo m n) = Z.modulo (Z.of_nat m) (Z.of_nat n).
Proof.
  intros m n Hnz.

  apply Nat2Z.inj_mod; try lia.
Qed.

Lemma inj_gcd : forall m n : nat,
Zis_gcd m n (Nat.gcd m n).
Proof.  intros.  econstructor.
       assert( Nat.divide (Nat.gcd m n) m ). 
       apply Nat.gcd_divide_l. unfold Nat.divide in *. 
       destruct H.   
         unfold Z.divide. exists x . rewrite<- Nat2Z.inj_mul.
        rewrite H at 1. reflexivity. 
        assert( Nat.divide (Nat.gcd m n) n ). 
        apply Nat.gcd_divide_r. unfold Nat.divide in *. 
       destruct H.   
         unfold Z.divide. exists x . rewrite<- Nat2Z.inj_mul.
        rewrite H at 1. reflexivity. 
     

        intros. apply Zdivide_Zabs_inv_l in H. 
        apply Zdivide_Zabs_inv_l in H0.  
        assert((0 <= Z.abs x)%Z). lia.  
         pose (IZN (Z.abs x) H1). destruct e. rewrite H2 in *.
        apply Zdivide_Zabs_l . rewrite H2. 
        unfold Z.divide in *. destruct H. destruct H0.

        assert((0 <= x1 * x0)%Z). lia.   
        
        pose (Z.le_0_mul x1 x0 H3). destruct o.  destruct H4. 
         apply IZN in H4. destruct H4.   rewrite H4 in *. 
         assert((0 <= x2 * x0)%Z). lia.  
         pose (Z.le_0_mul x2 x0 H6). destruct o.  destruct H7. 
          apply IZN in H7. destruct H7.   rewrite H7 in *.  

        assert(Nat.divide x0 (Nat.gcd m n) )%nat. 
        apply Nat.gcd_divide_iff. split; unfold Nat.divide.
        exists x3.  apply Nat2Z.inj_iff. rewrite H. rewrite Nat2Z.inj_mul. reflexivity.  
        exists x4. apply Nat2Z.inj_iff. rewrite H0. rewrite Nat2Z.inj_mul. reflexivity. 
        unfold Nat.divide in *.  destruct H9. 
        exists x5.  rewrite H9. rewrite Nat2Z.inj_mul. reflexivity.
         destruct H7.  assert(x0=0)%nat. lia. rewrite H9 in *.
         exists 0%Z. 
         rewrite Z.mul_0_r in *. subst. assert( Z0= 0%nat). lia. rewrite H4 in *.  
         apply inj_eq. 
          apply Nat.gcd_eq_0. split. apply Nat2Z.inj_iff.  assumption.
          apply Nat2Z.inj_iff.  assumption.
          destruct H4. 
          assert(x0=0)%nat. lia. rewrite H6 in *.
          exists 0%Z. 
          rewrite Z.mul_0_r in *. subst. assert( Z0= 0%nat). lia. rewrite H6 in *.  
          apply inj_eq. 
           apply Nat.gcd_eq_0. split. apply Nat2Z.inj_iff.  assumption.
           apply Nat2Z.inj_iff.  assumption.
Qed.
End ContFrac.


Module Type Param.
Parameter x:nat.
Parameter N:nat. 
Parameter r:nat. 
Hypothesis Hr: r > 0 /\ x ^ r mod N =1 /\ (forall j, x ^ j mod N =1 -> r<=j).
Hypothesis H: (Nat.gcd x N =1 ) /\ 2 <= x <= N-1.
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


Hypothesis HtL:  (t>0)%nat /\ (L>0)%nat /\ (2 ^ t >= r).
Hypothesis HNL:  (N < (2^L))%nat. 
Hypothesis HU_plus: WF_Unitary U_plus /\ ( U_plus × (∣ 0 ⟩_ (2^L)) = (∣ 1 ⟩_ (2^L))).
Hypothesis HU: WF_Unitary U /\ (forall j:nat, j< N -> U × (Base_vec (2 ^ L) j) = (Base_vec (2 ^ L) (x * j mod N))) /\ 
                               (forall j:nat, j>=N /\ j<(2^L)-> U × (Base_vec (2 ^ L) j) = (Base_vec (2 ^ L) j)).
Hypothesis HQFT: WF_Unitary QFT /\ forall k:nat, QFT × (∣ k ⟩_ (2^t)) =
/ √ 2 ^ t .* (big_sum (fun j : nat => (cos (((2 * PI)/(2^t)) * j * k)%R,  sin (((2 * PI)/(2^t)) * j * k)%R) .*  (∣ j ⟩_ (2^t))) (2 ^ t)).
Hypothesis (Ht: forall s:nat,  s < r-> exists j, j < (2^t) /\ ((( s / r) * 2^t)%R =  j)).


Definition  H := p.H .
Definition  Hr := p.Hr .
Definition  U_f (i:nat):= exp_U U i.
Definition  Us (s:nat):=  / √ r .* (big_sum (fun k:nat=> (cos (- ((2 * PI)) * (s /r) * k)%R,  sin (- ((2 * PI)) * ( s / r) * k)%R) .*  Base_vec (2 ^ L) (x ^ k mod N)) (r) ) .
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
Proof. intros. pose Hr. apply ContFrac.Legendre_rational_bound with (s/ (Nat.gcd s r))%nat.
       apply Nat.div_str_pos. split.  
       assert(Nat.gcd s r <> 0)%nat. intro. 
       apply Nat.gcd_eq_0 in H1. destruct H1. unfold r in *. lia.
       lia. pose(Nat.gcd_divide_r s r). apply Nat.divide_pos_le in d. lia. 
       unfold r. lia. apply  Nat.div_lt_upper_bound. unfold r. lia. 
       apply Nat.mul_lt_mono_pos_r. apply pow_gt_0. lia.
       apply ContFrac.Rabs_eq_0. 
       apply Rminus_diag_eq. 
       apply eq_trans with (s/r). pose (Ht s H0). destruct e. 
       rewrite Rdiv_unfold in H1. destruct H1. 
       rewrite Rmult_assoc in H2.  rewrite (Rmult_comm (/ r) ) in H2.
       rewrite <-Rmult_assoc in H2.  
       rewrite <-(ContFrac.div_INR (s*2^t) _ x0). rewrite mult_INR. rewrite pow_INR.
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
       lia. apply ContFrac.inj_gcd. 

Qed.

Local Open Scope nat_scope.
Lemma HU_s: 
  / √ r .*  (big_sum (fun s:nat=> Us s) (r) ) =(∣ 1 ⟩_ (2^L)).
Proof. pose H. pose Hr. assert(0<r)%R. rewrite IZR_INR_0. 
      apply lt_INR. apply a0. 
      assert(0<x)%R. rewrite IZR_INR_0. 
      apply lt_INR. unfold x. lia. pose Hr.  
      unfold Us. rewrite Mscale_Msum_distr_r. rewrite Mscale_assoc. 
       rewrite big_sum_swap_order. 
       rewrite (big_sum_eq_bounded _ ((fun i : nat =>
       (@big_sum C _ (fun j : nat =>
          (cos (- (2 * PI) * (j / r) * i), sin (- (2 * PI) * (j / r) * i))) r)
          .* ∣ x ^ i mod N ⟩_ (2^L)))).
        rewrite (big_sum_unique  (r .* ∣ x ^ r mod N ⟩_ (2^L) )).
        repeat rewrite Mscale_assoc.
        assert(√ r<>0).  
        apply sqrt_neq_0_compat; try assumption.
        rewrite <-RtoC_inv; try assumption. 
        rewrite RtoC_mult. 
        rewrite <-Rinv_mult_distr_depr; try assumption.
        rewrite sqrt_sqrt. rewrite RtoC_mult. 
        rewrite Rinv_l. Msimpl. destruct a0. destruct H4. unfold x.
        unfold r. unfold N.    rewrite H4.
        reflexivity. apply Rgt_neq_0. assumption. lra. 
        exists 0. split. apply Hr. 
        split. f_equal. 
        rewrite (@big_sum_eq_bounded  C C_is_monoid _ (fun j=>1%R)).  
        rewrite big_sum_constant. apply times_1_n. 
        intros. rewrite Rmult_0_r. rewrite cos_0. 
        rewrite sin_0. reflexivity. 
        destruct a0. destruct H3. unfold x.
        unfold r. unfold N.  rewrite H3. simpl. 
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
/ √ 2 ^ t .* big_sum (fun z0 : nat => ∣ z0 ⟩_ (2^t)) (2 ^ t) ⊗ ∣ 1 ⟩_ (2^L)
= / √ (r *2^t) .*  (big_sum (fun s:nat=>(big_sum (fun j=>(Base_vec (2^t) j)) (2^t)) ⊗ (Us s)) (r) ).
Proof. intros.   rewrite<- HU_s. pose Hr.  
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
Proof.  unfold Us. intros.  pose HNL. pose (H). assert(forall i,  x^i mod N < (2^L)).
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
Proof. intros. pose HU. pose HNL. pose Hr. unfold Us. rewrite Mscale_mult_dist_r.
       rewrite Mscale_assoc. rewrite Cmult_comm.
       rewrite <-Mscale_assoc. f_equal. 
       rewrite Mmult_Msum_distr_l. 
       rewrite <-Mscale_Msum_distr_r.
       rewrite (big_sum_eq_bounded _ 
       ((fun i : nat =>  ((cos (- (2 * PI ) * (s / r) * (i))%R, sin (- (2 * PI ) * (s / r) * (i))%R)) .* ∣ x ^ (i+1) mod N ⟩_ (2^L)))).
       rewrite (big_sum_eq_bounded ((fun i : nat =>
       (cos (2 * PI * (s / r)), sin (2 * PI * (s / r))) .* ((cos (- (2 * PI) * (s / r) * i),
            sin (- (2 * PI) * (s / r) * i)).* ∣ x ^ i mod N ⟩_ (2^L)))) 
       ((fun i : nat =>  ((cos (-(2 * PI ) * (s / r) * (i-1%nat)), sin (-(2 * PI) * (s / r) * (i-1%nat))) .* ∣ x ^ i mod N ⟩_ (2^L))))).
       rewrite (big_sum_move_r ((fun i : nat =>
       (cos (- (2 * PI) * (s / r) * (i - 1%nat)),
        sin (- (2 * PI) * (s / r) * (i - 1%nat)))
       .* ∣ x ^ i mod N ⟩_ (2^L)))).  apply big_sum_eq_bounded.
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
       lia.   destruct a0 as [ a1]. destruct H0.  unfold x. unfold r. unfold N.
       simpl. rewrite H0. rewrite Nat.mod_small. reflexivity. pose H. lia.     
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
       rewrite Nat.mul_1_r. reflexivity. pose H. lia.   
       apply Nat.mod_upper_bound. unfold N. pose H. lia.   
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
 (∣ i ⟩_ (2^t) × ⟨ i ∣_ (2^t)) ⊗ (U_f i)) (2 ^ t)) v.
Proof.  intros. unfold UCtrl_v. pose HU. type_sovle.
apply Logic.eq_trans with (∣ x0 ⟩_ (2^t) × ⟨ x0 ∣_ (2^t) ⊗ I (2 ^ L)
× (I (2 ^ t) ⊗  U_f x0)). f_equal; type_sovle'; try lia. 
rewrite kron_mixed_product; Msimpl; try reflexivity.
unfold U_f. apply WF_expU. apply a. 
Qed.


Lemma  simpl_Uf: 
UCtrl_v 0 t t (t + L) 0 (t + L) U_f
( / √ (r * 2 ^ t)
 .* big_sum (fun s : nat => big_sum (fun j : nat => ∣ j ⟩_ (2^t)) (2 ^ t) ⊗ Us s) r) =
( / √ (r) .* big_sum (fun s : nat => (/ √ (2 ^ t)).*  big_sum (fun j : nat =>(cos ((2*PI/2^t)* j *(s/r * 2^t)), 
sin ((2*PI/2^t)* j *(s/r * 2^t))) .* ∣ j ⟩_ (2^t)) (2 ^ t)⊗ Us s) r).
Proof. intros. rewrite U_f'. pose Hr.  
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
(∣ x1 ⟩_ (2^t) × ⟨ x1 ∣_ (2^t) × ∣ x1 ⟩_ (2^t)) ⊗  ((cos ((2*PI/2^t)* x1 *(x0/r * 2^t)), sin ((2*PI/2^t)* x1 *(x0/r * 2^t))) .* Us x0))).
rewrite kron_mixed_product. f_equal.
rewrite simpl_expU. f_equal. 
rewrite Mmult_assoc. rewrite base_inner_1. unfold c_to_Vector1.
Msimpl. rewrite Mscale_kron_dist_r.
rewrite Mscale_kron_dist_l.
reflexivity. assumption.  
intros.
rewrite kron_mixed_product.
rewrite Mmult_assoc. rewrite base_inner_0. unfold  c_to_Vector1.
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
             .* ∣ j ⟩_ (2^t)) (2 ^ t) ⊗ Us s) r)
 =( / √ r .* big_sum  (fun s : nat =>   (Base_vec (2^t) (s * (2^t) / r )) ⊗  Us s) r).
Proof. 
unfold U_v. type_sovle. pose Hr.
assert(2^t=1* 2^t). lia. destruct H0.
assert( 2^t * 2^L= 2^(t+L)). type_sovle'. destruct H0.
rewrite Mscale_mult_dist_r. f_equal.
rewrite Mmult_Msum_distr_l. 
apply big_sum_eq_bounded.  intros. 
rewrite kron_mixed_product. Msimpl.
f_equal. pose HQFT. 
apply unitary_trans. intuition.
apply WF_base. apply Nat.div_lt_upper_bound. unfold r. lia.
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
rewrite (ContFrac.div_INR _ _  x2); try reflexivity;
unfold r; try lia; try assumption.  
apply WF_adjoint. apply HQFT.
Qed.


Ltac seman_sovle:=
  unfold assert_implies;
  intros; 
  rewrite sat_Assert_to_State in *;
   rewrite seman_find in *;
   try match goal with 
   H: WF_dstate ?mu /\ WF_formula ?P /\ 
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


Lemma s_r_t_relation: forall i, 
i< r -> i*(2^t) /r < (2^t).
Proof. intros. pose Hr.  
apply Nat.div_lt_upper_bound. unfold r. lia.
apply Nat.mul_lt_mono_pos_r. apply pow_gt_0.
assumption.   
Qed.

Lemma i_j_le: forall i j, 
i< r-> j<r->
i< j -> i*(2^t) /r < j*(2^t) /r.
Proof. intros. apply INR_lt. pose Ht.  pose Hr.
pose (e  i H0). pose (e j H1). 
destruct e0. destruct e1. 
unfold Rdiv in *. rewrite (Rmult_comm  _ (/r)) in H3.
rewrite (Rmult_comm  _ (/r)) in H4. 
rewrite Rmult_assoc in H3.
rewrite Rmult_assoc in H4.
rewrite (Rmult_comm   (/r)) in H3.
rewrite (Rmult_comm  (/r)) in H4.
destruct H3. destruct H4.
rewrite <-(ContFrac.div_INR _ _ x0).
rewrite <-(ContFrac.div_INR _ _ x1). unfold Rdiv.
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
pose Ht.  pose Hr.
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
rewrite <-(ContFrac.div_INR _ _ x0) in H4.
rewrite <-(ContFrac.div_INR _ _ x1) in H4.
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
intros. unfold Us. pose Hr. pose H.
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
rewrite base_inner_1. unfold c_to_Vector1. split.  
Msimpl. rewrite Mscale_assoc. rewrite trace_mult_dist.
rewrite trace_I. Csimpl. rewrite Cmult_comm. reflexivity.
intros.  rewrite Mscale_mult_dist_r.
rewrite Mscale_adj.
repeat rewrite Mscale_mult_dist_l.
rewrite base_inner_0. unfold c_to_Vector1.
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
pose Hr. destruct a1 as [ a1 ]. destruct H9. apply H10 in H8. 
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
pose Hr. destruct a1 as [ a1 ]. destruct H9. apply H10 in H8. 
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
      (Nat.sub (Init.Nat.add t L) 0) 0 t 0 (t + L) (∣ i ⟩_ (2^(t - 0)) × ⟨ i ∣_ (2^(t - 0)))
         (/ √ r .* big_sum (fun s : nat => ∣ s * 2 ^ t / r ⟩_ (2^t) ⊗ Us s) r)) ^ 2)%R)
  (fun i : nat =>
   P i /\s
   (| (/
       norm
         (@U_v (Nat.sub t O)
         (Nat.sub (Init.Nat.add t L) 0) 0 t 0 (t + L) (∣ i ⟩_ (2^(t - 0)) × ⟨ i ∣_ (2^(t - 0)))
            (/ √ r .* big_sum (fun s : nat => ∣ s * 2 ^ t / r ⟩_ (2^t) ⊗ Us s) r)))%R
      .* @U_v (Nat.sub t O)
      (Nat.sub (Init.Nat.add t L) 0) 0 t 0 (t + L) (∣ i ⟩_ (2^(t - 0)) × ⟨ i ∣_ (2^(t - 0)))
           (/ √ r .* big_sum (fun s : nat => ∣ s * 2 ^ t / r ⟩_ (2^t) ⊗ Us s) r) >[ 0, t + L])) 
  (2 ^ (t - 0)) ->> big_pOplus (fun _ : nat => (/ r)%R) (fun s : nat => P' s) r .
Proof.   pose Hr. pose HtL. pose H. pose Hr.
         assert(forall i j x0, ∣ i ⟩_ (2^t) × ⟨ i ∣_ (2^t) ⊗ I (2 ^ L) × (∣ j ⟩_ (2^t) ⊗ Us x0)=
         (@Mmult ((2^t) * ((2^L))) ((2^t) * ((2^L)))  1 
         (∣ i ⟩_ (2^t) × ⟨ i ∣_ (2^t) ⊗ I (2 ^ L)) (∣ j ⟩_ (2^t) ⊗ Us x0) ) ).
         reflexivity. intros.  

         assert(forall i, i< r->(norm
         (@U_v t (Init.Nat.add t L) 0 t 0 (t + L)  (∣ i * 2 ^ t / r ⟩_ (2^t) × ⟨ i * 2 ^ t / r ∣_ (2^t))
         (/ √ r .* big_sum (fun s : nat => ∣ s * 2 ^ t / r ⟩_ (2^t) ⊗ Us s) r)))= (/ √ r)%R).
         intros. unfold U_v. type_sovle. 
         rewrite <-Mscale_Msum_distr_r.
         repeat rewrite Nat.mul_1_l.
         rewrite Mmult_Msum_distr_l. 
         rewrite (@big_sum_unique (Matrix ((2^t) * ((2^L))) 1) (M_is_monoid ((2^t) * ((2^L))) 1) (/ √ r .* (∣ i * 2 ^ t / r ⟩_ (2^t) ⊗ Us i)) 
          ). 
          assert((2^t)* 2^L= 2^(t+L)). type_sovle'. destruct H3.
          rewrite norm_scale.
          rewrite norm_kron. rewrite norm_base_1. rewrite norm_Us. rewrite Rmult_1_r. rewrite Rmult_1_r.
          rewrite Cmod_inv.  rewrite Cmod_R. rewrite Rabs_right. reflexivity.
          apply Rgt_ge. apply sqrt_lt_R0. unfold r.
          rewrite IZR_INR_0.   apply lt_INR. lia. apply RtoC_neq.  apply sqrt_neq_0_compat. unfold r.
          rewrite IZR_INR_0.   apply lt_INR. lia. assumption. assumption.  
          apply s_r_t_relation. assumption.

         exists i.  
         split. assumption.  split.
         rewrite Mscale_mult_dist_r. rewrite <-H0. 
         rewrite kron_mixed_product. Msimpl.  rewrite Mmult_assoc. rewrite base_inner_1.
         unfold c_to_Vector1. Msimpl.  reflexivity. apply WF_base.
            apply s_r_t_relation. assumption.
            apply s_r_t_relation. assumption.
         intros. rewrite Mscale_mult_dist_r. rewrite <-H0.  
         rewrite kron_mixed_product. Msimpl.  rewrite Mmult_assoc. rewrite base_inner_0.
         unfold c_to_Vector1. Msimpl. reflexivity. apply i_j_neq; try assumption.
         apply s_r_t_relation. assumption.   apply s_r_t_relation. assumption. 
         apply WF_mult; try apply WF_adjoint;
         apply WF_base.   apply s_r_t_relation. assumption. 
         apply s_r_t_relation. assumption.
         
         eapply implies_trans. type_sovle. 
         eapply (big_Oplus_solve _ _ _ r  (fun s=> (s * 2^t/r))). pose HtL. lia.  
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
         assert((2^t)* 2^L= 2^(t+L)). type_sovle'. destruct H5. auto_wf.
         
         intros. rewrite Mscale_mult_dist_r. rewrite <-H0. 
         rewrite kron_mixed_product. Msimpl.  rewrite Mmult_assoc. rewrite base_inner_0.
         unfold c_to_Vector1. Msimpl. reflexivity.  
         intro. destruct H4. exists x0. split. assumption. auto. assumption.
         apply s_r_t_relation. assumption.  
         intros.   apply s_r_t_relation. assumption. 

         simpl. econstructor.
         simpl. rewrite big_pOplus_get_npro.
         rewrite <-fun_to_list_big_Oplus_eq.
         apply Forall_fun_to_list.
         intros.
         simpl. split; auto. 
        split; try lia.
        unfold U_v. simpl. Msimpl.
        apply WF_scale. 
        apply WF_mult.
        apply WF_kron; type_sovle'.
        rewrite Nat.mul_1_l.
        apply WF_mult.
        apply WF_base. apply s_r_t_relation. lia.
        apply WF_adjoint. 
        apply WF_base. apply s_r_t_relation. lia.
        auto_wf. 
        assert(2 ^ t * 2 ^ L = 1 * 2 ^ t * 2 ^ (t + L - t)).
        rewrite Nat.add_comm. rewrite Nat.add_sub.
        rewrite Nat.mul_1_l. reflexivity.
        destruct H4. 
        
        apply WF_scale. apply WF_Msum.
        intros. 

        apply WF_kron; type_sovle'.
         auto_wf.  
         apply WF_base. apply s_r_t_relation. lia.
         apply WF_Us. 
         apply WF_mult.
        apply WF_base. apply s_r_t_relation. lia.
        apply WF_adjoint. 
        apply WF_base. apply s_r_t_relation. lia.
        
       
         econstructor.
          try rewrite big_pOplus_get_pro. 
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
          apply rule_OCon''.
          rewrite big_pOplus_get_npro.
          rewrite <-fun_to_list_big_Oplus_eq.
          apply Forall_fun_to_list.
          intros. simpl. auto.
         
          repeat  rewrite big_pOplus_get_pro. reflexivity.
          repeat rewrite big_pOplus_get_npro. repeat rewrite <-fun_to_list_big_Oplus_eq.
          apply Forall_two_forall. intros. apply rule_Conj_split_l.
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


Lemma div_le: forall a b, 
0<a-> b<>0->
a/b <=a.
Proof. intros. destruct (Nat.eq_dec b0 1). subst. rewrite Nat.div_1_r. lia.  simpl.
assert(a / b0 < a). 
    apply Nat.div_lt; try lia. lia.  
  
Qed.


Lemma times_1_I:forall (n:nat), 
times_n (I 1) n = n .* I 1 .
Proof. induction n; intros. Msimpl. reflexivity.
rewrite S_O_plus_INR.
simpl . rewrite IHn.
solve_matrix.
Qed.


Lemma pure_state_vector_meas':
Pure_State_Vector
  (/ √ r
   .* big_sum
        (fun s : nat =>
         ∣ s * 2 ^ t / r ⟩_ (2 ^ t) ⊗ Us s) r) .
Proof. unfold Pure_State_Vector. 
split.
apply WF_scale. apply WF_Msum.
intros. apply WF_kron; type_sovle'.
apply WF_base. apply s_r_t_relation. lia.
apply WF_Us.
rewrite Mscale_adj.
rewrite Msum_adjoint.
rewrite Mscale_mult_dist_r.
rewrite Mscale_mult_dist_l.
rewrite Mscale_assoc.
rewrite Mmult_Msum_distr_r.
erewrite big_sum_eq_bounded;
[| intros; rewrite Mmult_Msum_distr_l; try reflexivity ].
erewrite big_sum_eq_bounded;
[ | intros; apply big_sum_unique; exists x0 ; split; try lia; split;[reflexivity|] ].
erewrite (big_sum_eq_bounded _ (fun x0 => C1 .* I 1)).
Msimpl. rewrite big_sum_constant. 
rewrite times_1_I.
pose Hr.
rewrite<- RtoC_inv; try unfold r; try apply sqrt_neq_0_compat; try rewrite IZR_INR_0; try apply lt_INR; try lia.   
rewrite Cmult_comm.
rewrite Cconj_R.

rewrite  RtoC_mult.
rewrite Mscale_assoc.
rewrite <-Rinv_mult_distr_depr; 
try apply sqrt_neq_0_compat; try rewrite IZR_INR_0; try apply lt_INR; try lia.   
rewrite sqrt_sqrt; try lra. rewrite RtoC_mult.
rewrite Rinv_l. Msimpl. reflexivity.
rewrite IZR_INR_0.
apply not_0_INR. lia. 

rewrite IZR_INR_0. apply le_INR. lia.


intros. 
rewrite kron_adjoint.
rewrite kron_mixed_product.
rewrite base_inner_1. Msimpl.
pose H. destruct a. 
pose (norm_Us x0 H0 H1) .
assert(WF_Matrix (Us x0)).
apply WF_Us. 
pose (norm_1_pure_vec (Us x0) H3 e).
destruct p. rewrite H5. unfold c_to_Vector1. Msimpl.
 reflexivity. 

apply s_r_t_relation. lia.
intros. 
rewrite kron_adjoint.
rewrite kron_mixed_product.
rewrite base_inner_0. unfold c_to_Vector1.
 Msimpl. reflexivity.
 apply i_j_neq; try lia. 
 apply s_r_t_relation. lia.
 apply s_r_t_relation. lia.
Qed.



Theorem OF_correctness: 
{{BTrue }} OF {{BEq z ' r}}.
Proof.
       pose HtL. pose H. pose Hr. 
       pose (Qsys_to_Set_min_max t (t+L)). destruct a2; try lia.
       pose (Qsys_to_Set_min_max 0 t). destruct a2; try lia.   

       unfold OF. 
       eapply rule_seq.
       eapply rule_conseq_l; try eapply rule_SAssgn with (F:=  (BEq z ' 1)).
       (* implies_trans_solve 1 Assn_conj_F; try apply rule_Conj_two; try apply implies_refl;[|not_In_solve]; *)
       implies_trans_solve 0 rule_PT; try apply Assn_true_F; not_In_solve.

       eapply rule_seq.
       eapply rule_conseq_l; try eapply rule_SAssgn with (F:=(  (BEq z ' 1) /\s ( BEq b ' (AMod ( APow x  (z '))  N )))).
       implies_trans_solve 1 Assn_conj_F; try eapply rule_Conj_two; try apply implies_refl; [|not_In_solve];
       implies_trans_solve 0  rule_PT;  unfold b'; apply Assn_true_F;  not_In_solve.  

       eapply rule_conseq_l with (P':=( ( (BLt z ' r) /\p (BNeq b ' 1)))).
       (* implies_trans_solve 1 SAnd_PAnd_eq. apply rule_Conj_two; *)

       assert(1<>r). unfold r. 
       intro. rewrite <-H4 in *. simpl in *.  destruct a1 as [a1]. destruct H5.
       rewrite Nat.mod_small in H5; try rewrite Nat.mul_1_r in *; try lra.
       rewrite H5 in *. lia. lia. assert(1<r). unfold r in *. lia.     

      seman_sovle; [simpl; auto| | ];
       destruct H6; unfold Pure_eval in *;
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
      eapply rule_qframe'; [ | |split; try apply rule_QInit]; try simpl; try lia.
      rewrite Qsys_inter_empty'; try lia. 
       split. apply inter_empty. left. reflexivity.
       rewrite H0. rewrite H1. lia. 
    

      *eapply rule_seq.
      eapply rule_qframe; simpl;  [ | | split; try apply rule_QUnit_One']; try simpl; try lia.
      rewrite Qsys_inter_empty'; try lia. 
      split. apply inter_empty. left. reflexivity.
      rewrite H2. rewrite H3. lia. 
    
      unfold U_v; repeat rewrite Nat.sub_diag; rewrite Nat.sub_0_r; simpl;
      rewrite kron_1_l; auto_wf; rewrite kron_1_r; auto_wf; rewrite Had_N.

      *eapply rule_seq.
      eapply rule_qframe'; simpl; [ | |split; try apply rule_QUnit_One']; try simpl; try lia. 
      rewrite Qsys_inter_empty'; try lia.
      split. apply inter_empty. left. reflexivity.
      rewrite H0. rewrite H1. lia. 
      pose HU_plus. destruct a2. assert(L=t + L - t). lia. 
      unfold U_v; repeat rewrite Nat.sub_diag;
      simpl; rewrite kron_1_l; auto_wf; try rewrite kron_1_r; auto_wf; destruct H6; try rewrite H5.

      *eapply rule_seq.  
      eapply rule_conseq_l. eapply rule_odotT.
      eapply rule_conseq_l. eapply rule_Separ.
      assert(L=t + L - t). lia. destruct H6.
      assert(t=t-0). lia.  destruct H6.  
      rewrite simpl_H_Uplus.
      eapply rule_QUnit_Ctrl; try lia.  rewrite simpl_Uf.

      * eapply rule_seq.
      eapply rule_QUnit_One'; try lia. 
      assert(t=t-0). lia. destruct H6.
      assert(t+L=t+L-0). lia. destruct H6.
      rewrite simpl_QFT'.

      * eapply rule_seq. 
  
      eapply rule_conseq_l';
      [eapply rule_QMeas with (s:=0) (e:=t+L)(P:=P);
     [  | ] | apply rule_Conj_two; [ apply implies_refl | ]   ] .
       lia. 
       assert((2 ^ t * 2 ^ L )=(2 ^ (t+L- 0))).
       rewrite Nat.sub_0_r. repeat rewrite Nat.pow_add_r.
       simpl. reflexivity. destruct H6.
       apply pure_state_vector_meas'. 
      implies_trans_solve 0  rule_PT.
      rewrite Nat.sub_0_r. unfold P.    
      apply big_Sand_Assn_true.   
      intros. simpl. unfold not. apply In_empty.

      *eapply rule_seq. 
      eapply rule_conseq_l  with (big_pOplus (fun i:nat=>(/  r)%R ) (fun s:nat=> P' s) r).
      eapply big_Oplus_solve'.  unfold x. unfold N. lia. 
      eapply rule_conseq_l .  eapply rule_Oplus. rewrite big_pOplus_get_npro. 
      unfold P'.
      eapply rule_conseq_l with 
      (Assn_sub z (Afun CFq (CF_bound (2 ^ t)) (z') ' (2 ^ t))
      (ANpro [ SPure ((BLt (z) '  r )) ; SPure (BEq (z) ' r)])).
      apply implies_trans with (Assn_sub z (Afun CFq (CF_bound (2 ^ t)) (z') ' (2 ^ t)) 
      (big_Oplus (fun s : nat => <{ (z) ' =  r / (AGcd s r) }>) r)).
      apply Assn_sub_Plus. rewrite <-fun_to_list_big_Oplus_eq.
      apply Forall_fun_to_list. intros. simpl. auto.
      rewrite <-fun_to_list_big_Oplus_eq.
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
      assert(0<r). unfold r. lia.  
      assert(r / Nat.gcd i r <= r). apply div_le; unfold r in *; try lia.
      intro. apply Nat.gcd_eq_0 in H10. lia. lia.  
      destruct H9. left. apply Nat.ltb_lt in H9. 
      rewrite H9. auto. right. apply Nat.eqb_eq in H9. rewrite H9. auto.
      destruct H7.
      unfold assert_implies. intros. rewrite sat_Assert_to_State in H6.
      rewrite seman_find in H6.
   

      apply sat_State_Npro; try apply H6. 
      split; simpl; auto. 

      apply rule_assgn.
      eapply rule_conseq_l'. apply rule_assgn. 
      unfold b'.  simpl. apply Assn_sub_Plus.
       econstructor.
      simpl. auto. 
      econstructor.
      simpl. auto. econstructor.


      econstructor.
      eapply implies_trans with (<{  (z) ' < r }> /\s (SAssn b <{ x ^ (z) ' % N }> <{ (b) ' <> 1 }>)).
      apply rule_Conj_two. apply implies_refl.
      rule_solve. intros. apply H8 in H18.
      unfold State_eval in *.  unfold Pure_eval in *.
      unfold beval in *. unfold aeval in *. unfold fst in *.
      unfold s_update_cstate.  rewrite c_update_find_eq.
      bdestruct (c_find z x0 <? r).   
      bdestruct (x ^ c_find z x0 mod N =? 1).
      unfold x in *. unfold N in *. unfold r in *. 
      apply H11 in H20. lia.  auto. destruct H18. 

      apply Assn_conj_F. simpl.

      not_In_solve.

      econstructor. 

      eapply implies_trans with (<{  (z) ' = r }> /\s (SAssn b <{ x ^ (z) ' % N }> <{ ~ (b) ' <> 1 }>)).
      apply rule_Conj_two. apply implies_refl.
      rule_solve. intros. apply H8 in H18.
      unfold State_eval in *.  unfold Pure_eval in *.
      unfold beval in *. unfold aeval in *. unfold fst in *.
      unfold s_update_cstate.  rewrite c_update_find_eq.  
      bdestruct (c_find z x0 =? r). rewrite H19.   
      unfold x in *. unfold N in *. unfold r in *. rewrite H10. simpl. lia.
      destruct H18.  

      apply Assn_conj_F. simpl.

      not_In_solve.

      econstructor.

      assert(L=t+L-t). lia. destruct H6.    apply H4. 

      implies_trans_solve 0 SAnd_PAnd_eq. 
      unfold assert_implies; intros;
      apply sat_NPro_State. split; try assumption.
      simpl. auto.

      apply rule_Conj_split_l. 
Qed.
End OF.

