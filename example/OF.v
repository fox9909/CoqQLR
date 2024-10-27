Require Import Lists.List.
Require Import Reals.
Require Import Coquelicot.Complex.
Require Import Strings.String.


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

Local Open Scope com_scope.
Local Open Scope assert_scope.
Local Open Scope nat_scope.
Local Open Scope matrix_scope.
Local Open Scope rule_scope.  


Module Type Param.
Parameter x:nat.
Parameter N:nat. 
Definition z:nat := 0.
Definition r:= ord x N.
Hypothesis H: r>0 /\ 2 <= x <= N-1.
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
Hypothesis HQFT: WF_Unitary QFT /\ forall k:nat, QFT × (∣ k ⟩_ t) =
 / √ 2 ^ t .* (big_sum (fun j : nat => (cos (((2 * PI)/(2^t)) * j * k),  sin (((2 * PI)/(2^t)) * j * k)) .*  (∣ j ⟩_ t)) (2 ^ t)).
Hypothesis HU_plus: WF_Unitary U_plus /\ ( U_plus × (∣ 0 ⟩_ L) = (∣ 1 ⟩_ L)).
Hypothesis (Ht: forall j s:nat, and ((delt_n j < 2^t)%nat /\ (s < r)%nat) ((s/r * 2^t) = delt_n j)).
Hypothesis HU: WF_Unitary U /\ (forall j:nat, j< N -> U × (Vec (2 ^ L) j) = (Vec (2 ^ L) (x * j mod N))) /\ 
                               (forall j:nat, j>=N /\ j<(2^L)-> U × (Vec (2 ^ L) j) = (Vec (2 ^ L) j)).
Definition  H := p.H .
Definition  U_f (i:nat):= exp_U U i.
Definition  Us (s:nat):=  / √ r .* (big_sum (fun k:nat=> (cos (- ((2 * PI)) * (s/r) * k),  sin (- ((2 * PI)) * (s/r) * k)) .*  Vec (2 ^ L) (x ^ k mod N)) (r) ) .
Definition  b:nat := 1.
Definition  z':nat:=2 .
Definition  b' := (AMod (APow x z ') (N)) .
Definition  P (s:nat): Pure_formula := (BEq z' ' ((s/r * 2^t))) .

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
       z  := (Afun f (Rdiv) z' ' ((2^t)));
       b := b'
       end }>. 

Lemma HU_s: 
  / √ r .*  (big_sum (fun s:nat=> Us s) (r) ) =(∣ 1 ⟩_ (L)).
Proof. unfold Us. rewrite Mscale_Msum_distr_r. rewrite Mscale_assoc. 
       rewrite big_sum_swap_order. 
       rewrite (big_sum_eq_bounded _ ((fun i : nat =>
       (@big_sum C _ (fun j : nat =>
          (cos (- (2 * PI) * (j / r) * i), sin (- (2 * PI) * (j / r) * i))) r)
          .* ∣ x ^ i mod N ⟩_ (L)))).
Admitted.



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

Lemma cons_sin_plus_mult: forall i j, 
(cos (i + j ), sin (i +j ))=((cos i, sin i) * (cos j , sin j))%C.
Proof. intros. rewrite cos_plus. rewrite sin_plus. 
       unfold Cmult. simpl. f_equal. rewrite Rplus_comm.
       reflexivity.
Qed.


Lemma simpl_U_Us: forall s,
U × Us s = (cos ((2*PI )*(s/r )), sin ((2*PI) *(s/r))) .* Us s.
Proof. intros. pose HU. pose HNL. pose H. unfold Us. rewrite Mscale_mult_dist_r.
       rewrite Mscale_assoc. rewrite Cmult_comm.
       rewrite <-Mscale_assoc. f_equal. 
       rewrite Mmult_Msum_distr_l. 
       rewrite <-Mscale_Msum_distr_r.
       rewrite (big_sum_eq_bounded _ 
       ((fun i : nat =>  ((cos (- (2 * PI ) * (s / r) * i), sin (- (2 * PI ) * (s / r) * i)) .* ∣ x ^ (i+1) mod N ⟩_ (L))))).
       rewrite (big_sum_eq_bounded ((fun i : nat =>
       (cos (2 * PI * (s / r)), sin (2 * PI * (s / r))) .* ((cos (- (2 * PI) * (s / r) * i),
            sin (- (2 * PI) * (s / r) * i)).* ∣ x ^ i mod N ⟩_ (L)))) 
       ((fun i : nat =>  ((cos (-(2 * PI ) * (s / r) * (i-1)), sin (-(2 * PI) * (s / r) * (i-1))) .* ∣ x ^ i mod N ⟩_ (L))))).
       admit.
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
Admitted.


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
 =( / √ r .* big_sum  (fun s : nat =>   (Vec (2^t) (s/r * 2^t)) ⊗  Us s) r) .
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
apply WF_vec. rewrite <-(Nat.mul_1_l (2 ^ t)) at 2.
apply Nat.mul_lt_mono_pos_r. apply pow_gt_0. 
apply Nat.div_lt_upper_bound. unfold r. lia.
rewrite Nat.mul_1_r. assumption. 
destruct a0. rewrite H2.  
f_equal. repeat rewrite RtoC_pow. repeat rewrite <-RtoC_inv. 
f_equal. f_equal.  rewrite sqrt_pow. reflexivity. lra.
apply sqrt_neq_0_compat. apply pow_lt. lra. 
apply pow_nonzero. apply sqrt2_neq_0.
apply big_sum_eq_bounded. intros.
f_equal. f_equal; f_equal; f_equal. pose Ht. admit.
admit. 
apply WF_adjoint. apply HQFT.
Admitted.


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
       inversion_clear H0; simpl in H4.
       apply ceval_single_1 in H4.
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


Theorem OF_correctness: 
{{BEq ((Nat.gcd x N)) 1 }} OF {{BEq z ' r}}.
Proof. pose HtL. pose (Qsys_to_Set_min_max t (t+L)). destruct a0; try lia.
                pose (Qsys_to_Set_min_max 0 t). destruct a0; try lia.   
unfold OF.
eapply rule_seq.
eapply rule_conseq_l'.
eapply rule_assgn with (F:=(BEq z ' 1)).
eapply implies_trans. apply rule_PT. apply Assn_true_F. unfold not. simpl. apply In_empty.  
eapply rule_seq.
eapply rule_conseq_l'.
eapply rule_assgn with (F:=( (BEq z ' 1) /\s ( BEq b ' (AMod ( APow x  (z '))  N )))).
implies_trans_solve 1 Assn_conj_F.  
eapply rule_Conj_two; try apply implies_refl.
implies_trans_solve 0  rule_PT.  unfold b'. apply Assn_true_F.


simpl; intro; try repeat match goal with 
H:NSet.In ?b (NSet.union ?c1 ?c2)|-_ => apply NSet.union_1 in H;
destruct H end;
try match goal with 
H:NSet.In ?b (NSet.add ?a (NSet.empty)) |-_ => apply NSet.add_3 in H;
try discriminate end;
try match goal with 
H:NSet.In ?b NSet.empty |- _ => eapply In_empty; apply H end.

simpl;intro; try repeat match goal with 
H:NSet.In ?b (NSet.union ?c1 ?c2)|-_ => apply NSet.union_1 in H;
destruct H end;
try match goal with 
H:NSet.In ?b (NSet.add ?a (NSet.empty)) |-_ => apply NSet.add_3 in H;
try discriminate end;
try match goal with 
H:NSet.In ?b NSet.empty |- _ => eapply In_empty; apply H end.

eapply rule_conseq_l with (P':=( (BNeq z ' r /\p (BNeq b ' 1)))).
assert(1<>r). admit.


seman_sovle; destruct H5; unfold Pure_eval in *;
unfold beval in *; unfold aeval in *; unfold fst in *;
bdestruct (c_find z x0 =? 1).
try rewrite H7;
try apply Nat.eqb_neq in H4; try rewrite H4;  try auto.
destruct H5. 
bdestruct(c_find b x0 =? x ^ c_find z x0 mod N).
rewrite H8.  rewrite H7. simpl. rewrite Nat.mul_1_r.

rewrite Nat.mod_small. bdestruct (x=?1). 
pose H. unfold x in H9. lia. auto. pose H. unfold x.
unfold N. lia.    
 destruct H6. destruct H5.
eapply rule_conseq.
eapply rule_while with (F0:= (BNeq z ' r)) (F1:= (BEq z ' r)).
*eapply rule_seq.
eapply rule_conseq_l.
apply rule_PT.
apply rule_QInit. 
*eapply rule_seq.
eapply rule_conseq_l.
apply rule_OdotE.
eapply rule_qframe'. simpl. apply HtL. 
split. apply rule_QInit. simpl. 
split. apply inter_empty. left. reflexivity.
right.  rewrite H0. lia.  
* eapply rule_seq.
eapply rule_qframe. simpl. pose HtL. lia.  
split. apply rule_QUnit_One'. lia. 
simpl. 
split. apply inter_empty. left. reflexivity.
left.  rewrite H3.  lia. 
unfold U_v. repeat rewrite Nat.sub_diag. rewrite Nat.sub_0_r. simpl.
rewrite kron_1_l; auto_wf. rewrite kron_1_r; auto_wf. 
rewrite Had_N.  
* eapply rule_seq.
eapply rule_qframe'. simpl. apply HtL. 
split. apply rule_QUnit_One'. lia. 
simpl.
split. apply inter_empty. left. reflexivity.
right. rewrite H0; lia. 
 unfold U_v. repeat rewrite Nat.sub_diag.
simpl. pose HU_plus. rewrite kron_1_l; auto_wf. rewrite kron_1_r; auto_wf.
destruct a0. assert(L=t + L - t). lia. destruct H6.
rewrite H5.
* eapply rule_seq.
eapply rule_conseq_l.
eapply rule_odotT.
eapply rule_conseq_l.
eapply rule_Separ.
assert(L=t + L - t). lia. destruct H6.
assert(t=t-0). lia. destruct H6.
rewrite simpl_H_Uplus.
eapply rule_QUnit_Ctrl. lia. 
rewrite simpl_Uf.
* eapply rule_seq.
eapply rule_QUnit_One'. lia. 
assert(t=t-0). lia. destruct H6.
assert(t+L=t+L-0). lia. destruct H6.
rewrite simpl_QFT'.
* eapply rule_seq. 
eapply rule_conseq_l'.
eapply rule_QMeas with (s:=0) (e:=t+L) (P:=P). lia.
admit.  unfold P. apply rule_Conj_two. 
apply implies_refl. implies_trans_solve 0  rule_PT.   
admit. 
*eapply rule_seq. 
eapply rule_conseq_l. 
eapply rule_Oplus. rewrite big_pOplus_get_npro.
eapply rule_conseq_l'.
eapply rule_assgn with (F:= (BEq z '(Afun f (fun r1 r2 : nat => (r1 / r2)%R) z' ' ((2 ^ t))))).
eapply implies_trans'. apply Assn_true_F. simpl.  

intro; try repeat match goal with 
H:NSet.In ?b (NSet.union ?c1 ?c2)|-_ => apply NSet.union_1 in H;
destruct H end;
try match goal with 
H:NSet.In ?b (NSet.add ?a (NSet.empty)) |-_ => apply NSet.add_3 in H;
try discriminate end;
try match goal with 
H:NSet.In ?b NSet.empty |- _ => eapply In_empty; apply H end.
  admit.
eapply rule_conseq_l'. apply rule_Dassgn. 
eapply implies_trans. apply rule_PT. unfold b'.

eapply implies_trans'. apply (Assn_impl b  <{ x ^ (z) ' % N }>
(BEq b ' (<{ x ^ (z) ' % N }>))). 

unfold assert_implies. intros.
rewrite sat_Assert_to_State in *. 
admit.
apply Assn_true. simpl. 
intro; try repeat match goal with 
H:NSet.In ?b (NSet.union ?c1 ?c2)|-_ => apply NSet.union_1 in H;
destruct H end;
try match goal with 
H:NSet.In ?b (NSet.add ?a (NSet.empty)) |-_ => apply NSet.add_3 in H;
try discriminate end;
try match goal with 
H:NSet.In ?b NSet.empty |- _ => eapply In_empty; apply H end. 
assert(L=t+L-t). lia. destruct H4. 
apply a0.

implies_trans_solve 0 SAnd_PAnd_eq. 
unfold assert_implies. intros.
rewrite sat_Assert_to_State in *.
econstructor. 
assert(Datatypes.length [1%R;0%R] =
Datatypes.length
[<{ (z) ' <> r }> /\s <{ (b) ' <> 1 }>;
<{ (z) ' = r }> /\s <{ ~ (b) ' <> 1 }>] ). reflexivity.
apply H5. simpl. econstructor. eapply WF_sat_State.
apply H4. unfold distribution_formula.  simpl. split. 
econstructor. lra. econstructor. lra. econstructor.
repeat rewrite sum_over_list_cons. rewrite sum_over_list_nil.
repeat rewrite Rplus_0_r. reflexivity.
apply (npro_formula_cons  _ (<{ (z) ' = r }> /\s <{ ~ (b) ' <> 1 }>)) in H4.
assumption. 
assert(Sorted.Sorted (StateMap.Raw.PX.ltk (elt:=qstate s e)) [(([r;1]), d_trace (mu) .* (Mmult (Vec  (2^(e-s)) 0) (adjoint (Vec  (2^(e-s)) 0))))]).
apply Sorted.Sorted_cons. apply Sorted.Sorted_nil.
apply Sorted.HdRel_nil.
exists (StateMap.Build_slist H5).
split. unfold d_trace. simpl. unfold s_trace.
unfold q_trace.  simpl. rewrite Rplus_0_r.
rewrite trace_mult_dist. rewrite Cmod_mult.
rewrite Cmod_R. rewrite Rabs_right.
rewrite trace_mult'. rewrite Vec_inner_1. 
unfold c_to_Vector1. Msimpl. rewrite trace_I.
rewrite Cmod_1. rewrite Rmult_1_r. reflexivity.
apply pow_gt_0.
apply WF_sat_State in H4. destruct H4.
apply WF_dstate_in01_aux in H6. lra.
econstructor. admit.
econstructor. simpl.  admit.
econstructor. apply rule_Conj_split_l. 
Admitted.
End OF.


