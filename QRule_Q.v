Require Import Reals.
Require Import Coquelicot.Complex.
Require Import Strings.String.
Require Import Lists.List.
Import ListNotations.

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
From Quan Require Import QState.
From Quan Require Import QIMP.
From Quan Require Import QAssert.
From Quan Require Import ParDensityO.
From Quan Require Import Basic_Supplement.


(* Lemma big_sum_Mmult_l : forall (n m o:nat) (M: Matrix n m) (f:nat-> Matrix m o) n', 
    M × big_sum f n' = big_sum (fun x => M × f x) n'.
Proof. intros. induction n'.
       simpl. rewrite Mmult_0_r. reflexivity.
       simpl. rewrite Mmult_plus_distr_l.
       rewrite IHn'. reflexivity.
Qed.

Lemma big_sum_Mmult_r : forall (n m o:nat) (M: Matrix n o) (f:nat-> Matrix m n) n', 
    big_sum f n'  ×  M = big_sum (fun x => f x × M) n'.
Proof. intros. induction n'.
       simpl. rewrite Mmult_0_l. reflexivity.
       simpl. rewrite Mmult_plus_distr_r.
       rewrite IHn'. reflexivity.
Qed. *)

Local Open Scope nat_scope.


Definition U_v {s' e' s e:nat} (U: Square (2^(e'-s'))) (v: Vector (2^(e-s))):
Vector (2^(e-s)) := 
@Mmult ((2^(e-s)))  (2^(e-s)) 1  (I (2^(s'-s)) ⊗ U ⊗ (I (2^(e-e'))))  v.


(* Notation "U [ s' e' ] v":= (U_v s' e' _ _ U v) (at level 80, 
  no associativity) : assert_scope. *)
Lemma Mmult_inject{m n o:nat}: forall (A C:Matrix m n)
(B:Matrix n o), 
A × B = C × B -> A= C.
Proof. intros.  unfold Mmult in *.
      prep_matrix_equality.
      revert x. revert y. 
      assert( ~(exists y x :nat , A x y <> C x y) -> 
      forall y x : nat, A x y = C x y  ). 
      intros. unfold not in H0. 
      assert( A x y = C x y <-> ~(A x y <> C x y)).
      split. intros. unfold not. intros. apply H2 in H1.
      destruct H1. apply NF_1. unfold not.  intros. 
      apply H2 in H1. destruct H1. rewrite H1. 
        unfold not.
       intros. 
       assert(exists y x : nat, A x y = C x y -> False ).
       exists y. exists x. assumption.
       apply H0 in H3. destruct H3. 
Admitted.


(* Lemma Mmult_trans{n1 m1 n2 n3 m3 n4}: forall (A: Matrix n1 m1) (B:Matrix n2 n2)
(C:Matrix n3 m3) (D:Matrix n4 n4), WF_Matrix C->
n2=n3 -> m3=n4 -> n1 =n2 -> m1=n4 -> WF_Unitary  B -> WF_Unitary D->
A= @Mmult n2 m3 n4 (@Mmult n2 n2 m3  B  C) D->
@Mmult n2 n4 n4 (@Mmult n2 n2 m1  B†  A) D† = C.
Proof. intros.  subst.  repeat  rewrite <-Mmult_assoc.
 unfold WF_Unitary in *. destruct H4. rewrite H1.
 destruct H5. repeat rewrite Mmult_assoc. assert((D × (D) †)= I n4).
 assert(D × ((D) † × D)= D). rewrite H3. rewrite Mmult_1_r.
 reflexivity. assumption. rewrite <-Mmult_assoc in H4.
 assert(D= I n4  × D). rewrite Mmult_1_l. reflexivity.
 assumption. rewrite <-H4 in H5 at 1. apply Mmult_inject in H5.
 assumption.   rewrite H4. rewrite Mmult_1_r. rewrite Mmult_1_l. reflexivity.
 intuition. intuition. Qed.

Lemma Mmult_assoc': forall {m n o p q r: nat} (A : Matrix m n) (B : Matrix o p) (C : Matrix q r),
n=o -> p=q ->
@Mmult m p r (@Mmult m n p A B) C =@Mmult m n r A (@Mmult o p r B C).
Proof. intros; subst. apply Mmult_assoc. 
Qed.

Lemma kron_assoc': forall {m n p q r s t u v w : nat} (A : Matrix m n) (B : Matrix p q) 
(C : Matrix r s) (_ : @WF_Matrix m n A) (_ : @WF_Matrix p q B)
(_ : @WF_Matrix r s C), 
t=(Init.Nat.mul p r)-> u=(Init.Nat.mul q s)->
v=(Init.Nat.mul m p) ->w=(Init.Nat.mul n q)->
(@kron v w r s (@kron m n p q A B) C) =
(@kron m n t u A (@kron p q r s B C)) .
Proof. intros. subst. apply kron_assoc; assumption.  
Qed. *)
 
#[export]Hint Resolve WF_vec: wf_db.
#[export]Hint Resolve WF_mult: wf_db.
#[export] Hint Extern 1 (pow_gt_0) => lia : wf_db.

Ltac type_sovle':=
  try (repeat rewrite  <-pow_add_r; f_equal ; lia).

Lemma  Ptrace_trace: forall  n (A:Square (2^n)) s e,
s <= n - e->
trace (PMpar_trace A  s e) = trace A.
Proof. intros. rewrite Ptrace_l_r'.
   assert(2^(n-e-s)=1 * 2 ^ (n - e - s) * 1) . lia.
   destruct H0. rewrite big_sum_trace.
   rewrite (big_sum_eq_bounded  _ ((fun i : nat =>
   trace (big_sum
      (fun j : nat =>
        ( (∣ i ⟩_ (s) × ⟨ i ∣_ (s)) ⊗ I (2 ^ (n - e - s)) ⊗  (∣ j ⟩_ (e)  × ⟨ j ∣_ (e)) × A))
        (2 ^ e))))).
    rewrite <-big_sum_trace.
    assert(2^n = 2^s * 2^(n-e -s) * (2^e)). 
    repeat rewrite<- Nat.pow_add_r. admit. destruct H0.
    f_equal.
    rewrite (big_sum_eq_bounded  _ ((fun i : nat =>
    @Mmult (2^n) (2^n) (2^n) ( (∣ i ⟩_ (s) × ⟨ i ∣_ (s)) ⊗   I (2 ^ (n - e - s))
    ⊗  (big_sum
      (fun j : nat => (∣ j ⟩_ (e) × ⟨ j ∣_ (e)) ) 
      (2 ^ e) ))  A ))  ).
Admitted.
     



Local Open Scope nat_scope.
 Theorem rule_Qinit_aux:  forall  s e (n:nat) (st :state n) (st': state n),
WF_state st->
ceval_single (QInit s e) [st] [st'] ->
State_eval (QExp_s s e  (Vec (2^(e-s)) 0)) st'.
Proof.  intros s e n st st' H'. intros. simpl in *.
        destruct st. destruct st'.
        inversion H; subst.  inversion H7; subst.
        rewrite Ptrace_l_r' in *.  
        injection H6. intros. 
        rewrite <-H0.  simpl snd.
        unfold QInit_fun.
        assert((e-s)%nat= (n - (n - e) - s)%nat).
        lia. destruct H2.  
        assert((2 ^ s * 2 ^ (e - s) * 2 ^ (n - e))%nat=(2 ^ n)%nat).
        type_sovle'.  destruct H2.
        Local Open Scope C_scope.     
       remember (((R1 /
       Cmod
         (trace
            (big_sum
               (fun i0 : nat =>
                I (2 ^ s) ⊗ (∣ 0 ⟩_ (e - s) × ⟨ i0 ∣_ (e - s))
                ⊗ I (2 ^ (n - e)) × q
                × (I (2 ^ s) ⊗ (∣ 0 ⟩_ (e - s) × ⟨ i0 ∣_ (e - s))
                   ⊗ I (2 ^ (n - e))) †) (2 ^ (e - s)))))%R)).
      split. lia. split. lia.
      remember (fun i : nat =>
       @big_sum (Square (2^(e-s))) (M_is_monoid (2 ^ (e-s)) (2 ^ (e-s)))
         (fun j : nat =>
         r  .* @big_sum (Square (2^(e-s))) (M_is_monoid (2 ^ (e-s)) (2 ^ (e-s)))
         (fun i0 : nat => ((∣ 0 ⟩_ (e - s) × ⟨ i0 ∣_ (e - s))) ×
         (⟨ i ∣_ (s) ⊗ I (2^ (e-s)) ⊗ ⟨ j ∣_ (n - e) × q × 
         (⟨ i ∣_ (s) ⊗ I (2^ (e-s))  ⊗ ⟨ j ∣_ (n - e) ) † )  ×
         ((∣ i0 ⟩_ (e - s) × ⟨ 0 ∣_ (e - s)))) (2 ^ (e - s))) (2 ^ (n - e))). 
      rewrite (@big_sum_eq_bounded (Square (2^(e-s))) _ _  m ((2 ^ s))).
   rewrite Heqm.   
   remember ((fun i : nat => ∣ 0 ⟩_ (e - s) × ( big_sum (fun j : nat =>
      r  .* big_sum (fun i0 : nat => ⟨ i0 ∣_ (e - s) × 
            (⟨ i ∣_ (s) ⊗ I (2 ^ (e - s)) ⊗ ⟨ j ∣_ (n - e) × q
               × (⟨ i ∣_ (s) ⊗ I (2 ^ (e - s)) ⊗ ⟨ j ∣_ (n - e)) †)  
               × ∣ i0 ⟩_ (e - s) ) (2 ^ (e - s))) (2 ^ (n - e)) ) × ⟨ 0 ∣_ (e - s))). 
   rewrite (big_sum_eq_bounded _ m0 _).  rewrite Heqm0. 
   rewrite <-(Mmult_Msum_distr_r _ _ (∣ 0 ⟩_ (e - s)) †).
   rewrite <-Mmult_Msum_distr_l.  unfold outer_product. 
   assert(∣ 0 ⟩_ (e - s) × ⟨ 0 ∣_ (e - s) = ∣ 0 ⟩_ (e - s) × I 1 × ⟨ 0 ∣_ (e - s)). 
   rewrite Mmult_1_r. reflexivity.  apply WF_vec. 
   apply pow_gt_0.   
   rewrite H2. f_equal. f_equal. 
   remember ((fun i : nat => r .* (trace (big_sum (fun j : nat => 
   ((⟨ i ∣_ (s) ⊗ I (2 ^ (e - s)) ⊗ ⟨ j ∣_ (n - e) × q
   × (⟨ i ∣_ (s) ⊗ I (2 ^ (e - s)) ⊗ ⟨ j ∣_ (n - e)) †)) )
    (2 ^ (n - e)))  .* I 1))). 
  rewrite (big_sum_eq_bounded _ m1 _ ). rewrite Heqm1.
  rewrite Mscale_Msum_distr_r. rewrite<- big_sum_Mscale_r.
  rewrite<-big_sum_trace. rewrite Mscale_assoc.
  
  rewrite Heqr. admit. 
  
  rewrite Heqm1.   
  intros. rewrite big_sum_trace. rewrite big_sum_Mscale_r.  
 rewrite<- Mscale_Msum_distr_r.  apply big_sum_eq_bounded. 
  intros. f_equal. assert((2 ^ (e - s))%nat=(1 * 2 ^ (e - s) * 1)%nat).
  lia. destruct H8. 
  apply trace_base.   apply WF_mult. apply WF_mult. auto_wf. 
  unfold WF_state in H'. simpl in H'. unfold WF_qstate in H'.
  apply WF_Mixed in H'.
  assert((2 ^ s * 2 ^ (e - s) * 2 ^ (n - e))%nat=(2 ^ n)%nat).
  type_sovle'. destruct H8. assumption. auto_wf.
  

  rewrite Heqm0.  intros.
   assert((2 ^ (e - s))%nat= (1 * 2 ^ (e - s) * 1)%nat).
   lia. destruct H4.
  rewrite Mmult_Msum_distr_l. rewrite Mmult_Msum_distr_r.
  apply big_sum_eq_bounded.  intros.  rewrite Mscale_mult_dist_r.  
   rewrite Mscale_mult_dist_l.   
  rewrite Mmult_Msum_distr_l.   rewrite Mmult_Msum_distr_r.
  f_equal. apply big_sum_eq_bounded. 
   intros.  repeat rewrite <-Mmult_assoc.  reflexivity.
 
  rewrite Heqm.  intros. apply big_sum_eq_bounded.  intros.
  rewrite Mscale_mult_dist_r. rewrite Mmult_Msum_distr_l. 
   rewrite Mscale_mult_dist_l. f_equal; type_sovle. 
   rewrite Mmult_Msum_distr_r.  
  apply big_sum_eq_bounded. 
  intros.   rewrite<-Mmult_assoc. rewrite <-Mmult_assoc.
      repeat rewrite kron_mixed_product. 
      repeat rewrite Mmult_1_r. repeat rewrite Mmult_1_l.
   repeat rewrite kron_adjoint.   rewrite Mmult_assoc.  rewrite Mmult_assoc.
   repeat rewrite id_adjoint_eq. rewrite Mmult_adjoint. 
    repeat rewrite kron_mixed_product.  
    repeat rewrite Mmult_1_r. repeat rewrite Mmult_1_l. 
   rewrite <-Mmult_assoc.  
 assert((2^(e-s))%nat =(1 * 2 ^ (e - s) * 1)%nat). lia. destruct H8.
 assert((2 ^ s * 2 ^ (e - s) * 2 ^ (n - e))%nat=(2 ^ n)%nat). type_sovle'. 
  destruct H8. 
 rewrite Mmult_assoc_5. f_equal. 
 f_equal. apply Logic.eq_trans with ((I 1 ⊗ (∣ 0 ⟩_ (e - s) × ⟨ x1 ∣_ (e - s)) ⊗ I 1) 
 × (⟨ x ∣_ (s) ⊗ I (2 ^ (e - s)) ⊗ ⟨ x0 ∣_ (n - e))) .
 repeat rewrite kron_mixed_product.  repeat rewrite Mmult_1_l.
 rewrite Mmult_1_r. reflexivity. apply WF_mult. 
 apply WF_vec. apply pow_gt_0. auto_wf. auto_wf. 
 auto_wf. f_equal; try lia.   
 rewrite kron_1_l. rewrite kron_1_r. reflexivity. 
 apply WF_mult. 
 apply WF_vec. apply pow_gt_0. auto_wf. 

 apply Logic.eq_trans with ((⟨ x ∣_ (s)) † ⊗ I (2 ^ (e - s))
 ⊗ (⟨ x0 ∣_ (n - e)) † × (I 1 ⊗ (∣ x1 ⟩_ (e - s) × ⟨ 0 ∣_ (e - s)) ⊗ I 1) 
 ) . repeat rewrite kron_mixed_product.  repeat rewrite Mmult_1_l.
 repeat rewrite Mmult_1_r. repeat rewrite adjoint_involutive. reflexivity.
 auto_wf. auto_wf.   apply WF_mult. auto_wf. apply WF_adjoint. 
 apply WF_vec.  apply pow_gt_0.  f_equal;  try lia.   
 rewrite kron_1_l. rewrite kron_1_r. reflexivity. 
 apply WF_mult. auto_wf. apply WF_adjoint. 
 apply WF_vec.   apply pow_gt_0. auto_wf. auto_wf.  

apply WF_mult. auto_wf. apply WF_adjoint. apply WF_vec.
apply pow_gt_0. 
apply WF_mult.  apply WF_vec. 
apply pow_gt_0. auto_wf. auto_wf. auto_wf. 
lia.
 Admitted. 




 Lemma Mmult_trans'{n}: forall (A B C D: Square n) ,
 WF_Matrix C-> WF_Unitary  B -> WF_Unitary D->
 A= B × C × D->
 (B† × A) × D† = C.
 Proof. intros. rewrite H2.   repeat  rewrite <-Mmult_assoc.
  unfold WF_Unitary in *. destruct H0. rewrite H3.
  destruct H1. repeat rewrite Mmult_assoc. assert((D × (D) †)= I n). 
  assert(D × ((D) † × D)= D).
 rewrite H4. rewrite Mmult_1_r.
 reflexivity. assumption. rewrite <-Mmult_assoc in H5.
 assert(D= I n  × D). rewrite Mmult_1_l. reflexivity. 
 assumption. rewrite <-H5 in H6 at 1.
  apply Mmult_inject in H6.
 assumption.   rewrite H5. 
   rewrite Mmult_1_r. rewrite Mmult_1_l. reflexivity.
  intuition. intuition. Qed.

  (* Lemma big_sum_Mmult_l' : forall (n m o p:nat) (M: Matrix n m) (f:nat-> Matrix o p) n', 
  m=o->
  @Mmult n m p M  (big_sum f n') = big_sum (fun x => M × f x) n'.
Proof. intros; subst. induction n'.
     simpl. rewrite Mmult_0_r. reflexivity.
     simpl. rewrite Mmult_plus_distr_l.
     rewrite IHn'. reflexivity.
Qed.


Lemma big_sum_Mmult_r' : forall (n m o p:nat) (M: Matrix o p) (f:nat-> Matrix m n) n', 
  n=o->
  @Mmult m n p (big_sum f n')    M = big_sum (fun x => f x × M) n'.
Proof. intros; subst. induction n'.
     simpl. rewrite Mmult_0_l. reflexivity.
     simpl. rewrite Mmult_plus_distr_r.
     rewrite IHn'. reflexivity.
Qed. *)

Lemma Mmult_kron_5: forall {m1 n1 m2 n2 m3 n3 m4 n4 m5 n5:nat} (A: Matrix m1 n1)
(B: Matrix m2 n2) (C: Matrix m3 n3) (D: Matrix m4 n4) (E: Matrix m5 n5), 
WF_Matrix A -> WF_Matrix B -> WF_Matrix C -> WF_Matrix D -> WF_Matrix E->
A ⊗ (B ⊗ C ⊗ D) ⊗ E= (A ⊗ B) ⊗ C ⊗ (D ⊗ E).
Proof. intros. repeat rewrite <-kron_assoc; try reflexivity;
       auto_wf.
Qed.


Ltac type_sovle:=
   try (rewrite <-Nat.pow_add_r; rewrite Nat.mul_1_r;  f_equal;
   rewrite Nat.add_comm; rewrite Nat.sub_add; [reflexivity|assumption]);
   try (repeat rewrite Nat.mul_1_l; repeat rewrite Nat.mul_1_r; reflexivity);
   try ( repeat rewrite <-Nat.pow_add_r; f_equal; f_equal;
   rewrite Nat.add_comm; rewrite Nat.sub_add; [reflexivity|assumption]);
   try (repeat rewrite <-Nat.pow_add_r; f_equal; rewrite Nat.add_comm; rewrite Nat.sub_add;
   [reflexivity|assumption]);
   try (repeat rewrite <-Nat.pow_add_r; f_equal;  rewrite Nat.sub_add;
   [reflexivity|assumption]);
   try (symmetry;  apply add_sub_eq_l; apply sub_add;
   intuition);
   try (rewrite mul_1_r;
   rewrite Nat.add_0_r; reflexivity);
   try ( rewrite <-pow_add_r; rewrite <-pow_add_r; f_equal;
   repeat rewrite <-le_plus_minus'; reflexivity).

Lemma pow_add_assoc_3: forall ( s s' e' e:nat ),
s<=s'->s'<=e'->e'<=e->
(2 ^ (e - s) )%nat=
(2 ^ (s' - s) * 2 ^ (e' - s') * 2 ^ (e - e'))%nat.
Proof. intros.  
repeat rewrite <-Nat.pow_add_r. f_equal. lia. 
Qed.


Local Open Scope assert_scope.
Local Open Scope nat_scope.
Theorem rule_QUnit_aux:  forall s' e' s e (U: Square (2^(e'-s'))) (v: Vector (2^(e-s)))
(n:nat) (st :state n) (st': state n),
s<=s' /\ e' <=e ->
WF_state st->WF_Matrix v->
ceval_single (QUnit_One s' e' U) [st] [st'] ->
State_eval (QExp_s s  e  (U_v U† v) ) st->
State_eval (QExp_s s  e  v ) st'.
Proof. 
      intros s' e' s e U v n st st' He H' Hv. 
      intros. simpl in *. rewrite Ptrace_l_r' in *.
      assert((e-s)%nat= (n - (n - e) - s)%nat).
      f_equal; lia.  destruct H1. 
      unfold U_v in *. unfold outer_product in *.
      rewrite Mmult_adjoint in H0.
      rewrite <-Mmult_assoc in H0.
      inversion H; subst. inversion H9; subst.
      clear H9. apply inj_pair2_eq_dec in H3.
      apply inj_pair2_eq_dec in H3. subst.
      injection H7. intros. rewrite<- H1. simpl in *.
      rewrite (Mmult_assoc _ v (v) †) in H0.
      destruct H0. destruct H2. split. intuition.
      split. intuition.
      apply Mmult_trans'  in H3. rewrite <- H3. clear H3.

      remember (((R1 / Cmod (trace (QUnit_One_fun s' e' U rho))))%R).
      remember (((R1 / Cmod (trace rho))%R)).  
      unfold QUnit_One_fun. unfold q_update. unfold super.
      assert(2 ^ (e - s)= 2 ^ (s' - s) * 2 ^ (e' - s') * 2 ^ (e - e')).
      type_sovle'. destruct H3.  
      assert(2 ^ (e - s)= (2 ^ (e - s) + 0) * 1); type_sovle. destruct H3.
      rewrite Mmult_Msum_distr_l. rewrite Mmult_Msum_distr_r.
      apply big_sum_eq_bounded. intros.
      rewrite Mmult_Msum_distr_l. rewrite Mmult_Msum_distr_r.
      apply big_sum_eq_bounded. intros. 

      rewrite  (Mmult_assoc _ rho _). 
      rewrite <-Mscale_mult_dist_r.   
      rewrite <-Mscale_mult_dist_l.
      rewrite  <-(Mmult_assoc _ (r .* rho) _).  
      assert((@adjoint (Nat.pow (S (S O)) n) (Nat.pow (S (S O)) n) 
      ((I (2 ^ s') ⊗ U ⊗ I (2 ^ (n - e')))))=
      (((I (2 ^ s') ⊗ U ⊗ I (2 ^ (n - e'))))) † ).
      f_equal; type_sovle'.  rewrite H6.
      repeat rewrite kron_adjoint. repeat rewrite id_adjoint_eq. 
      repeat rewrite adjoint_involutive.
      assert( 2 ^ (s) * 2 ^ (e - s) * 2 ^ (n - e)= 2 ^ (n)).
      type_sovle'. destruct H9.  
      repeat rewrite Mmult_assoc_5.  f_equal. f_equal. 

  assert( 2 ^ (s' - s) * 2 ^ (e' - s') * 2 ^ (e - e')= 2 ^ (e - s)).
  type_sovle'. destruct H9. 
  repeat rewrite kron_adjoint.   rewrite adjoint_involutive.
  eapply Logic.eq_trans with ((I 1 ⊗ ((I (2 ^ (s' - s))) † ⊗ U ⊗ (I (2 ^ (e - e'))) †) ⊗ I 1) 
  × (⟨ x ∣_ (s) ⊗ I (2 ^ (s' - s) * 2 ^ (e' - s') * 2 ^ (e - e'))
   ⊗ ⟨ x0 ∣_ (n - e))). repeat rewrite kron_mixed_product.  
   repeat rewrite Mmult_1_r; try auto_wf. repeat rewrite Mmult_1_l; try auto_wf.
   eapply Logic.eq_trans with ((⟨ x ∣_ (s)
   ⊗ I (2 ^ (s' - s) * 2 ^ (e' - s') * 2 ^ (e - e'))
   ⊗ ⟨ x0 ∣_ (n - e)) × ((I (2^s)) ⊗ ((I (2 ^ (s'-s))) ⊗ U ⊗ I (2 ^ (e - e'))) ⊗ I (2^(n-e)) )).
   rewrite Mmult_kron_5; try auto_wf. f_equal; try lia.   
   f_equal; try type_sovle'. 
     rewrite id_kron. f_equal; try type_sovle'. f_equal; type_sovle'.
     rewrite id_kron. f_equal. try type_sovle'. apply H8. 
     repeat rewrite kron_mixed_product.  
     repeat rewrite Mmult_1_r; try auto_wf. repeat rewrite Mmult_1_l; try auto_wf.
    repeat  rewrite id_adjoint_eq.  f_equal. destruct H8. auto_wf. destruct H8. auto_wf. 
    f_equal;  type_sovle'; try lia. rewrite kron_1_l. rewrite kron_1_r. reflexivity.
    destruct H8. auto_wf.

    admit.

    assert( 2 ^ (s' - s) * 2 ^ (e' - s') * 2 ^ (e - e')= 2 ^ (e - s)).
    type_sovle'. destruct H9. 
    eapply Logic.eq_trans with ((∣ x ⟩_ (s)
    ⊗ I (2 ^ (s' - s) * 2 ^ (e' - s') * 2 ^ (e - e'))
    ⊗ ∣ x0 ⟩_ (n - e))× (I 1 ⊗ (I (2 ^ (s' - s)) ⊗ (U) † ⊗ I (2 ^ (e - e'))) ⊗ I 1) ). 
    repeat rewrite kron_mixed_product.  
     repeat rewrite Mmult_1_r; try auto_wf. repeat rewrite Mmult_1_l; try auto_wf.
     eapply Logic.eq_trans with (  
     ((I (2^s)) ⊗ ((I (2 ^ (s'-s))) ⊗ (U) † ⊗ I (2 ^ (e - e'))) ⊗ I (2^(n-e)) )
     × (∣ x ⟩_ (s)
   ⊗ I (2 ^ (s' - s) * 2 ^ (e' - s') * 2 ^ (e - e'))
   ⊗ ∣ x0 ⟩_ (n - e))). 
     rewrite Mmult_kron_5; try auto_wf. f_equal; type_sovle.   
     f_equal; type_sovle'. rewrite id_kron. f_equal; type_sovle'.
     f_equal; type_sovle'. rewrite id_kron. f_equal; type_sovle'. 
      apply WF_adjoint. apply H8. 
       repeat rewrite kron_mixed_product.  
       repeat rewrite Mmult_1_r; try auto_wf. repeat rewrite Mmult_1_l; try auto_wf.
       f_equal. destruct H8; auto_wf. destruct H8; auto_wf. 
      f_equal; type_sovle. rewrite kron_1_l. rewrite kron_1_r. reflexivity.
      destruct H8. auto_wf. auto_wf.  


      assert( 2 ^ (s' - s) * 2 ^ (e' - s') * 2 ^ (e - e')= 2 ^ (e - s)).
      type_sovle'.  destruct H4.   
     
   eapply kron_unitary.  apply kron_unitary.
   apply id_unitary .  apply transpose_unitary. apply H8. 
   apply id_unitary.
   apply transpose_unitary.
   assert((2 ^ (s'- s) * 2 ^ (e' - s') * 2 ^ (e- e'))= 2 ^(e-s)).
   type_sovle'. destruct H4. 
   apply kron_unitary.  apply kron_unitary.
   apply id_unitary . apply transpose_unitary. apply H8.
    apply id_unitary.
    apply Nat.eq_dec. apply Nat.eq_dec. 
    lia. lia.
   Admitted.


  
   Local Open Scope C_scope.
Theorem rule_Meas_aux:  forall s' e' s e (v: Vector (2^(e-s))) z x
(n:nat) (st :state n) (st': state n),
s<=s'/\ s' <= e'/\ e'<=e->
WF_state st->WF_Matrix v-> (z< 2^(e'-s'))->
st'= s_update x z (((I (2^(s'))) ⊗ ((Vec (2^(e'-s')) z ) × (Vec (2^(e'-s')) z )†) ⊗ (I (2^(n-e'))))) st->
State_eval (QExp_s  s  e  v ) st->
State_eval (QExp_s  s  e  ((R1 / (@norm (2^(e-s)) ((U_v  (∣ z ⟩_ (e'-s') × ⟨ z ∣_ (e'-s')) v))))%R .* 
                          (U_v  (∣ z ⟩_ (e'-s') × ⟨ z ∣_ (e'-s')) v))) 
                          (s_scale ((R1 / (@norm (2^(e-s)) ((U_v  (∣ z ⟩_ (e'-s') × ⟨ z ∣_ (e'-s')) v)))) ^2) st').
Proof.  intros s' e' s e v z x n st st' He' H' Hv Hz. intros.  
remember ((R1 / norm (U_v (∣ z ⟩_ (e' - s') × ⟨ z ∣_ (e' - s')) v))%R). 
simpl in *. 
unfold outer_product in *.
rewrite Mscale_adj.  
rewrite Mscale_mult_dist_r. 
rewrite Mscale_mult_dist_l. 
repeat rewrite Mscale_assoc.  
remember (((R1 / Cmod (trace ((r * (r * 1))%R .* snd st')))%R * (r * (r * 1))%R)).
 rewrite trace_mult_dist in Heqc. rewrite Rmult_1_r in Heqc.
 rewrite Rdiv_unfold in Heqc. rewrite Rmult_1_l in Heqc.
 rewrite Cmod_mult in Heqc.
 rewrite Cmod_R in Heqc. rewrite Rabs_right in Heqc.
 rewrite Cmult_comm in Heqc.  rewrite Rinv_mult in Heqc.
 rewrite RtoC_mult in Heqc.
 rewrite <-Rmult_assoc in Heqc.  rewrite Rinv_r in Heqc.  
unfold U_v in *.
rewrite Mmult_adjoint. 
rewrite <-Mmult_assoc.
rewrite (Mmult_assoc _ v _).
destruct H0 as [Hs H0]. destruct H0 as [He H0].
rewrite <-H0.
repeat rewrite Ptrace_l_r'. 
assert((e-s)%nat= (n - (n - e) - s)%nat). lia. destruct H1.
destruct st. destruct st'. 
 unfold s_update in H. simpl in *.
injection H. intros. rewrite H1.
remember ((R1 / Cmod (trace q))%R).
assert((2 ^ (e - s))%nat= (2 ^ (s' - s) * 2 ^ (e' - s') * 2 ^ (e - e'))%nat).
type_sovle'. destruct H3. 
assert((2 ^ (e - s))%nat= ((2 ^ (e - s) + 0) * 1)%nat). lia.
 destruct H3.
rewrite Mmult_Msum_distr_l. rewrite Mmult_Msum_distr_r.
rewrite <-Mscale_Msum_distr_r.
split. assumption. split. assumption. 
apply big_sum_eq_bounded. 
intros.  rewrite Mmult_Msum_distr_l. rewrite Mmult_Msum_distr_r.
rewrite <-Mscale_Msum_distr_r. 
apply big_sum_eq_bounded. 
intros.


unfold q_update. unfold super.
rewrite (Mmult_assoc _ q _). 
rewrite <-Mscale_mult_dist_r.
rewrite <-Mscale_mult_dist_l.
rewrite <-(Mmult_assoc _ (c .* q) _).
rewrite <-Mscale_mult_dist_l.
rewrite <-Mscale_mult_dist_r.
rewrite <-Mscale_mult_dist_l.
rewrite <-Mscale_mult_dist_r.

Local Open Scope nat_scope.
assert((@adjoint (Nat.pow (S (S O)) n) (Nat.pow (S (S O)) n) 
(I (2 ^ s') ⊗ (∣ z ⟩_ (e' - s') × ⟨ z ∣_ (e' - s'))
⊗ I (2 ^ (n - e')) )=
  ((I (2 ^ s') ⊗ (∣ z ⟩_ (e' - s') × ⟨ z ∣_ (e' - s'))
  ⊗ I (2 ^ (n - e')) )) † )). 
 f_equal; type_sovle'. 
  rewrite H5.  repeat rewrite kron_adjoint. 
  repeat rewrite id_adjoint_eq. repeat rewrite adjoint_involutive.
  clear H5.

assert( 2 ^ (s) * 2 ^ (e - s) * 2 ^ (n - e)= 2 ^ (n)).
type_sovle'. destruct H5.  
repeat rewrite Mmult_assoc_5.  f_equal. f_equal. 

  assert( 2 ^ (s' - s) * 2 ^ (e' - s') * 2 ^ (e - e')= 2 ^ (e - s)).
  type_sovle'.  destruct H5. 
  eapply Logic.eq_trans with ((I 1 ⊗ ((I (2 ^ (s' - s))) ⊗ (∣ z ⟩_ (e' - s') × ⟨ z ∣_ (e' - s')) ⊗ (I (2 ^ (e - e')))) ⊗ I 1) 
  × (⟨ x0 ∣_ (s) ⊗ I (2 ^ (s' - s) * 2 ^ (e' - s') * 2 ^ (e - e'))
   ⊗ ⟨ x1 ∣_ (n - e))). repeat rewrite kron_mixed_product.  
   repeat rewrite Mmult_1_r; try auto_wf. repeat rewrite Mmult_1_l; try auto_wf.
   eapply Logic.eq_trans with ((⟨ x0 ∣_ (s)
   ⊗ I (2 ^ (s' - s) * 2 ^ (e' - s') * 2 ^ (e - e'))
   ⊗ ⟨ x1 ∣_ (n - e)) × ((I (2^s)) ⊗ ((I (2 ^ (s'-s))) ⊗ (∣ z ⟩_ (e' - s') × ⟨ z ∣_ (e' - s')) ⊗ I (2 ^ (e - e'))) ⊗ I (2^(n-e)) )).
   rewrite Mmult_kron_5; try auto_wf. f_equal; type_sovle'.  lia.   
   f_equal; type_sovle'. 
     rewrite id_kron. f_equal; type_sovle'. f_equal; type_sovle'.
   rewrite id_kron. f_equal; type_sovle'.  
     repeat rewrite kron_mixed_product.  
     repeat rewrite Mmult_1_r; try auto_wf. repeat rewrite Mmult_1_l; try auto_wf.
    repeat  rewrite id_adjoint_eq.  f_equal. 
    f_equal; type_sovle. rewrite kron_1_l. rewrite kron_1_r. reflexivity.
    auto_wf. rewrite Mscale_assoc. f_equal.
    
    
  
    rewrite Heqc.  rewrite Cconj_R. rewrite H1.
    rewrite Heqr0.  
    unfold q_update. unfold super.
    assert(2 ^ (n)=  2 ^ (s) * 2 ^ (e - s) * 2 ^ (n - e)).
    type_sovle'. destruct H5.
    (* remember (I (2 ^ s') ⊗ (∣ z ⟩_ (e' - s') × ⟨ z ∣_ (e' - s')) ⊗ I (2 ^ (n - e'))). *)
    rewrite trace_mult. 
    assert( ( 2 ^ (s') * 2 ^ (e' - s') * 2 ^ (n - e'))= 2 ^ (n)).
    type_sovle'. destruct H5.
    repeat rewrite kron_adjoint. repeat rewrite id_adjoint_eq.
    rewrite Mmult_adjoint. rewrite adjoint_involutive.
    rewrite <-Mmult_assoc. repeat rewrite kron_mixed_product.
    repeat rewrite Mmult_1_r.   
    rewrite Heqr. repeat  rewrite RtoC_mult.   repeat rewrite Rdiv_unfold.
   repeat rewrite Rmult_1_l. 
   repeat rewrite <-Rinv_mult. unfold norm.  rewrite sqrt_sqrt.
 unfold inner_product.  rewrite Mmult_adjoint.
 assert( 2 ^ (s' - s) * 2 ^ (e' - s') * 2 ^ (e - e')= 2 ^ (e - s)).
 type_sovle'.  destruct H5. repeat rewrite kron_adjoint.
 repeat rewrite id_adjoint_eq.  rewrite Mmult_adjoint. rewrite adjoint_involutive.
 remember ((I (2 ^ (s' - s)) ⊗ (∣ z ⟩_ (e' - s') × ⟨ z ∣_ (e' - s'))
 ⊗ I (2 ^ (e - e')))). 
rewrite <-(Mmult_assoc _ m v). rewrite (Mmult_assoc _ m m).
rewrite Heqm. repeat rewrite kron_mixed_product. 
repeat  rewrite Mmult_1_r.
rewrite <-Mmult_assoc.  rewrite (Mmult_assoc  _ (⟨ z ∣_ (e' - s'))).
  assert((⟨ z ∣_ (e' - s') × ∣ z ⟩_ (e' - s'))= I 1).
  admit. rewrite H5. rewrite Mmult_1_r.
 admit. auto_wf. auto_wf. auto_wf. apply inner_product_ge_0.
 auto_wf. auto_wf.

    assert( 2 ^ (s' - s) * 2 ^ (e' - s') * 2 ^ (e - e')= 2 ^ (e - s)).
    type_sovle'. destruct H5. repeat rewrite kron_adjoint.   
    eapply Logic.eq_trans with ((∣ x0 ⟩_ (s)
    ⊗ I (2 ^ (s' - s) * 2 ^ (e' - s') * 2 ^ (e - e'))
    ⊗ ∣ x1 ⟩_ (n - e))× (I 1 ⊗ ((I (2 ^ (s' - s))) †
    ⊗ (∣ z ⟩_ (e' - s') × ⟨ z ∣_ (e' - s')) †
    ⊗ (I (2 ^ (e - e'))) †) ⊗ I 1) ). 
    repeat rewrite kron_mixed_product.  
     repeat rewrite Mmult_1_r; try auto_wf. repeat rewrite Mmult_1_l; try auto_wf.
     eapply Logic.eq_trans with (  
     ((I (2^s)) ⊗ ((I (2 ^ (s'-s))) ⊗ ((∣ z ⟩_ (e' - s') × ⟨ z ∣_ (e' - s'))) † ⊗ I (2 ^ (e - e'))) ⊗ I (2^(n-e)) )
     × (∣ x0 ⟩_ (s)
   ⊗ I (2 ^ (s' - s) * 2 ^ (e' - s') * 2 ^ (e - e'))
   ⊗ ∣ x1 ⟩_ (n - e))). 
     rewrite Mmult_kron_5; try auto_wf. f_equal; type_sovle'; try lia.   
     f_equal; type_sovle'. 
     f_equal; type_sovle'.  rewrite id_kron. f_equal; type_sovle'.
     rewrite id_kron. f_equal; type_sovle'.  
       repeat rewrite kron_mixed_product.   
       repeat rewrite Mmult_1_r; try auto_wf. repeat rewrite Mmult_1_l; try auto_wf.
       repeat rewrite id_adjoint_eq.
       f_equal. 
      f_equal; type_sovle. rewrite kron_1_l. rewrite kron_1_r. reflexivity.
       auto_wf.  lia. lia. 
       admit. admit.
Admitted.

Lemma  Forall_big_pOplus: forall (f1:nat-> R) f2 n0,
(forall i, (0 <= f1 i)%R)-> 
Forall (fun x0 : R * State_formula => (0 <= fst x0)%R) (big_pOplus f1 f2 n0 ) .
Proof. intros.  induction n0. simpl. apply Forall_nil.
    simpl.  apply Forall_app. split. assumption.
    econstructor. simpl. apply  H. apply Forall_nil.
  
Qed.


Lemma sum_over_list_app_formula : forall x l,
  sum_over_list_formula (x ++ l) = (sum_over_list_formula x + sum_over_list_formula l)%R.
Proof. induction x; intros. simpl. rewrite sum_over_list_nil_formula.
    rewrite Rplus_0_l. reflexivity.
    simpl. repeat  rewrite sum_over_list_cons_formula.
    rewrite IHx. rewrite Rplus_assoc. reflexivity.
Qed.    

Lemma  sum_over_list_big_pOplus: forall (f1:nat-> R) f2 n0,
sum_over_list_formula (big_pOplus  f1 f2 n0)=
big_sum f1 n0.
Proof. intros. induction n0. simpl. rewrite sum_over_list_nil_formula.
    reflexivity.
    simpl. rewrite sum_over_list_app_formula. 
    f_equal. assumption. rewrite sum_over_list_cons_formula.
    rewrite sum_over_list_nil_formula. rewrite Rplus_0_r.
    simpl. reflexivity.
  
Qed.



Lemma State_eval_conj: forall n (mu:list (cstate * qstate n)) (F1 F2:State_formula),
State_eval_dstate  (F1 /\ F2) mu <->
State_eval_dstate   F1 mu/\ State_eval_dstate F2 mu .
Proof. intros. split; intros; 
       induction mu; 
       simpl in H. destruct H.
       -destruct mu; destruct a; inversion_clear H; simpl;
        intuition. 
      -destruct H. destruct H. 
      -destruct a. destruct mu. simpl. econstructor. 
       destruct H. inversion_clear H. inversion_clear H0.
      split; intuition. apply Forall_nil.
      simpl.  destruct H. inversion_clear H.
      inversion_clear H0. intuition. 
Qed.

Lemma big_sum_fst:forall (f:nat-> C) n0,
fst (big_sum  f  n0)= big_sum (fun x=> fst (f x)) n0.
Proof. induction n0; intros. simpl. reflexivity.
  simpl. f_equal. intuition.
Qed.

Lemma  big_sum_0_0: forall (f:nat-> Vector 1) n0,
(big_sum f n0) 0 0 =  big_sum (fun x=>  (f x) 0 0) n0  .
Proof. intros. induction n0. simpl. unfold Zero. reflexivity.
        simpl. unfold ".+". f_equal. assumption.
  
Qed.

Fixpoint fun_to_list{G:Type} (g: nat-> G) (n_0 : nat) : list (G) := 
  match n_0 with
  | 0 => []
  | S n' => (fun_to_list g n') ++ [g n']
  end. 

  Lemma fun_to_list_length{G:Type}: forall (g: nat-> G) (n_0 : nat),
  length (fun_to_list g n_0) = n_0.
  Proof. induction n_0. simpl. reflexivity.
         simpl. rewrite app_length. rewrite IHn_0. 
         simpl. intuition.
   
  Qed.


  Lemma big_pOplus_length: forall  (f : nat -> R) (g : nat -> State_formula) (n_0 : nat),
  length (big_pOplus f g n_0) = n_0.
  Proof. induction n_0. simpl. reflexivity.
         simpl. rewrite app_length. rewrite IHn_0. 
         simpl. intuition.
   
  Qed.
  
Lemma  get_pro_app: forall (pF1 pF2:pro_formula),
get_pro_formula (pF1 ++pF2)= get_pro_formula pF1 ++ get_pro_formula pF2.
Proof. induction pF1. simpl. intuition.
destruct a.
     simpl. intros. f_equal. intuition. 
   
Qed.




  Lemma big_pOplus_get_pro: forall  (f : nat -> R) (g : nat -> State_formula) (n_0 : nat),
  get_pro_formula (big_pOplus f g n_0) = fun_to_list f n_0.
  Proof. induction n_0. simpl. reflexivity.
         simpl. rewrite get_pro_app.  rewrite IHn_0. 
         simpl. intuition.
  Qed. 



  Fixpoint big_map2{n:nat} (p_n :list R) (mu_n: list (list (cstate *qstate n))) : list (cstate *qstate n) :=
           match p_n ,mu_n with 
            |[], [] => []
            |[], _ => []
            | _ ,[]=> []
            | hg::tg, hf:: tf =>StateMap.Raw.map2 (option_app) 
                                (StateMap.Raw.map (fun i => hg.* i) hf) (big_map2 tg tf)
             end.


   Fixpoint dstate_to_list{n:nat}  (mu_n: list (dstate n)) : (list (list (cstate *qstate n))):=
     match mu_n with 
     |nil => nil 
     |muh::mut=> (StateMap.this muh) :: (dstate_to_list mut)
     end.

  
  Lemma big_dapp_this{n:nat}:
  forall  (p_n:list R)  (mu_n:list (dstate n)) (mu':dstate n),
  (Forall (fun x=> x<>0%R) p_n)->
  big_dapp' p_n mu_n mu'->
  StateMap.this (mu') =
   big_map2 p_n (dstate_to_list mu_n).
  Proof.  induction p_n; destruct mu_n; intros; inversion H0;subst.
    simpl; try reflexivity
    f_equal. intuition. 
    inversion_clear H.  inversion H6;subst. lra.
    simpl. f_equal. apply IHp_n. assumption. assumption.   
  Qed.

  

  Lemma dstate_to_list_length{n:nat}: forall (mu1 mu2: list (dstate n)),
  dstate_to_list (mu1++ mu2) = dstate_to_list mu1 ++ (dstate_to_list mu2) .
  Proof. induction mu1; simpl. intuition.
         intros. f_equal. intuition.
           
   
  Qed.
  
  
  Lemma fun_dstate_to_list {n:nat}: forall n_0 (f: nat-> dstate n),
  dstate_to_list (fun_to_list f  n_0)=
  fun_to_list (fun i:nat => StateMap.this (f i)) n_0  .
  Proof. induction n_0. intros. simpl. reflexivity.
         intros. simpl.  rewrite dstate_to_list_length. 
         rewrite IHn_0. simpl.  reflexivity.
   
  Qed.

  Lemma  pro_to_npro_formula_app: forall (pF1 pF2:pro_formula),
  pro_to_npro_formula (pF1 ++pF2)= pro_to_npro_formula pF1 ++ pro_to_npro_formula pF2.
Proof. induction pF1. simpl. intuition.
destruct a.
     simpl. intros. f_equal. intuition. 
   
Qed.

  Lemma big_pOplus_get_npro: forall  (f : nat -> R) (g : nat -> State_formula) (n_0 : nat),
  pro_to_npro_formula (big_pOplus f g n_0) = fun_to_list g n_0.
  Proof. induction n_0. simpl. reflexivity.
         simpl. rewrite pro_to_npro_formula_app.  rewrite IHn_0. 
         simpl. intuition.
  Qed. 


  Lemma big_and_app{n:nat}:forall  (f1: list (dstate n)) (g1: list State_formula )  (f2: list (dstate n)) 
  (g2: list State_formula) ,
  big_and f1 g1->
  big_and f2 g2->
  big_and (f1++f2) (g1++g2).
  Proof.  induction f1; destruct g1; simpl; intros.
          assumption.
          destruct H. destruct H.
          split. intuition. 
          apply IHf1. intuition. intuition.
Qed.
  

Local Open Scope nat_scope.
  Lemma big_and_sat{n:nat}:forall  n_0 (f:nat->dstate n) (g:nat-> State_formula),
  (forall j,  sat_State (f j) (g j)) ->
big_and (fun_to_list f n_0) (fun_to_list g n_0)  .
  Proof. induction n_0. intros. simpl. intuition.
          intros. simpl. assert((S n_0)= n_0+1). rewrite add_comm.
           reflexivity.   apply big_and_app.
           apply IHn_0. assumption. simpl. split. apply H. intuition.   
   
  Qed.
  
  

             Lemma big_dapp_this'{n:nat}:
             forall  (p_n:list R)  (mu_n:list (dstate n)),
             StateMap.this (big_dapp p_n mu_n) =
              big_map2 p_n (dstate_to_list mu_n).
             Proof.  induction p_n; destruct mu_n; simpl;
             unfold StateMap.Raw.empty; try reflexivity.
             f_equal. apply IHp_n. 
             Qed.

Lemma big_dapp'_to_app{n:nat}: forall (p_n:list R) (mu_n:list (dstate n)) ,  
length p_n= length mu_n->
(Forall (fun x => x<>0%R) p_n)->
big_dapp' p_n mu_n (big_dapp p_n mu_n).
Proof.  induction p_n; intros. inversion H0; subst. destruct mu_n.
 simpl. apply big_app_nil. discriminate H.
 destruct mu_n. discriminate H. 
  simpl.  apply big_app_cons. 
  apply d_scalar_r. inversion H0.
  assumption. apply IHp_n. injection H. intuition.
  inversion_clear H0.
assumption.
Qed.


Lemma  Forall_fun_to_list: forall (f: R-> Prop) g n0,
(forall i, f (g i))->
Forall f (fun_to_list g n0)  .
Proof. induction n0; intros. simpl. apply Forall_nil.
 simpl. rewrite Forall_app. split. apply IHn0. intros.
 apply H. econstructor. apply H. apply Forall_nil.
  
Qed.

Lemma  big_app_map2{ n:nat}: forall (f1: nat-> R) (f2: nat->  (list (cstate * qstate n))) n0,
big_map2 (fun_to_list f1 n0) (fun_to_list f2 n0) = 
big_app (fun x => StateMap.Raw.map (fun q=> (f1 x)  .* q) (f2 x)) n0 .
Proof. induction n0; intros. simpl. reflexivity.
simpl. rewrite <-IHn0. Admitted.


Theorem rule_Meas_aux':forall s' e' s e (v: Vector (2^(e-s))) x (P :nat-> (Pure_formula))
(n:nat) (st :state n) (mu: dstate n),
s<=s' /\ e'<=e->
(norm v = 1)%R -> WF_Matrix v->
ceval (QMeas x s' e') st mu-> 
sat_Assert st ((QExp_s  s  e  v) /\ big_Sand (fun i:nat => (Assn_sub i x (P i))) (2^(e'-s'))) ->
sat_Assert mu  (big_pOplus (fun i:nat=> ( (@norm (2^(e-s)) ((U_v  (∣ i ⟩_ (e'-s') × ⟨ i ∣_ (e'-s')) v)))) ^ 2)%R
                               (fun i:nat=> SAnd ((P i))  (QExp_s  s  e ((R1 / ( (@norm (2^(e-s)) ((U_v  (∣ i ⟩_ (e'-s') × ⟨ i ∣_ (e'-s')) v)))))%R.* 
                               (U_v  (∣ i ⟩_ (e'-s') × ⟨ i ∣_ (e'-s')) v)))) (2^(e'-s'))).
Proof. 
intros s' e' s e v x P n st mu  He Hv Hv'. intros. destruct mu as [ mu IHmu]. 
inversion_clear H; simpl in H3.
inversion H3; subst. 
inversion H10; subst. 
rewrite sat_Assert_to_State in *.
inversion_clear H0. apply State_eval_conj in H6.
destruct H6. econstructor.  intuition.
inversion H11; subst. 
econstructor. apply Forall_big_pOplus. 
intros. apply pow2_ge_0.
 rewrite sum_over_list_big_pOplus. simpl.
  unfold U_v. unfold norm. 
  rewrite (big_sum_eq_bounded  _ ((fun i : nat => (fst
  ⟨ I (2 ^ (s' - s))
    ⊗ (∣ i ⟩_ (e' - s') × ⟨ i ∣_ (e' - s'))
    ⊗ I (2 ^ (e - e')) × v,
  I (2 ^ (s' - s))
  ⊗ (∣ i ⟩_ (e' - s') × ⟨ i ∣_ (e' - s'))
  ⊗ I (2 ^ (e - e')) × v ⟩)))).
rewrite<- big_sum_fst. unfold inner_product.
apply Logic.eq_trans with (fst C1).  f_equal.
assert( 2^(e-s)= (2 ^ (s' - s)) * (2^(e'-s')) *  (2 ^ (e - e')) ).
type_sovle'. destruct H7.  
rewrite (big_sum_eq_bounded _ (fun x0 : nat =>
(v † × (I (2 ^ (s' - s)) ⊗ (∣ x0 ⟩_ (e' - s') × ⟨ x0 ∣_ (e' - s')) ⊗ I (2 ^ (e - e'))) × v) 
0 0)).  remember ((fun x0 : nat =>
((v) †
 × (I (2 ^ (s' - s))
    ⊗ (∣ x0 ⟩_ (e' - s') × ⟨ x0 ∣_ (e' - s'))
    ⊗ I (2 ^ (e - e'))) × v))).   rewrite (big_sum_eq_bounded _ 
    (fun x0:nat => (m x0) 0 0)). 
    rewrite <-big_sum_0_0. rewrite Heqm.  
    rewrite <-Mmult_Msum_distr_r.  
    rewrite <-Mmult_Msum_distr_l. 
    rewrite <-kron_Msum_distr_r.   
    rewrite <-kron_Msum_distr_l. 
    rewrite big_sum_I.  repeat rewrite id_kron.
    assert( 2^(e-s)= (2 ^ (s' - s)) * (2^(e'-s')) *  (2 ^ (e - e')) ).
    type_sovle'. destruct H7.
    rewrite Mmult_1_r. unfold norm in Hv. unfold inner_product in Hv.
    admit. auto_wf.
    intros. rewrite Heqm. reflexivity. intros.
repeat rewrite Mmult_adjoint. 
assert( (2 ^ (s' - s)) * (2^(e'-s')) *  (2 ^ (e - e'))= 2^(e-s) ).
type_sovle'. destruct H8. repeat rewrite kron_adjoint. repeat rewrite id_adjoint_eq.
rewrite Mmult_adjoint. rewrite adjoint_involutive.
remember ((I (2 ^ (s' - s)) ⊗ (∣ x0 ⟩_ (e' - s') × ⟨ x0 ∣_ (e' - s'))
⊗ I (2 ^ (e - e')))). 
rewrite<- Mmult_assoc. rewrite (Mmult_assoc  _ m m). 
f_equal. f_equal. rewrite Heqm. repeat rewrite kron_mixed_product.
repeat rewrite Mmult_1_r. rewrite <-Mmult_assoc.  
rewrite (Mmult_assoc  _ (⟨ x0 ∣_ (e' - s')) _). 
assert((⟨ x0 ∣_ (e' - s') × ∣ x0 ⟩_ (e' - s'))= I 1).
admit. rewrite H8. rewrite Mmult_1_r. reflexivity.
auto_wf. auto_wf. auto_wf. simpl. reflexivity.
intros.  rewrite Rmult_1_r. rewrite sqrt_sqrt. f_equal.
f_equal; type_sovle'. f_equal; type_sovle'. f_equal; type_sovle'.
apply inner_product_ge_0. 

assert(forall j, Sorted.Sorted(StateMap.Raw.PX.ltk (elt:=qstate n)) 
[(c_update x j (fst st),
(R1 /( (@norm (2^(e-s))
            (U_v (∣ j ⟩_ (e' - s') × ⟨ j ∣_ (e' - s')) v))
       ^ 2))%R .* (q_update
  (I (2 ^ s')
   ⊗ (∣ j ⟩_ (e' - s')
      × ⟨ j ∣_ (e' - s'))
   ⊗ I (2 ^ (n - e'))) 
  (snd st)))]). intros. apply Sorted.Sorted_cons.
  apply Sorted.Sorted_nil. apply Sorted.HdRel_nil.
econstructor. 

rewrite big_pOplus_get_pro. 
assert(big_dapp'
(fun_to_list
(fun i : nat =>
 ((@norm (2^(e-s)) (U_v (∣ i ⟩_ (e' - s') × ⟨ i ∣_ (e' - s')) v))
  ^ 2)%R) (2 ^ (e' - s')))

       (fun_to_list (fun j : nat =>
       StateMap.Build_slist (H7 j) ) (2 ^ (e' - s')))
  
   (big_dapp  (fun_to_list
   (fun i : nat =>
    (
       (@norm (2^(e-s)) (U_v (∣ i ⟩_ (e' - s') × ⟨ i ∣_ (e' - s')) v))
     ^ 2)%R) (2 ^ (e' - s')))
          (fun_to_list (fun j : nat =>
          StateMap.Build_slist (H7 j) ) (2 ^ (e' - s')))) ).
apply big_dapp'_to_app.
repeat rewrite fun_to_list_length.
reflexivity.  apply Forall_fun_to_list. 
intros.  admit.
apply H8.
unfold dstate_eq. simpl.
inversion_clear H11. rewrite map2_nil_r. 
 rewrite big_dapp_this'.
  rewrite fun_dstate_to_list.  simpl.
  rewrite big_app_map2.     
 admit. 
 rewrite big_pOplus_get_npro. 
 apply big_and_sat.  intros.
  econstructor.  admit.
  apply State_eval_conj. 
  split.  simpl StateMap.this.   
  admit.
  simpl StateMap.this.
  econstructor.
  assert((c_update x j (fst st),
  (R1 /
   (norm (U_v (∣ j ⟩_ (e' - s') × ⟨ j ∣_ (e' - s')) v) *
    (norm (U_v (∣ j ⟩_ (e' - s') × ⟨ j ∣_ (e' - s')) v) * 1)))%R
  .* q_update
       (I (2 ^ s') ⊗ (∣ j ⟩_ (e' - s') × ⟨ j ∣_ (e' - s')) ⊗ I (2 ^ (n - e')))
       (snd st))=
 s_scale ((R1 /
 (norm (U_v (∣ j ⟩_ (e' - s') × ⟨ j ∣_ (e' - s')) v) ^ 2))%R )   
  (c_update x j (fst st), q_update
       (I (2 ^ s') ⊗ (∣ j ⟩_ (e' - s') × ⟨ j ∣_ (e' - s')) ⊗ I (2 ^ (n - e')))
       (snd st))). unfold s_scale.
       simpl. reflexivity.  rewrite H8.
apply rule_Meas_aux.

admit. admit.
Admitted.


