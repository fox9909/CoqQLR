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
       remember ((C1 / trace (big_sum  (fun i : nat =>
             I (2 ^ s) ⊗ (∣ 0 ⟩_ (e - s) × (∣ i ⟩_ (e - s)) †)
             ⊗ I (2 ^ (n - e)) × q
             × (I (2 ^ s) ⊗ (∣ 0 ⟩_ (e - s) × (∣ i ⟩_ (e - s)) †)
             ⊗ I (2 ^ (n - e))) †) (2 ^ (e - s))))).
      split. lia. split. lia.
      remember (fun i : nat =>
       @big_sum (Square (2^(e-s))) (M_is_monoid (2 ^ (e-s)) (2 ^ (e-s)))
         (fun j : nat =>
         c1  .* @big_sum (Square (2^(e-s))) (M_is_monoid (2 ^ (e-s)) (2 ^ (e-s)))
         (fun i0 : nat => ((∣ 0 ⟩_ (e - s) × ⟨ i0 ∣_ (e - s))) ×
         (⟨ i ∣_ (s) ⊗ I (2^ (e-s)) ⊗ ⟨ j ∣_ (n - e) × q × 
         (⟨ i ∣_ (s) ⊗ I (2^ (e-s))  ⊗ ⟨ j ∣_ (n - e) ) † )  ×
         ((∣ i0 ⟩_ (e - s) × ⟨ 0 ∣_ (e - s)))) (2 ^ (e - s))) (2 ^ (n - e))). 
      rewrite (@big_sum_eq_bounded (Square (2^(e-s))) _ _  m ((2 ^ s))).
   rewrite Heqm.   
   remember ((fun i : nat => ∣ 0 ⟩_ (e - s) × ( big_sum (fun j : nat =>
      c1  .* big_sum (fun i0 : nat => ⟨ i0 ∣_ (e - s) × 
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
   remember ((fun i : nat => c1.* (trace (big_sum (fun j : nat => 
   ((⟨ i ∣_ (s) ⊗ I (2 ^ (e - s)) ⊗ ⟨ j ∣_ (n - e) × q
   × (⟨ i ∣_ (s) ⊗ I (2 ^ (e - s)) ⊗ ⟨ j ∣_ (n - e)) †)) )
    (2 ^ (n - e)))  .* I 1))). 
  rewrite (big_sum_eq_bounded _ m1 _ ). rewrite Heqm1.
  rewrite Mscale_Msum_distr_r. rewrite<- big_sum_Mscale_r.
  rewrite<-big_sum_trace. rewrite Mscale_assoc.   admit. 
  
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

      remember ((C1 / trace (QUnit_One_fun s' e' U rho))%C).
      remember ((C1 / trace rho)%C).  
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
      rewrite  <-(Mmult_assoc _ (c .* rho) _).  
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
State_eval (QExp_s  s  e  ((C1 / (@trace (2^(e-s)) ((U_v  (∣ z ⟩_ (e'-s') × ⟨ z ∣_ (e'-s')) v)))).* 
                          (U_v  (∣ z ⟩_ (e'-s') × ⟨ z ∣_ (e'-s')) v))) st'.
Proof.  intros s' e' s e v z x n st st' He' H' Hv Hz. intros. simpl in *. 
unfold outer_product in *.
rewrite Mscale_adj.  
rewrite Mscale_mult_dist_r. 
rewrite Mscale_mult_dist_l. 
rewrite Mscale_assoc. 
remember ((C1 / trace (U_v (∣ z ⟩_ (e' - s') × ⟨ z ∣_ (e' - s')) v)) ^* *
(C1 / trace (U_v (∣ z ⟩_ (e' - s') × ⟨ z ∣_ (e' - s')) v))).
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
remember ((C1 /
trace 
  (q_update
     (I (2 ^ s') ⊗ (∣ z ⟩_ (e' - s') × ⟨ z ∣_ (e' - s'))
      ⊗ I (2 ^ (n - e'))) q))). 
remember (C1 / trace q).
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
rewrite <-(Mmult_assoc _ (c2 .* q) _).
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
    auto_wf. 

     admit. 

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
Admitted.



(* Theorem rule_Meas_aux':forall s' e' s e (v: Vector (2^(e-s))) x (P :nat-> (Pure_formula))
(n:nat) (st :state n) (mu: dstate n),
ceval (QMeas x s' e') st mu->
sat_Assert st ((QExp_s  s  e  v) /\ big_Sand (fun i:nat => (Assn_sub i x (P i))) (2^(e'-s'))) ->
sat_Assert mu  (big_pOplus (fun i:nat=> (Cmod (@trace (2^(e-s)) ((U_v  (∣ i ⟩_ (e'-s') × ⟨ i ∣_ (e'-s')) v)))) ^ 2)%R
                               (fun i:nat=> SAnd ((P i))  (QExp_s  s  e ((C1 / (Cmod (@trace (2^(e-s)) ((U_v  (∣ i ⟩_ (e'-s') × ⟨ i ∣_ (e'-s')) v))))).* 
                               (U_v  (∣ i ⟩_ (e'-s') × ⟨ i ∣_ (e'-s')) v)))) (2^(e'-s'))).
Proof. 
intros. destruct mu as [ mu IHmu]. 
inversion_clear H; simpl in H3.
inversion H3; subst. 
inversion H10; subst. 
rewrite sat_Assert_to_State in *.
inversion_clear H0. apply State_eval_conj in H4.
destruct H4. econstructor.  intuition. 


admit.
assert(forall j, Sorted.Sorted(StateMap.Raw.PX.ltk (elt:=qstate n)) 
[(c_update x j (fst st),
(C1 /(Cmod (@trace (2^(e-s))
            (U_v (∣ j ⟩_ (e' - s') × ⟨ j ∣_ (e' - s')) v))
       ^ 2)%R) .* (q_update
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
 (Cmod
    (@trace (2^(e-s)) (U_v (∣ i ⟩_ (e' - s') × ⟨ i ∣_ (e' - s')) v))
  ^ 2)%R) (2 ^ (e' - s')))
       (fun_to_list (fun j : nat =>
       StateMap.Build_slist (H5 j) ) (2 ^ (e' - s')))
  
   (big_dapp  (fun_to_list
   (fun i : nat =>
    (Cmod
       (@trace (2^(e-s)) (U_v (∣ i ⟩_ (e' - s') × ⟨ i ∣_ (e' - s')) v))
     ^ 2)%R) (2 ^ (e' - s')))
          (fun_to_list (fun j : nat =>
          StateMap.Build_slist (H5 j) ) (2 ^ (e' - s')))) ).
apply big_dapp'_to_app.
repeat rewrite fun_to_list_length.
reflexivity.

admit.
apply H6.
unfold dstate_eq. simpl.
  rewrite map2_nil.  rewrite map2_l_refl.
 rewrite big_dapp_this'.
  rewrite fun_dstate_to_list.  simpl.
 admit. 
 rewrite big_pOplus_get_npro. 
 apply big_and_sat.  intros.
  econstructor.  admit.
  apply State_eval_conj. 
  split.  simpl StateMap.this.  
  admit.
  simpl StateMap.this.  
admit. admit.
Admitted. *)


