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


Lemma big_sum_Mmult_l : forall (n m o:nat) (M: Matrix n m) (f:nat-> Matrix m o) n', 
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
Qed.

Local Open Scope nat_scope.


Definition U_v {s' e' s e:nat} (U: Square (2^(e'-s'))) (v: Vector (2^(e-s))): Vector (2^(e-s)) := 
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


Lemma Mmult_trans{n1 m1 n2 n3 m3 n4}: forall (A: Matrix n1 m1) (B:Matrix n2 n2)
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
Qed.
 
#[export]Hint Resolve WF_vec: wf_db.
#[export]Hint Resolve WF_mult: wf_db.
#[export] Hint Extern 1 (pow_gt_0) => lia : wf_db.

Ltac type_sovle':=
   try repeat rewrite Nat.add_0_r;
   try rewrite Nat.mul_1_l ; try rewrite Nat.mul_1_r;
   try rewrite Nat.add_comm; try rewrite Nat.sub_add;
   try rewrite Nat.add_0_r;
   try symmetry;
   try f_equal. 

Local Open Scope nat_scope.
 Theorem rule_Qinit_aux:  forall  s e (n:nat) (st :state n) (st': state n),
WF_state st->
ceval_single (QInit s e) [st] [st'] ->
State_eval (QExp_s s e  (Vec (2^(e-s)) 0)) st'.
Proof.  intros s e n st st' H'. intros. simpl in *. rewrite Ptrace_l_r' in *. 
        destruct st. destruct st'.
        inversion H; subst.  inversion H1; subst. 
        injection H6. intros. rewrite <-H0. simpl. unfold QInit_fun. 
        assert((e-s)%nat= (n - (n - e) - s)%nat).
        type_sovle'. apply add_sub_eq_l. apply sub_add. 
         admit. destruct H3.  
        assert((2 ^ s * 2 ^ (e - s) * 2 ^ (n - e))%nat=(2 ^ n)%nat). 
        rewrite <-pow_add_r. rewrite <-pow_add_r. f_equal.
        repeat rewrite <-le_plus_minus'. reflexivity.   
        admit. admit. destruct H3.
        Local Open Scope C_scope.     
       remember ((C1 / trace (big_sum  (fun i : nat =>
             I (2 ^ s) ⊗ (∣ 0 ⟩_ (e - s) × (∣ i ⟩_ (e - s)) †)
             ⊗ I (2 ^ (n - e)) × q
             × (I (2 ^ s) ⊗ (∣ 0 ⟩_ (e - s) × (∣ i ⟩_ (e - s)) †)
             ⊗ I (2 ^ (n - e))) †) (2 ^ (e - s))))).
      split. admit. split. admit.
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
   rewrite H3 . f_equal. f_equal. 
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
  type_sovle. destruct H7. 
  apply trace_base.   apply WF_mult. apply WF_mult. auto_wf. 
  unfold WF_state in H'. simpl in H'. unfold WF_qstate in H'.
  apply WF_Mixed in H'.
  assert((2 ^ s * 2 ^ (e - s) * 2 ^ (n - e))%nat=(2 ^ n)%nat).
  rewrite <-pow_add_r. rewrite <-pow_add_r. f_equal.
  repeat rewrite <-le_plus_minus'. reflexivity.  
  admit. admit. destruct H7. assumption.
   auto_wf.
  

  rewrite Heqm0.  intros.
   assert((2 ^ (e - s))%nat= (1 * 2 ^ (e - s) * 1)%nat).
   type_sovle. destruct H4.
  rewrite big_sum_Mmult_l. rewrite big_sum_Mmult_r.
  apply big_sum_eq_bounded.  intros.  rewrite Mscale_mult_dist_r.  
   rewrite Mscale_mult_dist_l.   
  rewrite big_sum_Mmult_l.   rewrite big_sum_Mmult_r.
  f_equal. apply big_sum_eq_bounded. 
   intros.  repeat rewrite <-Mmult_assoc.  reflexivity.
 
  rewrite Heqm.  intros. apply big_sum_eq_bounded.  intros. 
  remember (⟨ x ∣_ (s) ⊗ I (2 ^ (e - s))).
  remember (⟨ x0 ∣_ (n - e)).
  assert((1 * 2 ^ (e - s) * 1)%nat=(Init.Nat.mul (Init.Nat.add (Nat.pow (S (S O)) (sub e s)) O) (S O))%nat).
  type_sovle'. destruct H5.  
  remember (m0 ⊗ m1). 
  remember ((@kron (Init.Nat.add (Nat.pow (S (S O)) (sub e s)) O)
  (Init.Nat.mul (Nat.pow (S (S O)) s)
     (Nat.pow (S (S O)) (sub e s))) 
  (S O) (Nat.pow (S (S O)) (sub n e)) m0 m1)).
  assert(m2=m3). rewrite Heqm2. rewrite Heqm3.
  Set Printing All.
 
  remember (m0 ⊗ m1).
   remember (⟨ x ∣_ (s) ⊗ I (2 ^ (e - s)) ⊗ ⟨ x0 ∣_ (n - e)).
  assert ((@kron (Init.Nat.add (Nat.pow (S (S O)) (sub e s)) O)
  (Init.Nat.mul (Nat.pow (S (S O)) s)
     (Nat.pow (S (S O)) (sub e s))) 
  (S O) (Nat.pow (S (S O)) (sub n e))
  (@kron (S O) (Nat.pow (S (S O)) s)
     (Nat.pow (S (S O)) (sub e s))
     (Nat.pow (S (S O)) (sub e s))
     (@adjoint (Nat.pow (S (S O)) s) 
        (S O) (Vec (Nat.pow (S (S O)) s) x))
     (I (Nat.pow (S (S O)) (sub e s))))
  (@adjoint (Nat.pow (S (S O)) (sub n e)) 
     (S O) (Vec (Nat.pow (S (S O)) (sub n e)) x0))) = m0).
     rewrite Heqm0.    reflexivity. rewrite H5. rewrite Heqm0.
  rewrite Mscale_mult_dist_r. rewrite big_sum_Mmult_l. 
   rewrite Mscale_mult_dist_l. f_equal; try rewrite mul_1_r;
   try rewrite Nat.add_0_r; try reflexivity. 
   rewrite big_sum_Mmult_r.  
  apply big_sum_eq_bounded. 
  intros.   rewrite<-Mmult_assoc. rewrite <-Mmult_assoc. 
  rewrite <-Heqm0.
  remember ((I (2 ^ s) ⊗ (∣ 0 ⟩_ (e - s) × ⟨ x1 ∣_ (e - s)) ⊗ I (2 ^ (n - e)))).
   assert ((@Mmult (Nat.pow (S (S O)) (sub e s))
   (Init.Nat.mul (Init.Nat.mul (Nat.pow (S (S O)) s)
         (Nat.pow (S (S O)) (Init.Nat.sub e s)))
      (Nat.pow (S (S O)) (Init.Nat.sub n e)))
   (Init.Nat.mul
      (Init.Nat.mul (Nat.pow (S (S O)) s)
         (Nat.pow (S (S O)) (Init.Nat.sub e s)))
      (Nat.pow (S (S O)) (Init.Nat.sub n e))) m0 m1)= m0 × m1).
      rewrite Heqm1. rewrite Heqm0. f_equal. rewrite mul_1_l.
      rewrite mul_1_r. reflexivity. rewrite H8. rewrite Heqm0.
      rewrite Heqm1. repeat rewrite kron_mixed_product. 
      repeat rewrite Mmult_1_r. repeat rewrite Mmult_1_l.
   repeat rewrite kron_adjoint.   rewrite Mmult_assoc.  rewrite Mmult_assoc.
   repeat rewrite id_adjoint_eq. rewrite Mmult_adjoint. 
    remember(I (2 ^ s) ⊗ ((⟨ x1 ∣_ (e - s)) † × ⟨ 0 ∣_ (e - s))
    ⊗ I (2 ^ (n - e))).
    assert ((@kron
    (Init.Nat.mul (Nat.pow (S (S O)) s)
       (Nat.pow (S (S O)) (sub e s)))
    (Nat.pow (S (S O)) (sub e s))
    (Nat.pow (S (S O)) (sub n e)) (S O)
    (@kron (Nat.pow (S (S O)) s) (S O)
       (Nat.pow (S (S O)) (sub e s))
       (Nat.pow (S (S O)) (sub e s))
       (Vec (Nat.pow (S (S O)) s) x)
       (I (Nat.pow (S (S O)) (sub e s))))
    (Vec (Nat.pow (S (S O)) (sub n e)) x0))= 
    (∣ x ⟩_ (s) ⊗ I (2 ^ (e - s)) ⊗ ∣ x0 ⟩_ (n - e))).
    f_equal. rewrite mul_1_l. reflexivity. rewrite H9.
    remember ((∣ x ⟩_ (s) ⊗ I (2 ^ (e - s)) ⊗ ∣ x0 ⟩_ (n - e))).
    remember (m2 × m3).
    assert (@Mmult
    (Init.Nat.mul
       (Init.Nat.mul (Nat.pow (S (S O)) s)
          (Nat.pow (S (S O)) (Init.Nat.sub e s)))
       (Nat.pow (S (S O)) (Init.Nat.sub n e)))
    (Init.Nat.mul
       (Init.Nat.mul (Nat.pow (S (S O)) s)
          (Nat.pow (S (S O)) (Init.Nat.sub e s)))
       (Nat.pow (S (S O)) (Init.Nat.sub n e)))
    (Nat.pow (S (S O)) (sub e s)) m2 m3 = m2 × m3).
    rewrite Heqm2. remember Heqm3. f_equal. 
    rewrite mul_1_l. rewrite mul_1_r. reflexivity.
    rewrite H10. rewrite Heqm2. rewrite Heqm3. 
    repeat rewrite kron_mixed_product.  
    repeat rewrite Mmult_1_r. repeat rewrite Mmult_1_l. 
     rewrite <-Mmult_assoc.   
 assert((2^(e-s))%nat =(1 * 2 ^ (e - s) * 1)%nat).
rewrite mul_1_l. rewrite mul_1_r. reflexivity. destruct H11.
assert(∣ 0 ⟩_ (e - s) × ⟨ x1 ∣_ (e - s)=I (1)⊗ (∣ 0 ⟩_ (e - s) × ⟨ x1 ∣_ (e - s)) ⊗ I (1)).
rewrite kron_1_l. rewrite kron_1_r. reflexivity.
apply WF_mult. auto_wf. apply WF_vec. apply pow_gt_0. apply WF_adjoint.
apply WF_vec. assumption.  rewrite H11. 
rewrite <-Heqm0.  remember (I 1 ⊗ (∣ 0 ⟩_ (e - s) × ⟨ x1 ∣_ (e - s)) ⊗ I 1).
remember ( ⟨ x ∣_ (s) ⊗ I (2 ^ (e - s)) ⊗ ⟨ x0 ∣_ (n - e)) as m10.
rewrite Heqm0. 
assert((@Mmult (Nat.pow (S (S O)) (sub e s))
(Nat.pow (S (S O)) (sub e s))
(Init.Nat.mul
   (Init.Nat.mul (Nat.pow (S (S O)) s)
      (Nat.pow (S (S O)) (sub e s)))
   (Nat.pow (S (S O)) (sub n e))) m5 m10)=m5 × m10 ).
   f_equal; try (rewrite mul_1_l; rewrite mul_1_r; reflexivity).
   repeat rewrite <-Mmult_assoc. 
   rewrite H12. rewrite Heqm5. rewrite Heqm10. 
repeat rewrite kron_mixed_product. 
repeat rewrite Mmult_1_l. 
rewrite Mmult_1_r at 1.  rewrite kron_1_l at 1.
 rewrite kron_1_r. repeat  rewrite Mmult_assoc.
 f_equal. f_equal. 
 assert(∣ x1 ⟩_ (e - s) × ⟨ 0 ∣_ (e - s)=I (1)⊗ (∣ x1 ⟩_ (e - s) × ⟨ 0 ∣_ (e - s)) ⊗ I (1)).
 rewrite kron_1_l. rewrite kron_1_r. reflexivity.

 apply WF_mult. auto_wf. 
 apply WF_adjoint. apply WF_vec.  apply pow_gt_0.
 rewrite H13.  
 remember ((⟨ x ∣_ (s)) † ⊗ I (2 ^ (e - s)) ⊗ (⟨ x0 ∣_ (n - e)) †).
 remember ((I 1 ⊗ (∣ x1 ⟩_ (e - s) × ⟨ 0 ∣_ (e - s)) ⊗ I 1)).
 assert((@Mmult
 (Init.Nat.mul
    (Init.Nat.mul (Nat.pow (S (S O)) s)
       (Nat.pow (S (S O)) (sub e s)))
    (Nat.pow (S (S O)) (sub n e)))
 (Nat.pow (S (S O)) (sub e s))
 (Nat.pow (S (S O)) (sub e s)) m6 m7)=m6 × m7).
 f_equal; try (rewrite mul_1_l; rewrite mul_1_r; reflexivity).  
rewrite H14. rewrite Heqm6. rewrite Heqm7. 
 repeat rewrite kron_mixed_product.  repeat rewrite Mmult_1_r.
 rewrite Mmult_1_l.  f_equal; try f_equal; try rewrite adjoint_involutive;
 try reflexivity.  
 
apply WF_mult. auto_wf. apply WF_adjoint. apply WF_vec.
apply pow_gt_0. auto_wf. auto_wf. 
apply WF_mult. auto_wf.  apply WF_vec.
apply pow_gt_0. auto_wf. 
apply WF_mult. auto_wf.  apply WF_vec. 
apply pow_gt_0. auto_wf. auto_wf. auto_wf.
auto_wf. auto_wf. apply WF_mult. auto_wf. apply WF_adjoint. apply WF_vec.
apply pow_gt_0. apply WF_mult.  apply WF_vec.
apply pow_gt_0. auto_wf. auto_wf. auto_wf.

 Admitted. *)




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

  Lemma big_sum_Mmult_l' : forall (n m o p:nat) (M: Matrix n m) (f:nat-> Matrix o p) n', 
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
Qed.




Local Open Scope assert_scope.
Local Open Scope nat_scope.
(* Theorem rule_QUnit_aux:  forall s' e' s e (U: Square (2^(e'-s'))) (v: Vector (2^(e-s)))
(n:nat) (st :state n) (st': state n),
WF_state st->WF_Matrix v->
ceval_single (QUnit_One s' e' U) [st] [st'] ->
State_eval (QExp_s s  e  (U_v U† v) ) st->
State_eval (QExp_s s  e  v ) st'.
Proof. intros s' e' s e U v n st st' H' Hv. intros. simpl in *. 
    rewrite Ptrace_l_r' in *.
    assert((e-s)%nat= (n - (n - e) - s)%nat). admit. destruct H1. 
    unfold U_v in *.
    unfold outer_product in *.
    (* remember ((I (2 ^ (s' - s)) ⊗ (U) † ⊗ I (2 ^ (e - e')))). *)
    (* assert((2 ^ (s' - s) * 2 ^ (e' - s') * 2 ^ (e - e'))=2^(e-s)).
    admit. destruct H1.   *)
    rewrite Mmult_adjoint in H0.
    rewrite <-Mmult_assoc in H0.
    inversion H; subst.
    inversion H9; subst.
    clear H9. apply inj_pair2_eq_dec in H3.
    apply inj_pair2_eq_dec in H3. subst.
    injection H7. intros.
    rewrite<- H1. simpl in *.
    rewrite (Mmult_assoc _ v (v) †) in H0.
    destruct H0. destruct H2. split. intuition.
    split. intuition.
    apply Mmult_trans'  in H3. 
    rewrite <- H3.  
  remember ((C1 / trace (q_update (I (2 ^ s') ⊗ U ⊗ I (2 ^ (n - e'))) rho))%C).
  remember ((C1 / trace rho)%C).
  assert(2 ^ (e - s)= 2 ^ (s' - s) * 2 ^ (e' - s') * 2 ^ (e - e')).
  admit. destruct H4. 
  assert(2 ^ (e - s)= (2 ^ (e - s) + 0) * 1). rewrite mul_1_r.
  rewrite Nat.add_0_r. reflexivity. destruct H4.
  rewrite big_sum_Mmult_l. rewrite big_sum_Mmult_r.
  apply big_sum_eq_bounded. 
  intros.  rewrite big_sum_Mmult_l. rewrite big_sum_Mmult_r.
  apply big_sum_eq_bounded. 
  intros.  
  unfold q_update. unfold super. 
  rewrite  (Mmult_assoc _ rho _).
  rewrite <-Mscale_mult_dist_r.   rewrite <-Mscale_mult_dist_l.
  rewrite  <-(Mmult_assoc _ (c .* rho) _).
  assert((@adjoint (Nat.pow (S (S O)) n) (Nat.pow (S (S O)) n) 
  ((I (2 ^ s') ⊗ U ⊗ I (2 ^ (n - e')))))=
  (((I (2 ^ s') ⊗ U ⊗ I (2 ^ (n - e'))))) † ). f_equal. admit. admit. 
  rewrite H9.  repeat rewrite kron_adjoint. 
  repeat rewrite id_adjoint_eq. repeat rewrite adjoint_involutive.
  assert( 2 ^ (s) * 2 ^ (e - s) * 2 ^ (n - e)= 2 ^ (n)).
  admit. destruct H10. 
  assert( 2 ^ (s' - s) * 2 ^ (e' - s') * 2 ^ (e - e')= 2 ^ (e - s)).
  admit. destruct H10.   
  assert(I (2 ^ (s' - s) * 2 ^ (e' - s') * 2 ^ (e - e'))= I (2 ^ (s' - s))
  ⊗ I (2 ^ (e' - s')) ⊗ I (2 ^ (e - e'))). rewrite id_kron. rewrite id_kron.
  reflexivity. rewrite H10. repeat rewrite kron_adjoint.
  repeat rewrite id_adjoint_eq. repeat rewrite adjoint_involutive.
  assert(I (2 ^ (s' - s)) ⊗ U ⊗ I (2 ^ (e - e'))=
 I 1 ⊗ (I (2 ^ (s' - s)) ⊗ U ⊗ I (2 ^ (e - e'))) ⊗ I 1).
 rewrite kron_1_l. rewrite kron_1_r. reflexivity. apply WF_kron.
 reflexivity. reflexivity. apply WF_kron. reflexivity. reflexivity.
 apply WF_I. apply H8. apply WF_I.  
 rewrite H11.  
 remember ((I (2 ^ (s' - s)) ⊗ I (2 ^ (e' - s')) ⊗ I (2 ^ (e - e')))).
 remember (⟨ x ∣_ (s)). remember (⟨ x0 ∣_ (n - e)). 
 assert ((@kron 
 (Init.Nat.add
    (mul (mul (Nat.pow (S (S O)) (sub s' s)) (Nat.pow (S (S O)) (sub e' s')))
       (Nat.pow (S (S O)) (sub e e'))) O)
 (Init.Nat.mul (Nat.pow (S (S O)) s)
    (mul (mul (Nat.pow (S (S O)) (sub s' s)) (Nat.pow (S (S O)) (sub e' s')))
       (Nat.pow (S (S O)) (sub e e')))) (S O) (Nat.pow (S (S O)) (sub n e))
 (m0 ⊗ m) m1)= m0 ⊗ m ⊗ m1). 
   reflexivity. rewrite H12.
  repeat rewrite <- Mmult_assoc.
   remember (I 1 ⊗ (I (2 ^ (s' - s)) ⊗ U ⊗ I (2 ^ (e - e'))) ⊗ I 1 ).
   assert ((@Mmult
   (mul (mul (Nat.pow (S (S O)) (sub s' s)) (Nat.pow (S (S O)) (sub e' s')))
      (Nat.pow (S (S O)) (sub e e')))
   (mul (mul (Nat.pow (S (S O)) (sub s' s)) (Nat.pow (S (S O)) (sub e' s')))
      (Nat.pow (S (S O)) (sub e e')))
   (Init.Nat.mul
      (Init.Nat.mul (Nat.pow (S (S O)) s)
         (mul (mul (Nat.pow (S (S O)) (sub s' s)) (Nat.pow (S (S O)) (sub e' s')))
            (Nat.pow (S (S O)) (sub e e')))) (Nat.pow (S (S O)) (sub n e))) m2
            (m0 ⊗ m ⊗ m1))= m2 × (m0 ⊗ m ⊗ m1)).
            f_equal; try rewrite mul_1_l; try rewrite mul_1_r; try  reflexivity.
  rewrite H13.
   rewrite Heqm2. 
   repeat rewrite kron_mixed_product. rewrite Heqm.
   repeat rewrite kron_mixed_product.  repeat rewrite Mmult_1_r.
   repeat rewrite Mmult_1_l.

  repeat rewrite Mmult_assoc.
   assert((I (2 ^ (s' - s)) ⊗ (U) † ⊗ I (2 ^ (e - e')))=
 I 1 ⊗ (I (2 ^ (s' - s)) ⊗ (U) † ⊗ I (2 ^ (e - e'))) ⊗ I 1).
 rewrite kron_1_l. rewrite kron_1_r. reflexivity. apply WF_kron.
 reflexivity. reflexivity. apply WF_kron. reflexivity. reflexivity.
 apply WF_I. apply WF_adjoint. apply H8. apply WF_I.  
 rewrite H14.  
 remember ((I (2 ^ (s' - s)) ⊗ I (2 ^ (e' - s')) ⊗ I (2 ^ (e - e')))).
 remember (∣ x ⟩_ (s)). remember (∣ x0 ⟩_ (n - e)).
  remember (m4 ⊗ m3 ⊗ m5). 
 assert ((@kron (Init.Nat.mul (Nat.pow (S (S O)) s)
    (mul  (mul (Nat.pow (S (S O)) (sub s' s))
          (Nat.pow (S (S O)) (sub e' s')))
       (Nat.pow (S (S O)) (sub e e'))))
 (Init.Nat.add  (mul (mul (Nat.pow (S (S O)) (sub s' s))
          (Nat.pow (S (S O)) (sub e' s')))
       (Nat.pow (S (S O)) (sub e e'))) O)
 (Nat.pow (S (S O)) (sub n e))  (S O)
 (m4 ⊗ m3) m5)= m4 ⊗ m3 ⊗ m5). 
   reflexivity. rewrite H15. 
   remember (I 1 ⊗ (I (2 ^ (s' - s)) ⊗ (U) † ⊗ I (2 ^ (e - e'))) ⊗ I 1 ).
   assert ((@Mmult (Init.Nat.mul (Init.Nat.mul (Nat.pow (S (S O)) s)
         (mul (mul (Nat.pow (S (S O)) (sub s' s)) (Nat.pow (S (S O)) (sub e' s')))
            (Nat.pow (S (S O)) (sub e e')))) (Nat.pow (S (S O)) (sub n e)))
   (mul (mul (Nat.pow (S (S O)) (sub s' s))
         (Nat.pow (S (S O)) (sub e' s')))
      (Nat.pow (S (S O)) (sub e e')))
   (mul
      (mul (Nat.pow (S (S O)) (sub s' s))
         (Nat.pow (S (S O)) (sub e' s')))
      (Nat.pow (S (S O)) (sub e e')))
            (m4 ⊗ m3 ⊗ m5) m7 )=  (m4 ⊗ m3 ⊗ m5) × m7).
            f_equal; try rewrite mul_1_l; try rewrite mul_1_r; try  reflexivity.
  rewrite H16.
   rewrite Heqm7. 
   repeat rewrite kron_mixed_product. rewrite Heqm3.
   repeat rewrite kron_mixed_product.  repeat rewrite Mmult_1_r.
   repeat rewrite Mmult_1_l. 

   (* assert( 2 ^ (s') * 2 ^ (e' - s') * 2 ^ (n - e')= 2 ^ (n)).
   admit. destruct H12.  *)
   remember ((I (2 ^ (s' - s)) ⊗ I (2 ^ (e' - s'))
   ⊗ I (2 ^ (e - e')))).
   assert((I (2 ^ s') ⊗ U † ⊗ I (2 ^ (n - e')))=
   ( I (2^(s)) ⊗ (I (2 ^ (s' -s) ) ⊗ U † ⊗ I (2 ^ (e - e')) )  ⊗ I (2^(n-e)))).
   repeat rewrite <-kron_assoc. rewrite id_kron.
   assert(2 ^ s * 2 ^ (s' - s)=2^s'). 
   rewrite <-pow_add_r. f_equal. admit. rewrite H17. clear H17.
   admit. auto_wf. auto_wf. apply WF_adjoint. 
   apply H8.  auto_wf. apply WF_kron. reflexivity. reflexivity.
    auto_wf. apply WF_adjoint. apply H8. auto_wf.
   rewrite H17.
   remember ((I (2 ^ s)
   ⊗ (I (2 ^ (s' - s)) ⊗ (U) † ⊗ I (2 ^ (e - e')))
   ⊗ I (2 ^ (n - e)))).
  remember ((m4 ⊗ m8 ⊗ m5)). 
  
  remember (m9 × m10). 
  assert ((@Mmult
  (mul
     (mul (Nat.pow (S (S O)) s)
        (mul
           (mul (Nat.pow (S (S O)) (sub s' s))
              (Nat.pow (S (S O)) (sub e' s')))
           (Nat.pow (S (S O)) (sub e e'))))
     (Nat.pow (S (S O)) (sub n e)))
  (Init.Nat.mul
     (Init.Nat.mul (Nat.pow (S (S O)) s)
        (mul
           (mul (Nat.pow (S (S O)) (sub s' s))
              (Nat.pow (S (S O)) (sub e' s')))
           (Nat.pow (S (S O)) (sub e e'))))
     (Nat.pow (S (S O)) (sub n e)))
  (mul
     (mul (Nat.pow (S (S O)) (sub s' s))
        (Nat.pow (S (S O)) (sub e' s')))
     (Nat.pow (S (S O)) (sub e e'))) m9 m10)= m9 × m10).
     f_equal. rewrite mul_1_l. rewrite mul_1_r. reflexivity.
     rewrite H18. rewrite Heqm9. rewrite Heqm10. 
   repeat   rewrite kron_mixed_product.  rewrite Heqm8.
   repeat rewrite kron_mixed_product. repeat rewrite Mmult_1_r.
   repeat rewrite Mmult_1_l.

   repeat rewrite <-Mmult_assoc.  f_equal. 

   assert((I (2 ^ s') ⊗ U  ⊗ I (2 ^ (n - e')))=
   ( I (2^(s)) ⊗ (I (2 ^ (s' -s) ) ⊗ U  ⊗ I (2 ^ (e - e')) )  ⊗ I (2^(n-e)))).
  admit.  rewrite H19. 
  remember ((I (2 ^ s) ⊗ (I (2 ^ (s' - s)) ⊗ U ⊗ I (2 ^ (e - e')))
  ⊗ I (2 ^ (n - e)))). 
  remember ((I (2 ^ (s' - s)) ⊗ I (2 ^ (e' - s')) ⊗ I (2 ^ (e - e')))).
  remember (m0 ⊗ m13 ⊗ m1). remember (m14 × m12). 

assert((@Mmult
(mul
   (mul (Nat.pow (S (S O)) (sub s' s))
      (Nat.pow (S (S O)) (sub e' s')))
   (Nat.pow (S (S O)) (sub e e')))
(Init.Nat.mul
   (Init.Nat.mul (Nat.pow (S (S O)) s)
      (mul
         (mul (Nat.pow (S (S O)) (sub s' s))
            (Nat.pow (S (S O)) (sub e' s')))
         (Nat.pow (S (S O)) (sub e e'))))
   (Nat.pow (S (S O)) (sub n e)))
(mul
   (mul (Nat.pow (S (S O)) s)
      (mul
         (mul (Nat.pow (S (S O)) (sub s' s))
            (Nat.pow (S (S O)) (sub e' s')))
         (Nat.pow (S (S O)) (sub e e'))))
   (Nat.pow (S (S O)) (sub n e))) m14 m12)= m14 × m12). 
   f_equal. rewrite mul_1_l. rewrite mul_1_r. reflexivity.
   rewrite H20.
   rewrite Heqm14. rewrite Heqm12. 
   repeat   rewrite kron_mixed_product.  rewrite Heqm13.
   repeat rewrite kron_mixed_product. repeat rewrite Mmult_1_r.
   repeat rewrite Mmult_1_l. f_equal.  
   rewrite Heqc. unfold q_update. unfold super.
   rewrite Heqc0.  repeat rewrite Cdiv_unfold.
   assert(2^n =(2 ^ s *
   (2 ^ (s' - s) * 2 ^ (e' - s') * 2 ^ (e - e')) *
   2 ^ (n - e))). admit . destruct H21.
   assert((2^n)=(2 ^ s' * 2 ^ (e' - s') * 2 ^ (n - e'))).
   admit. destruct H21.  rewrite <-trace_mult_Unitary. 
   reflexivity. 
   assert((2 ^ s' * 2 ^ (e' - s') * 2 ^ (n - e'))= 2 ^(n)).
   admit. destruct H21. 
   apply kron_unitary.  apply kron_unitary.
   apply id_unitary . apply H8. apply id_unitary.

   admit.  apply H8. 
   rewrite Heqm1. rewrite Heqm5. auto_wf.
   auto_wf. auto_wf. rewrite Heqm0. 
   rewrite Heqm4. auto_wf. rewrite Heqm5. auto_wf.
   rewrite Heqm4. auto_wf. auto_wf. 
   apply WF_adjoint. apply H8.
   auto_wf.  apply WF_adjoint. apply H8.
   rewrite Heqm5. auto_wf. auto_wf. auto_wf.
   rewrite Heqm4. auto_wf.
   rewrite Heqm1. auto_wf. rewrite Heqm0.
   auto_wf. auto_wf. apply H8.
   auto_wf. auto_wf. 
   assert((2 ^ (s'- s) * 2 ^ (e' - s') * 2 ^ (e- e'))= 2 ^(e-s)).
   admit. destruct H4. 
   apply kron_unitary.  apply kron_unitary.
   apply id_unitary . apply transpose_unitary. apply H8. apply id_unitary.

   apply transpose_unitary.
   assert((2 ^ (s'- s) * 2 ^ (e' - s') * 2 ^ (e- e'))= 2 ^(e-s)).
   admit. destruct H4. 
   apply kron_unitary.  apply kron_unitary.
   apply id_unitary . apply transpose_unitary. apply H8.
    apply id_unitary.
    apply Nat.eq_dec. apply Nat.eq_dec.
   Admitted. *)

   Local Open Scope C_scope.
Theorem rule_Meas_aux:  forall s' e' s e (v: Vector (2^(e-s))) z x
(n:nat) (st :state n) (st': state n),
WF_state st->WF_Matrix v-> (z< 2^(e'-s'))->
st'= s_update x z (((I (2^(s'))) ⊗ ((Vec (2^(e'-s')) z ) × (Vec (2^(e'-s')) z )†) ⊗ (I (2^(n-e))))) st->
State_eval (QExp_s  s  e  v ) st->
State_eval (QExp_s  s  e  ((C1 / (@trace (2^(e-s)) ((U_v  (∣ z ⟩_ (e'-s') × ⟨ z ∣_ (e'-s')) v)))).* 
                          (U_v  (∣ z ⟩_ (e'-s') × ⟨ z ∣_ (e'-s')) v))) st'.
Proof.  intros s' e' s e v z x n st st' H' Hv Hz. intros. simpl in *. 
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
assert((e-s)%nat= (n - (n - e) - s)%nat). admit. destruct H1.
destruct st. destruct st'. 
 unfold s_update in H. simpl in *.
injection H. intros. rewrite H1.
remember ((C1 /
trace
  (q_update
     (I (2 ^ s') ⊗ (∣ z ⟩_ (e' - s') × ⟨ z ∣_ (e' - s'))
      ⊗ I (2 ^ (n - e))) q))). 
remember (C1 / trace q).
assert((2 ^ (e - s))%nat= (2 ^ (s' - s) * 2 ^ (e' - s') * 2 ^ (e - e'))%nat).
admit. destruct H3. 
assert((2 ^ (e - s))%nat= ((2 ^ (e - s) + 0) * 1)%nat). rewrite mul_1_r.
rewrite Nat.add_0_r. reflexivity. destruct H3.
rewrite big_sum_Mmult_l. rewrite big_sum_Mmult_r.
rewrite big_sum_Mscale_l.
split. assumption. split. assumption. 
apply big_sum_eq_bounded. 
intros.  rewrite big_sum_Mmult_l. rewrite big_sum_Mmult_r.
rewrite big_sum_Mscale_l. 
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
⊗ I (2 ^ (n - e)) )=
  ((I (2 ^ s') ⊗ (∣ z ⟩_ (e' - s') × ⟨ z ∣_ (e' - s'))
  ⊗ I (2 ^ (n - e)) )) † )). 
 f_equal. admit. admit. 
  rewrite H5.  repeat rewrite kron_adjoint. 
  repeat rewrite id_adjoint_eq. repeat rewrite adjoint_involutive.
  clear H5.
  assert( 2 ^ (s) * 2 ^ (e - s) * 2 ^ (n - e)= 2 ^ (n)).
  admit. destruct H5. 
  assert( 2 ^ (s' - s) * 2 ^ (e' - s') * 2 ^ (e - e')= 2 ^ (e - s)).
  admit. destruct H5.   
  assert(I (2 ^ (s' - s) * 2 ^ (e' - s') * 2 ^ (e - e'))= I (2 ^ (s' - s))
  ⊗ I (2 ^ (e' - s')) ⊗ I (2 ^ (e - e'))). rewrite id_kron. rewrite id_kron.
  reflexivity. rewrite H5. repeat rewrite kron_adjoint.
  repeat rewrite id_adjoint_eq. repeat rewrite adjoint_involutive.
  assert(I (2 ^ (s' - s)) ⊗ (∣ z ⟩_ (e' - s') × ⟨ z ∣_ (e' - s')) ⊗ I (2 ^ (e - e'))=
 I 1 ⊗ (I (2 ^ (s' - s)) ⊗ (∣ z ⟩_ (e' - s') × ⟨ z ∣_ (e' - s')) ⊗ I (2 ^ (e - e'))) ⊗ I 1).
 rewrite kron_1_l. rewrite kron_1_r. reflexivity. apply WF_kron.
 reflexivity. reflexivity. auto_wf. auto_wf. 
 rewrite H6.  
 remember ((I (2 ^ (s' - s)) ⊗ I (2 ^ (e' - s')) ⊗ I (2 ^ (e - e')))).
 remember (⟨ x0 ∣_ (s)). remember (⟨ x1 ∣_ (n - e)).
 assert ((@kron 
 (Init.Nat.add
    (mul (mul (Nat.pow (S (S O)) (sub s' s)) (Nat.pow (S (S O)) (sub e' s')))
       (Nat.pow (S (S O)) (sub e e'))) O)
 (Init.Nat.mul (Nat.pow (S (S O)) s)
    (mul (mul (Nat.pow (S (S O)) (sub s' s)) (Nat.pow (S (S O)) (sub e' s')))
       (Nat.pow (S (S O)) (sub e e')))) (S O) (Nat.pow (S (S O)) (sub n e))
 (m0 ⊗ m) m1)= m0 ⊗ m ⊗ m1). 
   reflexivity. rewrite H7.
  repeat rewrite <- Mmult_assoc.
   remember (I 1
   ⊗ (I (2 ^ (s' - s)) ⊗ (∣ z ⟩_ (e' - s') × ⟨ z ∣_ (e' - s'))
      ⊗ I (2 ^ (e - e'))) ⊗ I 1).
   assert ((@Mmult
   (mul (mul (Nat.pow (S (S O)) (sub s' s)) (Nat.pow (S (S O)) (sub e' s')))
      (Nat.pow (S (S O)) (sub e e')))
   (mul (mul (Nat.pow (S (S O)) (sub s' s)) (Nat.pow (S (S O)) (sub e' s')))
      (Nat.pow (S (S O)) (sub e e')))
   (Init.Nat.mul
      (Init.Nat.mul (Nat.pow (S (S O)) s)
         (mul (mul (Nat.pow (S (S O)) (sub s' s)) (Nat.pow (S (S O)) (sub e' s')))
            (Nat.pow (S (S O)) (sub e e')))) (Nat.pow (S (S O)) (sub n e))) m2
            (m0 ⊗ m ⊗ m1))= m2 × (m0 ⊗ m ⊗ m1)).
            f_equal; try rewrite mul_1_l; try rewrite mul_1_r; try  reflexivity.
  rewrite H8.
   rewrite Heqm2. 
   repeat rewrite kron_mixed_product. rewrite Heqm.
   repeat rewrite kron_mixed_product.  repeat rewrite Mmult_1_r.
   repeat rewrite Mmult_1_l.
   

   repeat rewrite Mmult_assoc.
   assert((I (2 ^ (s' - s)) ⊗ (∣ z ⟩_ (e' - s') × ⟨ z ∣_ (e' - s')) † ⊗ I (2 ^ (e - e')))=
 I 1 ⊗ (I (2 ^ (s' - s)) ⊗ (∣ z ⟩_ (e' - s') × ⟨ z ∣_ (e' - s')) † ⊗ I (2 ^ (e - e'))) ⊗ I 1).
 rewrite kron_1_l. rewrite kron_1_r. reflexivity. auto_wf. 
 rewrite H9.  
 remember ((I (2 ^ (s' - s)) ⊗ I (2 ^ (e' - s')) ⊗ I (2 ^ (e - e')))).
 remember (∣ x0 ⟩_ (s)). remember (∣ x1 ⟩_ (n - e)).
  remember (m4 ⊗ m3 ⊗ m5). 
 assert ((@kron (Init.Nat.mul (Nat.pow (S (S O)) s)
    (mul  (mul (Nat.pow (S (S O)) (sub s' s))
          (Nat.pow (S (S O)) (sub e' s')))
       (Nat.pow (S (S O)) (sub e e'))))
 (Init.Nat.add  (mul (mul (Nat.pow (S (S O)) (sub s' s))
          (Nat.pow (S (S O)) (sub e' s')))
       (Nat.pow (S (S O)) (sub e e'))) O)
 (Nat.pow (S (S O)) (sub n e))  (S O)
 (m4 ⊗ m3) m5)= m4 ⊗ m3 ⊗ m5). 
   reflexivity. rewrite H10. 
   remember (I 1 ⊗ (I (2 ^ (s' - s)) ⊗ (∣ z ⟩_ (e' - s') × ⟨ z ∣_ (e' - s')) † ⊗ I (2 ^ (e - e'))) ⊗ I 1 ).
   assert ((@Mmult (Init.Nat.mul (Init.Nat.mul (Nat.pow (S (S O)) s)
         (mul (mul (Nat.pow (S (S O)) (sub s' s)) (Nat.pow (S (S O)) (sub e' s')))
            (Nat.pow (S (S O)) (sub e e')))) (Nat.pow (S (S O)) (sub n e)))
   (mul (mul (Nat.pow (S (S O)) (sub s' s))
         (Nat.pow (S (S O)) (sub e' s')))
      (Nat.pow (S (S O)) (sub e e')))
   (mul
      (mul (Nat.pow (S (S O)) (sub s' s))
         (Nat.pow (S (S O)) (sub e' s')))
      (Nat.pow (S (S O)) (sub e e')))
            (m4 ⊗ m3 ⊗ m5) m7 )=  (m4 ⊗ m3 ⊗ m5) × m7).
            f_equal; try rewrite mul_1_l; try rewrite mul_1_r; try  reflexivity.
  rewrite H11.
   rewrite Heqm7. 
   repeat rewrite kron_mixed_product. rewrite Heqm3.
   repeat rewrite kron_mixed_product.  repeat rewrite Mmult_1_r.
   repeat rewrite Mmult_1_l.  
  
     
   assert((I (2 ^ s') ⊗ (∣ z ⟩_ (e' - s') × ⟨ z ∣_ (e' - s'))
   ⊗ I (2 ^ (n - e)))=
   ( I (2^(s)) ⊗ (I (2 ^ (s' -s) ) ⊗ (∣ z ⟩_ (e' - s') × ⟨ z ∣_ (e' - s'))  ⊗ I (2 ^ (e - e')) )  ⊗ I (2^(n-e)))).
  admit.  rewrite H12.
  remember ((I (2 ^ s) ⊗ (I (2 ^ (s' - s)) ⊗ (∣ z ⟩_ (e' - s') × ⟨ z ∣_ (e' - s')) ⊗ I (2 ^ (e - e')))
  ⊗ I (2 ^ (n - e)))). 
  remember ((I (2 ^ (s' - s)) ⊗ I (2 ^ (e' - s')) ⊗ I (2 ^ (e - e')))).
  assert((I (2 ^ s') ⊗ (∣ z ⟩_ (e' - s') × ⟨ z ∣_ (e' - s')) †
  ⊗ I (2 ^ (n - e)))=
  ( I (2^(s)) ⊗ (I (2 ^ (s' -s) ) ⊗  (∣ z ⟩_ (e' - s') × ⟨ z ∣_ (e' - s')) † ⊗ I (2 ^ (e - e')) )  ⊗ I (2^(n-e)))).
  admit. rewrite H13. 
  remember ((I (2 ^ s)
  ⊗ (I (2 ^ (s' - s)) ⊗ ((∣ z ⟩_ (e' - s') × ⟨ z ∣_ (e' - s'))) † ⊗ I (2 ^ (e - e')))
  ⊗ I (2 ^ (n - e)))).
 remember ((m4 ⊗ m9 ⊗ m5)).
assert((@Mmult
(mul
   (mul (Nat.pow (S (S O)) s)
      (mul
         (mul (Nat.pow (S (S O)) (sub s' s))
            (Nat.pow (S (S O)) (sub e' s')))
         (Nat.pow (S (S O)) (sub e e'))))
   (Nat.pow (S (S O)) (sub n e)))
(Init.Nat.mul
   (Init.Nat.mul (Nat.pow (S (S O)) s)
      (mul
         (mul (Nat.pow (S (S O)) (sub s' s))
            (Nat.pow (S (S O)) (sub e' s')))
         (Nat.pow (S (S O)) (sub e e'))))
   (Nat.pow (S (S O)) (sub n e)))
(mul
   (mul (Nat.pow (S (S O)) (sub s' s))
      (Nat.pow (S (S O)) (sub e' s')))
   (Nat.pow (S (S O)) (sub e e'))) m10 m11)= m10 × m11). 
   f_equal. rewrite mul_1_l. rewrite mul_1_r. reflexivity.
   rewrite H14.
   rewrite Heqm10. rewrite Heqm11. 
   repeat   rewrite kron_mixed_product.  rewrite Heqm9.
   repeat rewrite kron_mixed_product. repeat rewrite Mmult_1_r.
   repeat rewrite Mmult_1_l.

   repeat rewrite <-Mmult_assoc.  f_equal. 

  remember ((I (2 ^ (s' - s)) ⊗ I (2 ^ (e' - s')) ⊗ I (2 ^ (e - e')))).
  remember (m0 ⊗ m12 ⊗ m1). remember (m13 × m8).

  assert(@Mmult
  (mul
     (mul (Nat.pow (S (S O)) (sub s' s))
        (Nat.pow (S (S O)) (sub e' s')))
     (Nat.pow (S (S O)) (sub e e')))
  (Init.Nat.mul
     (Init.Nat.mul (Nat.pow (S (S O)) s)
        (mul
           (mul (Nat.pow (S (S O)) (sub s' s))
              (Nat.pow (S (S O)) (sub e' s')))
           (Nat.pow (S (S O)) (sub e e'))))
     (Nat.pow (S (S O)) (sub n e)))
  (mul
     (mul (Nat.pow (S (S O)) s)
        (mul
           (mul (Nat.pow (S (S O)) (sub s' s))
              (Nat.pow (S (S O)) (sub e' s')))
           (Nat.pow (S (S O)) (sub e e'))))
     (Nat.pow (S (S O)) (sub n e))) m13 m8 = m13 × m8).
   f_equal. rewrite mul_1_l. rewrite mul_1_r. reflexivity.
   rewrite H15.
   rewrite Heqm13. rewrite Heqm8. 
   repeat   rewrite kron_mixed_product.  rewrite Heqm12.
   repeat rewrite kron_mixed_product. repeat rewrite Mmult_1_r.
   repeat rewrite Mmult_1_l. f_equal. 
   rewrite Mscale_assoc. f_equal.  
   rewrite Heqc2. rewrite Heqc. rewrite Heqc3.
   admit. auto_wf. rewrite Heqm1. auto_wf.
   rewrite Heqm5. auto_wf. auto_wf. auto_wf.
   rewrite Heqm0. auto_wf. rewrite Heqm4. auto_wf.
   rewrite Heqm5. auto_wf. rewrite Heqm4. auto_wf.
   auto_wf. auto_wf. auto_wf. auto_wf. rewrite Heqm5.
   auto_wf. auto_wf. auto_wf. rewrite Heqm4. auto_wf.
   rewrite Heqm1. auto_wf. rewrite Heqm0. auto_wf.
   auto_wf. auto_wf. auto_wf.
Admitted.


