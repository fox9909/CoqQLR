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


Definition U_v {m n:nat}(s' e' s e:nat) (U: Square (2^m)) (v: Vector (2^n)):
Vector (2^(e-s)) := 
@Mmult ((2^(e-s)))  (2^(e-s)) 1  (I (2^(s'-s)) ⊗ U ⊗ (I (2^(e-e')))) v.


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

  Lemma trace_mult': forall (m n:nat) (A:Matrix m n) (B:Matrix n m),
  trace(Mmult A B) =trace (Mmult B A).
  Proof. intros. unfold trace. unfold Mmult. 
         rewrite big_sum_swap_order. 
         apply big_sum_eq. apply functional_extensionality.
         intros. apply big_sum_eq. apply functional_extensionality.
         intros.
  apply Cmult_comm. 
  Qed.


Lemma  Ptrace_trace: forall  n (A:Square (2^n)) s e,
s <= n - e-> e<=n -> WF_Matrix A->
trace (PMpar_trace A  s e) = trace A.
Proof. intros. rewrite Ptrace_l_r'.
   assert(2^(n-e-s)=1 * 2 ^ (n - e - s) * 1) . lia.
   destruct H2. rewrite big_sum_trace.
   rewrite (big_sum_eq_bounded  _ ((fun i : nat =>
   trace (big_sum
      (fun j : nat =>
        ( (∣ i ⟩_ (s) × ⟨ i ∣_ (s)) ⊗ I (2 ^ (n - e - s)) ⊗  (∣ j ⟩_ (e)  × ⟨ j ∣_ (e)) × A))
        (2 ^ e))))).
    rewrite <-big_sum_trace.
    assert(2^n = 2^s * 2^(n-e -s) * (2^e));type_sovle'. 
    f_equal; type_sovle'. destruct H2.
    rewrite (big_sum_eq_bounded  _ ((fun i : nat =>
    @Mmult (2^n) (2^n) (2^n) ( (∣ i ⟩_ (s) × ⟨ i ∣_ (s)) ⊗   I (2 ^ (n - e - s))
    ⊗  (big_sum
      (fun j : nat => (∣ j ⟩_ (e) × ⟨ j ∣_ (e)) ) 
      (2 ^ e) ))  A ))  ).
    rewrite <-Mmult_Msum_distr_r. repeat rewrite <-kron_Msum_distr_r.
    repeat rewrite big_sum_I. repeat rewrite id_kron.
    assert( 2^s * 2^(n-e -s) * (2^e)= 2^n);type_sovle'. 
    f_equal; type_sovle'. destruct H2.
    rewrite Mmult_1_l. reflexivity. assumption.
    intros.  rewrite kron_Msum_distr_l.
    assert(2^n = 2^s * 2^(n-e -s) * (2^e));type_sovle'. 
    f_equal; type_sovle'. destruct H3.
    rewrite Mmult_Msum_distr_r. reflexivity.
    intros. repeat  rewrite big_sum_trace. apply big_sum_eq_bounded.
    intros. rewrite trace_mult'.   
    rewrite <-Mmult_assoc. 
    apply Logic.eq_trans with (trace
    (∣ x ⟩_ (s) ⊗ I (2 ^ (n - e - s)) ⊗ ∣ x0 ⟩_ (e)
     × (⟨ x ∣_ (s) ⊗ I (2 ^ (n - e - s)) ⊗ ⟨ x0 ∣_ (e)) × A)).
     f_equal. f_equal. f_equal; try lia.
    repeat rewrite kron_mixed_product. 
    rewrite Mmult_1_r.  reflexivity.
    auto_wf. assumption.
Qed.
     
Lemma PMtrace_Super_swap{n:nat}: forall l m  (M: Square (2^(n-m-l))) (A:Square (2^n)) ,
l<=n-m -> m<=n-> WF_Matrix M->
super M (PMpar_trace A  l m)= @PMpar_trace n (super (I (2 ^ l) ⊗ M ⊗ I (2 ^ m)) A) l m.
Proof. intros. unfold super. repeat rewrite Ptrace_l_r'.  
       assert((2 ^ (n - m - l)) = 1 * (2 ^ (n - m - l)) * 1). lia.
        destruct H2.
       rewrite (Mmult_Msum_distr_l ((2 ^ l)) _ M).
       rewrite Mmult_Msum_distr_r.
       apply big_sum_eq_bounded.  intros.  
       assert((2 ^ (n - m - l)) = 1 * (2 ^ (n - m - l)) * 1). lia.
       destruct H3. 
       rewrite Mmult_Msum_distr_l.
       rewrite Mmult_Msum_distr_r.
       apply big_sum_eq_bounded.  intros. 
        rewrite Mmult_assoc_5.   rewrite Mmult_assoc_5.
        f_equal.  f_equal. 
        apply Logic.eq_trans with ((I 1 ⊗ M ⊗ I 1) × (⟨ x ∣_ (l) ⊗ I (2 ^ (n - m - l)) ⊗ ⟨ x0 ∣_ (m))).
        rewrite kron_1_l; auto_wf. rewrite kron_1_r. f_equal; try lia. 
        apply Logic.eq_trans with (⟨ x ∣_ (l) ⊗ I (2 ^ (n - m - l)) ⊗ ⟨ x0 ∣_ (m)
        × (I (2 ^ l) ⊗ M ⊗ I (2 ^ m))).
      repeat rewrite kron_mixed_product. repeat rewrite Mmult_1_l; auto_wf.
      repeat rewrite Mmult_1_r; auto_wf.  f_equal; auto_wf. 
      f_equal; lia. 

      apply Logic.eq_trans with ((∣ x ⟩_ (l) ⊗ I (2 ^ (n - m - l)) ⊗ ∣ x0 ⟩_ (m))× (I 1 ⊗ (M) † ⊗ I 1)  ).
        rewrite kron_1_l; auto_wf. rewrite kron_1_r. f_equal; try lia. 
        apply Logic.eq_trans with ((I (2 ^ l) ⊗ M ⊗ I (2 ^ m)) †
        × (∣ x ⟩_ (l) ⊗ I (2 ^ (n - m - l)) ⊗ ∣ x0 ⟩_ (m))). 
        repeat rewrite kron_adjoint. repeat rewrite id_adjoint_eq.
      repeat rewrite kron_mixed_product. repeat rewrite Mmult_1_l; auto_wf.
      repeat rewrite Mmult_1_r; auto_wf.  f_equal; auto_wf. 
      f_equal; lia. assumption. assumption. 
Qed.



#[export]Hint Unfold PMpar_trace: M_db.


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
        assert((e-s)%nat= (n - (n - e) - s)%nat).
        lia. destruct H2.  
        assert((2 ^ s * 2 ^ (e - s) * 2 ^ (n - e))%nat=(2 ^ n)%nat).
        type_sovle'.  destruct H2.
        remember (((R1 / Cmod (trace (QInit_fun s e q)))%R)).  
        split. lia. split. lia.
        unfold QInit_fun. 
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
  
  rewrite Heqr.  
  apply Logic.eq_trans with (C1 .* I 1). f_equal.   
  assert((2 ^ n)%nat= (2 ^ s * 2 ^ (e - s) * 2 ^ (n - e))%nat).
  type_sovle'. destruct H4. 
  rewrite QInit_trace. 
  assert( (2 ^ s * 2 ^ (e - s) * 2 ^ (n - e))%nat= (2 ^ n)%nat).
  type_sovle'. destruct H4. 
   assert( (n - (n - e) - s)%nat= (e-s)%nat).
  lia. destruct H4.  
  assert ((big_sum
  (fun i : nat =>
   big_sum
     (fun j : nat =>
      ⟨ i ∣_ (s) ⊗ I (2 ^ (n - (n - e) - s)) ⊗ ⟨ j ∣_ (n - e) × q
      × (⟨ i ∣_ (s) ⊗ I (2 ^ (n - (n - e) - s)) ⊗ ⟨ j ∣_ (n - e)) †)
     (2 ^ (n - e))) (2 ^ s))= @PMpar_trace n q s (n-e)).
  symmetry. rewrite Ptrace_l_r'. apply big_sum_eq_bounded.
  intros. apply big_sum_eq_bounded. intros. repeat rewrite kron_adjoint.
  rewrite id_adjoint_eq. repeat rewrite adjoint_involutive. f_equal. lia.
 rewrite H4. assert((2 ^ (n-(n-e)-s))% nat =(1 * 2 ^ ((n-(n-e)-s)) * 1)%nat). lia. destruct H5.
   rewrite Ptrace_trace. 

   assert(2^n= (2 ^ s * 2 ^ (n - (n - e) - s) * 2 ^ (n - e))).
  type_sovle'. destruct H5.
   unfold RtoC. 
   assert(@trace (2^n) q= (fst (@trace (2^n) q), snd (@trace (2^n) q))).
   destruct (trace q).
   reflexivity. rewrite H5.  rewrite mixed_state_trace_real.
  unfold Cmult. simpl. repeat  rewrite Rmult_0_l. rewrite Rmult_0_r.
  rewrite Rplus_0_l. rewrite Rminus_0_r. f_equal.
  rewrite Cmod_snd_0. rewrite Rdiv_unfold. rewrite Rmult_1_l.
  apply Rinv_l. assert((0 < fst (@trace (2^n) q))%R). 
 apply mixed_state_trace_gt0. apply H'.  lra.
 apply mixed_state_trace_gt0. apply H'. simpl. reflexivity.
 apply H'. lia. lia. apply WF_Mixed. apply H'. lia. 
 apply WF_Mixed. apply H'. apply Mscale_1_l.
  
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
Qed. 

Require Import ParDensityO.
Lemma WF_state_dstate_aux{n:nat}: forall (st:state n), 
WF_state st <-> WF_dstate_aux [st] .
Proof. split; unfold WF_dstate;
       destruct st; simpl; intros. 
    
       apply WF_cons. intuition. apply WF_nil. 
       unfold WF_state in H.  unfold WF_qstate in H. simpl in H.
       unfold d_trace_aux. unfold s_trace. simpl. rewrite Rplus_0_r.
       apply mixed_state_Cmod_1. intuition.

       inversion_clear H. intuition. 
Qed.


Lemma ceval_eq{n:nat}: forall (mu mu' mu1:list (cstate * qstate  n)) c,
mu1=mu'->
ceval_single c mu mu'->
ceval_single c mu mu1.
Proof. intros. rewrite H. assumption.
Qed.


Theorem rule_Qinit_aux' :  forall 
(s e n:nat) (mu : list (cstate * qstate n)) (mu': list (cstate * qstate n)),
WF_dstate_aux mu->
ceval_single (QInit s e) mu mu' ->
State_eval_dstate (BTrue) mu->
State_eval_dstate ((QExp_s s e  (Vec (2^(e-s)) 0))) mu'.
Proof. intros s e n mu. induction mu; intros. inversion H0; subst.
  --simpl in H0. simpl in H1. destruct H1.
  -- destruct mu. inversion H0; subst. inversion H8; subst.
     rewrite map2_nil_r in *.
      * econstructor.
       apply rule_Qinit_aux with ((sigma, rho)). 
       inversion_clear H. assumption. 
       assumption.  apply Forall_nil.
      
       *destruct a. inversion H0; subst. 
       apply d_seman_app_aux. 
       apply WF_ceval with (QInit s e) ([(c,q)]).
       apply WF_state_dstate_aux.  inversion_clear H. assumption.
       assert([(c, QInit_fun s e q)]= (StateMap.Raw.map2 (@option_app n) ([(c, QInit_fun s e q)])  ([]))).
       reflexivity.   rewrite H2. apply E_Qinit. assumption.  apply E_nil.

      apply WF_ceval with (QInit s e) ((p :: mu)).
      inversion_clear H. assumption. assumption.

      econstructor. apply rule_Qinit_aux with ((c, q)). 
      inversion_clear H. assumption.
      apply ceval_eq with ((StateMap.Raw.map2 (@option_app n) ([(c, QInit_fun s e q)])  ([]))).
      reflexivity. apply E_Qinit. assumption.  apply E_nil.
      apply Forall_nil.

      apply IHmu. inversion_clear H.  assumption. 
      intuition. inversion_clear H1.  apply State_eval_dstate_Forall.
      discriminate.  assumption.
Qed.    

Local Open Scope com_scope.
Definition hoare_triple
   (P:Assertion) (c : com) (Q : Assertion) : Prop :=
            forall (n:nat)  (mu : dstate n) (mu': dstate n),
               ceval c mu mu' ->
               sat_Assert  mu P ->
               sat_Assert  mu' Q.
Declare Scope rule_scope.
Notation "{{ P }}  c  {{ Q }}" :=
(hoare_triple P c Q) (at level 90, c custom com at level 99)
               : rule_scope.

Local Open Scope rule_scope.
Theorem rule_QInit: forall s e,
{{BTrue}} ( s e ) :Q= 0
{{(QExp_s s e  (Vec (2^(e-s)) 0))}}.
Proof. 
unfold hoare_triple;
intros s e n (mu,IHmu) (mu', IHmu').
intros. 
inversion_clear H; simpl in H3.
rewrite sat_Assert_to_State in *.
inversion_clear H0.
apply sat_F. intuition.
apply rule_Qinit_aux' with  mu.
intuition. intuition. assumption. 
Qed.



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
(s<=s')%nat->(s'<=e')%nat->(e'<=e)%nat->
(2 ^ (e - s) )%nat=
(2 ^ (s' - s) * 2 ^ (e' - s') * 2 ^ (e - e'))%nat.
Proof. intros.  
repeat rewrite <-Nat.pow_add_r. f_equal. lia. 
Qed.


Lemma  super_scale: forall {m n:nat} (M : Matrix m n) (A :Matrix n n) r,
super M (r .* A) =r.* (super M A) .
Proof. unfold super. intros. rewrite Mscale_mult_dist_r.
        rewrite Mscale_mult_dist_l. reflexivity.   
  
Qed.

Local Open Scope assert_scope.
Local Open Scope nat_scope.
Theorem rule_QUnit_aux:  forall s' e' s e (U: Square (2^(e'-s'))) (v: Vector (2^(e-s)))
(n:nat) (st :state n) (st': state n),
s<=s' /\ e' <=e ->
WF_state st->WF_Matrix v->
ceval_single (QUnit_One s' e' U) [st] [st'] ->
State_eval (QExp_s s  e  (U_v s' e' s e U† v) ) st->
State_eval (QExp_s s  e  v ) st'.
Proof. intros. simpl in *. destruct H3. destruct H4.
       split. intuition. split. intuition. 
       destruct st.  
      inversion H2; subst. inversion H15; subst.
      clear H15. apply inj_pair2_eq_dec in H8.
      apply inj_pair2_eq_dec in H8. subst.
      injection H13. intros. rewrite <-H6.
      rewrite <-PMtrace_scale in *. simpl in *.
      remember ((R1 /Cmod (trace (QUnit_One_fun s' e' U q)))%R).
      remember ((R1 / Cmod (trace q))%R).
      unfold QUnit_One_fun. unfold q_update.
      remember ((I (2 ^ s') ⊗ U ⊗ I (2 ^ (n - e')))).
      remember (I (2^s) ⊗ (I (2 ^ (s'-s))⊗ U ⊗ (I (2 ^ (e - e')))) ⊗ I (2 ^ (n - e))).
      apply Logic.eq_trans with (r .* PMpar_trace (super m0 q) s (n - e)).
      assert(m=m0). rewrite Heqm. rewrite Heqm0.
       rewrite Mmult_kron_5; auto_wf. repeat rewrite id_kron. 
       f_equal; type_sovle'; f_equal; type_sovle'; f_equal; type_sovle' .
       apply H14. rewrite H7.  f_equal. f_equal. f_equal; type_sovle'. 
       rewrite Heqm0. remember ((I (2 ^ (s' - s)) ⊗ U
       ⊗ I (2 ^ (e - e')))). 
       assert(2^(n-(n-e)-s)=((2 ^ (s' - s) * 2 ^ (e' - s') *
       2 ^ (e - e')))). type_sovle'. destruct H7.
       rewrite<-(PMtrace_Super_swap s (n-e) m1 q). 
       rewrite <-super_scale. 
       assert(r=r0).
       rewrite Heqr. rewrite Heqr0.
       assert((2 ^ n)%nat= (2 ^ s * 2 ^ (e - s) * 2 ^ (n - e))%nat).
        type_sovle'. destruct H7. 
        rewrite QUnit_One_trace.  reflexivity. lia.  apply WF_Mixed.
        apply H0. assumption. rewrite H7.  rewrite H5.
        unfold U_v. unfold outer_product.
        assert(2 ^ (s' - s) * 2 ^ (e' - s') * 2 ^ (e - e')= 2 ^ (e - s)).
        type_sovle'. destruct H8.
        assert(((2 ^ (s' - s) * 2 ^ (e' - s') *
        2 ^ (e - e')))=2^(n-(n-e)-s)). type_sovle'. destruct H8.
        unfold super. rewrite Heqm1. 
        rewrite Mmult_assoc_5. repeat rewrite Mmult_adjoint.
        repeat rewrite kron_adjoint.   repeat rewrite id_adjoint_eq. repeat rewrite adjoint_involutive.
        rewrite (Mmult_assoc (v) †).
        repeat rewrite kron_mixed_product.
        repeat rewrite Mmult_1_r; auto_wf. destruct H14.
        assert((U × (U) †)=I (2 ^ (e' - s'))). admit.
        rewrite H11. repeat rewrite id_kron. rewrite Mmult_1_l; auto_wf.
        rewrite Mmult_1_r; auto_wf. reflexivity. lia. lia. 
        rewrite Heqm1. apply WF_kron; auto_wf; type_sovle'.
        apply WF_kron; auto_wf; type_sovle'. apply H14.
        apply Nat.eq_dec. apply Nat.eq_dec.
Admitted.

Theorem rule_QUnit_One_aux' : forall s' e' s e (U: Square (2^(e'-s'))) (v: Vector (2^(e-s)))
(n:nat) (mu : list (cstate * qstate n)) (mu': list (cstate * qstate n)),
s<=s' /\ e' <=e ->
WF_dstate_aux mu->WF_Matrix v->
ceval_single (QUnit_One s' e' U) mu mu' ->
State_eval_dstate (QExp_s s  e  (U_v s' e' s e U† v) ) mu->
State_eval_dstate (QExp_s s  e  v ) mu'.
Proof. intros s' e' s e U v n mu. induction mu; intros. inversion H2; subst.
  -- simpl in H3. destruct H3.
  -- destruct mu. inversion H2; subst. inversion H12; subst. 
     apply inj_pair2_eq_dec in H6. apply inj_pair2_eq_dec in H6.
     destruct H6. rewrite map2_nil_r in *.
      * econstructor.
       apply rule_QUnit_aux with s' e' U1 ((sigma, rho)). intuition. 
       inversion_clear H0. assumption. 
       assumption. assumption. inversion_clear H3. assumption.  apply Forall_nil.
       apply Nat.eq_dec. apply Nat.eq_dec.
      
       *destruct a. inversion H2; subst.  
       apply inj_pair2_eq_dec in H6. apply inj_pair2_eq_dec in H6.
       destruct H6.
       apply d_seman_app_aux. 
       apply WF_ceval with (QUnit_One s' e' U1) ([(c,q)]).
       apply WF_state_dstate_aux.  inversion_clear H0. assumption.
       apply ceval_eq with ((StateMap.Raw.map2 (@option_app n) ([(c, QUnit_One_fun s' e' U1 q)])  ([]))).
       reflexivity.  apply E_Qunit_One. assumption. assumption.  apply E_nil.

      apply WF_ceval with (QUnit_One s' e' U1) ((p :: mu)).
      inversion_clear H0. assumption. assumption.

      econstructor.  apply rule_QUnit_aux with s' e' U1 ((c, q)). intuition. 
      inversion_clear H0. assumption. assumption. 
      apply ceval_eq with ((StateMap.Raw.map2 (@option_app n) ([(c, QUnit_One_fun s' e' U1 q)])  ([]))).
      reflexivity.  apply E_Qunit_One. assumption. assumption.  apply E_nil.
      inversion_clear H3. assumption.
      apply Forall_nil.

      apply IHmu. intuition. inversion_clear H0.  assumption. assumption. 
      intuition. inversion_clear H3.  apply State_eval_dstate_Forall.
      discriminate.  assumption. apply Nat.eq_dec. apply Nat.eq_dec.
Qed.    

Theorem rule_QUnit_One : forall s' e' s e (U: Square (2^(e'-s'))) (v: Vector (2^(e-s))),
s<=s' /\ e' <=e ->WF_Matrix v->
{{ QExp_s s  e  (U_v s' e' s e U† v) }} QUnit_One s' e' U {{ QExp_s s  e  v }}.
Proof. unfold hoare_triple;
intros s' e' s e U v Hs Hv n (mu,IHmu) (mu', IHmu').
intros. 
inversion_clear H; simpl in H3.
rewrite sat_Assert_to_State in *.
inversion_clear H0.
apply sat_F. intuition.
apply rule_QUnit_One_aux' with s' e' U mu.
intuition. intuition. assumption. assumption. assumption.
Qed.

(* Lemma  dstate_oplus:forall,
sat_Assert mu (D) -> sat_Assert mu' (D)->
sat_Assert (d_app mu mu') (D) .
Proof.
  
Qed. *)

(* Theorem rule_QUnit_Ctral : forall s' e' s e (U: Square (2^(e'-s'))) (v: Vector (2^(e-s))),
s<=s' /\ e' <=e ->WF_Matrix v->
{{ QExp_s s  e  (U_v U† v) }} QUnit_One s' e' U {{ QExp_s s  e  v }}.
Proof. unfold hoare_triple;
intros s' e' s e U v Hs Hv n (mu,IHmu) (mu', IHmu').
intros. 
inversion_clear H; simpl in H3.
rewrite sat_Assert_to_State in *.
inversion_clear H0.
apply sat_F. intuition.
apply rule_QUnit_One_aux' with s' e' U mu.
intuition. intuition. assumption. assumption. assumption.
Qed. *)

Lemma inner_trace: forall n (x: Vector (2 ^ n)),
WF_Matrix x->
 ((norm x) * (norm x))%R = (fst (trace (x × x †))).
Proof. intros. unfold norm. rewrite sqrt_sqrt. 
f_equal. unfold inner_product. rewrite trace_mult'.  unfold trace.
simpl. rewrite Cplus_0_l.  reflexivity. apply inner_product_ge_0.
Qed. 

Lemma fst_mult_swap: forall (x:R) (y:C),
fst (x * y)%C=  (x * fst y)%R
 .
Proof. intros. destruct y. simpl. rewrite Rmult_0_l.
      rewrite Rminus_0_r. reflexivity. Qed.


Lemma  RtoC_eq: forall r1 r2,
r1=r2-> RtoC r1= RtoC r2  .
Proof. intros. rewrite<-H. reflexivity. Qed.


Lemma nrom_not_0{n:nat}: forall(A:Vector n) ,
WF_Matrix A->
A<>Zero-> (norm A <>0)%R .
Proof. intros. unfold not.  intros.
 apply norm_zero_iff_zero in H1.
intuition. assumption.
Qed.


Lemma  Mixed_State_aux_eq{n:nat}: forall (q1 q2: Square (2^n)),
q1 = q2 -> Mixed_State_aux q1 -> Mixed_State_aux q2 .
Proof. intros. rewrite <-H. assumption.
Qed.

Lemma squre_not_0:forall (r:R),
(r<>0)%R->
(r^2<>0)%R .
Proof. intros. simpl. rewrite Rmult_1_r. apply Rmult_integral_contrapositive_currified.
assumption. assumption.
Qed.

Lemma WF_U_v:forall s' e' s e (v:Vector (2^(e-s))) (M:Square (2^(e'-s'))),
s<=s'/\ s' <= e'/\ e'<=e->
WF_Matrix v-> WF_Matrix M-> WF_Matrix (U_v s' e' s e M v).
Proof. intros. unfold U_v. auto_wf.
Qed.

#[export] Hint Resolve WF_U_v: wf_db.

Local Open Scope C_scope.
Lemma PMtrace_Meas{n:nat}: forall s' e' s e z (v:Vector (2^(e-s))) (q:Square (2^n)),
WF_qstate q->
s<=s'/\ s' <= e'/\ e'<=e /\ e<=n-> (z< 2^(e'-s')) ->WF_Matrix v->
(R1 / Cmod (trace q))%R .* PMpar_trace q s (n - e) = outer_product v v->
(norm (@U_v (e'-s') (e-s) s' e' s e (∣ z ⟩_ (e' - s') × ⟨ z ∣_ (e' - s')) v) *
norm (@U_v (e'-s') (e-s) s' e' s e (∣ z ⟩_ (e' - s') × ⟨ z ∣_ (e' - s')) v))%R * (trace q) = 
@trace (2^n) (@q_update n (I (2 ^ s') ⊗ (∣ z ⟩_ (e' - s') × ⟨ z ∣_ (e' - s')) ⊗ I (2 ^ (n - e'))) q).
Proof. intros s' e' s e z v q Uq. intros. rewrite inner_trace. unfold U_v.
assert(2 ^ (s' - s) * 2 ^ (e' - s') * 2 ^ (e - e')= 2 ^ (e - s))%nat.
type_sovle'.  destruct H3.
repeat rewrite Mmult_adjoint. repeat rewrite kron_adjoint.
repeat rewrite id_adjoint_eq. rewrite Mmult_adjoint. repeat rewrite adjoint_involutive.
rewrite <-Mmult_assoc.   rewrite (Mmult_assoc _ v).
unfold outer_product in H2. rewrite <-H2.
assert(((2 ^ (s' - s) * 2 ^ (e' - s') *
2 ^ (e - e')))=2^(n-(n-e)-s))%nat. type_sovle'. destruct H3. 
remember ((R1 / Cmod (trace q))%R).
remember ((I (2 ^ (s' - s))
⊗ (∣ z ⟩_ (e' - s') × ⟨ z ∣_ (e' - s'))
⊗ I (2 ^ (e - e')))). 
remember (PMpar_trace q s (n - e)).
rewrite Mscale_mult_dist_r. rewrite Mscale_mult_dist_l.
rewrite trace_mult_dist. 
rewrite fst_mult_swap. rewrite Cmult_comm.
rewrite<- RtoC_mult. rewrite Cmult_assoc.
 rewrite Heqr. 
repeat rewrite Rdiv_unfold.  repeat rewrite Rmult_1_l.
rewrite Cmod_snd_0. unfold RtoC. 
assert(@trace (2^n) q=
(fst (@trace (2^n) q), snd (@trace (2^n) q))).
destruct (trace q). reflexivity. rewrite H3.
rewrite mixed_state_trace_real.   
unfold Cmult. simpl. repeat rewrite Rmult_0_r.
repeat rewrite Rmult_0_l.
repeat rewrite Rminus_0_r. repeat rewrite Rplus_0_l.
rewrite Rmult_0_l. rewrite Rinv_r.  rewrite Rmult_1_l. 
remember ((q_update
(I (2 ^ s') ⊗ (∣ z ⟩_ (e' - s') × ⟨ z ∣_ (e' - s'))
 ⊗ I (2 ^ (n - e'))) q)).
 assert(@trace (2^n) q0=
(fst (@trace (2^n) q0), snd (@trace (2^n) q0))).
destruct (@trace (2^n) q0). reflexivity. rewrite H4. 
rewrite mixed_state_trace_real_aux.  simpl. 
f_equal. rewrite Heqm. rewrite Heqm0. 
apply Logic.eq_trans with (( fst (trace
(super (I (2 ^ (s' - s)) ⊗ (∣ z ⟩_ (e' - s') × ⟨ z ∣_ (e' - s'))
⊗ I (2 ^ (e - e'))) (@PMpar_trace n q s (n - e)))))). f_equal.
  f_equal; f_equal; f_equal; f_equal.  unfold super.  f_equal;f_equal.
repeat rewrite kron_adjoint. repeat rewrite Mmult_adjoint.
repeat rewrite id_adjoint_eq; rewrite adjoint_involutive. f_equal. 
f_equal. rewrite Heqq0. unfold q_update.   
assert(2^(n-(n-e)-s)=((2 ^ (s' - s) * 2 ^ (e' - s') *
2 ^ (e - e'))))%nat. type_sovle'. destruct H5.
rewrite PMtrace_Super_swap. rewrite Ptrace_trace; auto_wf.
assert(((2 ^ (s' - s) * 2 ^ (e' - s') *
2 ^ (e - e')))=2^(n-(n-e)-s))%nat. type_sovle'. destruct H5. 
rewrite Mmult_kron_5; auto_wf. repeat rewrite id_kron.    
f_equal; f_equal; type_sovle'; f_equal; type_sovle';
f_equal; type_sovle'. f_equal; type_sovle' . 
lia. lia. 
assert(2^n=(2 ^ s * 2 ^ (n - (n - e) - s) *
   2 ^ (n - e)))%nat.  type_sovle'. destruct H5.
apply WF_super. auto_wf. apply WF_Mixed. apply Uq.
lia. lia. auto_wf. rewrite Heqq0. unfold q_update.
unfold super. 
apply Mixed_State_aux_eq with ((I (2 ^ s') ⊗ (∣ z ⟩_ (e' - s') × ⟨ z ∣_ (e' - s')) ⊗ I (2 ^ (n - e'))
   × q
   × (I (2 ^ s') ⊗ (∣ z ⟩_ (e' - s') × ⟨ z ∣_ (e' - s'))
      ⊗ I (2 ^ (n - e'))) †)). f_equal; type_sovle'.
      f_equal; type_sovle'. 
  apply WF_dstate_init; try lia.  apply Mixed_State_aux_to_Mix_State.
  apply Uq. 
admit. apply Uq.  admit.
  apply mixed_state_trace_real. apply Uq. apply WF_U_v. lia. auto_wf. auto_wf. 
Admitted. 

Lemma base_innner: forall i n,
(i<(2^n))%nat->
⟨ i ∣_ (n) × ∣ i ⟩_ (n) = I 1.
Proof. intros. assert(⟨ i ∣_ (n) × ∣ i ⟩_ (n)= ⟨ i ∣_ (n) × I (2^n) ×  ∣ i ⟩_ (n)).
       rewrite Mmult_1_r. reflexivity. auto_wf. 
       rewrite H0. 
      rewrite inner'.  
       unfold I. bdestruct ((i =? i)). bdestruct (i <? 2 ^ n). simpl.
       rewrite Mscale_1_l. reflexivity.     
       lia. lia. auto_wf. assumption.
Qed.

Lemma Rinv_l': forall (r1 r2:R),
(r2<>0)%R->
r1=r2-> (/r1 * r2 = 1)%R.
Proof. intros. rewrite H0. apply Rinv_l. assumption.   
Qed.



Local Open Scope C_scope.
Theorem rule_Meas_aux:  forall s' e' s e (v: Vector (2^(e-s))) z x
(n:nat) (st :state n) (st': state n),
s<=s'/\ s' <= e'/\ e'<=e-> (norm v = 1)%R->
WF_state st->WF_Matrix v-> (z< 2^(e'-s'))->
st'= s_update x z (((I (2^(s'))) ⊗ ((Vec (2^(e'-s')) z ) × (Vec (2^(e'-s')) z )†) ⊗ (I (2^(n-e'))))) st->
State_eval (QExp_s  s  e  v ) st->
State_eval (QExp_s  s  e  ((R1 / (@norm (2^(e-s)) ((U_v s' e' s e (∣ z ⟩_ (e'-s') × ⟨ z ∣_ (e'-s')) v))))%R .* 
                          (U_v s' e' s e (∣ z ⟩_ (e'-s') × ⟨ z ∣_ (e'-s')) v))) 
                          (s_scale ((R1 / (@norm (2^(e-s)) ((U_v s' e' s e  (∣ z ⟩_ (e'-s') × ⟨ z ∣_ (e'-s')) v)))) ^2) st').
Proof. 

intros. remember ((R1 / norm (U_v s' e' s e (∣ z ⟩_ (e' - s') × ⟨ z ∣_ (e' - s')) v))%R). 
 destruct H5. destruct H6. split. intuition. split. intuition.

 destruct st. destruct st'. simpl. rewrite Mscale_assoc.
 rewrite Cmult_comm. rewrite Rmult_1_r.
 rewrite <-PMtrace_scale in *. simpl in H7. rewrite <-Mscale_assoc.
 remember ((R1 / Cmod (trace q))%R). 
 remember ((R1 / Cmod (trace ((r * (r))%R .* q0)))%R). 
 unfold s_update in H4. injection H4. intros.
 rewrite H8. unfold q_update.
 remember ((I (2 ^ s')⊗ (∣ z ⟩_ (e' - s')   × ⟨ z ∣_ (e' - s')) ⊗ I (2 ^ (n - e')))).
  remember (I (2^s) ⊗ (I (2 ^ (s'-s))⊗ (∣ z ⟩_ (e' - s')   × ⟨ z ∣_ (e' - s')) ⊗ (I (2 ^ (e - e')))) ⊗ I (2 ^ (n - e))).
      apply Logic.eq_trans with ((r * r)%R.* (r1 .* PMpar_trace (super m0 q) s (n - e))).
      assert(m=m0). rewrite Heqm. rewrite Heqm0.
       rewrite Mmult_kron_5; auto_wf. repeat rewrite id_kron. 
       f_equal; type_sovle'; f_equal; type_sovle'; f_equal; type_sovle' .
       rewrite H10.  f_equal; f_equal; f_equal; f_equal; type_sovle'. 
       rewrite Heqm0. 
       assert(2^(n-(n-e)-s)=((2 ^ (s' - s) * 2 ^ (e' - s') *
       2 ^ (e - e'))))%nat. type_sovle'. destruct H10.
       rewrite<-PMtrace_Super_swap; auto_wf. 
       rewrite <-super_scale.  
       assert(r1=r0). 
       rewrite Heqr1. rewrite Heqr0. f_equal. f_equal.
       rewrite H8. rewrite trace_mult_dist. rewrite Heqr.
       rewrite Rmult_div.  rewrite Heqm. 
       rewrite <-(PMtrace_Meas s' e' s e z v).
       rewrite Cmult_assoc.   
       rewrite RtoC_mult.  rewrite Rdiv_unfold. repeat rewrite Rmult_1_l.
       rewrite Rinv_l. apply Cmult_1_l.  admit. intuition. intuition.
       intuition. intuition. rewrite Heqr0 in H7. intuition.  admit. admit. 

        rewrite H10. rewrite H7.
        unfold U_v. unfold outer_product. 
        assert(2 ^ (s' - s) * 2 ^ (e' - s') * 2 ^ (e - e')= 2 ^ (e - s))%nat.
        type_sovle'. destruct H11.
        assert(((2 ^ (s' - s) * 2 ^ (e' - s') *
        2 ^ (e - e')))=2^(n-(n-e)-s))%nat. type_sovle'. destruct H11.
        rewrite Mscale_mult_dist_l. rewrite Mscale_adj.
        rewrite Mscale_mult_dist_r. repeat rewrite <-Mscale_mult_dist_l.
        rewrite Mscale_assoc. rewrite Cconj_R. rewrite RtoC_mult.
        repeat rewrite Mscale_mult_dist_l. f_equal.
        unfold super.
         repeat rewrite Mmult_adjoint. repeat rewrite kron_adjoint. 
        repeat rewrite id_adjoint_eq. repeat rewrite adjoint_involutive.
        repeat  rewrite Mmult_assoc. reflexivity.  lia. lia. 
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
  (forall j,  (j< n_0 )-> sat_State (f j) (g j)) ->
big_and (fun_to_list f n_0) (fun_to_list g n_0)  .
  Proof. induction n_0. intros. simpl. intuition.
          intros. simpl. assert((S n_0)= n_0+1). rewrite add_comm.
           reflexivity.   apply big_and_app.
           apply IHn_0. intros. apply H. lia.
           simpl.
           split.  apply H. lia. intuition.   
   
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


Lemma  Forall_fun_to_list{G:Type}: forall (f: G-> Prop) (g:nat->G) n0,
(forall i, i< n0 -> f (g i))->
Forall f (fun_to_list g n0)  .
Proof. induction n0; intros. simpl. apply Forall_nil.
 simpl. rewrite Forall_app. split. apply IHn0. intros.
 apply H. lia. econstructor. apply H. lia. apply Forall_nil.
  
Qed.


Lemma  big_map2_app{n:nat}: forall (f1 : list R) (g1: list( (list (cstate * qstate n)))) ( f2: list R) (g2: list( (list (cstate * qstate n)))),
length f1 =length g1 ->length f2 =
length g2->
big_map2 (f1 ++ f2 ) ( g1++g2)= StateMap.Raw.map2 option_app (big_map2 f1 g1) (big_map2 f2 g2).
Proof. induction f1;  induction g1; intros.
 simpl.  rewrite map2_r_refl. reflexivity. 
 discriminate H. discriminate H. 
simpl. 
rewrite IHf1. rewrite map_assoc.  f_equal.
injection H. intuition. assumption.
Qed.


Lemma  big_app_map2{ n:nat}: forall (f1: nat-> R) (f2: nat->  (list (cstate * qstate n))) n0,
big_map2 (fun_to_list f1 n0) (fun_to_list f2 n0) = 
big_app (fun x => StateMap.Raw.map (fun q=> (f1 x)  .* q) (f2 x)) n0 .
Proof. induction n0; intros. simpl. reflexivity.
simpl. rewrite <-IHn0. rewrite big_map2_app. 
f_equal. simpl. rewrite map2_nil_r. reflexivity.
repeat rewrite fun_to_list_length. reflexivity.
reflexivity.
Qed.


Local Open Scope com_scope.

Lemma ceval_single_1{n:nat}: forall (mu mu':list (state n)) X a,
ceval_single <{ X := a }> mu mu'->
mu'= d_update_cstate_aux X a mu .
Proof. induction mu;  intros;
       inversion H; subst.
       simpl. reflexivity.
       unfold d_update_cstate_aux.
       f_equal. apply IHmu.
       assumption. 
Qed.


Theorem rule_assgn: forall (D:Assertion) (i:nat) ( a:aexp),
             {{Assn_sub i a D}} i := a {{D}}.
Proof. unfold hoare_triple;
       intros F X a n (mu,IHmu) (mu', IHmu').
       intros. 
       inversion_clear H; simpl in H3.
       apply ceval_single_1 in H3.
       apply sat_Assert_dstate_eq with 
       ({|
        StateMap.this := d_update_cstate_aux X a mu;
        StateMap.sorted := d_update_cstate_sorted X a mu IHmu
      |}).
       unfold dstate_eq. simpl. intuition. 
       inversion_clear H0. unfold d_update_cstate in H.
       simpl in H. assumption.
Qed. 
Theorem rule_asgn_aux :  forall (P:Pure_formula) (i:nat) ( a:aexp) 
(n:nat) (mu : list (cstate * qstate n)) (mu': list (cstate * qstate n)),
WF_dstate_aux mu->
ceval_single (<{i := a}>) mu mu' ->
State_eval_dstate (Assn_sub_P i a P) mu->
State_eval_dstate P mu'.
Proof. intros P i a n mu. induction mu; intros; inversion H; subst.
  --simpl in H0. inversion H0; subst. simpl in H1. destruct H1.
  -- destruct mu. inversion H0; subst. inversion_clear H10; subst.
     simpl. econstructor.  simpl in H1. inversion_clear H1.
     assumption. apply Forall_nil.
     destruct a0. inversion_clear H0. 
     apply d_seman_app_aux.
     apply WF_state_dstate_aux.  
     apply WF_state_eq with (c,q). reflexivity.
     assumption. apply WF_ceval with (<{ i := a }>)
      ((p :: mu)). assumption. assumption.
    inversion_clear H1. simpl in H0. simpl.
    econstructor. assumption. apply Forall_nil.
     apply IHmu. intuition. assumption. 
     inversion_clear H1. apply State_eval_dstate_Forall.
     discriminate.  assumption.
Qed.    




Lemma Cdiv_1: forall (r1 r2: C),
 (r1<>C0%C)%C->
r1=r2 ->(r1 * / r2)%C= C1 .
Proof. intros. rewrite <-H0.  apply Cinv_r.
assumption.
Qed.





(* Lemma Mmult_eq_0: forall {m n o: nat}, forall (A:Matrix m n) (B:Vector n),
A ×  B = Zero -> A= Zero \/ B= Zero.
Proof. intros. assert( A= Zero \/ A <> Zero). apply Classical_Prop.classic.
      destruct H0. left. assumption.   assert( B= Zero \/ B<> Zero).
      apply Classical_Prop.classic.
      destruct  H1.  right . assumption.
       
Qed.


Lemma Mmult_not_0: forall {m n o: nat}, forall (A:Matrix m n) (B:Matrix n o),
A <> Zero /\ B<> Zero  ->
A ×  B <> Zero  .
Proof. intros. assert( A= Zero \/ A <> Zero). apply Classical_Prop.classic.
       destruct H0. intuition. 
       assert( B= Zero \/ B <> Zero).  apply Classical_Prop.classic.
       destruct H1. intuition. unfold not. intros.

Qed. *)


Lemma  big_app_eq_bound{n:nat}: forall (f1 f2: nat-> list (cstate *qstate n)) n0,
(forall i, (i<n0)%nat -> f1 i = f2 i) -> big_app f1 n0 = big_app f2 n0.
Proof. intros. induction n0; intros. simpl. reflexivity.
    simpl. f_equal. apply IHn0. intros. apply H. lia. 
    apply H. lia.
  
Qed.


Lemma  C_n0t_C0:  forall c:C, (fst c <> 0)%R->
(c<> C0)%C.
Proof. intros. unfold not. intros. destruct c. injection H0.
     intros.  rewrite H1 in H. simpl in H. lra.
  
Qed.



Local Open Scope nat_scope.
Theorem rule_Meas_aux':forall s' e' s e (v: Vector (2^(e-s))) x (P :nat-> (Pure_formula))
(n:nat) (st :state n) (mu: dstate n),
s<=s' /\ e'<=e->
(norm v = 1)%R -> WF_Matrix v->
ceval (QMeas x s' e') st mu-> 
sat_Assert st ((QExp_s  s  e  v) /\ big_Sand (fun i:nat => (Assn_sub_P x i (P i))) (2^(e'-s'))) ->
sat_Assert mu  (big_pOplus (fun i:nat=> (@norm (2^(e-s)) ((U_v s' e' s e (∣ i ⟩_ (e'-s') × ⟨ i ∣_ (e'-s')) v))) ^ 2)%R
                               (fun i:nat=> SAnd ((P i))  (QExp_s  s  e ((R1 / ( (@norm (2^(e-s)) ((U_v  s' e' s e (∣ i ⟩_ (e'-s') × ⟨ i ∣_ (e'-s')) v)))))%R.* 
                               (U_v s' e' s e (∣ i ⟩_ (e'-s') × ⟨ i ∣_ (e'-s')) v)))) (2^(e'-s'))).
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
    symmetry in Hv.
    apply sqrt_1_unique in Hv. 
    assert(((v) † × v) 0 0= (fst (((v) † × v) 0 0), snd (((v) † × v) 0 0))).
    destruct (((v) † × v) 0 0). reflexivity.
    rewrite H7. rewrite Hv. rewrite Vector_State_snd_0. reflexivity.
    assumption. auto_wf.

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
rewrite base_innner. rewrite Mmult_1_r. reflexivity.
auto_wf. assumption. auto_wf. auto_wf. simpl. reflexivity.
intros.  rewrite Rmult_1_r. rewrite sqrt_sqrt. f_equal.
f_equal; type_sovle'. f_equal; type_sovle'. f_equal; type_sovle'.
apply inner_product_ge_0. 

assert(forall j,  Sorted.Sorted(StateMap.Raw.PX.ltk (elt:=qstate n)) 
[(c_update x j (fst st),
(R1 /( (@norm (2^(e-s))
            (U_v s' e' s e(∣ j ⟩_ (e' - s') × ⟨ j ∣_ (e' - s')) v))
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
 ((@norm (2^(e-s)) (U_v s' e' s e (∣ i ⟩_ (e' - s') × ⟨ i ∣_ (e' - s')) v))
  ^ 2)%R) (2 ^ (e' - s')))

       (fun_to_list (fun j : nat =>
       StateMap.Build_slist (H7 j) ) (2 ^ (e' - s')))
  
   (big_dapp  (fun_to_list
   (fun i : nat =>
    (
       (@norm (2^(e-s)) (U_v s' e' s e (∣ i ⟩_ (e' - s') × ⟨ i ∣_ (e' - s')) v))
     ^ 2)%R) (2 ^ (e' - s')))
          (fun_to_list (fun j : nat =>
          StateMap.Build_slist (H7 j) ) (2 ^ (e' - s')))) ).
apply big_dapp'_to_app.
repeat rewrite fun_to_list_length.
reflexivity.  apply Forall_fun_to_list. 
intros. simpl. rewrite Rmult_1_r. rewrite inner_trace.
assert((fst
(@trace (2^(e-s))
   (U_v s' e' s e (∣ i ⟩_ (e' - s') × ⟨ i ∣_ (e' - s')) v
    × (U_v s' e' s e (∣ i ⟩_ (e' - s') × ⟨ i ∣_ (e' - s')) v) †)) > 0)%R).
apply mixed_state_trace_gt0_aux. apply Vector_Mix_State.
unfold U_v. auto_wf. admit. lra. unfold U_v. auto_wf.

apply H8.
unfold dstate_eq. simpl.
inversion_clear H11. rewrite map2_nil_r. 
 rewrite big_dapp_this'.
  rewrite fun_dstate_to_list.  simpl.
  rewrite big_app_map2. apply big_app_eq_bound. intros. 
  simpl.  f_equal.  f_equal. 
  remember ((norm (U_v s' e' s e (∣ i ⟩_ (e' - s') × ⟨ i ∣_ (e' - s')) v) *
  (norm (U_v s' e' s e (∣ i ⟩_ (e' - s') × ⟨ i ∣_ (e' - s')) v) * 1))%R).
  rewrite Mscale_assoc. rewrite Rdiv_unfold. rewrite Rmult_1_l.
  rewrite RtoC_mult.
  rewrite Rinv_r. rewrite Mscale_1_l.  unfold QMeas_fun.
  reflexivity. assert((r>0)%R). rewrite Heqr. 
  rewrite Rmult_1_r. rewrite inner_trace.  apply mixed_state_trace_gt0_aux.
  apply Vector_Mix_State. unfold U_v. auto_wf. 
  admit.  unfold U_v. auto_wf. lra. 
 rewrite big_pOplus_get_npro. 
 apply big_and_sat.  intros.
  econstructor.    admit.
  apply State_eval_conj.  
  split.   simpl StateMap.this.
  assert(State_eval_dstate (P j)  [(c_update x j (fst st),(snd st))]).
  apply rule_asgn_aux with x (ANum j) [st]. 
  apply WF_state_dstate_aux. apply WF_state_dstate in H5. apply H5.
 assert([(c_update x j (fst st), snd st)]= StateMap.Raw.map2 option_app ([(c_update x j (fst st), snd st)])  ([])).
 reflexivity. rewrite H9. assert(j= aeval st (ANum j)). 
  simpl. reflexivity. remember ((ANum j) ). destruct st. rewrite H12. 
   apply E_Asgn. apply E_nil. inversion_clear H6. 
   econstructor.  admit. apply Forall_nil.  
simpl in *.  inversion_clear H9.  econstructor.
apply state_eq_Pure with ((c_update x j (fst st), snd st)).
reflexivity. assumption. assumption.  
  simpl StateMap.this.
  econstructor.
  assert((c_update x j (fst st),
  (R1 /
   (norm (U_v s' e' s e (∣ j ⟩_ (e' - s') × ⟨ j ∣_ (e' - s')) v) *
    (norm (U_v  s' e' s e (∣ j ⟩_ (e' - s') × ⟨ j ∣_ (e' - s')) v) * 1)))%R
  .* q_update
       (I (2 ^ s') ⊗ (∣ j ⟩_ (e' - s') × ⟨ j ∣_ (e' - s')) ⊗ I (2 ^ (n - e')))
       (snd st))=
 s_scale ((R1 /
 (norm (U_v   s' e' s e (∣ j ⟩_ (e' - s') × ⟨ j ∣_ (e' - s')) v) ^ 2))%R )   
  (c_update x j (fst st), q_update
       (I (2 ^ s') ⊗ (∣ j ⟩_ (e' - s') × ⟨ j ∣_ (e' - s')) ⊗ I (2 ^ (n - e')))
       (snd st))). unfold s_scale.
       simpl. reflexivity.  rewrite H9.

       assert(State_eval (QExp_s  s  e  ((R1 / (@norm (2^(e-s)) ((U_v  s' e' s e (∣ j ⟩_ (e'-s') × ⟨ j ∣_ (e'-s')) v))))%R .* 
       (U_v  s' e' s e (∣ j ⟩_ (e'-s') × ⟨ j ∣_ (e'-s')) v))) 
       (s_scale ((R1 / (@norm (2^(e-s)) ((U_v  s' e' s e (∣ j ⟩_ (e'-s') × ⟨ j ∣_ (e'-s')) v)))) ^2) (s_update x j (((I (2^(s'))) ⊗ ((Vec (2^(e'-s')) j ) × (Vec (2^(e'-s')) j )†) ⊗ (I (2^(n-e'))))) st))).
       apply rule_Meas_aux with x st. lia.  assumption. apply WF_state_dstate.
       assumption. assumption. assumption. reflexivity.
       inversion_clear H0. apply H12. 
       unfold s_update in H12.
       assert(forall r1 r2:R, ((r1/r2)^2= r1^2 / r2^2))%R.
       intros.
       repeat rewrite Rdiv_unfold.
assert(forall r, r²= r ^ 2)%R. unfold "²". simpl. intros. rewrite Rmult_1_r.
reflexivity. repeat rewrite<-H13. rewrite Rsqr_mult. rewrite Rsqr_inv'. reflexivity.
 rewrite H13 in H12. 
       assert((R1 ^ 2=R1)%R). simpl. repeat rewrite Rmult_1_r. reflexivity.
       rewrite H14 in H12.
       apply H12.  apply Forall_nil.
   apply Forall_fun_to_list. intros.
  unfold d_trace. simpl. inversion_clear H11.
  rewrite map2_nil_r. 
 rewrite  QMeas_trace.  unfold s_trace. simpl. rewrite Rplus_0_r.
 rewrite Rmult_1_r.  f_equal. rewrite trace_mult_dist.
  rewrite inner_trace.  rewrite Rdiv_unfold. rewrite Rmult_1_l.
  unfold U_v.  rewrite Mmult_adjoint.
  assert(2 ^ (n)=  2 ^ (s) * 2 ^ (e - s) * 2 ^ (n - e)).
  repeat rewrite <-pow_add_r. f_equal. admit. destruct H9.
  assert( ( 2 ^ (s') * 2 ^ (e' - s') * 2 ^ (n - e'))= 2 ^ (n)).
  type_sovle'. destruct H9.
assert( 2 ^ (s' - s) * 2 ^ (e' - s') * 2 ^ (e - e')= 2 ^ (e - s)).
type_sovle'.  destruct H9. repeat rewrite kron_adjoint.
repeat rewrite id_adjoint_eq.  rewrite Mmult_adjoint. rewrite adjoint_involutive.
remember ((I (2 ^ (s' - s)) ⊗ (∣ i ⟩_ (e' - s') × ⟨ i ∣_ (e' - s'))
⊗ I (2 ^ (e - e')))). rewrite <-Mmult_assoc.  rewrite (Mmult_assoc _ v _).
simpl in H0. inversion_clear H0. destruct H9.
destruct H9.  unfold outer_product in H12.
assert( 2 ^ (s' - s) * 2 ^ (e' - s') * 2 ^ (e - e')= 2 ^ (e - s)).
type_sovle'.  destruct H13. 
rewrite <-H12. rewrite <-PMtrace_scale. 
simpl. apply Logic.eq_trans with (((/
fst
  (trace
     (super m ((R1 / Cmod (@trace  (2^n) (snd st)))%R .* @PMpar_trace n (snd st) s (n - e))
      )))%R *
@trace (2^n)
 (q_update
    (I (2 ^ s') ⊗ (∣ i ⟩_ (e' - s') × ⟨ i ∣_ (e' - s')) ⊗ I (2 ^ (n - e')))
    (snd st)))%C).  f_equal. f_equal. f_equal. f_equal. f_equal.
    unfold super. f_equal. rewrite Heqm. repeat rewrite kron_adjoint.
  repeat  rewrite id_adjoint_eq. rewrite Mmult_adjoint. rewrite adjoint_involutive.
  reflexivity.  f_equal.  type_sovle'.
  assert(2^(n-(n-e)-s)=2 ^ (s' - s) * 2 ^ (e' - s') * 2 ^ (e - e')).
  type_sovle'. destruct H13.
  rewrite super_scale. rewrite PMtrace_Super_swap.
  rewrite trace_mult_dist.  rewrite fst_mult_swap.
  rewrite Ptrace_trace. rewrite Rinv_mult. 
  unfold q_update. rewrite Rdiv_unfold. rewrite Rmult_1_l.
   rewrite Rinv_inv. rewrite Rmult_comm.
  rewrite Cmult_comm. 
  rewrite <-RtoC_mult.  rewrite Cmult_assoc.
  apply Logic.eq_trans with ((C1 * Cmod (@trace (2^n) (snd st)))%C).
  f_equal.  rewrite RtoC_inv. apply Cdiv_1. unfold RtoC.
  apply C_n0t_C0. 
  assert(fst
  (trace
     (super
        (I (2 ^ s') ⊗ (∣ i ⟩_ (e' - s') × ⟨ i ∣_ (e' - s'))
         ⊗ I (2 ^ (n - e'))) (snd st)))>0)%R.
  apply mixed_state_trace_gt0_aux.  unfold super.
  assert(2^n= 2^s' * 2^(e'-s') *2^(n-e')). type_sovle'.
  destruct H13.
  apply Mixed_State_aux_eq with (  (I (2 ^ s') ⊗ (∣ i ⟩_ (e' - s') × ⟨ i ∣_ (e' - s'))
  ⊗ I (2 ^ (n - e')) × snd st
  × (I (2 ^ s') ⊗ (∣ i ⟩_ (e' - s') × ⟨ i ∣_ (e' - s'))
     ⊗ I (2 ^ (n - e'))) †)). f_equal; type_sovle'. 
     f_equal; type_sovle'. 
  apply WF_dstate_init. lia. lia. lia. apply Mixed_State_aux_to_Mix_State.
  apply WF_state_dstate in H1.
  apply H1. assert(forall r:R, (r>0)%R-> (r<>0)%R). intros. lra. 
  apply H14.  assert(2^n= 2^s' * 2^(e'-s') *2^(n-e')). type_sovle'.
  destruct H15. apply H13.
 unfold RtoC. 
 rewrite <-(@mixed_state_trace_real_aux (2^n))with ((super
 (I (2 ^ s') ⊗ (∣ i ⟩_ (e' - s') × ⟨ i ∣_ (e' - s'))
  ⊗ I (2 ^ (n - e'))) (snd st))).
  apply Logic.eq_trans with (trace (super
  (I (2 ^ s') ⊗ (∣ i ⟩_ (e' - s') × ⟨ i ∣_ (e' - s'))
   ⊗ I (2 ^ (n - e'))) (snd st))). f_equal; type_sovle'.
   f_equal;
   type_sovle'. 
 remember ((super
 (I (2 ^ s') ⊗ (∣ i ⟩_ (e' - s') × ⟨ i ∣_ (e' - s'))
  ⊗ I (2 ^ (n - e'))) (snd st))).
  assert(trace m0 = ((fst (trace m0)), (snd (trace m0)))).
  destruct (trace m0). simpl. reflexivity.
  rewrite H13.  
  f_equal. rewrite Heqm0. rewrite Heqm. f_equal. f_equal; type_sovle'.
  apply Logic.eq_trans with (super
  (I (2 ^ s)
   ⊗ (I (2 ^ (s' - s))
      ⊗ (∣ i ⟩_ (e' - s') × ⟨ i ∣_ (e' - s'))
      ⊗ I (2 ^ (e - e'))) ⊗ I (2 ^ (n - e))) 
  (snd st)). f_equal; type_sovle'. 
  rewrite Mmult_kron_5. f_equal; type_sovle'. f_equal; type_sovle'.
  rewrite id_kron.
  f_equal; type_sovle'. rewrite id_kron. f_equal;type_sovle'. 
  auto_wf. auto_wf. auto_wf. auto_wf. auto_wf. 
  f_equal; type_sovle'. f_equal; type_sovle'. f_equal; type_sovle'.
  f_equal; type_sovle'. f_equal; type_sovle'. 
  unfold super.
  assert(2^n= 2^s' * 2^(e'-s') *2^(n-e')). type_sovle'.
  destruct H13.
  apply Mixed_State_aux_eq with (  (I (2 ^ s') ⊗ (∣ i ⟩_ (e' - s') × ⟨ i ∣_ (e' - s'))
  ⊗ I (2 ^ (n - e')) × snd st
  × (I (2 ^ s') ⊗ (∣ i ⟩_ (e' - s') × ⟨ i ∣_ (e' - s'))
     ⊗ I (2 ^ (n - e'))) †)). f_equal; type_sovle'. 
     f_equal; type_sovle'. 
  apply WF_dstate_init. lia. lia. lia. apply Mixed_State_aux_to_Mix_State.
  apply WF_state_dstate in H1. apply H1.
  assert(fst
  (trace
     (super
        (I (2 ^ s) ⊗ m
         ⊗ I (2 ^ (n - e))) (snd st)))>0)%R.
  apply mixed_state_trace_gt0_aux.  unfold super.
 rewrite Heqm. admit.  admit. 
 rewrite Cmult_1_l. unfold RtoC. destruct (trace (snd st)) eqn:E.
 rewrite Cmod_snd_0. simpl.  admit.
admit. admit.  lia. lia. rewrite Heqm.  admit.
lia. lia. rewrite Heqm. auto_wf. unfold U_v. auto_wf. intuition.
lia. apply Mixed_State_aux_to_Mix_State. apply WF_state_dstate in H5.
apply H5.
Admitted.

Fixpoint list_and{n:nat} (mu_n1 mu_n2: list (dstate n)) :=
match mu_n1, mu_n2 with 
|[], _ => []
|_,  [] =>[]
|(h1::t1), (h2::t2)=> (d_app h1 h2) :: (list_and t1 t2)
end.

Lemma lits_and_length{n:nat}: forall (mu_n1 mu_n2: list (dstate n)),
length mu_n1 = length mu_n2->
length (list_and mu_n1 mu_n2)= length mu_n1.
Proof. induction mu_n1; intros. simpl. reflexivity.
       destruct mu_n2. simpl. simpl in H. intuition. 
       simpl. f_equal. apply IHmu_n1. injection H. intuition. 
Qed.


Lemma big_dapp'_length{n:nat}: forall p_n (mu_n:list (dstate n)) (mu:dstate n),
big_dapp' p_n mu_n mu -> length p_n = length mu_n.
Proof. induction p_n; intros; destruct mu_n. reflexivity.
      inversion_clear H. inversion_clear H.
      inversion H; subst.
      simpl. f_equal. apply IHp_n with d0 .
      assumption.

   
Qed.


Lemma big_dapp_list_and{n:nat}: forall (p_n:list R)(mu_n1 mu_n2:list (dstate n)) ,
length mu_n1= length mu_n2->
dstate_eq (big_dapp p_n (list_and mu_n1 mu_n2))
(d_app (big_dapp p_n mu_n1) 
(big_dapp p_n mu_n2)) .
Proof. induction p_n; intros.  destruct mu_n1; destruct mu_n2; simpl;
        apply dstate_eq_sym; apply d_app_empty_l.

        destruct mu_n1; destruct mu_n2; simpl. apply dstate_eq_sym; apply d_app_empty_l.
        simpl in H. intuition. simpl in H. intuition.
        apply dstate_eq_trans with ((d_app (d_app (d_scale_not_0 a d) (d_scale_not_0 a (d0)))
        (big_dapp p_n (list_and mu_n1 mu_n2)))).
         apply d_app_eq. apply dstate_eq_sym. apply d_scalar_app_distr'.
        reflexivity. 
        apply dstate_eq_trans with ((d_app ((d_scale_not_0 a d))
        (d_app (big_dapp p_n mu_n1)
        (d_app (d_scale_not_0 a d0) (big_dapp p_n mu_n2))))).
        apply dstate_eq_trans with 
        ((d_app ((d_scale_not_0 a d))
        (d_app (d_scale_not_0 a d0)
        (big_dapp p_n (list_and mu_n1 mu_n2))))).
        apply d_app_assoc'. 
        apply d_app_eq. reflexivity. 
        apply dstate_eq_trans with ((d_app (d_app   (big_dapp p_n mu_n1) ((d_scale_not_0 a d0)))
        ((big_dapp p_n mu_n2)))). 
        
        apply dstate_eq_trans with ((d_app (d_app  ((d_scale_not_0 a d0)) (big_dapp p_n mu_n1))
        ((big_dapp p_n mu_n2)))).

        apply dstate_eq_trans with (d_app  (d_scale_not_0 a d0)
        (d_app (big_dapp p_n mu_n1) (big_dapp p_n mu_n2))).
        apply d_app_eq. reflexivity. apply IHp_n. injection H. intuition.
        apply dstate_eq_sym. apply d_app_assoc'.
        apply d_app_eq. apply d_app_comm. reflexivity.
        apply d_app_assoc'. apply dstate_eq_sym. apply d_app_assoc'.
Qed.

Lemma big_and_list_and{n:nat}: forall (mu_n1 mu_n2:list (dstate n)) (nF:npro_formula),
big_and mu_n1 nF->
big_and mu_n2 nF->
(Forall (fun x=> WF_dstate x) (list_and mu_n1 mu_n2))->
big_and (list_and mu_n1 mu_n2) nF.
Proof. induction mu_n1.  intros. destruct mu_n2. destruct nF. simpl.
     intuition. simpl in *. destruct H. destruct nF. simpl in *. destruct H0.
      simpl in *. destruct H.
      intros. destruct mu_n2. destruct nF. simpl in *. destruct H.
      simpl in *. destruct H0. destruct nF. simpl in H. destruct H.
      simpl in *. destruct H. destruct H0. inversion_clear H.
      inversion_clear H0.  split.  econstructor. inversion_clear H1. assumption.
      apply d_seman_app_aux. assumption. assumption. assumption. assumption.
      apply IHmu_n1. assumption. assumption. inversion_clear H1. assumption.   
Qed.


Lemma list_and_trace{n:nat}: forall (mu_n1 mu_n2:list (dstate n)) (a b:R),
(Forall (fun x=> WWF_dstate x) ( mu_n1 ))->
(Forall (fun x=> WWF_dstate x) ( mu_n2))->
Forall (fun mu_i : dstate n =>
        d_trace_aux (StateMap.this mu_i) = a) mu_n1->
        Forall
        (fun mu_i : dstate n =>
         d_trace_aux (StateMap.this mu_i) = b)
        mu_n2->
        Forall
        (fun mu_i : dstate n =>
         d_trace_aux (StateMap.this mu_i) = (a+b)%R)
        (list_and mu_n1 mu_n2).
Proof. induction mu_n1; intros; destruct mu_n2; simpl; try apply Forall_nil.
     inversion_clear H1. inversion_clear H2. 
        econstructor. unfold d_app. unfold StateMap.map2. simpl.
         rewrite d_trace_app_aux. f_equal. assumption. assumption.
         inversion_clear H. assumption. inversion_clear H0. assumption.
         apply IHmu_n1. inversion_clear H. assumption. inversion_clear H0. 
         assumption. assumption. assumption. 
Qed.


Lemma sat_dapp{n:nat}: forall (mu1 mu2:list (cstate *qstate n)) IHmu1 IHmu2 IHmu' (pF:pro_formula),
(Forall (fun x:R=>(x<>0)%R) (get_pro_formula pF))->
sat_Assert ({|
  StateMap.this := mu1;
  StateMap.sorted := IHmu1
|}) pF ->
sat_Assert ({|
  StateMap.this := mu2;
  StateMap.sorted := IHmu2
|}) pF ->
WF_dstate_aux ( StateMap.Raw.map2 option_app mu1 mu2)->
sat_Assert
  {|
    StateMap.this :=
      StateMap.Raw.map2 option_app mu1 mu2;
    StateMap.sorted := IHmu'
  |} pF.
Proof. intros. inversion_clear H0.  inversion_clear H5.
          inversion_clear H1. inversion_clear H10.
          econstructor. intuition. assumption. 
          econstructor. 
          assert(big_dapp' (get_pro_formula pF) (list_and mu_n mu_n0) (big_dapp (get_pro_formula pF) (list_and mu_n mu_n0) )).
          apply big_dapp'_to_app.  rewrite lits_and_length.
          apply big_dapp'_length with mu'. assumption.
          rewrite <-(big_dapp'_length ((get_pro_formula pF)) mu_n mu').
          rewrite <-(big_dapp'_length ((get_pro_formula pF)) mu_n0 mu'0).
          reflexivity. assumption. assumption.
          assumption. 
          apply H10. unfold dstate_eq in *. simpl in *.
          rewrite big_dapp_list_and. unfold d_app. unfold StateMap.map2.
          simpl.  f_equal.  rewrite H6. apply big_dapp_eq with (get_pro_formula pF) mu_n.
          assumption.   apply big_dapp'_to_app.  apply big_dapp'_length with mu'. assumption.
          assumption. rewrite H11. 
          apply big_dapp_eq with (get_pro_formula pF) mu_n0.
          assumption.   apply big_dapp'_to_app.  apply big_dapp'_length with mu'0. assumption.
          assumption.   rewrite <-(big_dapp'_length ((get_pro_formula pF)) mu_n mu').
          rewrite <-(big_dapp'_length ((get_pro_formula pF)) mu_n0 mu'0).
          reflexivity. assumption. assumption.
          apply big_and_list_and. assumption. assumption.
          admit. unfold d_trace in *. simpl in *.
          rewrite d_trace_app_aux. 
          apply list_and_trace. 
          apply Forall_WWF_WF.
          apply WF_big_and with (pro_to_npro_formula pF).
          assumption. 
          apply Forall_WWF_WF.
          apply WF_big_and with (pro_to_npro_formula pF).
          assumption. assumption. assumption.
          unfold dstate_eq in *. simpl in *.
          rewrite H6. 
          apply WWF_dstate_big_dapp with pF mu_n. 
          apply Forall_WWF_WF.
          apply WF_big_and with (pro_to_npro_formula pF).
          assumption. assumption.
          inversion_clear H4. assumption.
          unfold dstate_eq in *. simpl in *.
          rewrite H11. 
          apply WWF_dstate_big_dapp with pF mu_n0. 
          apply Forall_WWF_WF.
          apply WF_big_and with (pro_to_npro_formula pF).
          assumption. assumption.
          inversion_clear H4. assumption.
Admitted.


Theorem rule_Meas_aux'':forall s' e' s e (v: Vector (2^(e-s))) x (P :nat-> (Pure_formula))
(n:nat) (mu mu': dstate n),
s<=s' /\ e'<=e->
(norm v = 1)%R -> WF_Matrix v->
ceval (QMeas x s' e') mu mu'-> 
sat_State mu ((QExp_s  s  e  v) /\ big_Sand (fun i:nat => (Assn_sub_P x i (P i))) (2^(e'-s'))) ->
sat_Assert mu'  (big_pOplus (fun i:nat=> (@norm (2^(e-s)) ((U_v s' e' s e (∣ i ⟩_ (e'-s') × ⟨ i ∣_ (e'-s')) v))) ^ 2)%R
                               (fun i:nat=> SAnd ((P i))  (QExp_s  s  e ((R1 / ( (@norm (2^(e-s)) ((U_v s' e' s e (∣ i ⟩_ (e'-s') × ⟨ i ∣_ (e'-s')) v)))))%R.* 
                               (U_v  s' e' s e (∣ i ⟩_ (e'-s') × ⟨ i ∣_ (e'-s')) v)))) (2^(e'-s'))).
Proof.  intros s' e' s e v x P n  (mu, IHmu). induction mu; intros; destruct mu' as(mu', IHmu').
        inversion H2; subst. simpl in H6. inversion_clear H6. 
-- simpl in H3.  apply WF_sat_State in H3. simpl in H3. destruct H3. destruct H3. reflexivity.
--destruct mu. inversion_clear H2. simpl in H6.  inversion H6; subst. inversion_clear H13.
apply rule_Meas_aux' with x ((sigma, rho)). assumption. assumption. assumption.
apply E_com. apply WF_state_dstate. inversion_clear H4. assumption.
apply WF_ceval with (<{ x :=M [[s' e']] }>) ([(sigma, rho)]).
apply WF_state_dstate_aux. inversion_clear H4. assumption.
assumption. assumption.  rewrite sat_Assert_to_State. inversion_clear H3.
econstructor. apply WF_state_dstate_aux. inversion_clear H4. assumption. assumption.

inversion_clear H2. simpl in H6.  inversion H6; subst.
assert(Sorted.Sorted (StateMap.Raw.PX.ltk (elt:=qstate n)) (big_app
(fun j : nat =>
 [(c_update x j sigma, QMeas_fun s' e' j rho)])
(2 ^ (e' - s')))). apply big_app_sorted. intros. apply 
Sorted.Sorted_cons. apply 
Sorted.Sorted_nil. apply Sorted.HdRel_nil.
assert(Sorted.Sorted (StateMap.Raw.PX.ltk (elt:=qstate n)) mu'0). 
apply ceval_sorted with (<{ x :=M [[s' e']] }>)
(p::mu). inversion_clear IHmu. assumption. assumption.
apply sat_dapp with H2 H7. rewrite big_pOplus_get_pro.
apply Forall_fun_to_list. intros.  admit.
apply rule_Meas_aux' with x ((sigma, rho)). assumption. assumption.
assumption. apply E_com. apply WF_state_dstate. inversion_clear H4. assumption.
apply WF_ceval with (<{ x :=M [[s' e']] }>) ([(sigma, rho)]).
apply WF_state_dstate_aux. inversion_clear H4. assumption.
apply ceval_eq with ((StateMap.Raw.map2 option_app
(big_app
   (fun j : nat =>
    [(c_update x j sigma, QMeas_fun s' e' j rho)])
   (2 ^ (e' - s'))) [])). simpl. rewrite map2_nil_r. reflexivity.
apply E_Meas. assumption. apply E_nil.
apply ceval_eq with ((StateMap.Raw.map2 option_app
(big_app
   (fun j : nat =>
    [(c_update x j sigma, QMeas_fun s' e' j rho)])
   (2 ^ (e' - s'))) [])). simpl. rewrite map2_nil_r. reflexivity.
apply E_Meas. assumption. apply E_nil.
inversion_clear H3. 
rewrite sat_Assert_to_State. econstructor.
apply WF_state_dstate. inversion_clear H4. assumption.
inversion_clear H9. econstructor. assumption. 
apply Forall_nil. inversion_clear IHmu.
apply IHmu0 with H8. assumption. assumption.
assumption.  apply E_com.  inversion_clear H4.
assumption. 
apply WF_ceval with (<{ x :=M [[s' e']] }>) (p::mu).
inversion_clear H4. assumption. 
assumption. assumption. inversion_clear H3. 
econstructor. inversion_clear H4. assumption.
inversion_clear H11. apply State_eval_dstate_Forall. discriminate.
assumption.  assumption.   
Admitted.

Theorem rule_QMeas : forall s' e' s e (v: Vector (2^(e-s))) x (P :nat-> (Pure_formula)),
s<=s' /\ e'<=e->
(norm v = 1)%R -> WF_Matrix v->
{{ (QExp_s  s  e  v) /\ big_Sand (fun i:nat => (Assn_sub_P x i (P i))) (2^(e'-s')) }}
 QMeas x s' e' 
{{ big_pOplus (fun i:nat=> (@norm (2^(e-s)) ((U_v s' e' s e (∣ i ⟩_ (e'-s') × ⟨ i ∣_ (e'-s')) v))) ^ 2)%R
 (fun i:nat=> SAnd ((P i))  (QExp_s  s  e ((R1 / ( (@norm (2^(e-s)) ((U_v s' e' s e (∣ i ⟩_ (e'-s') × ⟨ i ∣_ (e'-s')) v)))))%R.* 
 (U_v s' e' s e (∣ i ⟩_ (e'-s') × ⟨ i ∣_ (e'-s')) v)))) (2^(e'-s')) }}.
Proof. unfold hoare_triple.
intros. 
rewrite sat_Assert_to_State in *.
apply rule_Meas_aux'' with x mu. assumption.
intuition. intuition. assumption. assumption. 
Qed.


