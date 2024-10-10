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
From Quan Require Import QState_L.
From Quan Require Import QIMP_L.
From Quan Require Import QAssert_L.
From Quan Require Import ParDensityO.
Import Par_trace.


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
(* Lemma Mmult_inject{m n o:nat}: forall (A C:Matrix m n)
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
Admitted. *)


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


     
Lemma PMtrace_Super_swap{s e:nat}: forall l r  (M: Square (2^(r-l))) (A:qstate s e) ,
s<=l /\l<=r /\ r<=e -> WF_Matrix M->
super M (PMpar_trace A  l r)= @PMpar_trace s e (super (I (2 ^ (l-s)) ⊗ M ⊗ I (2 ^ (e-r))) A) l r.
Proof. intros. unfold super. repeat rewrite Ptrace_l_r'.  
       assert((2 ^ (r-l)) = 1 * (2 ^ (r- l)) * 1). lia.
        destruct H1.
       rewrite (Mmult_Msum_distr_l ((2 ^ (l-s))) _ M).
       rewrite Mmult_Msum_distr_r.
       apply big_sum_eq_bounded.  intros.  
       assert((2 ^ (r-l)) = 1 * (2 ^ (r- l)) * 1). lia.
       destruct H2. 
       rewrite Mmult_Msum_distr_l.
       rewrite Mmult_Msum_distr_r.
       apply big_sum_eq_bounded.  intros. 
        rewrite Mmult_assoc_5.   rewrite Mmult_assoc_5.
        f_equal.  f_equal. 
        apply Logic.eq_trans with ((I 1 ⊗ M ⊗ I 1) × (⟨ x ∣_ (l-s) ⊗ I (2 ^ (r- l)) ⊗ ⟨ x0 ∣_ (e-r))).
        rewrite kron_1_l; auto_wf. rewrite kron_1_r. f_equal; try lia. 
        apply Logic.eq_trans with (⟨ x ∣_ (l-s) ⊗ I (2 ^ (r- l)) ⊗ ⟨ x0 ∣_ (e-r)
        × (I (2 ^ (l-s)) ⊗ M ⊗ I (2 ^ (e-r)))).
      repeat rewrite kron_mixed_product. repeat rewrite Mmult_1_l; auto_wf.
      repeat rewrite Mmult_1_r; auto_wf.  f_equal; auto_wf. 
      f_equal; lia. 

      apply Logic.eq_trans with ((∣ x ⟩_ (l-s) ⊗ I (2 ^ (r- l)) ⊗ ∣ x0 ⟩_ (e-r))× (I 1 ⊗ (M) † ⊗ I 1)  ).
        rewrite kron_1_l; auto_wf. rewrite kron_1_r. f_equal; try lia. 
        apply Logic.eq_trans with ((I (2 ^ (l-s)) ⊗ M ⊗ I (2 ^ (e-r))) †
        × (∣ x ⟩_ (l-s) ⊗ I (2 ^ (r- l)) ⊗ ∣ x0 ⟩_ (e-r))). 
        repeat rewrite kron_adjoint. repeat rewrite id_adjoint_eq.
      repeat rewrite kron_mixed_product. repeat rewrite Mmult_1_l; auto_wf.
      repeat rewrite Mmult_1_r; auto_wf.  f_equal; auto_wf. 
      f_equal; lia. intuition. intuition. 
Qed.


Lemma big_sum_par_trace{ s e: nat}: forall n (f:nat-> Square (2^(e-s)) ) l r ,
s<=l/\l<=r/\ r<=e->
PMpar_trace (big_sum f n) l r=
big_sum (fun i :nat =>PMpar_trace (f i) l r ) n .
Proof. induction n; intros; simpl.  
       unfold PMpar_trace. 
       unfold PMLpar_trace.
       rewrite (big_sum_eq  _ ((fun i : nat =>
       Zero ))). rewrite big_sum_0.  simpl.
       unfold PMRpar_trace. 
       rewrite (big_sum_eq  _ ((fun i : nat =>
       Zero ))). rewrite big_sum_0. reflexivity.
       intuition. apply functional_extensionality.
       intros.
       assert(2 ^ (l - s) * 2 ^ (r - l) = 2 ^ (r - s) * 1).
       rewrite mul_1_r.
       type_sovle'. destruct H0.
       rewrite Mmult_0_r. rewrite Mmult_0_l. reflexivity.
        intuition.
       apply functional_extensionality.
       intros. 
       assert(2 ^ (r - s) * 2 ^ (e - r) = 2 ^ (e - s) ).
       type_sovle'. destruct H0.
       rewrite Mmult_0_r. rewrite Mmult_0_l. reflexivity.
      unfold qstate in *.
      rewrite PMtrace_plus.
      rewrite <-IHn. reflexivity. assumption.
Qed.

Lemma Mmult_kron_5: forall {m1 n1 m2 n2 m3 n3 m4 n4 m5 n5:nat} (A: Matrix m1 n1)
(B: Matrix m2 n2) (C: Matrix m3 n3) (D: Matrix m4 n4) (E: Matrix m5 n5), 
WF_Matrix A -> WF_Matrix B -> WF_Matrix C -> WF_Matrix D -> WF_Matrix E->
A ⊗ (B ⊗ C ⊗ D) ⊗ E= (A ⊗ B) ⊗ C ⊗ (D ⊗ E).
Proof. intros. repeat rewrite <-kron_assoc; try reflexivity;
       auto_wf.
Qed.

Lemma PMpar_trace_ceval_swap_Qinit{ s e:nat}: forall (q: qstate s e ) s0 e0 l r,
s<=l/\l<=s0 /\s0<=e0 /\ e0<=r /\ r<=e-> 
@WF_Matrix (2^(e-s)) (2^(e-s)) q -> 
@PMpar_trace  s e (QInit_fun s0 e0 q) l r = QInit_fun s0 e0 (PMpar_trace q l r) .
Proof. intros. unfold QInit_fun. unfold q_update.
       rewrite big_sum_par_trace.
       apply big_sum_eq_bounded. 
       intros. assert(0<(2^(e0 - s0))). lia.  
      rewrite PMtrace_Super_swap. f_equal.
      f_equal; type_sovle'.  
      assert(  2 ^ (s0 - l) * 2 ^ (e0 - s0) * 2 ^ (r - e0)= 2 ^ (r - l)).
      type_sovle'. destruct H3.
      rewrite Mmult_kron_5; auto_wf. 
      repeat rewrite id_kron. f_equal; type_sovle';
      f_equal; type_sovle'; f_equal; type_sovle'.
      lia. auto_wf. lia.   
Qed. 

Lemma PMpar_trace_ceval_swap_QUnit_one{ s e:nat}: forall (q: qstate s e ) s0 e0 
(U:Square (2^(e0-s0))) l r,
s<=l/\l<=s0 /\s0<=e0 /\ e0<=r /\ r<=e-> 
@WF_Matrix (2^(e-s)) (2^(e-s)) q -> 
WF_Unitary U->
@PMpar_trace  s e (QUnit_One_fun s0 e0 U q) l r = QUnit_One_fun s0 e0 U (PMpar_trace q l r) .
Proof. intros. unfold QUnit_One_fun.
       unfold q_update. 
       rewrite PMtrace_Super_swap. 
      f_equal; f_equal; type_sovle'.
      assert( 2 ^ (s0 - l) * 2 ^ (e0 - s0) * 2 ^ (r - e0)= 2 ^ (r - l) ).
      type_sovle'. destruct H2.
      rewrite Mmult_kron_5; auto_wf. 
      repeat rewrite id_kron. f_equal; type_sovle';
      f_equal; type_sovle'; f_equal; type_sovle'.
       apply H1. lia. destruct H1. auto_wf. 
Qed.

Lemma PMpar_trace_ceval_swap_QUnit_Ctrl{ s e:nat}: forall (q: qstate s e ) s0 e0 s1 e1  
(U: nat -> Square (2^(e1-s1))) l r,
s<=l/\l<=s0 /\s0<=e0 /\ e0 <=s1 /\ s1 <= e1 /\ e1<=r /\ r<=e-> 
@WF_Matrix (2^(e-s)) (2^(e-s)) q -> 
(forall j, WF_Unitary (U j ))->
@PMpar_trace  s e (QUnit_Ctrl_fun s0 e0  s1 e1 U q) l r 
= QUnit_Ctrl_fun s0 e0 s1 e1 U (PMpar_trace q l r) .
Proof. intros. unfold QUnit_Ctrl_fun.
       unfold q_update.
      rewrite PMtrace_Super_swap.
      f_equal. f_equal; type_sovle'.
      rewrite kron_Msum_distr_l.
      rewrite kron_Msum_distr_r.
      apply big_sum_eq_bounded.
      intros. 
      remember (I (2 ^ (s0 - l)) ⊗ (∣ x ⟩_ (e0 - s0) × ⟨ x ∣_ (e0 - s0)) ⊗ I (2 ^ (r - e0))).
      remember ( (I (2 ^ (s1 - l)) ⊗ U x ⊗ I (2 ^ (r - e1)))).
      apply Logic.eq_trans with 
      (@kron (2^(l-s)) (2^(l-s)) (2 ^ (s0 - l) * 2 ^ (e0 - s0) * 2 ^ (r - e0))
      (2 ^ (s1 - l) * 2 ^ (e1 - s1) * 2 ^ (r - e1))
      (I (2 ^ (l - s)) × I (2 ^ (l - s)))
       (m × m0)
      ⊗ (I (2 ^ (e - r)) × I (2 ^ (e - r)))).
      repeat rewrite <-kron_mixed_product.
      rewrite Heqm. rewrite Heqm0.
       rewrite Mmult_kron_5; auto_wf.
       repeat rewrite id_kron.  
      f_equal; type_sovle'. f_equal; type_sovle';
      f_equal; type_sovle'. 
      f_equal; type_sovle'. 
      assert(2 ^ (s1 - l) * 2 ^ (e1 - s1) * 2 ^ (r - e1)= 
      2 ^ (s0 - l) * 2 ^ (e0 - s0) * 2 ^ (r - e0)).
      type_sovle'. destruct H3.
      rewrite Mmult_kron_5; auto_wf.
      repeat rewrite id_kron.  
      f_equal; type_sovle'; f_equal; type_sovle'.
      f_equal; type_sovle'.
      apply H1. repeat rewrite Mmult_1_r; auto_wf.
      f_equal; type_sovle'. f_equal; type_sovle'.
      f_equal; type_sovle'. lia. 
      apply WF_Msum.
      intros. assert(WF_Unitary (U i)). auto.
      destruct H3. auto_wf.
Qed.


Lemma PMpar_trace_ceval_swap_QMeas{ s e:nat}: forall (q: qstate s e ) s0 e0 j l r,
s<=l/\l<=s0 /\s0<=e0 /\ e0<=r /\ r<=e-> 
@WF_Matrix (2^(e-s)) (2^(e-s)) q -> 
j<2^(e0-s0)->
@PMpar_trace  s e (QMeas_fun s0 e0 j q) l r = QMeas_fun s0 e0 j (PMpar_trace q l r) .
Proof. intros. unfold QMeas_fun.
       unfold q_update. 
       rewrite PMtrace_Super_swap.
      assert( 2 ^ (s0 - l) * 2 ^ (e0 - s0) * 2 ^ (r - e0)= 2 ^ (r - l) ).
      type_sovle'. destruct H2.
      f_equal. f_equal; type_sovle'.
      rewrite Mmult_kron_5; auto_wf. 
      repeat rewrite id_kron. f_equal; type_sovle';
      f_equal; type_sovle'; f_equal; type_sovle'.
      lia.  auto_wf. 
Qed.


#[export]Hint Unfold PMpar_trace: M_db.

Import Par_trace.

Lemma pure_vector0{s e:nat} : Pure_State_Vector (∣ 0 ⟩_ (e - s)). 
Proof. econstructor. apply WF_vec. apply pow_gt_0.
       apply Vec_inner_1. apply pow_gt_0.
        Qed.

Local Open Scope nat_scope.
Theorem rule_Qinit_aux:  forall  s e (s' e':nat) (st :state s' e') (st': state s' e'),
WF_state st->
ceval_single (QInit s e) [st] [st'] ->
State_eval (QExp_s s e  (Vec (2^(e-s)) 0)) st'.
Proof. 
      intros s e s' e' st st' H'. intros. simpl in *.
      destruct st. destruct st'.
      inversion H; subst.  inversion H7; subst. 
      simpl. injection H6. intros.  
      rewrite <-H0.  rewrite <-PMtrace_scale.
      rewrite PMpar_trace_ceval_swap_Qinit.
      rewrite QInit_trace.
      split. apply pure_vector0 .  
      split. lia. split. lia.   split. lia.
      unfold QInit_fun. remember ((PMpar_trace q s e)).
      rewrite (big_sum_eq_bounded  _   
      (fun i0:nat=> (∣ 0 ⟩_ (e - s) × (⟨ i0 ∣_ (e - s) × q1 
      × (∣ i0 ⟩_ (e - s))) × ⟨ 0 ∣_ (e - s)))).
      rewrite <-(@Mmult_Msum_distr_r (2^(e-s)) 1 (2^(e-s))).
      rewrite <-(@Mmult_Msum_distr_l 1 1 (2^(e-s))).
      rewrite trace_base. rewrite Mscale_mult_dist_r.
      rewrite Mmult_1_r. rewrite Rdiv_unfold.
      rewrite Rmult_1_l.  rewrite Heqq1.
      rewrite Ptrace_trace. rewrite Mscale_mult_dist_l.
      rewrite Mscale_assoc.  unfold RtoC. 
      assert(@trace (2^(e'-s')) q= (fst (@trace (2^(e'-s')) q), snd (@trace (2^(e'-s')) q))).
      destruct (trace q). 
      reflexivity. rewrite H2.  rewrite mixed_state_trace_real.
      unfold Cmult. simpl. repeat  rewrite Rmult_0_l. rewrite Rmult_0_r.
      rewrite Rplus_0_l. rewrite Rminus_0_r. 
      rewrite Cmod_snd_0. simpl. rewrite Rinv_l.
      rewrite Mscale_1_l. unfold outer_product. reflexivity.
      assert((0 < fst (@trace (2^(e'-s')) q))%R). 
      apply mixed_state_trace_gt0. apply H'.  lra.
      apply mixed_state_trace_gt0. apply H'. simpl. reflexivity.
      apply H'. lia.  apply WF_Mixed. apply H'.
      apply WF_vec. apply pow_gt_0.  rewrite Heqq1.
      apply WF_Mixed. apply Mix_par_trace. lia.  apply H'. 
      intros. repeat rewrite Nat.sub_diag. rewrite kron_1_l. 
      rewrite kron_1_r. 
      unfold q_update. unfold super. rewrite Mmult_adjoint.
      rewrite adjoint_involutive. rewrite Mmult_assoc_5.
      reflexivity. assert(0<2^(e-s)). lia. auto_wf. 
      lia. apply WF_Mixed. apply H'. lia.  
      apply WF_Mixed. apply H'.
Qed.

Require Import ParDensityO.



Lemma ceval_eq{s e:nat}: forall (mu mu' mu1:list (cstate * qstate s e)) c,
mu1=mu'->
ceval_single c mu mu'->
ceval_single c mu mu1.
Proof. intros. rewrite H. assumption.
Qed.


 Theorem rule_Qinit_aux' :  forall 
(s e s' e' :nat) (mu : list (cstate * qstate s' e')) (mu': list (cstate * qstate s' e')),
WF_dstate_aux mu->
ceval_single (QInit s e) mu mu' ->
State_eval_dstate (BTrue) mu->
State_eval_dstate ((QExp_s s e  (Vec (2^(e-s)) 0))) mu'.
Proof. intros s e s' e' mu. induction mu; intros. inversion H0; subst.
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
       assert([(c, QInit_fun s e q)]= (StateMap.Raw.map2 (@option_app s' e') ([(c, QInit_fun s e q)])  ([]))).
       reflexivity.   rewrite H2. apply E_Qinit. assumption.  apply E_nil.

      apply WF_ceval with (QInit s e) ((p :: mu)).
      inversion_clear H. assumption. assumption.

      econstructor. apply rule_Qinit_aux with ((c, q)). 
      inversion_clear H. assumption.
      apply ceval_eq with ((StateMap.Raw.map2 (@option_app s' e') ([(c, QInit_fun s e q)])  ([]))).
      reflexivity. apply E_Qinit. assumption.  apply E_nil.
      apply Forall_nil.

      apply IHmu. inversion_clear H.  assumption. 
      intuition. inversion_clear H1.  apply State_eval_dstate_Forall.
      discriminate.  assumption.
Qed.   

Local Open Scope com_scope.
Definition hoare_triple
   (P:Assertion) (c : com) (Q : Assertion) : Prop :=
            forall (s e :nat)  (mu : dstate s e) (mu': dstate s e),
               ceval c mu mu' ->
               sat_Assert  mu P ->
               sat_Assert  mu' Q.
Declare Scope rule_scope.
Notation "{{ P }}  c  {{ Q }}" :=
(hoare_triple P c Q) (at level 90, c custom com at level 99)
               : rule_scope.

Local Open Scope rule_scope.
(* Theorem rule_QInit: forall s e,
{{BTrue}} ( s e ) :Q= 0
{{(QExp_s s e  (Vec (2^(e-s)) 0))}}.
Proof. 
unfold hoare_triple.
intros s e s' e' (mu,IHmu) (mu', IHmu').
intros. 
inversion_clear H; simpl in H3.
rewrite sat_Assert_to_State in *.
inversion_clear H0.
apply sat_F. apply H2. intuition.
apply rule_Qinit_aux' with  mu.
intuition. intuition. assumption. 
Qed. *)



 (* Lemma Mmult_trans'{n}: forall (A B C D: Square n) ,
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
  intuition. intuition. Qed. *)

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

Lemma Unitary_I{n:nat}: forall (U:Square n),
WF_Unitary U -> (U) † × U = I n .
Proof. intros. destruct H. assumption.
  
Qed.


Local Open Scope assert_scope.
Local Open Scope nat_scope.

Lemma U_v_inv{s' e' s e}: forall (U: Square (2 ^ (e' - s'))) (v: Vector (2 ^ (e - s))),
s<=s' /\s' <=e' /\ e' <=e ->WF_Unitary U->
WF_Matrix v->
U_v s' e' s e U (U_v s' e' s e (U) † v) = v.
Proof. intros. unfold U_v. 
       rewrite <-Mmult_assoc.
       assert(2 ^ (s' - s) * 2 ^ (e' - s') * 2 ^ (e - e')= 2 ^ (e - s)).
      type_sovle'. destruct H2.
      repeat  rewrite kron_mixed_product.
      Msimpl. 
      apply transpose_unitary in H0.
      destruct H0.
      rewrite adjoint_involutive in H2.
      rewrite H2. 
      rewrite id_kron.
      rewrite id_kron.
      Msimpl. reflexivity.
Qed.


Theorem rule_QUnit_aux:  forall s' e' s e (U: Square (2^(e'-s'))) (v: Vector (2^(e-s)))
(s0 e0:nat) (st :state s0 e0) (st': state s0 e0),
s<=s' /\ e' <=e ->
WF_state st->(WF_Matrix v )->
ceval_single (QUnit_One s' e' U) [st] [st'] ->
State_eval (QExp_s s  e  (U_v s' e' s e U† v) ) st->
State_eval (QExp_s s  e  v ) st'.
Proof. intros. simpl in *. destruct H3. destruct H4.
       destruct st.  
      inversion H2; subst. inversion H15; subst.
      clear H15. apply inj_pair2_eq_dec in H8.
      apply inj_pair2_eq_dec in H8. subst.
      injection H13. intros.
      split. rewrite <-(U_v_inv  U); try lia; try assumption. 
      apply pure_state_vector_unitary_pres.
      assumption.
      assert(2 ^ (s' - s) * 2 ^ (e' - s') * 2 ^ (e - e')= 2 ^ (e - s)).
      type_sovle'. destruct H7.
      repeat apply kron_unitary; auto; try apply id_unitary. 
      split. intuition. split. intuition. split. intuition. 
      rewrite <-H6.
      simpl in *. rewrite <-PMtrace_scale in *.
      rewrite QUnit_One_trace. 
      rewrite PMpar_trace_ceval_swap_QUnit_one.
      rewrite QUnit_One_fun_scale.
      destruct H5. destruct  H7. 
      rewrite H8. unfold U_v. 
      unfold outer_product.
      unfold QUnit_One_fun.
      unfold q_update. unfold super.
      repeat rewrite Mmult_adjoint.
      assert(2 ^ (s' - s) * 2 ^ (e' - s') * 2 ^ (e - e')= 2 ^ (e - s)).
      type_sovle'. destruct H9.
      repeat rewrite kron_adjoint.
      repeat rewrite id_adjoint_eq.
      rewrite<-(Mmult_assoc _ (v) †) .
      rewrite (Mmult_assoc _ v ).
      rewrite Mmult_assoc_5. rewrite adjoint_involutive.
      assert((I (2 ^ (s' - s)) ⊗ (U) ⊗ I (2 ^ (e - e')))=
      ((I (2 ^ (s' - s)) ⊗ ((U) †) ⊗ I (2 ^ (e - e'))))†).
      repeat rewrite kron_adjoint. 
      repeat rewrite id_adjoint_eq. rewrite adjoint_involutive.  reflexivity.
      rewrite H9. rewrite Unitary_I.
      repeat rewrite Mmult_1_l; auto_wf.
      repeat rewrite Mmult_1_r; auto_wf.
      reflexivity.  apply kron_unitary.
      apply kron_unitary. apply id_unitary.
      apply transpose_unitary. assumption.
      apply id_unitary. lia. lia. apply WF_Mixed. apply H0. assumption.
      lia.   apply WF_Mixed. apply H0. assumption.
        apply Nat.eq_dec. apply Nat.eq_dec.
Qed.

Theorem rule_QUnit_One_aux' : forall s' e' s e (U: Square (2^(e'-s'))) (v: Vector (2^(e-s)))
(s0 e0:nat) (mu : list (cstate * qstate s0 e0)) (mu': list (cstate * qstate s0 e0)),
s<=s' /\ e' <=e ->
WF_dstate_aux mu->WF_Matrix v->
ceval_single (QUnit_One s' e' U) mu mu' ->
State_eval_dstate (QExp_s s  e  (U_v s' e' s e U† v) ) mu->
State_eval_dstate (QExp_s s  e  v ) mu'.
Proof. intros s' e' s e U v s0 e0 mu. induction mu; intros. inversion H2; subst.
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
       apply ceval_eq with ((StateMap.Raw.map2 (@option_app s0 e0) ([(c, QUnit_One_fun s' e' U1 q)])  ([]))).
       reflexivity.  apply E_Qunit_One. assumption. assumption.  apply E_nil.

      apply WF_ceval with (QUnit_One s' e' U1) ((p :: mu)).
      inversion_clear H0. assumption. assumption.

      econstructor.  apply rule_QUnit_aux with s' e' U1 ((c, q)). intuition. 
      inversion_clear H0. assumption. assumption. 
      apply ceval_eq with ((StateMap.Raw.map2 (@option_app s0 e0) ([(c, QUnit_One_fun s' e' U1 q)])  ([]))).
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
intros s' e' s e U v Hs Hv s0 e0 (mu,IHmu) (mu', IHmu').
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
Lemma PMtrace_Meas{s0 e0:nat}: forall s' e' s e z (v:Vector (2^(e-s))) (q:Square (2^(e0-s0))),
WF_qstate q->
s0<=s/\s<=s'/\ s' <= e'/\ e'<=e /\ e<=e0-> (z< 2^(e'-s')) ->WF_Matrix v->
(R1 / Cmod (trace q))%R .* PMpar_trace q s e = outer_product v v->
(norm (@U_v (e'-s') (e-s) s' e' s e (∣ z ⟩_ (e' - s') × ⟨ z ∣_ (e' - s')) v) *
norm (@U_v (e'-s') (e-s) s' e' s e (∣ z ⟩_ (e' - s') × ⟨ z ∣_ (e' - s')) v))%R * (trace q) = 
@trace (2^(e0-s0)) (QMeas_fun  s' e' z q).
Proof. intros s' e' s e z v q Uq. intros. 
rewrite <-(Ptrace_trace _ _ _ s e).
rewrite <-(Ptrace_trace _ _ ((QMeas_fun s' e' z q)) s e).
rewrite PMpar_trace_ceval_swap_QMeas.
assert(PMpar_trace q s e = (Cmod (trace q)).*  (outer_product v v)).
rewrite<-H2. rewrite Rdiv_unfold. rewrite Rmult_1_l.
rewrite Mscale_assoc. rewrite RtoC_mult.
 rewrite Rinv_r. rewrite Mscale_1_l. reflexivity.
 assert(Cmod (trace q) > 0%R)%R. apply mixed_state_Cmod_1.
 apply Uq. lra. rewrite H3. rewrite <-QMeas_fun_scale.
repeat rewrite trace_mult_dist.
rewrite Cmult_comm. rewrite <-Cmult_assoc.
 f_equal. unfold QMeas_fun. 
 assert(trace (outer_product v v)= C1).
 rewrite <-H2. rewrite trace_mult_dist.
  rewrite Ptrace_trace. rewrite Rdiv_unfold.
  rewrite Rmult_1_l. 
  assert(trace q= (fst (trace q), snd (trace q))).
  destruct (trace q). reflexivity.
  rewrite H4. rewrite Cmod_snd_0. 
  rewrite mixed_state_trace_real.
  simpl. unfold Cmult. simpl. 
  repeat rewrite Rmult_0_l. rewrite Rmult_0_r.
  rewrite Rplus_0_r. rewrite Rminus_0_r.
  rewrite Rinv_l. reflexivity.
  assert(fst (trace q) > 0%R)%R.
  apply mixed_state_trace_gt0. apply Uq.
  lra. apply Uq. simpl. 
  apply mixed_state_trace_gt0. apply Uq.
  simpl. rewrite mixed_state_trace_real.
  reflexivity. apply Uq. simpl.
  lia. apply WF_Mixed. apply Uq. rewrite H4.
  rewrite Cmult_1_l.
    
rewrite inner_trace. unfold U_v.
  unfold q_update. unfold super.
  unfold outer_product. 
  repeat rewrite Mmult_adjoint.
  assert(2 ^ (s' - s) * 2 ^ (e' - s') * 2 ^ (e - e')= 2 ^ (e - s))%nat.
type_sovle'.  destruct H5.
  repeat rewrite kron_adjoint.
  repeat rewrite id_adjoint_eq.
  rewrite <-Mmult_assoc. rewrite (Mmult_assoc _ v).
  rewrite Mmult_adjoint. rewrite adjoint_involutive.
  remember ((I (2 ^ (s' - s))
  ⊗ (∣ z ⟩_ (e' - s') × ⟨ z ∣_ (e' - s'))
  ⊗ I (2 ^ (e - e')) × (v × (v) †)
  × (I (2 ^ (s' - s))
     ⊗ (∣ z ⟩_ (e' - s') × ⟨ z ∣_ (e' - s'))
     ⊗ I (2 ^ (e - e'))))).
  assert(m=Zero \/ m<>Zero). 
  apply Classical_Prop.classic.
  destruct H5. rewrite H5. rewrite Zero_trace.
  reflexivity. 
assert(@trace ((2 ^ (s' - s) * 2 ^ (e' - s') *
2 ^ (e - e'))) m=
(fst (@trace ((2 ^ (s' - s) * 2 ^ (e' - s') *
2 ^ (e - e'))) m), snd (@trace ((2 ^ (s' - s) * 2 ^ (e' - s') *
2 ^ (e - e'))) m))). 
destruct (trace m). reflexivity. rewrite H6. 
rewrite mixed_state_trace_real_aux. simpl. reflexivity.
assert(super (I (2 ^ (s' - s))
⊗ (∣ z ⟩_ (e' - s') × ⟨ z ∣_ (e' - s'))
⊗ I (2 ^ (e - e')))  ((v × (v) †)) = m).
rewrite Heqm. unfold super.
repeat rewrite kron_adjoint. 
rewrite Mmult_adjoint. repeat rewrite id_adjoint_eq.
 rewrite adjoint_involutive. reflexivity.
 rewrite <-H7. 
  apply mixed_super_aux. auto_wf.
  apply Vector_Mix_State. assumption. 
 intro. rewrite H8 in *. unfold outer_product  in *.
 rewrite Mmult_0_l in *. rewrite Zero_trace in *.
 injection H4. lra.  rewrite H7. assumption.
   apply WF_U_v. lia. auto_wf. auto_wf.
   lia. lia. apply WF_Mixed. apply Uq.
   assumption. lia. unfold QMeas_fun. 
   unfold q_update. apply WF_super.
   auto_wf. apply WF_Mixed. apply Uq.
   lia.     apply WF_Mixed. apply Uq.
Qed. 

Lemma QMeas_not_Zero_trace{s0 e0:nat}: forall s' e' z (q:Square (2^(e0-s0)))(c:cstate ),
WF_qstate q->
s0<=s'/\ s' <= e'/\ e'<=e0-> 
(z< 2^(e'-s')) ->
(QMeas_fun  s' e' z q)<> Zero ->
@trace (2^(e0-s0)) (QMeas_fun  s' e' z q) <> C0.
Proof. intros. 
       assert( WF_qstate (QMeas_fun s' e' z q) ).
       apply WF_qstate_QMeas; try assumption.
      apply WF_qstate_not_0 in H3.
      apply C0_fst_neq. assumption.
Qed.
       

Lemma QMeas_not_Zero{s0 e0:nat}: forall s' e' s e z (v:Vector (2^(e-s))) (q:Square (2^(e0-s0))) (c:cstate),
WF_qstate q->
s0<=s/\s<=s'/\ s' <= e'/\ e'<=e /\ e<=e0-> 
(z< 2^(e'-s')) ->WF_Matrix v->
(R1 / Cmod (trace q))%R .* PMpar_trace q s e = outer_product v v->
(QMeas_fun  s' e' z q) <> Zero ->
(norm (@U_v (e'-s') (e-s) s' e' s e (∣ z ⟩_ (e' - s') × ⟨ z ∣_ (e' - s')) v)) <> 0%R.
Proof. intros. 
       assert( @trace (2^(e0-s0)) (QMeas_fun  s' e' z q) <> C0).
       apply QMeas_not_Zero_trace; try assumption. lia. 
       rewrite <-(PMtrace_Meas _ _  s e _ v) in H5; try assumption.
       intro. rewrite H6 in H5.
        rewrite Rmult_0_l in H5. rewrite Cmult_0_l in H5.
        destruct H5. reflexivity.
Qed.




Lemma Rinv_l': forall (r1 r2:R),
(r2<>0)%R->
r1=r2-> (/r1 * r2 = 1)%R.
Proof. intros. rewrite H0. apply Rinv_l. assumption.   
Qed.


(* Lemma WF_QMeas{s' e':nat}:  forall (s e i j:nat) (sigma: cstate)  (rho: qstate s' e'),
s'<=s/\s<=e/\ e<=e'->
j<(2^(e-s)) ->WF_qstate rho->
(QMeas_fun s e j rho) <> Zero ->
@WF_qstate s' e' ((QMeas_fun s e j rho)).
Proof. intros. unfold QMeas_fun. econstructor.  apply Mixed_State_aux_to_Mix_State. 
 split. unfold q_update. apply mixed_super_aux. 
 auto_wf. apply Mixed_State_aux_to_Mix_State. apply H1.
 unfold QMeas_fun in *. unfold q_update in *.
 assumption.
 apply Rle_trans with (@d_trace_aux s' e' ((big_app (fun j:nat=> 
 [((c_update i j sigma), (QMeas_fun s e j rho)) ]) 
 (2^(e-s))))).
 rewrite big_app_trace. 
 unfold QMeas_fun. simpl.  

 simpl.
 
 unfold q_update. unfold super.
 rewrite trace_mult'.
 assert(2 ^ (s - s') * 2 ^ (e - s) * 2 ^ (e' - e)= 2 ^ (e' - s'))%nat.
 type_sovle'. destruct H3.
 repeat rewrite kron_adjoint. repeat rewrite id_adjoint_eq.
 rewrite <-Mmult_assoc.
 repeat rewrite kron_mixed_product. repeat rewrite Mmult_1_r.
 rewrite Mmult_adjoint. rewrite  adjoint_involutive.
 rewrite <-Mmult_assoc. rewrite (Mmult_assoc _  (⟨ j ∣_ (e - s))).
 rewrite (Vec_inner_1). rewrite Mmult_1_r.
 rewrite trace_


Proof.
  
Qed. *)

Theorem rule_asgn_aux :  forall (P:Pure_formula) (i:nat) ( a:aexp) 
(s e:nat) (mu : list (cstate * qstate s e)) (mu': list (cstate * qstate s e)),
WF_dstate_aux mu->
ceval_single (<{i := a}>) mu mu' ->
State_eval_dstate (Assn_sub_P i a P) mu->
State_eval_dstate P mu'.
Proof. intros P i a s e mu. induction mu; intros; inversion H; subst.
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

Local Open Scope C_scope.
Theorem rule_Meas_aux:  forall s' e' s e (v: Vector (2^(e-s))) z x
(s0 e0:nat) (st :state s0 e0) (st': state s0 e0) (P:nat-> Pure_formula),
(norm (U_v s' e' s e (∣ z ⟩_ (e' - s') × ⟨ z ∣_ (e' - s')) v)<> 0%R) ->
s0 <= s /\ s <= s' /\ s' <= e' /\ e' <= e <= e0-> 
WF_state st-> (z< 2^(e'-s'))->
(State_eval ((QExp_s  s  e  v ) /\ (big_Sand (fun i:nat => (Assn_sub_P x i (P i))) (2^(e'-s')))) st ) ->
State_eval ( (P z) /\  (QExp_s  s  e  ((/ (@norm (2^(e-s)) ((U_v s' e' s e (∣ z ⟩_ (e'-s') × ⟨ z ∣_ (e'-s')) v))))%R .* 
                                                (U_v s' e' s e (∣ z ⟩_ (e'-s') × ⟨ z ∣_ (e'-s')) v)))) 
                          (s_scale (( / ((@norm (2^(e-s)) ((U_v s' e' s e  (∣ z ⟩_ (e'-s') × ⟨ z ∣_ (e'-s')) v)))%R ^ 2))) 
                                                    (c_update x z (fst st), QMeas_fun s' e' z (snd st))).
Proof. 
      intros s' e' s e v z x s0 e0 st st'. intros.
      remember (( norm (U_v s' e' s e (∣ z ⟩_ (e' - s') × ⟨ z ∣_ (e' - s')) v))%R). 
      destruct H3. destruct H3.  
      split.  unfold s_scale. simpl. 
      assert(State_eval_dstate (P z)  [(c_update x z (fst st),(snd st))]).
      apply rule_asgn_aux with x (ANum z) [st]. 
      apply WF_state_dstate_aux. assumption.
      assert([(c_update x z (fst st), snd st)]= StateMap.Raw.map2 option_app ([(c_update x z (fst st), snd st)])  ([])).
      reflexivity. rewrite H6. assert(z= aeval st (ANum z)). 
      simpl. reflexivity. remember ((ANum z) ). destruct st.
      rewrite H7.  apply E_Asgn. apply E_nil.
      econstructor. admit. apply Forall_nil.     
      simpl in *.  inversion_clear H6. 
      apply state_eq_Pure with ((c_update x z (fst st), snd st)).
      simpl. reflexivity. apply H7. 
      split. admit.   
      split. intuition. split. intuition.
      split. intuition. 
      destruct st. destruct st'.  simpl in *. rewrite Mscale_assoc.
      rewrite Cmult_comm. rewrite Rmult_1_r.
      rewrite <-PMtrace_scale in *.  rewrite <-Mscale_assoc.
      remember ((R1 / Cmod (trace q))%R).
      remember ((R1 / Cmod (trace ((/ (r * r))%R .* QMeas_fun s' e' z q)))%R).
      rewrite PMpar_trace_ceval_swap_QMeas; try assumption; try lia. 
      rewrite  QMeas_fun_scale; try lia; auto_wf .
      assert(r1=r0). 
      rewrite Heqr1. rewrite Heqr0. f_equal. f_equal.
      rewrite trace_mult_dist. rewrite Heqr.
      rewrite <-(PMtrace_Meas _ _ s e _ v); try assumption; try lia. 
      rewrite Cmult_assoc. rewrite RtoC_mult.
      rewrite Rinv_l.   apply Cmult_1_l.
      apply Rmult_integral_contrapositive_currified; try rewrite <-Heqr; try assumption.
      apply H3.  rewrite <-Heqr0. apply H5. rewrite H6.
      destruct H5. destruct H7. destruct H8.
      rewrite H9.   unfold U_v. unfold outer_product. 
      assert(((2 ^ (s' - s) * 2 ^ (e' - s') *
      2 ^ (e - e')))=2^((e0-s0)-(e0-e)-(s-s0)))%nat. type_sovle'. destruct H9.
      rewrite Mscale_mult_dist_l. rewrite Mscale_adj.
      rewrite Mscale_mult_dist_r. repeat rewrite <-Mscale_mult_dist_l.
      rewrite Mscale_assoc. rewrite Cconj_R. rewrite RtoC_mult.
      repeat rewrite Mscale_mult_dist_l. f_equal. admit.
       unfold QMeas_fun.  unfold q_update. unfold super.
       assert(2 ^ (s' - s) * 2 ^ (e' - s') * 2 ^ (e - e')= 2 ^ (e - s))%nat.
      type_sovle'. destruct H9.
      repeat rewrite Mmult_adjoint. repeat rewrite kron_adjoint. 
      repeat rewrite id_adjoint_eq. repeat rewrite adjoint_involutive.
      repeat  rewrite Mmult_assoc. reflexivity.
      apply WF_Mixed. apply H1.
Admitted.





Lemma State_eval_conj: forall s e (mu:list (cstate * qstate s e)) (F1 F2:State_formula),
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
  

  Fixpoint big_map2{s e:nat} (p_n :list R) (mu_n: list (list (cstate *qstate s e))) : list (cstate *qstate s e) :=
           match p_n ,mu_n with 
            |[], [] => []
            |[], _ => []
            | _ ,[]=> []
            | hg::tg, hf:: tf =>StateMap.Raw.map2 (option_app) 
                                (StateMap.Raw.map (fun i => hg.* i) hf) (big_map2 tg tf)
             end.



  

  Lemma dstate_to_list_length{s e:nat}: forall (mu1 mu2: list (dstate s e)),
  dstate_to_list (mu1++ mu2) = dstate_to_list mu1 ++ (dstate_to_list mu2) .
  Proof. induction mu1; simpl. intuition.
         intros. f_equal. intuition.
  Qed.
  
  
  Lemma fun_dstate_to_list {s e:nat}: forall n_0 (f: nat-> dstate s e),
  dstate_to_list (fun_to_list f  n_0)=
  fun_to_list (fun i:nat => StateMap.this (f i)) n_0  .
  Proof. induction n_0. intros. simpl. reflexivity.
         intros. simpl.  rewrite dstate_to_list_length. 
         rewrite IHn_0. simpl.  reflexivity.
  Qed.

Require Import Forall_two.
  Lemma Forall_two_app{A B:Type}:forall (P:A-> B-> Prop)  (f1: list A) (g1: list B )  (f2: list A) 
  (g2: list B) ,
  (Forall_two P f1 g1)->
  (Forall_two P f2 g2)->
  (Forall_two P (f1++f2) (g1++g2)).
  Proof.  induction f1; destruct g1; simpl; intros; inversion_clear H.
          assumption. 
          econstructor. assumption.
          apply IHf1. intuition. intuition.
Qed.
  

Local Open Scope nat_scope.




Lemma Forall_two_forall{A B:Type}:forall n (P: A-> B-> Prop) (f:nat-> A) (g:nat-> B),
(forall j,  (j< n)-> P (f j) (g j)) ->
(Forall_two (fun i j=> P i j) (fun_to_list f n) (fun_to_list g n)).
Proof.
induction n. intros. simpl. econstructor. 
intros. simpl. apply Forall_two_app.
 apply IHn. intros. apply H. lia.
 simpl.
 econstructor. apply H. lia. econstructor.
Qed.


             (* Lemma big_dapp_this'{s e:nat}:
             forall  (p_n:list R)  (mu_n:list (dstate s e)),
             StateMap.this (big_dapp p_n mu_n) =
              big_map2 p_n (dstate_to_list mu_n).
             Proof.  induction p_n; destruct mu_n; simpl;
             unfold StateMap.Raw.empty; try reflexivity.
             f_equal. apply IHp_n. 
             Qed.

Lemma big_dapp'_this{s e:nat}:
forall  (p_n:list R)  (mu_n:list (dstate s e)) mu,
(big_dapp p_n mu_n mu)
StateMap.this this=
big_map2 p_n (dstate_to_list mu_n).
Proof.  induction p_n; destruct mu_n; simpl;
unfold StateMap.Raw.empty; try reflexivity.
f_equal. apply IHp_n. 
Qed. *)


Lemma  Forall_fun_to_list{G:Type}: forall (f: G-> Prop) (g:nat->G) n0,
(forall i, i< n0 -> f (g i))->
Forall f (fun_to_list g n0)  .
Proof. induction n0; intros. simpl. apply Forall_nil.
 simpl. rewrite Forall_app. split. apply IHn0. intros.
 apply H. lia. econstructor. apply H. lia. apply Forall_nil.
  
Qed.


Lemma  big_map2_app{s e:nat}: forall (f1 : list R) (g1: list( (list (cstate * qstate s e)))) ( f2: list R) (g2: list( (list (cstate * qstate s e)))),
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


Lemma  big_app_map2{s e:nat}: forall (f1: nat-> R) (f2: nat->  (list (cstate * qstate s e))) n0,
big_map2 (fun_to_list f1 n0) (fun_to_list f2 n0) = 
big_app (fun x => StateMap.Raw.map (fun q=> (f1 x)  .* q) (f2 x)) n0 .
Proof. induction n0; intros. simpl. reflexivity.
simpl. rewrite <-IHn0. rewrite big_map2_app. 
f_equal. simpl. rewrite map2_nil_r. reflexivity.
repeat rewrite fun_to_list_length. reflexivity.
reflexivity.
Qed.

Lemma  big_app_map2'{s e:nat}: forall n0 (f1: nat-> R) (f2: nat-> ((cstate * qstate s e)))  mu mu',
(forall i, snd (f2 i) = Zero -> f1 i =0%R) ->
big_map2' (fun_to_list f1 n0) (fun_to_list (fun i=> [f2 i]) n0) mu ->
big_app' (fun x =>s_scale  (f1 x) (f2 x)) n0 mu'->
mu= mu'.
Proof.  induction n0; intros. inversion_clear H0; inversion_clear H1. 
 reflexivity. 
 simpl in H0.
 apply big_map2_app' in H0. 
 destruct H0. destruct H0. destruct H0.
 destruct H0.  
 
 inversion_clear H1.
simpl in H4.
destruct (Req_dec (f1 n0) 0).
rewrite H1 in *. inversion H3; subst.
inversion H11; subst. inversion_clear H12.
simpl. rewrite map2_nil_r. apply IHn0 with f1 f2; try assumption.
lra. assert(snd (f2 n0) = Zero).
apply (scale_Zero (f1 n0) (snd (f2 n0)) H4). 
apply C0_fst_neq.  assumption. apply H in H6.
rewrite H6 in *. lra. rewrite H2.
f_equal.  apply IHn0 with f1 f2; try assumption.
inversion_clear H3.  inversion_clear H6.
rewrite map2_nil_r. inversion H1; subst.
rewrite<-H6 in *. simpl in *. rewrite Mscale_0_l in *.
destruct H4. reflexivity. unfold s_scale.
destruct (f2 n0). simpl. reflexivity.
repeat rewrite fun_to_list_length. reflexivity.
reflexivity.
Qed.


Local Open Scope com_scope.

Lemma ceval_single_1{s e:nat}: forall (mu mu':list (state s e)) X a,
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
       intros F X a s e (mu,IHmu) (mu', IHmu').
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


Lemma  big_app_eq_bound{s e:nat}: forall (f1 f2: nat-> list (cstate *qstate s e)) n0,
(forall i, (i<n0)%nat -> f1 i = f2 i) -> big_app f1 n0 = big_app f2 n0.
Proof. intros. induction n0; intros. simpl. reflexivity.
    simpl. f_equal. apply IHn0. intros. apply H. lia. 
    apply H. lia.
  
Qed.


Lemma  big_app_eq_bound'{s e:nat}: forall (f1 f2: nat->  (cstate *qstate s e)) n0 mu1 mu2,
big_app' f1 n0 mu1->
big_app' f2 n0 mu2->
(forall i, (i<n0)%nat -> f1 i = f2 i) -> mu1 =mu2.
Proof.  induction n0; intros; inversion_clear H; inversion_clear H0. 
       simpl. reflexivity.
       apply IHn0; try assumption. intros. apply H1. lia.
       rewrite H1 in H2 . rewrite H2 in H. destruct H. reflexivity.
       lia. 
       rewrite <-H1 in H. rewrite H in H2. destruct H2. reflexivity.
       lia. 
       
      f_equal. apply IHn0; try assumption. intros. apply H1. lia.
      f_equal. 
    apply H1. lia.
Qed.
  

Lemma  C_n0t_C0:  forall c:C, (fst c <> 0)%R->
(c<> C0)%C.
Proof. intros. unfold not. intros. destruct c. injection H0.
     intros.  rewrite H1 in H. simpl in H. lra.
  
Qed.



Lemma big_add_emit_0{s e:nat}: forall n (p_n:nat-> R) (F_n:nat-> State_formula) (mu_n:nat-> (dstate s e)) pF mu,
(forall i : nat, i< n-> p_n i <> 0%R -> sat_State (mu_n i) (F_n i))->
emit_0 (fun_to_list p_n n) (fun_to_list F_n n) pF->
emit_0 (fun_to_list p_n n) (fun_to_list mu_n n) mu->
(Forall_two (fun i j => sat_State i j) mu pF).
Proof. induction n; intros. inversion_clear H0.
       inversion_clear H1. econstructor.
       simpl in H0. simpl in H1.
       pose (emit_0_exsist (fun_to_list p_n n) (fun_to_list F_n n)).
       pose (emit_0_exsist [p_n n] [F_n n]).
       destruct e0; destruct e1;
       repeat rewrite fun_to_list_length; try reflexivity.
       assert(pF = x ++ x0).
       eapply emit_0_app; [apply H2| apply H3 | apply H0].
       pose (emit_0_exsist (fun_to_list p_n n) (fun_to_list mu_n n)).
       pose (emit_0_exsist [p_n n] [mu_n n]).
       destruct e0; destruct e1;
       repeat rewrite fun_to_list_length; try reflexivity.
       assert(mu = x1 ++ x2).
       eapply emit_0_app; [apply H5| apply H6 | apply H1].
       rewrite H4. rewrite H7.
       apply Forall_two_app. apply IHn with p_n F_n mu_n; try assumption.
       intros. apply H. lia. assumption.
       inversion_clear H3;
       inversion_clear H6;
       inversion_clear H9; inversion_clear H10.
       econstructor.
       lra. lra.
       econstructor. apply H. lia. assumption. 
       econstructor.
Qed.




Lemma big_pOplus'_sat{s e:nat}: forall n (p_n:nat-> R) (F_n:nat-> State_formula) (mu_n:nat-> (dstate s e)) pF mu,
big_pOplus' p_n F_n n pF->
big_dapp' (fun_to_list p_n n) (fun_to_list mu_n n) mu->
(forall i, i<n -> ((p_n i)<> 0)%R -> sat_State (mu_n i) (F_n i)) ->
(forall i, i<n -> ((p_n i)<> 0)%R -> d_trace (mu_n i) = d_trace mu)->
sat_Pro mu pF.
Proof. intros. 
       pose (emit_0_exsist (fun_to_list p_n n) (fun_to_list p_n n)).
       pose (emit_0_exsist (fun_to_list p_n n) (fun_to_list F_n n)).
       pose (emit_0_exsist (fun_to_list p_n n) (fun_to_list mu_n n)).
       destruct e0. 
       repeat rewrite fun_to_list_length; reflexivity.
       destruct e1.
       repeat rewrite fun_to_list_length; reflexivity.
       destruct e2.
       repeat rewrite fun_to_list_length; reflexivity.
       pose (big_dapp_emit_0 (fun_to_list p_n n) (fun_to_list mu_n n) mu x x1).
       destruct e0; try assumption.  destruct H6.
       econstructor. 
       rewrite (big_pOplus'_get_pro  p_n F_n  n _ x); try assumption.
       apply H7. apply H6.
       rewrite (big_pOplus_get_npro'  p_n F_n  n _ x0); try assumption.
       apply big_add_emit_0 with n p_n F_n mu_n; try assumption.
       eapply emit_0_dtrace. intros. apply H2.
       apply H8. apply H9.
       apply H5.
Qed.


       

       
Lemma  big_sum_mult_l_R: forall r (f:nat-> R) n,
(r * big_sum f n)%R = (big_sum (fun i=> (r * (f i)))%R n) .
Proof. induction n; intros. simpl. rewrite Rmult_0_r.
       reflexivity.
       simpl. rewrite Rmult_plus_distr_l.
       rewrite IHn. reflexivity.
Qed.





Local Open Scope nat_scope.
Theorem rule_Meas_aux':forall s' e' s e (v: Vector (2^(e-s))) x (P :nat-> (Pure_formula))
(s0 e0:nat) (st :state s0 e0) (mu: dstate s0 e0) pF,
s <= s' /\ s' <= e' /\ e' <= e->
ceval (QMeas x s' e') st mu-> 
sat_Assert st ((QExp_s  s  e  v) /\ big_Sand (fun i:nat => (Assn_sub_P x i (P i))) (2^(e'-s'))) ->
(big_pOplus' (fun i:nat=> (@norm (2^(e-s)) ((U_v s' e' s e (∣ i ⟩_ (e'-s') × ⟨ i ∣_ (e'-s')) v))) ^ 2)%R
                               (fun i:nat=> SAnd ((P i))  (QExp_s  s  e (( / ( (@norm (2^(e-s)) ((U_v  s' e' s e (∣ i ⟩_ (e'-s') × ⟨ i ∣_ (e'-s')) v)))))%R.* 
                             (U_v s' e' s e (∣ i ⟩_ (e'-s') × ⟨ i ∣_ (e'-s')) v)))) (2^(e'-s'))) pF ->
sat_Assert mu pF.
Proof. 
intros s' e' s e v x P s0 e0 st mu pF He H H0 Hp. 
intros. destruct mu as [ mu IHmu]. 
inversion_clear H; simpl in H3.
inversion H3; subst. 
inversion H11; subst. clear H11. clear H3. 
rewrite sat_Assert_to_State in *.

remember (fun j:nat => (@norm (2^(e-s))
(U_v s' e' s e(∣ j ⟩_ (e' - s') × ⟨ j ∣_ (e' - s')) v))).


pose (@big_app'_exsist s0 e0 ((2 ^ (e' - s'))) ((fun j : nat =>
s_scale ((r j) ^2) 
(s_scale ( /( r j ^ 2))%R (c_update x j (fst st),  QMeas_fun s' e' j (snd st)))))).
destruct e1.

assert(x0 = mu''). eapply big_app_eq_bound'. apply H. apply H12.
intros.  unfold s_scale. simpl. 
assert((QMeas_fun s' e' i (snd st)= Zero) \/ QMeas_fun s' e' i (snd st)<> Zero).
apply Classical_Prop.classic. destruct H4.
assert(@trace (2^(e0-s0)) (QMeas_fun s' e' i (snd st))= C0).
rewrite H4.  rewrite Zero_trace. reflexivity.
assert( r i= 0%R). rewrite Heqr. admit.  
rewrite H6. repeat rewrite Rmult_0_l. rewrite Mscale_0_l. rewrite H4.
reflexivity. 
assert( r i <>0%R). rewrite Heqr. admit.
rewrite Mscale_assoc. 
rewrite RtoC_mult. 
rewrite Rinv_r. rewrite Mscale_1_l.  unfold QMeas_fun.
reflexivity. admit.  rewrite H3 in *.

assert(forall j,  Sorted.Sorted(StateMap.Raw.PX.ltk (elt:=qstate s0 e0)) 
[s_scale (/( r j ^ 2))%R (c_update x j (fst st),  QMeas_fun s' e' j (snd st))]).
intros. apply Sorted.Sorted_cons. apply Sorted.Sorted_nil. apply Sorted.HdRel_nil.
rewrite Heqr in *.

pose (big_dapp_exsist (fun_to_list (fun j : nat => ( r j ^ 2)%R) (2 ^ (e' - s'))) 
(fun_to_list (fun j : nat => StateMap.Build_slist (H4 j) ) (2 ^ (e' - s')))).
destruct e1.  repeat rewrite fun_to_list_length. reflexivity.

rewrite Heqr in *.

assert(dstate_eq x1
{| StateMap.this :=
    StateMap.Raw.map2 option_app mu'' [];
  StateMap.sorted := IHmu
|}). unfold dstate_eq. simpl. rewrite map2_nil_r.
apply big_dapp_this  in H5.
 rewrite (@fun_dstate_to_list s0 e0 ((2 ^ (e' - s')))
 ) in H5. simpl in H5. 
 eapply (big_app_map2' _ _ _ _ _ _ H5); try assumption.

apply sat_Pro_dstate_eq with x1; try assumption.
inversion_clear H0. inversion_clear H8. clear H9.

econstructor. apply WF_dstate_eq with {|
  StateMap.this := StateMap.Raw.map2 option_app mu'' [];
  StateMap.sorted := IHmu
|}; try assumption.  intuition. 
econstructor. apply Forall_big_pOplus' in Hp.
assumption. intros. apply pow2_ge_0. 



apply sum_over_list_big_pOplus' in Hp. rewrite Hp.
rewrite (big_sum_eq_bounded  _ 
((fun i : nat => (( (/Cmod (@trace (2^(e0-s0)) (snd st)))) * 
 (s_trace (c_update x i (fst st),
 QMeas_fun s' e' i (snd st)))))%R)).
rewrite <-(big_sum_mult_l_R  ). 
rewrite <-(big_app'_trace _ _ mu''); try assumption.
rewrite (QMeas_trace' s' e' x s0 (fst st) (snd st)); try lia; try assumption.
unfold s_trace. simpl. rewrite Rinv_l. reflexivity.
assert((Cmod (@trace (2^(e0-s0)) (snd st)) > 0)%R).
apply mixed_state_Cmod_1. apply WF_state_dstate in H1.
apply H1. lra. apply Mixed_State_aux_to_Mix_State.
apply WF_state_dstate in H1. apply H1.
intros. unfold WWF_state. simpl.  
assert((QMeas_fun s' e' i (snd st)= Zero) \/ QMeas_fun s' e' i (snd st)<> Zero).
apply Classical_Prop.classic. destruct H9.
right. assumption. left. split. apply WWF_qstate_QMeas.
lia. assumption. lia. apply Mixed_State_aux_to_Mix_State.
apply WF_state_dstate in H1. apply H1. lia.
intros. unfold s_trace. simpl.
destruct H0. destruct H0. simpl in H11.
rewrite <-(PMtrace_Meas  _ _ s e _ v);
try lia; try assumption.
rewrite Cmod_mult. rewrite (Rmult_comm _ (Cmod (trace (snd st)))).
repeat rewrite <-Rmult_assoc. rewrite Rinv_l.
rewrite Rmult_1_l. rewrite Rmult_1_r.
rewrite Cmod_R. rewrite  Rabs_right. reflexivity.
admit. 
assert((Cmod (@trace (2^(e0-s0)) (snd st)) > 0)%R).
apply mixed_state_Cmod_1. apply WF_state_dstate in H1.
apply H1. lra.  
apply WF_state_dstate in H1. apply H1. apply H0.  rewrite PMtrace_scale.
apply H11.

eapply big_pOplus'_sat . apply Hp.  apply H5. 
intros. 
econstructor. 
admit.  econstructor. apply rule_Meas_aux; try assumption. 
simpl in H9. intro. rewrite H11 in H9. rewrite Rmult_0_l in *.
lra. destruct H0. destruct H0. lia. 
 apply WF_state_dstate. assumption. destruct st. simpl snd in *.
assumption. econstructor. 


intros. unfold dstate_eq in *. 
unfold d_trace. simpl in H6.  
rewrite map2_nil_r in H6. 
rewrite H6.  simpl.  
rewrite  (QMeas_trace' s' e' x i (fst st) (snd st)); try assumption; try lia. 
 unfold s_trace. simpl. rewrite Rplus_0_r.
rewrite Rmult_1_r.  f_equal. rewrite trace_mult_dist.
destruct H0. destruct H0. simpl in H13.
rewrite <-(PMtrace_Meas _ _ s e _ v); try assumption; try lia.
rewrite Cmult_assoc. rewrite RtoC_mult. 
rewrite Rinv_l. rewrite Cmult_1_l. reflexivity.
simpl in H9. rewrite Rmult_1_r in H9. assumption.
apply WF_state_dstate. assumption. 
apply H0.  rewrite PMtrace_scale.
apply H13. apply Mixed_State_aux_to_Mix_State.
apply WF_state_dstate. assumption.
Admitted.

Fixpoint list_and{s e:nat} (mu_n1 mu_n2: list (dstate s e)) :=
match mu_n1, mu_n2 with 
|[], _ => []
|_,  [] =>[]
|(h1::t1), (h2::t2)=> (d_app h1 h2) :: (list_and t1 t2)
end.

Lemma lits_and_length{s e:nat}: forall (mu_n1 mu_n2: list (dstate s e)),
length mu_n1 = length mu_n2->
length (list_and mu_n1 mu_n2)= length mu_n1.
Proof. induction mu_n1; intros. simpl. reflexivity.
       destruct mu_n2. simpl. simpl in H. intuition. 
       simpl. f_equal. apply IHmu_n1. injection H. intuition. 
Qed.


Lemma big_dapp'_length{s e:nat}: forall p_n (mu_n:list (dstate s e)) (mu:dstate s e),
big_dapp' p_n mu_n mu -> length p_n = length mu_n.
Proof. induction p_n; intros; destruct mu_n. reflexivity.
      inversion_clear H. inversion_clear H.
      inversion H; subst.
      simpl. f_equal. apply IHp_n with d0 .
      assumption.
Qed.


Lemma big_dapp_list_and{s e:nat}: forall (p_n:list R)(mu_n1 mu_n2:list (dstate s e)) ,
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

Lemma big_and_list_and{s e:nat}: forall (mu_n1 mu_n2:list (dstate s e)) (nF:npro_formula),
(Forall_two (fun i j => sat_State i j) mu_n1 nF)->
(Forall_two (fun i j => sat_State i j) mu_n2 nF)->
(Forall (fun x=> WF_dstate x) (list_and mu_n1 mu_n2))->
(Forall_two (fun i j => sat_State i j)  (list_and mu_n1 mu_n2) nF).
Proof. induction mu_n1.  intros. destruct mu_n2. destruct nF. simpl.
     intuition. simpl in *. inversion_clear H0.
     destruct nF. simpl in *. inversion_clear H0.
     inversion_clear H. 
      intros. destruct mu_n2. destruct nF. simpl in *. inversion_clear H.
      simpl in *. inversion_clear H0. destruct nF. simpl in H. inversion_clear H.
      simpl in *. inversion_clear H. inversion_clear H0.
      econstructor. 
      apply d_seman_app''. assumption. assumption. 
      inversion_clear H1. assumption. 
      apply IHmu_n1. assumption. assumption. inversion_clear H1. assumption.   
Qed.


Lemma list_and_trace{s e:nat}: forall (mu_n1 mu_n2:list (dstate s e)) (a b:R),
(Forall (fun x=> WWF_dstate x) ( mu_n1 ))->
(Forall (fun x=> WWF_dstate x) ( mu_n2))->
Forall (fun mu_i : dstate s e =>
        d_trace_aux (StateMap.this mu_i) = a) mu_n1->
        Forall
        (fun mu_i : dstate s e =>
         d_trace_aux (StateMap.this mu_i) = b)
        mu_n2->
        Forall
        (fun mu_i : dstate s e =>
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


Lemma sat_dapp{s e:nat}: forall (mu1 mu2:list (cstate *qstate s e)) IHmu1 IHmu2 IHmu' (pF:pro_formula),
(Forall (fun x:R=>(0<x)%R) (get_pro_formula pF))->
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
          apply WWF_dstate_big_dapp with (get_pro_formula pF)  mu_n. 
          apply Forall_WWF_WF.
          apply WF_big_and with (pro_to_npro_formula pF).
          assumption. assumption.
          inversion_clear H4. assumption.
          unfold dstate_eq in *. simpl in *.
          rewrite H11. 
          apply WWF_dstate_big_dapp with (get_pro_formula pF) mu_n0. 
          apply Forall_WWF_WF.
          apply WF_big_and with (pro_to_npro_formula pF).
          assumption. assumption.
          inversion_clear H4. assumption.
Admitted.


Theorem rule_Meas_aux'':forall s' e' s e (v: Vector (2^(e-s))) x (P :nat-> (Pure_formula))
(s0 e0:nat) (mu mu': dstate s0 e0) pF,
s <= s' /\ s' <= e' /\ e' <= e->
ceval (QMeas x s' e') mu mu'-> 
sat_State mu ((QExp_s  s  e  v) /\ big_Sand (fun i:nat => (Assn_sub_P x i (P i))) (2^(e'-s'))) ->
(big_pOplus' (fun i:nat=> (@norm (2^(e-s)) ((U_v s' e' s e (∣ i ⟩_ (e'-s') × ⟨ i ∣_ (e'-s')) v))) ^ 2)%R
                               (fun i:nat=> SAnd ((P i))  (QExp_s  s  e (( / ( (@norm (2^(e-s)) ((U_v s' e' s e (∣ i ⟩_ (e'-s') × ⟨ i ∣_ (e'-s')) v)))))%R.* 
                               (U_v  s' e' s e (∣ i ⟩_ (e'-s') × ⟨ i ∣_ (e'-s')) v)))) (2^(e'-s')) pF) ->
sat_Assert mu' pF .
Proof.  intros s' e' s e v x P s0 e0  (mu, IHmu). induction mu;  intros mu'  pF; intros; destruct mu' as(mu', IHmu').
-- simpl in H1.  apply WF_sat_State in H1. simpl in H1. destruct H1. destruct H1. reflexivity.
--destruct mu. inversion_clear H0. simpl in H5.  inversion H5; subst. inversion H12; subst.
clear H12. 
apply (rule_Meas_aux' s' e' s e v x P _ _ (sigma, rho)); try assumption.
simpl.  econstructor.  apply H3. apply H4. simpl. apply H5.
apply sat_Assert_dstate_eq with {|
  StateMap.this := [(sigma, rho)];
  StateMap.sorted := IHmu
|}. unfold dstate_eq. simpl. reflexivity.
rewrite sat_Assert_to_State. apply H1. 

inversion_clear H0. simpl in H5.  inversion H5; subst.
assert(Sorted.Sorted (StateMap.Raw.PX.ltk (elt:=qstate s0 e0)) (big_app
(fun j : nat =>
 [(c_update x j sigma, QMeas_fun s' e' j rho)])
(2 ^ (e' - s')))). apply big_app_sorted. intros. apply 
Sorted.Sorted_cons. apply 
Sorted.Sorted_nil. apply Sorted.HdRel_nil.
assert(Sorted.Sorted (StateMap.Raw.PX.ltk (elt:=qstate s0 e0)) mu'0). 
apply ceval_sorted with (<{ x :=M [[s' e']] }>)
(p::mu). inversion_clear IHmu. assumption. assumption.
assert(Sorted.Sorted (StateMap.Raw.PX.ltk (elt:=qstate s0 e0)) mu''). 
apply ceval_sorted with (<{ x :=M [[s' e']] }>)
([(sigma, rho)]). apply 
Sorted.Sorted_cons. apply 
Sorted.Sorted_nil. apply Sorted.HdRel_nil.
apply ceval_QMeas; try lia. assumption.
apply sat_dapp with H7 H6.

remember ((fun i : nat =>
(norm (U_v s' e' s e(∣ i ⟩_ (e' - s') × ⟨ i ∣_ (e' - s')) v) ^ 2)%R)).
pose (emit_0_exsist ( fun_to_list r  ((2 ^ (e' - s')))) ( fun_to_list r  ((2 ^ (e' - s'))))).
destruct e1. rewrite fun_to_list_length. reflexivity.
erewrite big_pOplus'_get_pro; [| apply H2 | apply  H8]. 
admit. 
apply (rule_Meas_aux' s' e' s e v x P _ _ (sigma, rho)); try assumption.
econstructor. inversion_clear H3.  apply WF_state_dstate.
assumption.  apply WF_ceval with (<{ x :=M [[s' e']] }>) ([(sigma, rho)]).
apply WF_state_dstate_aux. inversion_clear H3. assumption.
apply ceval_QMeas; try lia. simpl. assumption.
apply ceval_QMeas; try lia. simpl. assumption.
inversion_clear H1.
rewrite sat_Assert_to_State. econstructor. 
apply WF_state_dstate. inversion_clear H8. assumption.
inversion_clear H9. econstructor. apply H1.
econstructor.

inversion_clear IHmu.
apply IHmu0 with H8. assumption.  apply E_com; try assumption.
inversion_clear H3. assumption. 
apply WF_ceval with (<{ x :=M [[s' e']] }>) (p::mu).
inversion_clear H3. assumption. 
assumption.  inversion_clear H1. inversion_clear H14. 
econstructor. inversion_clear H3. assumption.
 apply State_eval_dstate_Forall. discriminate.
assumption.  assumption. assumption.  

Admitted.

Theorem rule_QMeas : forall s' e' s e (v: Vector (2^(e-s))) x (P :nat-> (Pure_formula)) pF,
s <= s' /\ s' <= e' /\ e' <= e->
big_pOplus' (fun i:nat=> (@norm (2^(e-s)) ((U_v s' e' s e (∣ i ⟩_ (e'-s') × ⟨ i ∣_ (e'-s')) v))) ^ 2)%R
 (fun i:nat=> SAnd ((P i))  (QExp_s  s  e (( / ( (@norm (2^(e-s)) ((U_v s' e' s e (∣ i ⟩_ (e'-s') × ⟨ i ∣_ (e'-s')) v)))))%R.* 
 (U_v s' e' s e (∣ i ⟩_ (e'-s') × ⟨ i ∣_ (e'-s')) v)))) (2^(e'-s')) pF ->
{{ (QExp_s  s  e  v) /\ big_Sand (fun i:nat => (Assn_sub_P x i (P i))) (2^(e'-s')) }}
 QMeas x s' e' 
{{ pF }}.
Proof. unfold hoare_triple.
intros. 
rewrite sat_Assert_to_State in *.
eapply rule_Meas_aux''. apply H. apply H1. apply H2.
apply H0.
Qed.


