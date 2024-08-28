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
From Quan Require Import ParDensityO.
From Quan Require Import QState_L.
From Quan Require Import QIMP_L.
From Quan Require Import QAssert_L.
From Quan Require Import Par_trace.
From Quan Require Import QRule_Q_L.
From Quan Require Import QRule_E_L.
From Quan Require Import QRule_I_L.

Local Open Scope com_scope.

Local Open Scope nat_scope.


(*-------------------------par_trace---------------------------*)
Fixpoint Free_QExp'(qs :QExp) := 
  match qs with 
  |QExp_s s e v => (s, e) 
  |QExp_t qs1 qs2 => (min (fst (Free_QExp' qs1)) (fst (Free_QExp' qs2)),
                      max  (snd (Free_QExp' qs1))  (snd (Free_QExp' qs2) ))
  end.


Lemma  le_min: forall s e, 
s<=e -> min s e= s .
Proof. induction s; intros. simpl. reflexivity.
       destruct e. 
       simpl. lia. 
       simpl. f_equal. apply IHs.
       lia.
Qed.

Lemma  le_max: forall s e, 
s<=e -> max s e= e .
Proof. induction s; intros. simpl. reflexivity.
       destruct e. 
       simpl. lia. 
       simpl. f_equal. apply IHs.
       lia.
Qed.


  Lemma min_le: forall s0 e0 s1 e1, 
  s0<=e0 /\ e0=s1 /\ s1<=e1 ->
  min s0 s1 = s0 /\
  max e0 e1= e1.
  Proof. intros. split; [apply le_min| apply le_max]; lia. 
  Qed.
  

Fixpoint Free_State(F:State_formula):=
  match F with 
    |SPure P => (0, 0)
    |SQuan qs=> Free_QExp' qs 
    |SOdot F1 F2=>  (min (fst (Free_State F1)) (fst (Free_State F2)),
                    max  (snd (Free_State F1))  (snd (Free_State F2) ))
    |SAnd F1 F2 =>  (min (fst (Free_State F1)) (fst (Free_State F2)),
                     max  (snd (Free_State F1))  (snd (Free_State F2) ))
    (* |SNot F'=> Free_state F'
    | Assn_sub X a F => Free_state F *)
  end.

Lemma nat_eq_mod_div: forall a b c, a=b <-> 
(a / c = b/c) /\ (a mod c = b mod c) .
Proof. intros. intuition. 
       rewrite (div_mod_eq a c).
       rewrite (div_mod_eq b c).
       rewrite H0. rewrite H1. reflexivity.
Qed.

Lemma nat_neq_mod_div: forall a b c, a<>b <-> 
(a / c <> b/c) \/ (a mod c <> b mod c) .
Proof. intros. split. intros. 
       unfold not in *.
       apply Classical_Prop.not_and_or.
       unfold not. intros. rewrite <-nat_eq_mod_div in H0.
       intuition.
       intros.  unfold not. intros.
       rewrite (nat_eq_mod_div  _ _ c) in H0.
       destruct H. intuition.
       intuition.
Qed.



Lemma Vec_kron: forall x m n,
∣ x / 2 ^ n ⟩_ (m) ⊗ ∣ x mod 2 ^ n ⟩_ (n) =
Vec ((2^(m+n))) x.
Proof. intros.
prep_matrix_equality.
       unfold kron.
       destruct y.
       simpl. 
       bdestruct (x0=?x).
       subst.
       assert((x / 2 ^ n =? x / 2 ^ n) = true ).
       rewrite Nat.eqb_eq. reflexivity.
       rewrite H. clear H. 
       assert((x mod 2 ^ n =? x mod 2 ^ n) = true ).
       rewrite Nat.eqb_eq. reflexivity.
       rewrite H.
       apply Cmult_1_l.
       rewrite (nat_neq_mod_div _ _ (2^n)) in H.
       destruct H. 
       apply Neq_i_j in H.
       rewrite H. rewrite Cmult_0_l.
       reflexivity.
       apply Neq_i_j in H.
       rewrite H. rewrite Cmult_0_r.
       reflexivity.
       rewrite Nat.div_1_r.
       simpl. rewrite Cmult_0_l.
       reflexivity. 
Qed.

Lemma PMLpar_trace_assoc{ s e :nat}: forall (q:qstate s e) r r',
s<=r' /\ r'<=r /\ r<=e->
PMLpar_trace (PMLpar_trace q r)  r'=
PMLpar_trace q  r'.
Proof. intros. unfold PMLpar_trace.
       
       rewrite (big_sum_eq_bounded  
       _ ((fun i : nat =>
        big_sum
           (fun i0 : nat =>
            I (2 ^ (r' - s)) ⊗ ⟨ i ∣_ (r - r') ⊗ ⟨ i0 ∣_ (e - r) × q
            × ((I (2 ^ (r' - s)) ⊗ ∣ i ⟩_ (r - r')) ⊗ ∣ i0 ⟩_ (e - r)))
           (2 ^ (e - r))))).
      rewrite big_sum_double_sum.
      assert(2 ^ (e - r')= 2 ^ (e - r) * 2 ^ (r - r')).
      type_sovle'. destruct H0.
      apply big_sum_eq_bounded.
      intros.
      f_equal; type_sovle'.
      f_equal; type_sovle'.
      rewrite kron_assoc; auto_wf. 
      f_equal; type_sovle'.
      assert(e - r'= r-r'+ (e-r)).
      lia. rewrite H1.
      assert( ∣ x / 2 ^ (e - r) ⟩_ (r - r')
      ⊗ ∣ x mod 2 ^ (e - r) ⟩_ (e - r) =
      ∣ x ⟩_ (r - r' + (e - r))).
      apply (Vec_kron x (r-r') (e-r)).
      assert(adjoint (∣ x / 2 ^ (e - r) ⟩_ (r - r')
      ⊗ ∣ x mod 2 ^ (e - r) ⟩_ (e - r))=
      adjoint (∣ x ⟩_ (r - r' + (e - r)))).
      rewrite H2. reflexivity.
      rewrite kron_adjoint in H3.
      assumption.
      apply WF_adjoint.
      apply WF_vec. 
      apply div_lt_upper_bound.
      apply Nat.pow_nonzero. lia. 
      assert(2 ^ (e - r) * 2 ^ (r - r') = 2^(e-r')).
      type_sovle'. rewrite H1. assumption.
     apply WF_adjoint.
     apply WF_vec.
     apply mod_bound_pos.
     lia. apply pow_gt_0.
      rewrite kron_assoc; auto_wf.
      f_equal; type_sovle'.
      apply Vec_kron.
      apply WF_vec. 
      apply div_lt_upper_bound.
      apply Nat.pow_nonzero. lia. 
      assert(2 ^ (e - r) * 2 ^ (r - r') = 2^(e-r')).
      type_sovle'. rewrite H1. assumption.
      
     apply WF_vec.   apply mod_bound_pos.
     lia. apply pow_gt_0.
      assert(2^(r'-s) * 2^(r-r')=2^(r-s)*1).
      rewrite Nat.mul_1_r.   
      type_sovle'. destruct H0.
      intros.
       rewrite Mmult_Msum_distr_l.
       rewrite Mmult_Msum_distr_r.
       apply big_sum_eq_bounded.
       intros. 
       rewrite Mmult_assoc_5.
       apply Logic.eq_trans with (I (2 ^ (r' - s)) ⊗ ⟨ x ∣_ (r - r')
       ⊗ I 1 × (I (2 ^ (r' - s)) ⊗ I (2^(r-r')) ⊗ ⟨ x0 ∣_ (e - r)) × q
       × (I (2 ^ (r' - s)) ⊗ I (2^(r - r')) ⊗ ∣ x0 ⟩_ (e - r)
          × (I (2 ^ (r' - s)) ⊗ ∣ x ⟩_ (r - r') ⊗ I 1 ))).
      f_equal; type_sovle'. 
      f_equal; type_sovle'.
      f_equal; type_sovle'.
      rewrite Nat.mul_1_r. type_sovle'.
      rewrite kron_1_r. reflexivity.
      rewrite id_kron; f_equal; type_sovle'.
      f_equal; type_sovle'.
      f_equal; type_sovle'.
      rewrite Nat.mul_1_r. reflexivity.
      rewrite id_kron; f_equal; type_sovle'.
      f_equal; type_sovle'. 
      rewrite kron_1_r. reflexivity.
      repeat rewrite kron_mixed_product.
      repeat rewrite Mmult_1_l; auto_wf.
      repeat rewrite Mmult_1_r;auto_wf.
      reflexivity.
Qed.

Lemma PMRpar_trace_assoc{ s e :nat}: forall (q:qstate s e) l l',
s<=l /\ l<=l' /\ l'<=e->
PMRpar_trace (PMRpar_trace q l)  l'=
PMRpar_trace q  l'.
Proof. intros. unfold PMRpar_trace.
       
       rewrite (big_sum_eq_bounded  
       _ ((fun i : nat =>
        big_sum
           (fun i0 : nat =>
             (⟨ i0 ∣_ (l-s) ⊗ ⟨ i ∣_ (l' - l) ⊗  I (2 ^ (e - l')) ) × q
            × ((  ∣ i0 ⟩_ (l- s)) ⊗ ∣ i ⟩_ (l' - l) ⊗ (I (2 ^ (e-l'))  )))
           (2 ^ ( l- s))))).
       rewrite big_sum_swap_order.
      rewrite big_sum_double_sum.
      assert(2 ^ (l' - s)= 2 ^ (l' -l ) * 2 ^ (l - s)).
      type_sovle'. destruct H0.
      apply big_sum_eq_bounded.
      intros.
      f_equal; type_sovle'.
      f_equal; type_sovle'.
      f_equal; type_sovle'.
      assert(l' - s = l -s + (l' -l)).
      lia. rewrite H1.
      assert(∣ x / 2 ^ (l' - l) ⟩_ (l - s)
      ⊗ ∣ x mod 2 ^ (l' - l) ⟩_ (l' - l)=
      ∣ x ⟩_ (l - s + (l' - l))).
      apply Vec_kron.
      assert(adjoint ( ∣ x / 2 ^ (l' - l) ⟩_ (l - s)
      ⊗ ∣ x mod 2 ^ (l' - l) ⟩_ (l' - l))=
      adjoint (∣ x ⟩_ (l - s + (l' - l)))).
      rewrite H2. reflexivity.
      rewrite kron_adjoint in H3.
      apply H3.
      f_equal; type_sovle'.
      apply Vec_kron.
      assert(2^(l'-l) * 2^(e-l')=1 * 2^(e-l)).
      rewrite Nat.mul_1_l. 
      type_sovle'. destruct H0.
      intros.
      rewrite Mmult_Msum_distr_l.
      rewrite Mmult_Msum_distr_r.
      apply big_sum_eq_bounded.
      intros. 
      rewrite Mmult_assoc_5.
      apply Logic.eq_trans with ( I 1  ⊗ ⟨ x ∣_ (l'-l) ⊗  I (2 ^ (e-l')) 
      × ( ⟨ x0 ∣_ (l- s) ⊗ I (2 ^ (l'-l)) ⊗ I (2^(e-l')) ) × q
      × ( ∣ x0 ⟩_ (l - s) ⊗ I (2 ^ (l' - l)) ⊗ I (2^(e - l')) 
      × (I 1 ⊗ ∣ x ⟩_ (l'- l) ⊗  I (2 ^ (e- l'))  ))).
      f_equal; type_sovle'.
      f_equal; type_sovle'.
      f_equal; type_sovle'.
      rewrite Nat.mul_1_l. type_sovle'.
      rewrite kron_1_l; auto_wf. reflexivity.
      rewrite kron_assoc; auto_wf.
      rewrite id_kron; f_equal; type_sovle'.
      f_equal; type_sovle'.
      f_equal; type_sovle'.
      rewrite Nat.mul_1_l. reflexivity.
      rewrite kron_assoc; auto_wf.
      rewrite id_kron; f_equal; type_sovle'.
      f_equal; type_sovle'. 
      rewrite kron_1_l; auto_wf. reflexivity.
      repeat rewrite kron_mixed_product.
      repeat rewrite Mmult_1_l; auto_wf.      
      repeat rewrite Mmult_1_r;auto_wf.       
      reflexivity.
Qed.

Lemma Par_trace_comm{ s e :nat}: forall (q:qstate s e) l r ,
s<=l /\ l<=r /\ r<=e->
PMRpar_trace (PMLpar_trace q r) l=
PMLpar_trace (PMRpar_trace q l) r.
Proof. intros. unfold PMRpar_trace. 
       unfold PMLpar_trace.
       rewrite (big_sum_eq_bounded 
       _ ((fun i : nat =>
      big_sum
      (fun i0 : nat =>
      ⟨ i ∣_ (l - s) ⊗ I (2 ^ (r - l)) ⊗ ⟨ i0 ∣_ (e - r) × q
      × ((∣ i ⟩_ (l - s) ⊗ I (2 ^ (r - l))) ⊗ ∣ i0 ⟩_ (e - r)))
      (2 ^ (e - r))))).
      
      rewrite (big_sum_eq_bounded 
      (fun i : nat =>
      I (2 ^ (r - l)) ⊗ ⟨ i ∣_ (e - r)
      × big_sum
       (fun i0 : nat =>
        ⟨ i0 ∣_ (l - s) ⊗ I (2 ^ (e - l)) × q
        × (∣ i0 ⟩_ (l - s) ⊗ I (2 ^ (e - l))))
       (2 ^ (l - s)) × (I (2 ^ (r - l)) ⊗ ∣ i ⟩_ (e - r)))
      ((fun i : nat =>
     big_sum
     (fun i0 : nat =>
     ⟨ i0 ∣_ (l - s) ⊗ I (2 ^ (r - l)) ⊗ ⟨ i∣_ (e - r) × q
     × ((∣ i0 ⟩_ (l - s) ⊗ I (2 ^ (r - l))) ⊗ ∣ i ⟩_ (e - r)))
     (2 ^ (l-s))))).
     rewrite big_sum_swap_order at 1.
     apply big_sum_eq_bounded. 
     intros. reflexivity.
     intros.
     assert(2^(r-l) * 2^(e-r)=1 * 2^(e-l)).
      rewrite Nat.mul_1_l.   
      type_sovle'. destruct H1.
      intros.
       rewrite Mmult_Msum_distr_l.
       rewrite Mmult_Msum_distr_r.
       apply big_sum_eq_bounded.
       intros. 
       rewrite Mmult_assoc_5.
       apply Logic.eq_trans with ( I 1 ⊗ I (2 ^ (r - l)) ⊗ ⟨ x ∣_ (e - r)
        × ( ⟨ x0 ∣_ (l - s) ⊗ I (2 ^ (r- l)) ⊗ I (2^(e-r)) ) × q
       ×  ( ∣ x0 ⟩_ (l - s) ⊗ I (2 ^ (r - l)) ⊗ I (2^(e - r)) 
          × (  I 1  ⊗ I (2 ^ (r - l)) ⊗ ∣ x ⟩_ (e - r)  ))).
      f_equal; type_sovle'. 
      f_equal; type_sovle'.
      f_equal; type_sovle'.
      rewrite Nat.mul_1_l. type_sovle'.
      rewrite kron_1_l; auto_wf. reflexivity.
      rewrite kron_assoc; auto_wf.
      rewrite id_kron; f_equal; type_sovle'.
      f_equal; type_sovle'.
      f_equal; type_sovle'.
      rewrite Nat.mul_1_l. reflexivity.
      rewrite kron_assoc; auto_wf.
      rewrite id_kron; f_equal; type_sovle'.
      f_equal; type_sovle'. 
      rewrite kron_1_l; auto_wf. reflexivity.
      repeat rewrite kron_mixed_product.
      repeat rewrite Mmult_1_l; auto_wf.
      repeat rewrite Mmult_1_r;auto_wf.
      reflexivity.
      
      assert(2^(l -s ) * 2^(r -l )= 2^(r - s) * 1).
      rewrite Nat.mul_1_r.   
      type_sovle'. destruct H0.
      intros.
       rewrite Mmult_Msum_distr_l.
       rewrite Mmult_Msum_distr_r.
       apply big_sum_eq_bounded.
       intros. 
       rewrite Mmult_assoc_5.
       apply Logic.eq_trans with ( ⟨ x ∣_ (l - s ) ⊗ I (2 ^ (r - l))  ⊗ I 1
        × ( I (2 ^ ( l- s)) ⊗ I (2^ (r - l)) ⊗ ⟨ x0 ∣_ (e - r) ) × q
        ×  (  I (2 ^ (l- s)) ⊗ I (2^(r - l)) ⊗ ∣ x0 ⟩_ (e - r)
        × ( ∣ x ⟩_ (l - s) ⊗ I (2 ^ (r - l)) ⊗ I 1 ))).
      f_equal; type_sovle'. lia. lia.  
      f_equal; type_sovle'. lia. 
      f_equal; type_sovle'. lia. lia. 
      rewrite kron_1_r; auto_wf. reflexivity.
      rewrite id_kron; f_equal; type_sovle'.
      f_equal; type_sovle'.
      f_equal; type_sovle'. lia. lia.
      rewrite id_kron; f_equal; type_sovle'.
      f_equal; type_sovle'.  
      rewrite kron_1_r; auto_wf. reflexivity.
      repeat rewrite kron_mixed_product.
      repeat rewrite Mmult_1_l; auto_wf.
      repeat rewrite Mmult_1_r;auto_wf.
      reflexivity.
Qed.



Lemma PMpar_trace_assoc{ s e :nat}: forall (q:qstate s e) l r l' r',
s<=l /\ l<=l' /\l' <=r' /\  r'<=r /\ r<=e->
PMpar_trace (PMpar_trace q l r) l' r'=
PMpar_trace q l' r'.
Proof. intros. unfold PMpar_trace. 
       rewrite Par_trace_comm; try lia.
       rewrite PMRpar_trace_assoc; try lia.
       rewrite Par_trace_comm; try lia.
       rewrite PMLpar_trace_assoc; try lia.
       rewrite Par_trace_comm; try lia.
       reflexivity. 
Qed. 




Lemma WF_PMLpar_trace{s e:nat}: forall (q:qstate s e)  r,
s<=r/\r<=e->
@WF_Matrix (2^(e-s)) (2^(e-s)) q->
@WF_Matrix  (2^(r-s)) (2^(r-s)) (PMLpar_trace q r).
Proof. intros. 
       unfold PMLpar_trace.
       assert((2^(r-s))=((2^(r-s))*1)).
       rewrite Nat.mul_1_r.
       type_sovle'. destruct H1.
       apply WF_Msum. intros.
       apply WF_mult. apply WF_mult.
       apply WF_kron; try rewrite Nat.mul_1_r ; type_sovle'; try reflexivity.
       auto_wf. auto_wf.
       assert((2 ^ (e - s)=
       2 ^ (r - s) * 2 ^ (e - r))). type_sovle'.
       destruct H2. assumption.
       apply WF_kron; try rewrite Nat.mul_1_r ; type_sovle'; try reflexivity.
       auto_wf. auto_wf.
Qed.

Lemma WF_PMRpar_trace{s e:nat}: forall (q:qstate s e)  l,
s<=l/\l<=e->
@WF_Matrix (2^(e-s)) (2^(e-s)) q->
@WF_Matrix  (2^(e-l)) (2^(e-l)) (PMRpar_trace q l).
Proof. intros. 
       unfold PMRpar_trace.
       assert((2^(e-l))=(1* (2^(e-l)))).
       rewrite Nat.mul_1_l.
       type_sovle'. destruct H1.
       apply WF_Msum. intros.
       apply WF_mult. apply WF_mult.
       apply WF_kron; try rewrite Nat.mul_1_l ; type_sovle'; try reflexivity.
       auto_wf. auto_wf.
       assert((2 ^ (e - s)=
       2 ^ (l- s) * 2 ^ (e - l))). type_sovle'.
       destruct H2. assumption.
       apply WF_kron; try rewrite Nat.mul_1_l ; type_sovle'; try reflexivity.
       auto_wf. auto_wf.
Qed.


Lemma PMRpar_trace_refl{s e : nat}: forall (l : nat) (q : qstate s e),
l = s -> @WF_Matrix  (2^(e-s)) (2^(e-s)) q  -> 
PMRpar_trace q l = q.
Proof. intros. subst. unfold PMRpar_trace. 
       rewrite Nat.sub_diag.  
       simpl. rewrite Mplus_0_l.
       rewrite Vec_I. rewrite id_adjoint_eq.
       rewrite kron_1_l; auto_wf.
       repeat rewrite Nat.add_0_r.
       repeat rewrite Nat.mul_1_r.
       repeat rewrite Mmult_1_l; auto_wf.
       repeat rewrite Mmult_1_r; auto_wf.
       reflexivity.   
Qed.

Lemma PMLpar_trace_refl{s e : nat}: forall (r : nat) (q : qstate s e),
 r=e -> @WF_Matrix  (2^(e-s)) (2^(e-s)) q  -> 
PMLpar_trace q r = q.
Proof. intros. subst. unfold PMLpar_trace. 
       rewrite Nat.sub_diag.  
       simpl. rewrite Mplus_0_l.
       rewrite Vec_I. rewrite id_adjoint_eq.
       rewrite kron_1_r; auto_wf.
       repeat rewrite Nat.add_0_r.
       repeat rewrite Nat.mul_1_r.
       repeat rewrite Mmult_1_l; auto_wf.
       repeat rewrite Mmult_1_r; auto_wf.
       reflexivity.   
Qed.



Lemma PMpar_trace_L {s e : nat}: forall (l r : nat) (q : qstate s e),
s=l/\ l<=r/\r<=e -> @WF_Matrix  (2^(e-s)) (2^(e-s)) q  -> 
PMpar_trace q l r = PMLpar_trace q r.
Proof. intros. destruct H. subst. unfold PMpar_trace. 
       rewrite PMRpar_trace_refl. 
       reflexivity. reflexivity.
       apply WF_PMLpar_trace.
       assumption. assumption. 
Qed.

Lemma PMpar_trace_R {s e : nat}: forall (l r : nat) (q : qstate s e),
r=e -> @WF_Matrix  (2^(e-s)) (2^(e-s)) q  -> 
PMpar_trace q l r = PMRpar_trace q l.
Proof. intros.  subst. unfold PMpar_trace. 
       rewrite PMLpar_trace_refl. 
       reflexivity. reflexivity.
       assumption. 
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


Lemma PMpar_trace_ceval_swap_Qinit{ s e:nat}: forall (q: qstate s e ) s0 e0 l r,
s<=l/\l<=s0 /\s0<=e0 /\ e0<=r /\ r<=e-> 
@WF_Matrix (2^(e-s)) (2^(e-s)) q -> 
@PMpar_trace  s e (QInit_fun s0 e0 q) l r = QInit_fun s0 e0 (PMpar_trace q l r) .
Proof. intros. unfold QInit_fun.
       rewrite big_sum_par_trace.
       apply big_sum_eq_bounded.
       intros. 
       remember (I (2 ^ (s0 - l)) ⊗ (∣ 0 ⟩_ (e0 - s0) × ⟨ x ∣_ (e0 - s0))
       ⊗ I (2 ^ (r - e0))).
       assert(m × PMpar_trace q l r × (m) † = 
       super m  (PMpar_trace q l r)).
       unfold super. reflexivity.
       rewrite H2.  
      rewrite Heqm. 
      assert(  2 ^ (r - l) = 2 ^ (s0 - l) * 2 ^ (e0 - s0) * 2 ^ (r - e0)).
      type_sovle'. destruct H3.
      rewrite PMtrace_Super_swap. 
      unfold super. 
      f_equal. f_equal; type_sovle'.
      f_equal; type_sovle'. 
      assert(  2 ^ (s0 - l) * 2 ^ (e0 - s0) * 2 ^ (r - e0)= 2 ^ (r - l)).
      type_sovle'. destruct H3.
      rewrite Mmult_kron_5; auto_wf. 
      repeat rewrite id_kron. f_equal; type_sovle'.
      f_equal; type_sovle'. f_equal; type_sovle'.
      f_equal; type_sovle'. 
      apply WF_mult. apply WF_vec.
      lia.  auto_wf. 
      assert(  2 ^ (s0 - l) * 2 ^ (e0 - s0) * 2 ^ (r - e0)= 2 ^ (r - l)).
      type_sovle'. destruct H3.
      rewrite Mmult_kron_5; auto_wf. 
      repeat rewrite id_kron. f_equal; type_sovle'.
      f_equal; type_sovle'. f_equal; type_sovle'.
      f_equal; type_sovle'.  f_equal; type_sovle'. 
      apply WF_mult. apply WF_vec.
      lia.  auto_wf. intuition.
      apply WF_kron; type_sovle'; auto_wf.
      apply WF_kron; type_sovle'; auto_wf.
      apply WF_mult. apply WF_vec; lia. 
      auto_wf. intuition.  
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
      assert( 2 ^ (s0 - l) * 2 ^ (e0 - s0) * 2 ^ (r - e0)= 2 ^ (r - l) ).
      type_sovle'. destruct H2.
      f_equal. f_equal; type_sovle'.
      rewrite Mmult_kron_5; auto_wf. 
      repeat rewrite id_kron. f_equal; type_sovle'.
      f_equal; type_sovle'. f_equal; type_sovle'.
      f_equal; type_sovle'.  apply H1.
      intuition. destruct H1. auto_wf. 
Qed.

Lemma PMpar_trace_ceval_swap_QUnit_Ctrl{ s e:nat}: forall (q: qstate s e ) s0 e0 s1 e1  
(U: nat -> Square (2^(e1-s1))) l r,
s<=l/\l<=s0 /\s0<=e0 /\ e0 <=s1 /\ s1 <= e1 /\ e1<=r /\ r<=e-> 
@WF_Matrix (2^(e-s)) (2^(e-s)) q -> 
(forall j, WF_Unitary (U j ))->
@PMpar_trace  s e (QUnit_Ctrl_fun s0 e0  s1 e1 U q) l r = QUnit_Ctrl_fun s0 e0 s1 e1 U (PMpar_trace q l r) .
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
      f_equal; type_sovle'.
      rewrite Mmult_kron_5; auto_wf.
      repeat rewrite id_kron.  
      f_equal; type_sovle'; f_equal; type_sovle'.
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
      f_equal; type_sovle'.  
      intuition.
      apply WF_Msum.
      intros. 
      apply WF_mult; auto_wf.
      apply WF_kron; type_sovle'; auto_wf.
      apply WF_kron; type_sovle'; auto_wf.
      apply H1.
Qed.


Fixpoint WF_Matrix_dstate { s e:nat} (mu: list (cstate * qstate s e)) :=
  match mu with 
  |nil => True 
  | (c,q)::mu' => and (@WF_Matrix (2^(e-s)) (2^(e-s)) q)  (WF_Matrix_dstate mu') 
  end.

  Fixpoint d_par_trace{ s e: nat} (mu:list (cstate * qstate s e)) l r :=
  match mu with 
  | nil => nil 
  | (c, q)::mu' =>(c, PMpar_trace q l r):: (d_par_trace mu' l r)
  end.


  Lemma d_par_trace_assoc{ s e :nat}: forall (mu: list (cstate *qstate s e)) l r l' r',
s<=l /\ l<=l' /\l' <=r' /\  r'<=r /\ r<=e->
d_par_trace (d_par_trace mu l r) l' r'=
d_par_trace mu l' r'.
Proof. induction mu; intros.
       simpl. reflexivity.
       destruct a. 
       simpl. f_equal.
       rewrite PMpar_trace_assoc. reflexivity.
       intuition. apply IHmu. intuition. 
Qed. 


  Lemma ceval_seq_1{s e: nat }: forall 
  (mu mu': list (cstate *qstate s e)) c1 c2,
  ceval_single <{ c1; c2 }> mu mu' ->
  exists mu1,
  and (ceval_single c1 mu mu1)
  (ceval_single c2 mu1 mu').
  Proof. induction mu; intros; inversion H; subst.
         exists nil. split. econstructor. econstructor.
         exists mu1. intuition. 
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
      repeat rewrite id_kron. f_equal; type_sovle'.
      f_equal; type_sovle'. f_equal; type_sovle'.
      f_equal; type_sovle'. 
      intuition. auto_wf. 
Qed.


Lemma d_par_trace_refl{s e:nat}: forall l r (mu: list (cstate * qstate s e)),
l=s/\r=e-> WF_Matrix_dstate mu->
d_par_trace mu l r=mu.
Proof. induction mu; intros. simpl. reflexivity.
        destruct a. 
      simpl in *. f_equal. 
      f_equal. apply PMpar_trace_refl.
      intuition. intuition.
      apply IHmu. intuition. intuition.
Qed.

Lemma d_par_trace_map2{s e :nat}: forall (mu1 mu2: list (cstate *qstate s e)) l r,
(d_par_trace (StateMap.Raw.map2 option_app mu1 mu2) l r)=
( (StateMap.Raw.map2 option_app (d_par_trace mu1 l r ) (d_par_trace mu2 l r))).
Proof. induction mu1; induction mu2; intros.
       simpl. reflexivity.
       destruct a. 
       simpl.  repeat rewrite map2_r_refl.
       reflexivity.
       destruct a. simpl. repeat rewrite map2_l_refl.
       reflexivity.
       destruct a. destruct a0.   
       simpl. 
       destruct (Cstate_as_OT.compare c c0).
       simpl. rewrite IHmu1.
       simpl. reflexivity.
       simpl. rewrite PMtrace_plus.
       rewrite IHmu1.
       reflexivity.
       simpl. rewrite IHmu2.
       reflexivity.
Qed.


Lemma d_par_trace_app{ s e :nat}: forall n l r(f: nat -> list (cstate *qstate s e)),
(d_par_trace
        (big_app
           (fun j : nat => f j) n) l r)=
big_app (fun j :nat => d_par_trace (f j) l r) n. 
Proof. induction n; intros;
       simpl; try reflexivity.
       rewrite d_par_trace_map2.
       rewrite IHn. reflexivity.
Qed.

Lemma  subset_union: forall x y z, NSet.Subset (NSet.union x y) z ->
NSet.Subset x z /\ NSet.Subset y z.
Proof. intros. unfold NSet.Subset in *. 
       split. intros. 
       apply H. apply NSet.union_2.
       assumption.
       intros. apply H. apply NSet.union_3.
       assumption.
       
Qed.

(* Lemma subset_Qsys:forall s e l r, 
l<r->
NSet.Subset (Qsys_to_Set l r) (Qsys_to_Set s e ) ->
s<=l \/ r<=e. *)

Lemma In_Qsys_l_r: forall r l , 
l<r->
NSet.In l (Qsys_to_Set l r) /\
NSet.In (r-1) (Qsys_to_Set l r).
Proof. unfold Qsys_to_Set. induction r; induction l; intros; simpl.
 lia. lia.   
 simpl. split. destruct r.
 simpl.  
 apply NSet.add_1. reflexivity.
 apply NSet.add_2. 
 eapply IHr. lia.  
 rewrite sub_0_r.
 apply NSet.add_1. reflexivity.
 destruct r. lia.  
 pose H.
 apply Lt_n_i in l0. rewrite l0.
 split.
 bdestruct (l =? r).
 rewrite H0. apply NSet.add_1.
 reflexivity.
 apply NSet.add_2.
 apply IHr. lia.  
 rewrite sub_0_r.
 apply NSet.add_1.
 reflexivity.    
Qed.

Lemma In_empty: forall s, NSet.In s NSet.empty -> False .
Proof. 
Admitted.

Lemma Lt_n_i_false: forall n i, 
(n>=i) -> (n<?i = false).
Proof. intros.
Admitted. 

Lemma In_Qsys: forall r l s, 
l<r->
NSet.In s (Qsys_to_Set l r)<-> l<=s<r.
Proof. unfold Qsys_to_Set. 
induction r; intros.
lia.
destruct l.
simpl. split. intros.
bdestruct (s=?r).
rewrite H1. 
lia.
destruct r.  
apply NSet.add_3 in H0.
simpl in H0.
apply In_empty in H0.
destruct H0.
 intuition.
apply NSet.add_3 in H0.
apply IHr in H0. lia. 
lia.
intuition.
intros.
bdestruct (s=?r).
rewrite H1.
apply NSet.add_1.
reflexivity.
destruct r. 
assert(s=0). lia.
rewrite H2.  
apply NSet.add_1.
reflexivity.
apply NSet.add_2.
apply IHr. lia.  
lia.


simpl.  pose H.
apply Lt_n_i in l0.
rewrite l0.

bdestruct (S l <?r).
split; intros.
bdestruct (s=? r).
rewrite H2. lia.
apply NSet.add_3 in H1.
apply IHr in H1.
lia. intuition. intuition.

bdestruct (s=? r).
rewrite H2. apply NSet.add_1. reflexivity.
apply NSet.add_2. 
apply IHr . assumption.
lia. 

assert(forall l r, l>=r ->(Qsys_to_Set_aux l r NSet.empty = NSet.empty)).
intros. induction r0. 
 simpl. reflexivity.
 simpl. 
 assert(l1 <? S r0 = false).
 apply Lt_n_i_false. assumption.
 rewrite H2. reflexivity.
rewrite H1.
bdestruct (s=? r).
rewrite H2.
split;intros. lia.
apply NSet.add_1. reflexivity.
split; intros. 
apply NSet.add_3 in H3.
apply In_empty in H3.
destruct H3.
intuition.
lia. 
assumption.    
Qed.


Lemma subset_Qsys:forall s e l r, 
l<r-> 
NSet.Subset (Qsys_to_Set l r) (Qsys_to_Set s e ) ->
 s<=l /\ r<=e.
Proof. intro. intro. intro. intro. intro. 
apply NF_1. intros.
 apply Classical_Prop.not_and_or in H0.
unfold not. intros. 
destruct H0. unfold not in H0.
assert(s>l). intuition. 
unfold NSet.Subset in H1.
pose (H1 l). 
assert(NSet.In l (Qsys_to_Set s e)).
apply i. apply In_Qsys_l_r. assumption.
apply In_Qsys in H3. lia.
assert(s<e\/ ~ (s<e)).
apply Classical_Prop.classic.
destruct H5. assumption.
assert(s >= e). lia.
apply Lt_n_i_false in H6.
unfold Qsys_to_Set in H3.
destruct e.  
simpl in H3.  
apply In_empty in H3.
destruct H3.
 simpl in H3. rewrite H6 in H3.
 apply In_empty in H3. destruct H3.

assert(r>e). intuition. 
unfold NSet.Subset in H1.
pose (H1 (r-1)). 
assert(NSet.In (r-1) (Qsys_to_Set s e)).
apply i. apply In_Qsys_l_r. assumption.
apply In_Qsys in H3. lia.
assert(s<e\/ ~ (s<e)).
apply Classical_Prop.classic.
destruct H5. assumption.
assert(s >= e). lia.
apply Lt_n_i_false in H6.
unfold Qsys_to_Set in H3.
destruct e.  
simpl in H3.  
apply In_empty in H3.
destruct H3.
 simpl in H3. rewrite H6 in H3.
 apply In_empty in H3. destruct H3.
Qed.


Lemma Par_trace_ceval_swap: forall c s e (mu mu': list (cstate *qstate s e)) l r,
s<=l /\ l<=r /\ r<=e ->
NSet.Subset (snd (MVar c)) (Qsys_to_Set l r)
->
WF_Matrix_dstate mu ->
ceval_single c mu mu'->
ceval_single c (d_par_trace mu l r )
(d_par_trace mu' l r ).
Proof. induction c. intros. 
       {apply ceval_skip_1 in H2.
       subst. apply ceval_skip. }
       { admit. }
       { induction mu; intros. inversion_clear H2.
        simpl. econstructor.
        destruct a0. inversion H2 ;subst.
        rewrite d_par_trace_map2.
        simpl d_par_trace.
        rewrite (state_eq_aexp  _ (c,(PMpar_trace q l r) )).
        econstructor. apply IHmu. assumption.
        assumption. simpl in H1. intuition.
        assumption. reflexivity.  }
       { admit. }
       {intros. apply ceval_seq_1 in H2. 
       destruct H2. 
       apply ceval_seq with ((d_par_trace x l r)).
       apply IHc1. intuition.
       simpl in H0. apply subset_union in H0.
       intuition.  intuition. intuition.
       apply IHc2. intuition. 
       simpl in H0. apply subset_union in H0.
       intuition. 
        admit. intuition.  }
       {induction mu; intros. inversion H2; subst.
       simpl. econstructor.
       inversion H2; subst. 
       rewrite d_par_trace_map2.
      econstructor. rewrite (state_eq_bexp _  (sigma, rho)).
      intuition. reflexivity.
      apply IHmu.  intuition.
      intuition. inversion_clear H1.  assumption. assumption. 
      assert(d_par_trace [(sigma, rho)] l r = [(sigma, PMpar_trace rho l r)]).
      reflexivity. rewrite <-H3. apply IHc1. assumption.
      simpl in H0. apply subset_union in H0.
       intuition. inversion_clear H1. simpl. intuition. assumption. 
      rewrite d_par_trace_map2.
      apply E_IF_false. rewrite (state_eq_bexp _  (sigma, rho)).
      intuition. reflexivity.
      apply IHmu.  intuition.
      intuition. inversion_clear H1. assumption. assumption. 
      assert(d_par_trace [(sigma, rho)] l r = [(sigma, PMpar_trace rho l r)]).
      reflexivity. rewrite <-H3. apply IHc2.
      assumption.  
      simpl in H0. apply subset_union in H0.
       intuition. inversion_clear H1. simpl. intuition.
      assumption. 
          }
      { admit. }
      { induction mu; intros. inversion H2; subst.
      simpl. econstructor.
      inversion H2; subst.
      rewrite d_par_trace_map2.
      simpl d_par_trace.
      rewrite PMpar_trace_ceval_swap_Qinit.
     econstructor.  simpl in H0.   
     apply subset_Qsys in H0. intuition.
     admit.
     apply IHmu.  intuition. 
     intuition. inversion_clear H1. intuition.
     assumption.
     split. intuition.
       admit. inversion_clear H1. simpl. intuition. 
     }
     { induction mu; intros. inversion H2; subst.
      simpl. econstructor.
      inversion H2; subst.
      apply inj_pair2_eq_dec in H5.
      apply inj_pair2_eq_dec in H5.
      subst.
      rewrite d_par_trace_map2.
      simpl d_par_trace.
     rewrite  PMpar_trace_ceval_swap_QUnit_one.
     econstructor.  admit. assumption.  
     apply IHmu.  intuition. assumption. 
     inversion_clear H1. intuition.
     intuition. admit. inversion_clear H1. assumption.
     assumption.
    apply Nat.eq_dec.
     apply Nat.eq_dec.
     }
     { induction mu; intros. inversion H2; subst.
      simpl. econstructor.
      inversion H2; subst.
      apply inj_pair2_eq_dec in H8.
      apply inj_pair2_eq_dec in H8.
      subst.
      rewrite d_par_trace_map2.
      simpl d_par_trace.
      rewrite PMpar_trace_ceval_swap_QUnit_Ctrl.
     econstructor. admit. assumption.  
     apply IHmu.  intuition.
     intuition.
     inversion_clear H1. assumption.
     assumption. admit.
     inversion_clear H1. assumption.
     assumption.
     apply Nat.eq_dec.
     apply Nat.eq_dec.
     }
     { induction mu; intros. inversion H2; subst.
      simpl. econstructor.
      inversion H2; subst.
      rewrite d_par_trace_map2.
      rewrite d_par_trace_app.
      simpl d_par_trace.
      rewrite (big_app_eq_bound _
      ((fun j : nat =>
     [(c_update i j sigma,
     QMeas_fun s e j (PMpar_trace rho l r))]) )).
     econstructor. admit.  
     apply IHmu.  intuition.
     intuition. inversion_clear H1. assumption.
     assumption.
     intros. f_equal. f_equal.
     apply PMpar_trace_ceval_swap_QMeas. 
     admit. inversion_clear H1; assumption.
     assumption. 
     }
Admitted.

(*----------------------------separ-------------------*)

Lemma  Vec0: forall (n i x:nat), x = i -> Vec n i x 0= C1.
  Proof. intros. simpl Vec. bdestruct (x=?i). unfold not in H. intuition.
  intuition.
 Qed.

Lemma Vec_decom{ n:nat}: forall (v:Vector n),
WF_Matrix v ->
v= big_sum (fun i:nat=> (v i 0) .* (Vec n i)) n.
Proof. intros. prep_matrix_equality.
       unfold WF_Matrix in *.
       destruct y.
       assert(x< n \/ x >= n). lia. 
       destruct H0.
       rewrite Msum_Csum.
       rewrite (big_sum_unique  (v x 0)).
       reflexivity.
       exists x.
       split. intuition. 
       split. unfold scale. 
       rewrite Vec0. rewrite Cmult_1_r.
       reflexivity. reflexivity.
       intros. unfold scale.
       rewrite Vec1. rewrite Cmult_0_r.
       reflexivity. assumption.
       rewrite H.
       rewrite Msum_Csum.
       rewrite big_sum_0_bounded.
       reflexivity.
       intros.
       unfold scale.
       assert(WF_Matrix (Vec n x0)).
       auto_wf. unfold WF_Matrix in H2.
       rewrite H2. rewrite Cmult_0_r. reflexivity.
       left. 
       intuition.
       left. intuition.
       rewrite H.  
       rewrite Msum_Csum.
       rewrite big_sum_0_bounded.
       reflexivity.
       intros.
       unfold scale.
       assert(WF_Matrix (Vec n x0)).
       auto_wf. unfold WF_Matrix in H1.
       rewrite H1. rewrite Cmult_0_r. reflexivity.
       right. 
       intuition.
       right. intuition.

       
       
Qed.

Lemma big_sum_sum' : forall a b m n (f: nat->Matrix a b), 
  big_sum f (m + n) = big_sum f m .+ big_sum (fun x => f (m + x)%nat) n.
Proof. intros. rewrite big_sum_sum.
      reflexivity. 
Qed.


Lemma big_sum_kron : forall m n  a1 a2 b1 b2 (f: nat ->Matrix a1 a2) (g: nat->Matrix b1 b2), 
  n <> O ->
  kron (big_sum f m)  (big_sum g n) = big_sum (fun x => kron (f (x / n)%nat)  (g (x mod n)%nat)) (m * n). 
Proof.
 intros.
  induction m; simpl.
  + rewrite kron_0_l; reflexivity. 
  + rewrite kron_plus_distr_r.
    rewrite IHm. clear IHm.
    rewrite kron_Msum_distr_l.    
    remember ((fun x : nat => f (x / n) ⊗ g (x mod n))) as h.
    replace (big_sum (fun x : nat => f m ⊗ g x) n) with
            (big_sum (fun x : nat => h ((m * n) + x)%nat) n). 
    2:{
      subst.
      apply big_sum_eq_bounded.
      intros x Hx.
      rewrite Nat.div_add_l by assumption.
      rewrite Nat.div_small; trivial.
      rewrite Nat.add_0_r.
      rewrite Nat.add_mod by assumption.
      rewrite Nat.mod_mul by assumption.
      rewrite Nat.add_0_l.
      repeat rewrite Nat.mod_small; trivial. }
      remember (m * n).
      rewrite <-big_sum_sum'.
    rewrite Nat.add_comm.
    reflexivity.
Qed. 



Lemma Separ{m n: nat}: forall (v:Vector (2^(m+n))),
WF_Matrix v ->
(exists (e: nat-> C) (f: nat-> C), 
forall z, (z< (2^(m+n)))-> (v z 0)= (Cmult (e (z/(2^n)))  (f (z mod (2^n) ))))
-> exists (v1: Vector (2^m)) (v2 : Vector (2^n)),
and (WF_Matrix v1 /\ WF_Matrix v2)
(kron v1 v2 =v).
Proof. intros. destruct H0. destruct H0.
       exists (big_sum (fun i=> (x i) .* (Vec (2^m) i)) (2^m)).
       exists (big_sum (fun i=> (x0 i) .* (Vec (2^n) i)) (2^n)).
       split. split. apply WF_Msum.
       intros. auto_wf. 
       apply WF_Msum.
       intros. auto_wf. 
       rewrite big_sum_kron.
       rewrite Vec_decom with v.
       rewrite Nat.pow_add_r.
       apply big_sum_eq_bounded.
       intros. 
       rewrite Mscale_kron_dist_l.
       rewrite Mscale_kron_dist_r.
       rewrite Mscale_assoc.
       rewrite <-H0.
       f_equal. 
       rewrite <-pow_add_r.
       rewrite Vec_kron.
       reflexivity. 
       rewrite pow_add_r. assumption.
       assumption.
       assert(2^n >0).
       apply pow_gt_0.
       intuition.   
Qed.


Lemma  outer_product_eq': forall m (φ ψ : Matrix m 1),
 outer_product φ φ = outer_product ψ ψ -> φ = ψ .
Proof. intros. unfold outer_product in *.
      assert(φ × ((φ) †  ×  ψ) = ψ × ((ψ) † × ψ)).
      repeat rewrite <-Mmult_assoc.
      rewrite H. reflexivity. 
Admitted.

Lemma big_sum_par: forall m n j  a b(f: nat-> Matrix a b),
j<n ->
(forall i :nat, j<> (i mod n) -> f i = Zero)->
big_sum f (m * n) = big_sum (fun i=> f (i * n +j)) m .
Proof. induction m; intros; simpl. reflexivity.
       rewrite add_comm.
       rewrite big_sum_sum'.
       rewrite (IHm _ j _ _ _ ).
       f_equal.
       apply big_sum_unique.
       exists j. split. assumption.
       split. reflexivity.
       intros. 
       rewrite H0. reflexivity.
       rewrite add_comm.
       rewrite mod_add.
       rewrite mod_small.
       assumption. assumption.
       lia. assumption.
       assumption.
Qed.

Lemma Vec_linear{ n:nat}: forall (v1 v2 :Vector n) p,
v1= p .* v2 ->
(forall i, (v1 i 0) = Cmult p  (v2 i 0)).
Proof. intros. rewrite H. unfold scale.
       reflexivity.
Qed.

(* Lemma Vec_linear_exsist{ n:nat}: forall (v1 v2 :Vector n) ,
(exists p, v1= p .* v2) ->
exists p, (forall i, (v1 i 0) = Cmult p  (v2 i 0)).
Proof. intros. destruct H. rewrite H. exists x.
       intros. unfold scale.
       reflexivity.
Qed. *)


Definition Par_Pure_State { n:nat}(q:Square n): Prop :=
exists (p:R) (q': Square n), and (0<p<=1)%R  (Pure_State q' /\ q= p .* q').



Lemma  trace_I: trace (I 1) = C1.
Proof. unfold trace. simpl.  
      unfold I. simpl. rewrite Cplus_0_l.
      reflexivity.
       
Qed.


Lemma Mixed_pure: forall {n:nat} (ρ1 ρ2: Density n) (φ:Vector n), 
Mixed_State ρ1 ->
Mixed_State ρ2 ->
Pure_State_Vector φ ->
ρ1 .+  ρ2= φ  × φ†->  exists (p1 p2:R), 
and (and (0<p1<=1)%R (0<p2<=1)%R)
  (and (ρ1= p1 .* ( φ  × φ† )) (ρ2= p2 .* ( φ  × φ† ))).
Proof. intros. 
    assert(fst (trace ρ1) .* ((1 / fst (trace ρ1))%R.* ρ1) =ρ1).
    rewrite Mscale_assoc. rewrite Rdiv_unfold.
    rewrite Rmult_1_l. rewrite RtoC_mult.
    rewrite Rinv_r. rewrite Mscale_1_l. reflexivity.
    assert(fst (trace ρ1) > 0%R)%R. 
    apply mixed_state_trace_gt0. assumption.
    lra. 
   rewrite <-H3 in *.
    assert(fst (trace ρ2) .* ((1 / fst (trace ρ2))%R.* ρ2) =ρ2).
    rewrite Mscale_assoc. rewrite Rdiv_unfold.
    rewrite Rmult_1_l. rewrite RtoC_mult.
    rewrite Rinv_r. rewrite Mscale_1_l. reflexivity.
    assert(fst (trace ρ2) > 0%R)%R. 
    apply mixed_state_trace_gt0. assumption.
    lra.  rewrite <-H4 in *.
    remember (((1 / fst (trace ρ1))%R .* ρ1)).
    remember (((1 / fst (trace ρ2))%R .* ρ2)).
    assert(m = m0 \/ m <>  m0).
    apply Classical_Prop.classic.
    destruct H5. destruct H5. 
    rewrite <-Mscale_plus_distr_l in H2.
    rewrite <-RtoC_plus in H2.
    remember ((fst (trace ρ1) + fst (trace ρ2))%R ).
    rewrite <-H2.
    exists (fst (trace ρ1) / r)%R.
    exists (fst (trace ρ2) /r)%R.
    split. rewrite Heqr. 
    split.   admit. admit.
    repeat rewrite Rdiv_unfold.  
    repeat rewrite Mscale_assoc.
    repeat rewrite RtoC_mult.
    repeat rewrite Rmult_assoc.
    repeat rewrite Rinv_l. repeat rewrite Rmult_1_r.
    intuition. rewrite Heqr.
    assert((fst (trace ρ1)%R>0)%R). apply mixed_state_trace_gt0.
    rewrite<-H3. intuition.
    assert(fst (trace ρ2)>0)%R. apply mixed_state_trace_gt0.
    rewrite<-H4. intuition.
    assert(fst (trace ρ1) + fst (trace ρ2)>0)%R.
    apply Rplus_lt_0_compat; intuition.
    unfold not. intros. rewrite H8 in H7.
     lra.
    assert(fst (trace (Mmult (fst (trace ρ1) .* m .+ fst (trace ρ2) .* m0)  (fst (trace ρ1) .* m .+ fst (trace ρ2) .* m0)))<1)%R.
    apply Mixed_sqrt_trace. econstructor.
    apply mixed_state_trace_in01. rewrite<-H3. intuition.
    apply mixed_state_trace_in01. rewrite<-H4. intuition.
    rewrite <-mixed_state_fst_plus_aux.
    apply mixed_state_trace_in01. 
    rewrite <-H3. rewrite<-H4.
    rewrite H2. 
    assert(φ × (φ) † = R1 .* (φ × (φ) †)).
    rewrite Mscale_1_l. reflexivity.
    rewrite H6. apply Pure_S. lra. 
    econstructor . split. apply H1.
    reflexivity.
    apply Mixed_State_aux_to_Mix_State. 
    rewrite <-H3. assumption.
    apply Mixed_State_aux_to_Mix_State. 
    rewrite <-H4. assumption.
     rewrite Heqm.  
   admit. admit.
     assumption.
    assert(trace (Mmult (φ  × φ†)  (φ  × φ†))=C1).
    apply Pure_sqrt_trace. econstructor.
    split. apply H1. reflexivity. 
    assert (fst (trace (Mmult (fst (trace ρ1) .* m  .+ fst (trace ρ2) .* m0) (fst (trace ρ1) .* m  .+ fst (trace ρ2) .* m0)))=
             fst (trace (Mmult (φ  × φ†)  (φ  × φ†)))).
    rewrite H2. reflexivity.
    rewrite H7  in H8. 
    simpl in H8. lra.
Admitted.

Lemma Mixed_pure': forall {n:nat} (ρ1 ρ2: Density n) (φ:Vector n), 
Mixed_State ρ1 ->
Mixed_State ρ2 ->
Pure_State_Vector φ ->
(exists p, and (0<p<=1)%R (ρ1 .+  ρ2= p .* (φ  × φ†)))
->  exists (p1 p2:R), 
and (and (0<p1<=1)%R (0<p2<=1)%R)
  (and (ρ1= p1 .* ( φ  × φ† )) (ρ2= p2 .* ( φ  × φ† ))).
Proof. intros. destruct H2. destruct H2.
       assert(/x .* ρ1 .+ /x .* ρ2  = (φ × (φ) †)).
       rewrite <-Mscale_plus_distr_r.
       rewrite H3.
       rewrite Mscale_assoc.
       rewrite Cinv_l.
       rewrite Mscale_1_l.
       reflexivity.
       assert(x >0)%R. intuition. 
       unfold not. intros. 
       injection H5. intros.
      rewrite H6 in H4.

       lra. 
      apply Mixed_pure in H4.
      destruct H4. destruct H4.
      destruct H4. destruct H5.
      exists (x*x0)%R.
      exists (x*x1)%R.
      split. admit.
       repeat rewrite <-RtoC_mult.
       repeat rewrite <-Mscale_assoc.
       rewrite <-H5. rewrite <-H6.
       repeat rewrite Mscale_assoc.
       repeat rewrite Cinv_r.
       repeat rewrite Mscale_1_l.
      intuition. 
      assert(x >0)%R. intuition. 
      unfold not. intros. 
      injection H8. intros. lra. 
       
       admit.
       admit.
       assumption.
Admitted.




Lemma Mixed_pure_sum: forall {n:nat} (f: nat-> Density n) m 
(φ : Vector n), 
Pure_State_Vector φ ->
(forall i, (Mixed_State (f i))) ->
(exists p, and (0<p<=1)%R  ((big_sum f m) = p .* (φ  × φ†) ))->
(forall i, i<m -> 
exists p, and (0<p<=1)%R  ( (f i)= p .* (φ  × φ†))).
Proof. induction m; intros.
       simpl in *. destruct H1.
       destruct H1. 
       assert(@trace n Zero = trace (x .* (φ × (φ) †))).
       rewrite H3. reflexivity.
       rewrite Zero_trace in H4.
       rewrite trace_mult_dist in H4.
       destruct H.  rewrite trace_mult' in H4.
       rewrite H5 in H4. rewrite trace_I in H4.
       rewrite Cmult_1_r in H4.
       injection H4. intros. lra. 
       simpl in *.
       apply (Mixed_pure' (big_sum f m) ) in H1.
       destruct H1. destruct H1.
       assert(i=m \/ i<>m).
       apply Classical_Prop.classic.
       destruct H3.
       rewrite H3.
       exists x0. intuition.
       apply IHm.
       assumption.
       assumption.
       exists x. intuition. lia.
       apply Mixed_State_aux_to_Mix_State.
       split.
       admit. admit.
       apply H0.
       assumption.
Admitted.

Lemma Mixed_State_eq{n : nat}:  forall (q1 q2 : Square (2 ^ n)),
q1 = q2 -> Mixed_State q1 -> Mixed_State q2 .
Proof. intros. subst. intuition.
    
Qed.


Lemma Odot_Sepear{ s x e:nat}: forall (q: qstate s e),
s<=x/\x<=e ->
@Mixed_State (2^(e-s)) q->
@Par_Pure_State (2^(x-s)) (PMpar_trace q s x)->
exists (q1:qstate s x) (q2: qstate x e), 
and (@WF_Matrix  (2^(x-s))  (2^(x-s)) q1 /\ @WF_Matrix (2^(e-x))  (2^(e-x)) q2) 
(q = @kron (2^(x-s)) (2^(x-s)) (2^(e-x))  (2^(e-x)) q1 q2).
Proof. intros q Hs.
     unfold Par_Pure_State in *. intros.
       destruct H0. destruct H0.
       destruct H0. destruct H1.
       destruct H1. destruct H1.
       rewrite H3 in *. 
       rewrite PMpar_trace_L in *.
       induction H. destruct H4.
       destruct H4. subst.
       rewrite <-L_trace_scale in *.
       assert(p=x0).

       admit. subst.
       assert(((/x0)* x0)%R .* PMLpar_trace (x3 × (x3) †) x 
       = ((/x0)* x0)%R .* (x2 × (x2) †)).
       rewrite <-RtoC_mult. repeat rewrite <-Mscale_assoc.
       rewrite H2. reflexivity.
       rewrite Rinv_l in H3. 
       rewrite Mscale_1_l in H3.
       unfold PMLpar_trace in H3.
       assert(forall i : nat, i< (2 ^ (e - x)) ->
       exists p, and (0<p<=1)%R ((I (2 ^ (x - s)) ⊗ ⟨ i ∣_ (e - x) × (x3 × (x3) †)
       × (I (2 ^ (x - s)) ⊗ ∣ i ⟩_ (e - x))) =
       p .* ( x2 × (x2) †))).
       rewrite mul_1_r.
       apply Mixed_pure_sum. 
       assumption. 
       intros.
       admit. rewrite Mscale_1_l in H3.
       exists 1%R. 
       split. intuition. 
       rewrite Mscale_1_l.  
       assumption.
       assert(forall i : nat,i< (2 ^ (e - x))-> 
       exists p : R, 
         (and (0 < p <= 1)%R 
          (@Mmult _ (2^(x-s) * 2^(e-x)) 1 (I (2 ^ (x - s)) ⊗ ⟨ i ∣_ (e - x))  x3
         = sqrt p .* x2))).
       intros.
       pose (H5 i).
       destruct e0. assumption.  
       exists x1. 
       split. intuition. 
       apply outer_product_eq'.
       unfold outer_product.
       rewrite Mmult_adjoint.
       rewrite kron_adjoint.
       rewrite id_adjoint_eq.
       rewrite adjoint_involutive.
       rewrite <-Mmult_assoc.
       rewrite mul_1_r.
       rewrite Mscale_adj.
        rewrite Mscale_mult_dist_r.
       rewrite Mscale_mult_dist_l.
       rewrite Mscale_assoc.
       rewrite Cconj_R. 
       rewrite RtoC_mult.
       rewrite sqrt_sqrt.
       assert(2^(x-s) * 2^(e-x) = 2^(e-s)).
       type_sovle'. destruct H8.
       rewrite (Mmult_assoc _ x3).
       destruct H7.
       rewrite <-H8.
       f_equal; lia. lra.
       assert(forall i : nat, (i<(2^(e-x)))->
       exists p : R,
         (and (0 < p <= 1)%R 
          (big_sum (fun r=> (x3 (r*(2^(e-x))+ i)%nat 0) .* (Vec (2^(x-s)) r) ) (2^(x-s))= √ p .* x2))%type).
       intros. 
       pose (H6 i).
       destruct e0. assumption.
       destruct H8.
       exists x1.
       split. intuition.
       rewrite Vec_decom with x3 in H9.
       assert( 2^(e-s)=2^(x-s) * 2^(e-x)).
       type_sovle'. destruct H10.
       rewrite Mmult_Msum_distr_l in H9.
       rewrite (big_sum_eq_bounded _ (
              (fun i0 : nat =>
       (x3 i0 0) .*
       ( (∣ i0/(2^(e-x))  ⟩_ (x - s)) ⊗ 
        (⟨ i ∣_ (e - x) × ( ∣ i0 mod (2^(e-x))  ⟩_ (e - x)))) )))
        in H9.
        rewrite <-H9.
        assert( 2^(x-s) * 2^(e-x)= 2^(e-s)).
        type_sovle'. destruct H10.
        rewrite (big_sum_par  _ _ i).
        apply big_sum_eq_bounded.
        intros. f_equal.
        lia. 
        assert((x4 * 2 ^ (e - x) + i) / 2 ^ (e - x) = x4).
        rewrite add_comm.
        rewrite div_add. 
         rewrite div_small.
         rewrite add_0_l. reflexivity.
         assumption. apply Nat.pow_nonzero.
         lia. 
        assert((x4 * 2 ^ (e - x) + i) mod 2 ^ (e - x)= i).
        rewrite add_comm.
        rewrite mod_add. 
        rewrite mod_small.
        reflexivity.
        assumption. 
        apply Nat.pow_nonzero.
        lia.
        rewrite H11. rewrite H12. rewrite Vec_inner_1.
        rewrite kron_1_r. reflexivity.
        assumption. assumption.
        intros. rewrite Vec_inner_0.
        rewrite Mscale_0_l. rewrite kron_0_r.
        rewrite Mscale_0_r. reflexivity. assumption.
        assumption.
        apply mod_bound_pos.
        lia. apply pow_gt_0.  
       intros.
        rewrite Mscale_mult_dist_r.
        f_equal.
       assert(((x-s)+ (e-x) )=(e-s)).
       lia. destruct H11.
       rewrite <-Vec_kron.
       remember (I (2 ^ (x - s)) ⊗ ⟨ i ∣_ (e - x)).
       remember ((∣ x4 / 2 ^ (e - x) ⟩_ (x - s)
       ⊗ ∣ x4 mod 2 ^ (e - x) ⟩_ (e - x))).
       assert((@Mmult
       (Init.Nat.mul (Nat.pow (S (S O)) (sub x s)) (S O))
       (Nat.pow (S (S O)) (add (sub x s) (sub e x))) 
       (S O) m m0) = m × m0).
      f_equal; type_sovle'.
      rewrite H11.  rewrite Heqm. rewrite Heqm0.
       rewrite kron_mixed_product.
       rewrite Mmult_1_l; auto_wf. reflexivity.
       apply WF_vec.
       apply div_lt_upper_bound.
       apply Nat.pow_nonzero.
       lia. 
       assert(2 ^ (e - x) * 2 ^ (x - s) = 2^(x - s + (e - x))).
       type_sovle'. rewrite H12. 
       assumption.   destruct H4. assumption.
       assert(forall k, (k<(2^(e-x)))-> (exists lamda, forall j, 
       j < 2 ^ (x - s) ->
       (x3 (j * (2^(e-x)) + k) 0) = Cmult lamda (x3 (j * (2^(e-x))) 0))).
       intros.
       assert( 0 < 2 ^ (e - x)). apply pow_gt_0.
       pose (H7 k H8). 
       pose (H7 0 H9 ).
       destruct e0. destruct H10.
       destruct e1. destruct H12.
       exists (sqrt x1/ sqrt x4)%R. intros.
       remember (big_sum
       (fun r : nat =>
        x3 (r * 2 ^ (e - x) + k) 0
        .* ∣ r ⟩_ (x - s)) (2 ^ (x - s))).
        remember (big_sum
        (fun r : nat =>
         x3 (r * 2 ^ (e - x) + 0) 0
         .* ∣ r ⟩_ (x - s)) (2 ^ (x - s))).
       assert(  m j 0 = ((√ x1 / √ x4)%R  * m0 j 0)%C).
       apply (Vec_linear ).
       rewrite H11. rewrite H13. rewrite Mscale_assoc.
       rewrite RtoC_div. rewrite Cdiv_unfold. 
       rewrite <-Cmult_assoc. rewrite Cinv_l.
       rewrite Cmult_1_r. reflexivity.
       unfold not. intros. injection H15.
       intros. apply sqrt_eq_0 in H16. lra. lra.
       apply sqrt_neq_0_compat. lra.
       subst.
       repeat rewrite Msum_Csum in *.
        rewrite (big_sum_unique  (x3 (j * 2 ^ (e - x) + k) 0)) in H15.
        rewrite (big_sum_unique  (x3 (j * 2 ^ (e - x) ) 0)) in H15 .
        assumption. 
        exists j. split. assumption. 
        split. unfold scale. rewrite Vec0.
        rewrite Cmult_1_r. rewrite add_0_r.
        reflexivity. reflexivity. 
        intros. unfold scale. rewrite Vec1.
        rewrite Cmult_0_r. reflexivity.
        assumption.
        exists j. split. assumption.
        split. unfold scale. rewrite Vec0.
        rewrite Cmult_1_r. 
        reflexivity. reflexivity. 
        intros. unfold scale. rewrite Vec1.
        rewrite Cmult_0_r. reflexivity.
        assumption.
        
       assert(exists (v1 : Vector (2^(x-s))) (v2 : Vector (2^(e-x))),
       and (WF_Matrix v1 /\ WF_Matrix v2) 
        (kron  v1 v2 = x3)).
       apply Separ.  destruct H4. 
       assert(e-s= x - s + (e - x)).
       lia. destruct H10.  apply H4. 
       exists (fun i=> (x3 (i * 2 ^ (e - x)) 0)).
       assert(x3 0 0 = 0%R \/ x3 0 0 <> 0%R).
       apply Classical_Prop.classic.
       destruct H9.
       admit.
       exists (fun i=> Cdiv (x3 i 0) (x3 0 0)).
       intros.
       remember (z mod 2 ^ (e - x)).
       assert( exists j, z = j * 2 ^ (e - x) + n).
       exists (z/(2^(e-x))).
       rewrite Heqn. rewrite Nat.mul_comm.
       apply div_mod_eq. 
        destruct H11.
       assert(z / 2 ^ (e - x) = x1).
       rewrite H11. rewrite Heqn. 
       symmetry. rewrite add_comm.  rewrite div_add.
       rewrite div_small. rewrite add_0_l.
       reflexivity. 
       apply mod_bound_pos. lia.
       apply pow_gt_0. 
       apply Nat.pow_nonzero. lia.   rewrite H12.
       rewrite H11.
       assert(n < 2 ^ (e - x)).
       rewrite H11 in H12.
       rewrite add_comm in H12.
       rewrite div_add in H12.
       assert(n / 2 ^ (e - x) + x1 - x1 = x1 -x1).
       rewrite H12. reflexivity.
       rewrite Nat.sub_diag in H13.
        rewrite add_sub in H13.
        apply div_small_iff. apply Nat.pow_nonzero.
        lia. assumption. apply Nat.pow_nonzero. lia.  
      pose (H8 n H13).
      destruct e0. 
      rewrite H14.
      assert(0 < 2 ^ (x - s) ).
      apply pow_gt_0.
      pose (H14 0 H15).
      rewrite mul_0_l in e0. 
      rewrite add_0_l in e0. 
      rewrite e0.
      rewrite Cdiv_unfold.
      rewrite <-Cmult_assoc. 
      rewrite Cinv_r. 
      rewrite Cmult_1_r.
      rewrite Cmult_comm. reflexivity.
      assumption.
       rewrite <-H12.   
       apply div_lt_upper_bound. 
       apply Nat.pow_nonzero. lia.
       rewrite <-pow_add_r.
       rewrite add_comm. 
       assumption. 
       destruct H9.
       destruct H9.
       destruct H9.
       rewrite <-H10.
       exists (sqrt x0 .*  (x1 × (x1 ) †)).
       exists (sqrt x0 .*  (x4 × (x4 ) †)).
       rewrite Mscale_kron_dist_l.
       rewrite Mscale_kron_dist_r.
       rewrite Mscale_assoc.
       rewrite RtoC_mult.
       rewrite sqrt_sqrt.
       assert( 2 ^ (x - s) * 2 ^ (e - x) = 2 ^ (e - s) ).
       type_sovle'. destruct H11.
       f_equal. 
       rewrite <-kron_mixed_product.
       f_equal. rewrite <-kron_adjoint.
       split. split. apply WF_scale. 
       apply WF_mult. intuition. 
       apply WF_adjoint. intuition.
       apply WF_scale. 
       apply WF_mult. intuition.
       apply WF_adjoint. intuition.

       f_equal. lra. lra. 
       rewrite  L_trace_plus  in *.
       admit.
       lia. apply WF_Mixed. assumption.  
Admitted.

Lemma big_sum_mult_l_C: forall (c: C) (f: nat-> C) n, 
    (c * big_sum f n)%C = big_sum (fun x => (c * f x)%C) n.
Proof.
  intros.
  induction n.
  + simpl; apply Cmult_0_r.
  + simpl.
    rewrite Cmult_plus_distr_l. 
    rewrite IHn.
    reflexivity.
Qed.

Lemma big_sum_sum_C : forall m n (f: nat->C), 
  big_sum f (m + n) = (big_sum f m + big_sum (fun x => f (m + x)%nat) n)%C.
Proof. intros. rewrite big_sum_sum.
      reflexivity. 
Qed.

Lemma big_sum_product_C: forall m n (f g:nat-> C), 
  n <> O ->
  (big_sum f m * big_sum g n)%C = big_sum (fun x => (f (x / n)%nat * g (x mod n)%nat))%C (m * n). 
Proof.
  intros.
  induction m; simpl. 
  + rewrite Cmult_0_l; reflexivity. 
  + rewrite Cmult_plus_distr_r.
    rewrite IHm. clear IHm.
    rewrite big_sum_mult_l_C.
    remember ((fun x : nat => (f (x / n)%nat * g (x mod n)%nat))%C) as h.
    replace (big_sum (fun x : nat => (f m * g x)%C) n) with
            (big_sum (fun x : nat => h ((m * n) + x)%nat) n). 
    2:{
      subst.
      apply big_sum_eq_bounded.
      intros x Hx.
      rewrite Nat.div_add_l by assumption.
      rewrite Nat.div_small; trivial.
      rewrite Nat.add_0_r.
      rewrite Nat.add_mod by assumption.
      rewrite Nat.mod_mul by assumption.
      rewrite Nat.add_0_l.
      repeat rewrite Nat.mod_small; trivial. }
    rewrite <- big_sum_sum_C.
    rewrite Nat.add_comm.
    reflexivity.
Qed. 


Lemma trace_kron{m n}: forall (q1:Square m) (q2:Square n),
n<>0->
trace  (kron q1 q2)= (trace  (q1) * trace  q2)%C.
Proof. intros. unfold trace.
        rewrite big_sum_product_C.
        unfold kron. apply big_sum_eq_bounded.
        intros. reflexivity. assumption.  
Qed.

Lemma Odot_Sepear'{ s x e:nat}: forall (q: qstate s e),
s<=x/\x<=e ->
@Mixed_State (2^(e-s)) q->
@Par_Pure_State (2^(x-s)) (PMpar_trace q s x)->
@trace (2^(e-s)) (q) .* q = @kron (2^(x-s)) (2^(x-s)) (2^(e-x))  (2^(e-x)) (PMpar_trace q s x) 
(PMpar_trace q x e).
Proof. intros. apply (Odot_Sepear q H H0) in H1.
       destruct H1. destruct H1. 
       destruct H1. 
       pose H2. pose H2.
       apply PMpar_trace_l in e0.
       rewrite PMpar_trace_L. 
       rewrite e0. 
       apply PMpar_trace_r in e1.
       rewrite PMpar_trace_R.
       rewrite e1. 
       rewrite Mscale_kron_dist_l.
       rewrite Mscale_kron_dist_r.
       rewrite Mscale_assoc.
       rewrite H2. f_equal.
       
       assert(2^(x-s)*2^(e-x)= 2^(e-s))%nat.
       type_sovle'. destruct H3.
       rewrite Cmult_comm.
       apply trace_kron. apply Nat.pow_nonzero. lia. reflexivity.
       apply WF_Mixed. assumption.
       intuition. intuition.
       apply WF_Mixed. assumption.
       intuition.
       apply WF_Mixed. assumption.
       intuition. intuition.
       apply WF_Mixed. assumption.
Qed.

Lemma  Mixed_State_aux_to01':forall {n} (ρ : Density n),
Mixed_State_aux ρ ->
Mixed_State (( / (trace ρ))%C .* ρ) .
Proof. intros.  
       assert(trace ρ= ((fst (trace ρ)), snd (trace ρ))).
    destruct (trace ρ). reflexivity.
    rewrite H0. 
    assert(/ (fst (trace ρ), snd (trace ρ)) 
    = ((1 / (Cmod (trace ρ )))%R, 0%R) ).
     rewrite Cmod_snd_0. rewrite mixed_state_trace_real_aux.
     rewrite Rdiv_unfold. rewrite Rmult_1_l.
     assert(((/ fst (trace ρ))%R, 0%R) = RtoC ((/ fst (trace ρ))%R)).
     reflexivity. rewrite H1.
     rewrite RtoC_inv. f_equal.
     assert((0 < fst (trace ρ))%R).
     apply mixed_state_trace_gt0_aux.
     assumption. lra. 
     assumption.
     apply mixed_state_trace_gt0_aux.
     assumption. apply mixed_state_trace_real_aux.
     assumption. 
     rewrite H1. apply Mixed_State_aux_to01.
     assumption.
Qed. 

     


Lemma WF_qstate_to01{ s e:nat}: forall (q: qstate s e),
WF_qstate q ->
@WF_qstate  s e (/@trace (2^(e-s)) q .* q).
Proof. intros. unfold WF_qstate in *.
      split. apply Mixed_State_aux_to01'.
      apply Mixed_State_aux_to_Mix_State.
      intuition. intuition.
Qed.


Lemma Odot_Sepear''{ s x e:nat}: forall (q: qstate s e),
s<=x/\x<=e ->
@Mixed_State (2^(e-s)) q->
@Par_Pure_State (2^(x-s)) (PMpar_trace q s x)->
exists (q1:qstate s x) (q2: qstate x e), 
and (@WF_qstate  s x q1 /\ @WF_qstate x e q2) 
(q = @kron (2^(x-s)) (2^(x-s)) (2^(e-x))  (2^(e-x)) q1 q2).
Proof. intros. assert(@trace (2^(e-s)) (q) .* q = @kron (2^(x-s)) (2^(x-s)) (2^(e-x))  (2^(e-x)) (PMpar_trace q s x) 
(PMpar_trace q x e)).
apply Odot_Sepear'. assumption. assumption. assumption.
exists (/(@trace (2^(e-s)) q) .* (PMpar_trace q s x)).
exists (PMpar_trace q x e).
split. split. rewrite <-(Ptrace_trace _ _ _ s x).
apply WF_qstate_to01. 
apply WF_par_trace.  intuition.
unfold WF_qstate. split.  apply H0.
intuition. intuition. 
apply WF_Mixed. assumption.
apply (WF_par_trace s e x e q).
intuition. unfold WF_qstate. split.  apply H0.
intuition. 
rewrite Mscale_kron_dist_l.
rewrite <-H2. rewrite Mscale_assoc.
rewrite Cinv_l. rewrite Mscale_1_l.
reflexivity.
assert(@trace (2^(e-s)) q= ((fst (@trace (2^(e-s)) q)), snd (@trace  (2^(e-s)) q))).
    destruct (@trace (2^(e-s)) q ). reflexivity.
    rewrite H3.
unfold not. intros.
injection H4.
intros. 
assert(fst (@trace (2^(e-s)) q) > 0%R)%R.
apply mixed_state_trace_gt0.
assumption. lra.
Qed.



(*--------------------------------------------*)

Inductive q_combin'{s0 e0 s1 e1 s2 e2}: (qstate s0 e0) -> (qstate s1 e1)-> (qstate s2 e2)->Prop:=
|q_combin'': forall q0 q1, e0 = s1-> s0 = s2 -> e1 = e2 -> WF_qstate q0 ->
             WF_qstate q1->
            q_combin' q0 q1 (@kron (2^(e0-s0)) (2^(e0-s0)) (2^(e1-s1))  
            (2^(e1-s1)) q0 q1).

Inductive dstate_Separ{ s e: nat}: (list (cstate *qstate s e)) -> nat -> nat -> nat-> nat-> Prop :=
|dstate_Separ_nil: forall s0 e0 s1 e1, dstate_Separ nil s0 e0 s1 e1
|dstate_Separ_cons: forall s0 e0 s1 e1 c q mu' (q0_i: nat->qstate s0 e0) (q1_i:nat-> qstate s1 e1) n, 
                    e0 = s1-> s0 = s -> e1 = e ->
  (forall i, (WF_qstate (q0_i i))) ->
(forall i, (WF_qstate (q1_i i)))->
(q= big_sum (fun i=>@kron (2^(e0-s0)) (2^(e0-s0))  (2^(e1-s1)) (2^(e1-s1)) (q0_i i ) (q1_i i)) n)->
dstate_Separ mu' s0 e0 s1 e1->
dstate_Separ ((c,q)::mu') s0 e0 s1 e1.
(* Fixpoint dstate_Separ{ s e:nat}   (mu : list (cstate *qstate s e)) 
s0 e0 s1 e1: Prop:=
match mu with 
| nil => True 
|(c, q) :: mu' => 
(exists (q0_i: nat->qstate s0 e0) (q1_i:nat-> qstate s1 e1) n, 
and ((forall i, (WF_qstate (q0_i i))) /\
(forall i, (WF_qstate (q1_i i))))
(q= big_sum (fun i=>@kron (2^(e0-s0)) (2^(e0-s0))  (2^(e1-s1)) (2^(e1-s1)) (q0_i i ) (q1_i i)) n))
 /\ dstate_Separ mu' s0 e0 s1 e1
 end.  *)


Fixpoint dstate_qstate_eq {s e:nat} (mu1 mu2: list(cstate * qstate s e)):=
match mu1, mu2 with 
| nil , nil => True
|(c1,q1)::mu'1 , (c2,q2)::mu'2 => and (q1=q2) (dstate_qstate_eq mu'1 mu'2)
| _, _ => False 
end.


Fixpoint Considered_QExp (qs:QExp) : Prop :=
  match qs with 
  |QExp_s s e v => s<=e  
  |QExp_t qs1 qs2 => Considered_QExp qs1 /\ Considered_QExp qs2 /\ 
                    (((snd (Free_QExp' qs1))=(fst (Free_QExp' qs2)))
                    \/ ((snd (Free_QExp' qs2))=(fst (Free_QExp' qs1))))
  end.

Fixpoint Considered_Formula (F:State_formula) : Prop:=
  match F with
  | SPure P => True 
  | SQuan s => Considered_QExp s
  | SOdot F1 F2 => Considered_Formula F1 /\ Considered_Formula F2 
                   /\ (((snd (Free_State F1))=(fst (Free_State F2)))
                   \/ ((snd (Free_State F2))=(fst (Free_State F1))))
  |SAnd F1 F2 => Considered_Formula F1 /\ Considered_Formula F2 
                  /\  ((((fst (Free_State F1))=(fst (Free_State F2)))/\
                        ((snd (Free_State F1))=(snd (Free_State F2))))
                        \/ ((snd (Free_State F1))=(fst (Free_State F2))) 
                        \/ (((snd (Free_State F2))=(fst (Free_State F1)))))
  end. 

  

Lemma Considered_QExp_dom: forall qs,
Considered_QExp qs ->
fst (Free_QExp' qs) <=  snd (Free_QExp' qs) .
Proof. induction qs; 
simpl. intuition.
simpl; intros.
destruct H. 
destruct H0.
destruct H1.

apply IHqs1  in H.
apply IHqs2 in H0.
assert(min (fst (Free_QExp' qs1))
(fst (Free_QExp' qs2))=(fst (Free_QExp' qs1))/\
max (snd (Free_QExp' qs1))
  (snd (Free_QExp' qs2))=(snd (Free_QExp' qs2))).
apply min_le. intuition.
destruct H2. rewrite H2. rewrite H3.
apply le_trans with  (snd (Free_QExp' qs1)).
assumption. rewrite H1.
assumption.

apply IHqs1  in H.
apply IHqs2 in H0.
rewrite min_comm.
rewrite max_comm.
assert(min (fst (Free_QExp' qs2))
(fst (Free_QExp' qs1))=(fst (Free_QExp' qs2))/\
max (snd (Free_QExp' qs2))
  (snd (Free_QExp' qs1))=(snd (Free_QExp' qs1))).
apply min_le. intuition.
destruct H2. rewrite H2. rewrite H3.
apply le_trans with  (snd (Free_QExp' qs2)).
assumption. rewrite H1.
assumption.
Qed.



Lemma Considered_Formula_dom: forall F,
Considered_Formula F ->
fst (Free_State F) <=  snd (Free_State F) .
Proof. induction F; intros.
       simpl. intuition.
       apply Considered_QExp_dom. 
       assumption.

       simpl in H. 
       destruct H.
       destruct H0.
       destruct H1.
       
simpl.
apply IHF1  in H.
apply IHF2 in H0.
assert(min (fst (Free_State F1))
(fst (Free_State F2))=(fst (Free_State F1))/\
max (snd (Free_State F1))
  (snd (Free_State F2))=(snd (Free_State F2))).
apply min_le. intuition.
destruct H2. rewrite H2. rewrite H3.
apply le_trans with  (snd (Free_State F1)).
assumption. rewrite H1.
assumption.

simpl.
apply IHF1  in H.
apply IHF2 in H0.
rewrite min_comm.
rewrite max_comm.
assert(min (fst (Free_State F2))
(fst (Free_State F1))=(fst (Free_State F2))/\
max (snd (Free_State F2))
  (snd (Free_State F1))=(snd (Free_State F1))).
apply min_le. intuition.
destruct H2. rewrite H2. rewrite H3.
apply le_trans with  (snd (Free_State F2)).
assumption. rewrite H1.
assumption.

simpl in H. 
destruct H.
destruct H0.
destruct H1.

simpl.
apply IHF1  in H.
apply IHF2 in H0.
destruct H1. rewrite H1. rewrite H2.
rewrite min_id.
rewrite max_id. intuition.

destruct H1.

simpl.
apply IHF1  in H.
apply IHF2 in H0.
assert(min (fst (Free_State F1))
(fst (Free_State F2))=(fst (Free_State F1))/\
max (snd (Free_State F1))
  (snd (Free_State F2))=(snd (Free_State F2))).
apply min_le. intuition.
destruct H2. rewrite H2. rewrite H3.
apply le_trans with  (snd (Free_State F1)).
assumption. rewrite H1.
assumption.


simpl.
apply IHF1  in H.
apply IHF2 in H0.
rewrite min_comm.
rewrite max_comm.
assert(min (fst (Free_State F2))
(fst (Free_State F1))=(fst (Free_State F2))/\
max (snd (Free_State F2))
(snd (Free_State F1))=(snd (Free_State F1))).
apply min_le. intuition.
destruct H2. rewrite H2. rewrite H3.
apply le_trans with  (snd (Free_State F2)).
assumption. rewrite H1.
assumption. 
Qed.




Lemma Par_Pure_State_wedge{ s e: nat}:forall (q:qstate s e) s' x' e',
s<=s'/\ s'<=x'/\ x'<=e' /\ e'<= e ->
WF_qstate q->
@Par_Pure_State (2^(x'-s')) (PMpar_trace q s' x')->
@Par_Pure_State (2^(e'-x')) (PMpar_trace q x' e')->
@Par_Pure_State (2^(e'-s')) (PMpar_trace q s' e').
Proof. intros.
assert((PMpar_trace q s' x') = 
PMpar_trace (PMpar_trace q s' e') s' x').
rewrite  PMpar_trace_assoc.
reflexivity. intuition.
rewrite H3 in H1. 
assert((PMpar_trace q x' e') =
PMpar_trace (PMpar_trace q s' e') x' e'). 
rewrite PMpar_trace_assoc.
reflexivity. intuition.
rewrite H4 in H2. 
remember ((PMpar_trace q s' e')).
assert(@trace (2^(e'-s')) (q0) .* q0 =@kron (2^(x'-s')) (2^(x'-s')) 
(2^(e'-x'))  (2^(e'-x')) (PMpar_trace q0 s' x') (PMpar_trace q0 x' e') ).
apply Odot_Sepear'. intuition.
rewrite Heqq0.
apply WF_par_trace. intuition.
assumption.
assumption. 

unfold Par_Pure_State in *.
destruct H1. destruct H1. destruct H1.
destruct H6. destruct H6.
destruct H6. rewrite H8 in *.
destruct H2. destruct H2. destruct H2.
destruct H9. destruct H9.
destruct H9. rewrite H11 in *.
exists (x2 )%R.
exists (kron (x1 × (x1) †)  (x4 × (x4) †)).
assert( q0 =(C1 /  ( (@trace (2^(e'-s')) q0)))%C .* (x .* (x1 × (x1) †) ⊗ (x2 .* (x4 × (x4) †)))).
rewrite H7 in H5. rewrite H10 in H5.
rewrite <-H5. rewrite Cdiv_unfold.
rewrite Cmult_1_l. rewrite Mscale_assoc.
rewrite Cinv_l. rewrite Mscale_1_l.
reflexivity.

assert(@trace (2^(e'-s')) q0= ((fst (@trace (2^(e'-s')) q0)), snd (@trace  (2^(e'-s')) q0))).
    destruct (@trace (2^(e'-s')) q0 ). reflexivity.
    rewrite H12.
unfold not. intros.
injection H13.
intros. 
assert(fst (@trace (2^(e'-s')) q0) > 0%R)%R.
apply mixed_state_trace_gt0.
rewrite Heqq0. apply WF_par_trace.
intuition. assumption. lra.
split. assumption. 
split. rewrite <-kron_mixed_product.
rewrite <-kron_adjoint.
unfold Pure_State. exists  (x1 ⊗ x4).
econstructor.
assert((2^(x'-s')) * (2^(e'-x'))= 2 ^ (e' - s')).
type_sovle'. destruct H13. 
 apply pure_state_vector_kron.
 assumption. assumption.
reflexivity.
 rewrite H12.
rewrite Mscale_kron_dist_l.
rewrite Mscale_kron_dist_r.
repeat rewrite Mscale_assoc.
remember ((x1 × (x1) † ⊗ (x4 × (x4) †))).
rewrite Cdiv_unfold. 
rewrite Cmult_1_l.
rewrite <-(Ptrace_trace _ _ _  s' x').
rewrite H7. 
rewrite trace_mult_dist.
assert(trace (x1 × (x1) †)= C1).
rewrite trace_mult'. 
destruct H6. rewrite H13.
rewrite trace_I.
reflexivity. rewrite H13.
rewrite Cmult_1_r.
rewrite <-RtoC_inv.
rewrite RtoC_mult.
rewrite Rinv_l. rewrite Cmult_1_l. reflexivity.
lra. lra.  intuition.
rewrite Heqq0. unfold PMpar_trace.
apply WF_PMRpar_trace. 
intuition. apply WF_PMLpar_trace.
intuition. apply WF_Mixed. apply H0.
Qed.


Lemma QExp_eval_dom{ s e:nat}: forall qs c (q:qstate s e),
QExp_eval qs (c,q) -> s<=fst (Free_QExp' qs) /\ snd (Free_QExp' qs) <=e.
Proof. induction qs; intros.
       simpl in *. intuition.
       simpl in *.
       destruct H. destruct H0.
       apply IHqs1 in H0.
       apply IHqs2 in H1.
       split. 
       apply min_glb.
       intuition. intuition.
       apply max_lub_iff.
       intuition.
Qed.


Lemma State_eval_dom{ s e:nat}: forall F c (q:qstate s e),
State_eval F (c,q) -> s<=fst (Free_State F) /\ snd (Free_State F) <=e.
Proof. induction F; intros.
       simpl in *. admit. 
       simpl in *.
       apply QExp_eval_dom with c q.
       assumption. 
       destruct H. destruct H0.
       apply IHF1 in H0.
       apply IHF2 in H1.
       split. 
       apply min_glb.
       intuition. intuition.
       apply max_lub_iff.
       intuition.
       destruct H.
       apply IHF1 in H.
       apply IHF2 in H0.
       split. 
       apply min_glb.
       intuition. intuition.
       apply max_lub_iff.
       intuition.
Admitted.


Lemma dstate_eval_dom{ s e:nat}: forall F (mu:list (cstate * qstate s e)),
State_eval_dstate F mu  -> s<=fst (Free_State F) /\ snd (Free_State F) <=e.
Proof. induction mu; intros. destruct H.
     inversion H; subst.
     destruct a.
     apply State_eval_dom with c q.
     assumption. 
Qed.


Lemma QExp_eval_pure: forall qs s e c (q: qstate s e) ,
Considered_QExp qs ->
WF_qstate q->
QExp_eval qs (c, q)->
@Par_Pure_State (2^((snd (Free_QExp' qs))- ((fst (Free_QExp' qs)))))
(@PMpar_trace s e q ((fst (Free_QExp' qs))) (((snd (Free_QExp' qs)))) ).
Proof. induction qs; intros. unfold Par_Pure_State. 
       simpl in H1. 
       exists ((Cmod (@trace (2^(e0-s0)) q))%R).
       exists (outer_product v v).
       simpl. 
       rewrite <-PMtrace_scale in H1.
       unfold outer_product in H1.
       destruct H1. destruct H2.
       destruct H3. 
       split. 
       apply mixed_state_Cmod_1.
       apply H0. split. admit.
       unfold outer_product.
       rewrite <-H4.
       rewrite Mscale_assoc.
       rewrite RtoC_mult.
       rewrite Rdiv_unfold.
       rewrite Rmult_1_l.
       rewrite Rinv_r. 
       rewrite Mscale_1_l.
       reflexivity. 
       assert((Cmod (@trace (2^(e0-s0)) q) > 0)%R).
       apply mixed_state_Cmod_1.
       apply H0. lra.

       simpl QExp_eval in H1.  
       destruct H1. 
       destruct H2.
       pose H2 as H2'. pose H3 as H3'.
       apply IHqs1 in H2'.
       apply IHqs2 in H3'.
       simpl in H.
       destruct H.
       destruct H4.
       destruct H5.
       simpl.
       assert(min (fst (Free_QExp' qs1))
       (fst (Free_QExp' qs2))=(fst (Free_QExp' qs1))/\
       max (snd (Free_QExp' qs1))
         (snd (Free_QExp' qs2))=(snd (Free_QExp' qs2))).
       apply min_le. split. 
       apply Considered_QExp_dom. assumption.
       split. intuition.
       apply Considered_QExp_dom. assumption.
       destruct H6. rewrite H6. rewrite H7.
     apply (Par_Pure_State_wedge) with (snd (Free_QExp' qs1)).
     assert(s <= fst (Free_QExp' qs1) /\ snd (Free_QExp' qs1) <= e).
     apply QExp_eval_dom with c q. assumption.
     assert(s <= fst (Free_QExp' qs2) /\ snd (Free_QExp' qs2) <= e).
     apply QExp_eval_dom with c q. assumption.
     split.  intuition.
    split. apply Considered_QExp_dom. assumption. 
     split. rewrite H5. apply Considered_QExp_dom. assumption.
      intuition.  assumption. assumption. 
       rewrite H5. assumption.
      
       simpl.
       rewrite min_comm.
       rewrite max_comm.
       assert(min (fst (Free_QExp' qs2))
       (fst (Free_QExp' qs1))=(fst (Free_QExp' qs2))/\
       max (snd (Free_QExp' qs2))
         (snd (Free_QExp' qs1))=(snd (Free_QExp' qs1))).
       apply min_le. split. 
       apply Considered_QExp_dom. assumption.
       split. intuition.
       apply Considered_QExp_dom. assumption.
       destruct H6. rewrite H6. rewrite H7.
     apply (Par_Pure_State_wedge) with (snd (Free_QExp' qs2)).
     assert(s <= fst (Free_QExp' qs1) /\ snd (Free_QExp' qs1) <= e).
     apply QExp_eval_dom with c q. assumption.
     assert(s <= fst (Free_QExp' qs2) /\ snd (Free_QExp' qs2) <= e).
     apply QExp_eval_dom with c q. assumption.
     split. intuition.  
     split.  apply Considered_QExp_dom. assumption. 
     split. rewrite H5. apply Considered_QExp_dom. assumption.
      intuition. assumption. assumption. 
       rewrite H5. assumption.
        apply H.
        assumption.
        apply H.
        assumption.
Admitted.


Lemma State__eval_pure: forall F s e c (q: qstate s e) ,
Considered_Formula F ->
WF_qstate q->
State_eval F (c, q)->
@Par_Pure_State (2^((snd (Free_State F))- ((fst (Free_State F)))))
(@PMpar_trace s e q ((fst (Free_State F))) (((snd (Free_State F)))) ).
Proof. induction F; intros.
       simpl. admit.
       apply QExp_eval_pure with c.
       assumption. assumption.
       assumption.
        
       simpl QExp_eval in H1.  
       destruct H1. 
       destruct H2.
       pose H2 as H2'. pose H3 as H3'.
       apply IHF1 in H2'.
       apply IHF2 in H3'.
       simpl in H.
       destruct H.
       destruct H4.
       destruct H5.
       simpl.
       assert(min (fst (Free_State F1))
(fst (Free_State F2))=(fst (Free_State F1))/\
max (snd (Free_State F1))
  (snd (Free_State F2))=(snd (Free_State F2))).
apply min_le. split.
apply Considered_Formula_dom. assumption.
split. assumption.
apply Considered_Formula_dom. assumption.
destruct H6. rewrite H6. rewrite H7.
     apply Par_Pure_State_wedge with (snd (Free_State F1)).
     assert(s <= fst (Free_State F1) /\ snd (Free_State F1) <= e).
     apply State_eval_dom with c q. assumption.
     assert(s <= fst (Free_State F2) /\ snd (Free_State F2) <= e).
     apply State_eval_dom with c q. assumption.
     split. intuition. 
     split. 
     apply Considered_Formula_dom. assumption.
     split. 
     rewrite H5. 
     apply Considered_Formula_dom. assumption.
     intuition. assumption. assumption.
     rewrite H5.
     assumption.
       
     simpl.
     rewrite min_comm.
     rewrite max_comm.
     assert(min (fst (Free_State F2))
     (fst (Free_State F1))=(fst (Free_State F2))/\
     max (snd (Free_State F2))
       (snd (Free_State F1))=(snd (Free_State F1))).
     apply min_le. split. 
     apply Considered_Formula_dom. assumption.
     split. intuition.
     apply Considered_Formula_dom. assumption.
     destruct H6. rewrite H6. rewrite H7.
   apply (Par_Pure_State_wedge) with (snd (Free_State F2)).
   assert(s <= fst (Free_State F1) /\ snd (Free_State F1) <= e).
   apply State_eval_dom with c q. assumption.
   assert(s <= fst (Free_State F2) /\ snd (Free_State F2) <= e).
   apply State_eval_dom with c q. assumption.
   split. intuition.  
    split.  apply Considered_Formula_dom. assumption. 
   split. rewrite H5. apply Considered_Formula_dom. assumption.
    intuition.  assumption. assumption. 
     rewrite H5. assumption.


        apply H.
        assumption.
        apply H.
        assumption.

simpl in H. 
destruct H.
destruct H2.
destruct H3.
destruct H3.
simpl. rewrite H3. rewrite H4.
rewrite min_id. rewrite max_id.
apply IHF2 with c.
assumption. assumption.
apply H1.

destruct H3.

simpl.
assert(min (fst (Free_State F1))
(fst (Free_State F2))=(fst (Free_State F1))/\
max (snd (Free_State F1))
  (snd (Free_State F2))=(snd (Free_State F2))).
apply min_le. split.
apply Considered_Formula_dom. assumption.
split. assumption.
apply Considered_Formula_dom. assumption.
destruct H4. rewrite H5. rewrite H4.
     apply Par_Pure_State_wedge with (snd (Free_State F1)).
     assert(s <= fst (Free_State F1) /\ snd (Free_State F1) <= e).
     apply State_eval_dom with c q. apply H1. 
     assert(s <= fst (Free_State F2) /\ snd (Free_State F2) <= e).
     apply State_eval_dom with c q. apply H1. 
     split. intuition. 
     split. 
     apply Considered_Formula_dom. assumption.
     split. 
     rewrite H3. 
     apply Considered_Formula_dom. assumption.
     intuition. assumption.
     apply IHF1 with c. assumption. assumption.
     apply H1.
     rewrite H3.
     apply IHF2 with c. assumption. assumption.
     apply H1.
       
     simpl.
     rewrite min_comm.
     rewrite max_comm.
     assert(min (fst (Free_State F2))
     (fst (Free_State F1))=(fst (Free_State F2))/\
     max (snd (Free_State F2))
       (snd (Free_State F1))=(snd (Free_State F1))).
     apply min_le. split. 
     apply Considered_Formula_dom. assumption.
     split. intuition.
     apply Considered_Formula_dom. assumption.
     destruct H4. rewrite H5. rewrite H4.
     apply Par_Pure_State_wedge with (snd (Free_State F2)).
     assert(s <= fst (Free_State F1) /\ snd (Free_State F1) <= e).
     apply State_eval_dom with c q. apply H1. 
     assert(s <= fst (Free_State F2) /\ snd (Free_State F2) <= e).
     apply State_eval_dom with c q. apply H1. 
     split. intuition. 
     split. 
     apply Considered_Formula_dom. assumption.
     split. 
     rewrite H3. 
     apply Considered_Formula_dom. assumption.
     intuition. assumption.
     apply IHF2 with c. assumption. assumption.
     apply H1.
     rewrite H3.
     apply IHF1 with c. assumption. assumption.
     apply H1.
Admitted.




Lemma QExp_free_eval{s e:nat}:forall (qs: QExp) (st: state s e) s' e',
s<=s'/\ s'<=e' /\ e'<=e ->
s'<=(fst (Free_QExp' qs)) /\ (snd (Free_QExp' qs))<=e'->
@WF_Matrix (2^(e-s)) (2^(e-s)) (snd st)->
QExp_eval qs st <-> QExp_eval qs (fst st, (PMpar_trace (snd st) s' e')).
Proof. induction qs; split; intros. 
        simpl in *. rewrite PMtrace_scale.
        rewrite PMpar_trace_assoc. 
        split. lia.
        split. lia. split. lia. 
        rewrite Ptrace_trace. intuition.
        lia. assumption. lia.  
        simpl in *. 
        rewrite PMtrace_scale in H2.
        rewrite PMpar_trace_assoc in H2.
        rewrite Ptrace_trace in H2. 
        split. lia. split. lia. split. lia. 
        intuition. lia. assumption.  lia.
        simpl in H2. 
        simpl. split.  intuition.
        destruct st. simpl in *.
        assert(s <= fst (Free_QExp' qs1) /\ snd (Free_QExp' qs1) <= e).
     apply QExp_eval_dom with c q. intuition. 
     assert(s <= fst (Free_QExp' qs2) /\ snd (Free_QExp' qs2) <= e).
     apply QExp_eval_dom with c q. intuition. 
        split. 
        apply (IHqs1 (c, q)). assumption.
        intuition. assumption.
        intuition. 
        apply (IHqs2 (c,q)). assumption.
        intuition. assumption.
        intuition. 
        simpl in *. split.  intuition.
        destruct H2.
        destruct H3.
        (* destruct st. simpl in *.  *)
        (* assert(s <= fst (Free_QExp' qs1) /\ snd (Free_QExp' qs1) <= e).
     apply QExp_eval_dom with c q. intuition. 
     assert(s <= fst (Free_QExp' qs2) /\ snd (Free_QExp' qs2) <= e).
     apply QExp_eval_dom with c q. intuition.  *)
        split.
        apply IHqs1 in H3. 
        assumption. intuition.
        apply QExp_eval_dom with (fst st) (PMpar_trace (snd st) s' e').
        assumption.
        assumption.
        apply IHqs2 in H4. assumption.
        intuition.
        apply QExp_eval_dom with (fst st) (PMpar_trace (snd st) s' e').
        assumption. assumption.
Qed.
        
        
Lemma State_free_eval{s e:nat}:forall (F: State_formula) (st: state s e) s' e',
s<=s'/\ s'<=e' /\ e'<=e ->
s'<=(fst (Free_State F)) /\ (snd (Free_State F))<=e'->
@WF_Matrix (2^(e-s)) (2^(e-s)) (snd st) ->
State_eval F st <-> 
State_eval F (fst st, (PMpar_trace (snd st) s' e')).
Proof. induction F; split; intros. destruct st. 
    eapply state_eq_Pure with (c, q). 
    reflexivity. apply H2.
    destruct st. simpl in *.
    eapply state_eq_Pure with (c, PMpar_trace q s' e'). 
    reflexivity. intuition. destruct st.
    apply (QExp_free_eval _  (c, q)) .
    intuition. intuition. intuition.
    assumption.
    destruct st. simpl in *.
    rewrite QExp_free_eval. apply H2. 
    intuition. intuition. intuition. 
    simpl in *.
    split. intuition. 
    split. apply IHF1. assumption.
    split.
    apply min_glb_l with (fst (Free_State F2)).
    intuition.
    eapply max_lub_iff.  rewrite max_comm. apply H0.
    assumption. intuition.
    apply IHF2. assumption.
    split.
    apply min_glb_l with (fst (Free_State F2)).
    intuition.
    eapply max_lub_iff.   apply H0.
    assumption. intuition.
    simpl in *.
    split. intuition. 
    destruct H2. destruct H3.
    split. apply IHF1 in H3. assumption.
    intuition.
    split.
    apply min_glb_l with (fst (Free_State F2)).
    intuition.
    eapply max_lub_iff.  rewrite max_comm. apply H0.
     assumption. 
    apply IHF2 in H4. assumption. assumption.
    split.
    apply min_glb_l with (fst (Free_State F2)).
    intuition.
    eapply max_lub_iff.  apply H0.
     assumption. 
    simpl in *.
    split. apply IHF1. assumption.
    split.
    apply min_glb_l with (fst (Free_State F2)).
    intuition.
    eapply max_lub_iff.  rewrite max_comm. apply H0.
     assumption. intuition.
    apply IHF2. assumption.
    split.
    apply min_glb_l with (fst (Free_State F2)).
    intuition.
    eapply max_lub_iff.  apply H0.
     assumption. intuition.
    simpl in *.
    destruct H2.
    split. apply IHF1 in H2. assumption.
    intuition.
    split.
    apply min_glb_l with (fst (Free_State F2)).
    intuition.
    eapply max_lub_iff.  rewrite max_comm. apply H0.
     assumption. 
    apply IHF2 in H3. assumption. assumption.
    split.
    apply min_glb_l with (fst (Free_State F2)).
    intuition.
    eapply max_lub_iff.   apply H0.
     assumption. 
Qed.


Lemma seman_eq_two''{s e:nat}: forall F1 F2  c (q:qstate s e),
Considered_Formula (F1 ⊙ F2) /\
(snd (Free_State F1) = fst (Free_State F2))->
WF_qstate q->
State_eval (F1 ⊙ F2) (c, q) -> 
exists 
(q1:qstate (fst (Free_State F1)) (snd (Free_State F1)))
(q2:qstate (fst (Free_State F2)) (snd (Free_State F2))), 
(q_combin' q1 q2 (@PMpar_trace s e q (fst (Free_State (F1 ⊙ F2))) (snd (Free_State (F1 ⊙ F2))))).
Proof. intros F1 F2 c q H Hw. intros. 
        simpl in H.  
        destruct H.
        simpl.  
        assert(min (fst (Free_State F1))
        (fst (Free_State F2))=(fst (Free_State F1))/\
        max (snd (Free_State F1))
          (snd (Free_State F2))=(snd (Free_State F2))).
        apply min_le. split.
        apply Considered_Formula_dom. intuition.
        split. assumption.
        apply Considered_Formula_dom. intuition.
        destruct H2. rewrite H2. rewrite H3.
        remember ((fst (Free_State F1))) as s'.
        remember ((fst (Free_State F2))) as x.
        remember ((snd (Free_State F2))) as e'.
        remember (PMpar_trace q s' e').
       assert(exists (q1:qstate s' x) (q2: qstate x e'), 
       and (WF_qstate q1 /\ WF_qstate q2)
       (q0 = @kron (2^(x-s')) (2^(x-s')) (2^(e'-x))  (2^(e'-x)) q1 q2)).
       apply Odot_Sepear''.  
       rewrite Heqs'. rewrite Heqx. rewrite Heqe'.
       split. rewrite <-Heqx. rewrite<- H1.
       apply Considered_Formula_dom. apply H.
       apply Considered_Formula_dom. apply H.
       rewrite Heqq0. apply WF_par_trace.
       rewrite Heqs'. rewrite Heqe'.
       split. eapply State_eval_dom.
       apply H0. 
       split.
       apply le_trans with (snd (Free_State F1)).
       subst. apply Considered_Formula_dom.
       intuition. rewrite H1. rewrite Heqx.
       apply Considered_Formula_dom. intuition.
       eapply State_eval_dom. apply H0.
       assumption.
       rewrite <-H1. rewrite Heqs'.
       apply State__eval_pure with c.
       intuition. 
       rewrite Heqq0. 
       rewrite Heqs'. rewrite Heqe'.
       apply WF_par_trace.
       split. eapply State_eval_dom.
       apply H0. 
       split.
       apply le_trans with (snd (Free_State F1)).
       subst. apply Considered_Formula_dom.
       intuition. rewrite H1. rewrite Heqx.
       apply Considered_Formula_dom. intuition.
       eapply State_eval_dom. apply H0.
       assumption. rewrite Heqq0.
       assert( c= fst (c, q)). reflexivity.
       rewrite H4.
       assert(PMpar_trace q s' e'= PMpar_trace (snd (c, q)) s' e').
       reflexivity. rewrite H5.
       rewrite Heqs'. rewrite Heqe'.
        rewrite <-(State_free_eval F1 (c, q) ).
        simpl in H0. intuition.
        split. eapply State_eval_dom.
        apply H0. 
        split.
        apply le_trans with (snd (Free_State F1)).
        subst. apply Considered_Formula_dom.
        intuition. rewrite H1. rewrite Heqx.
        apply Considered_Formula_dom. intuition.
        eapply State_eval_dom. apply H0.
        split.  intuition. rewrite H1.
        rewrite Heqx. 
        apply Considered_Formula_dom.
        intuition. simpl. apply WF_Mixed.
       apply Hw.
       destruct H4. destruct H4.
       exists x0. exists x1.
       destruct H4. 
       rewrite H5. subst. rewrite H1.
        econstructor; auto. 
       intuition. intuition.
Qed.


Lemma seman_eq_two'''{s e:nat}: forall F1 F2  c (q:qstate s e),
Considered_Formula (F1 ⊙ F2) /\
(snd (Free_State F2) = fst (Free_State F1))->
WF_qstate q->
State_eval (F1 ⊙ F2) (c, q) -> 
exists 
(q1:qstate (fst (Free_State F2)) (snd (Free_State F2)))
(q2:qstate (fst (Free_State F1)) (snd (Free_State F1))), 
(q_combin' q1 q2 (@PMpar_trace s e q (fst (Free_State (F1 ⊙ F2))) (snd (Free_State (F1 ⊙ F2))))).
Proof. 

intros F1 F2 c q H Hw. intros. 
        simpl in H.  
        destruct H.
        simpl.  
        assert(min (fst (Free_State F2))
        (fst (Free_State F1))=(fst (Free_State F2))/\
        max (snd (Free_State F2))
          (snd (Free_State F1))=(snd (Free_State F1))).
        apply min_le. split.
        apply Considered_Formula_dom. intuition.
        split. assumption.
        apply Considered_Formula_dom. intuition.
        rewrite min_comm. rewrite max_comm.
        destruct H2. rewrite H2. rewrite H3.
        remember ((fst (Free_State F2))) as s'.
        remember ((snd (Free_State F2))) as x.
        remember ((snd (Free_State F1))) as e'.
        remember (PMpar_trace q s' e').
       assert(exists (q1:qstate s' x) (q2: qstate x e'), 
       and (WF_qstate q1 /\ WF_qstate q2)
       (q0 = @kron (2^(x-s')) (2^(x-s')) (2^(e'-x))  (2^(e'-x)) q1 q2)).
       apply Odot_Sepear''.
       subst.  
       split. 
       apply Considered_Formula_dom. apply H.
       rewrite H1.
       apply Considered_Formula_dom. apply H.
       rewrite Heqq0. apply WF_par_trace.
       rewrite Heqs'. rewrite Heqe'.
       split. eapply State_eval_dom.
       apply H0. 
       split.
       apply le_trans with (snd (Free_State F2)).
       subst. apply Considered_Formula_dom.
       intuition.  rewrite <-Heqx. rewrite H1.
       apply Considered_Formula_dom. intuition.
       eapply State_eval_dom. apply H0.
        assumption.
       subst. 
       apply State__eval_pure with c.
       intuition. 
       apply WF_par_trace.
       split. eapply State_eval_dom.
       apply H0. 
       split.
       apply le_trans with (snd (Free_State F2)).
       subst. apply Considered_Formula_dom.
       intuition.   rewrite H1.
       apply Considered_Formula_dom. intuition.
       eapply State_eval_dom. apply H0.
       assumption.
       assert( c= fst (c, q)). reflexivity.
       rewrite H4.
       assert(PMpar_trace q  (fst (Free_State F2))
       (snd (Free_State F1))= PMpar_trace (snd (c, q))  (fst (Free_State F2))
       (snd (Free_State F1))).
       reflexivity. rewrite H5.
        rewrite <-(State_free_eval F2 (c, q)  ).
        simpl in H0. intuition.
        split. eapply State_eval_dom.
       apply H0. 
       split.
       apply le_trans with (snd (Free_State F2)).
       subst. apply Considered_Formula_dom.
       intuition.  rewrite H1.
       apply Considered_Formula_dom. intuition.
       eapply State_eval_dom. apply H0.  
        split.  intuition. rewrite H1.

        apply Considered_Formula_dom.
        intuition. simpl. apply WF_Mixed.
       apply Hw.
       destruct H4. destruct H4.
       exists x0. exists x1.
       destruct H4. 
       rewrite H5. subst. rewrite H1.
        econstructor; auto.
        
        rewrite <-H1.
       intuition. rewrite <-H1. intuition.
Qed.
 

Lemma r1{s e:nat}: forall (mu : list (cstate *qstate s e)) F1 F2,
Considered_Formula (F1 ⊙ F2) /\
(snd (Free_State F1) = fst (Free_State F2))->
State_eval_dstate (F1 ⊙ F2) mu->
WF_dstate_aux mu ->
(dstate_Separ (d_par_trace mu (fst (Free_State (F1 ⊙ F2))) (snd (Free_State (F1 ⊙ F2)))) 
(fst (Free_State (F1))) (snd (Free_State (F1)))  (fst (Free_State (F2))) (snd (Free_State (F2)))).
Proof. induction mu; intros. 
       simpl. intuition.
       destruct mu. 
       destruct a. 
       simpl.
        

assert(exists (q1:qstate (fst (Free_State F1)) (snd (Free_State F1)))
(q2:qstate (fst (Free_State F2)) (snd (Free_State F2))), 
(q_combin' q1 q2 (@PMpar_trace s e q (fst (Free_State (F1 ⊙ F2))) (snd (Free_State (F1 ⊙ F2)))))).
apply seman_eq_two'' with c.
assumption. inversion_clear  H1. intuition.
inversion_clear H0. assumption.

destruct H2. destruct H2.
inversion H2; subst.
econstructor.
assumption.
apply H5.
apply H6.
assert((forall i : nat, WF_qstate ((fun i:nat=> x) i))).
intuition. apply H8.
assert(forall i : nat, WF_qstate ((fun i=>x0) i)).
intuition. apply H8.
apply Logic.eq_trans with 
(big_sum
  (fun i : nat =>
   (fun _ : nat => x) i ⊗ (fun _ : nat => x0) i) 
  1). simpl. 
  rewrite Mplus_0_l.
reflexivity. intuition.

econstructor.
destruct a. destruct p.

simpl.
assert(exists (q1:qstate (fst (Free_State F1)) (snd (Free_State F1)))
(q2:qstate (fst (Free_State F2)) (snd (Free_State F2))), 
(q_combin' q1 q2 (@PMpar_trace s e q (fst (Free_State (F1 ⊙ F2))) (snd (Free_State (F1 ⊙ F2)))))).
apply seman_eq_two'' with c.
assumption. inversion_clear  H1. intuition.
inversion_clear H0. assumption. 
destruct H2. destruct H2. 
inversion H2; subst.

econstructor; try assumption.

assert((forall i : nat, WF_qstate ((fun i:nat=> x) i))).
intuition. apply H8.
assert(forall i : nat, WF_qstate ((fun i=>x0) i)).
intuition. apply H8.
apply Logic.eq_trans with 
(big_sum
  (fun i : nat =>
   (fun _ : nat => x) i ⊗ (fun _ : nat => x0) i) 
  1). simpl. 
  rewrite Mplus_0_l.
reflexivity. intuition.

apply IHmu.
assumption.
inversion_clear H0.
apply H9.
inversion_clear H1. assumption.  
Qed.


Lemma r2{s e:nat}: forall (mu : list (cstate *qstate s e)) F1 F2,
Considered_Formula (F1 ⊙ F2) /\
(snd (Free_State F2) = fst (Free_State F1))->
State_eval_dstate (F1 ⊙ F2) mu->
WF_dstate_aux mu ->
(dstate_Separ (d_par_trace mu (fst (Free_State (F1 ⊙ F2))) (snd (Free_State (F1 ⊙ F2)))) 
(fst (Free_State (F2))) (snd (Free_State (F2)))  (fst (Free_State (F1))) (snd (Free_State (F1)))).
Proof. induction mu; intros. 
       simpl. intuition.
       destruct mu. 
       destruct a. 
       simpl.
        
assert(exists (q1:qstate (fst (Free_State F2)) (snd (Free_State F2)))
(q2:qstate (fst (Free_State F1)) (snd (Free_State F1))), 
(q_combin' q1 q2 (@PMpar_trace s e q (fst (Free_State (F1 ⊙ F2))) (snd (Free_State (F1 ⊙ F2)))))).
apply seman_eq_two''' with c.
assumption. inversion_clear  H1. intuition.
inversion_clear H0. assumption.

destruct H2. destruct H2.
inversion H2; subst.

econstructor; try assumption.

assert((forall i : nat, WF_qstate ((fun i:nat=> x) i))).
intuition. apply H8.
assert(forall i : nat, WF_qstate ((fun i=>x0) i)).
intuition. apply H8.
apply Logic.eq_trans with 
(big_sum
  (fun i : nat =>
   (fun _ : nat => x) i ⊗ (fun _ : nat => x0) i) 
  1). simpl. 
  rewrite Mplus_0_l.
reflexivity. intuition.

econstructor. 
destruct a. destruct p.

simpl.
assert(exists (q1:qstate (fst (Free_State F2)) (snd (Free_State F2)))
(q2:qstate (fst (Free_State F1)) (snd (Free_State F1))), 
(q_combin' q1 q2 (@PMpar_trace s e q (fst (Free_State (F1 ⊙ F2))) (snd (Free_State (F1 ⊙ F2)))))).
apply seman_eq_two''' with c.
assumption. inversion_clear  H1. intuition.
inversion_clear H0. assumption. 
destruct H2. destruct H2. 
inversion H2; subst.

econstructor; try assumption.

assert((forall i : nat, WF_qstate ((fun i:nat=> x) i))).
intuition. apply H8.
assert(forall i : nat, WF_qstate ((fun i=>x0) i)).
intuition. apply H8.
apply Logic.eq_trans with 
(big_sum
  (fun i : nat =>
   (fun _ : nat => x) i ⊗ (fun _ : nat => x0) i) 
  1). simpl. 
  rewrite Mplus_0_l.
reflexivity. intuition.



apply IHmu.
assumption.
inversion_clear H0.
apply H9.
inversion_clear H1. assumption.  
 Qed.

Lemma Lt_n_i_false: forall n x,
(n + x >= n) <-> (n + x <? n)=false.
Proof. intros.
       split.
       bdestruct (n + x <? n).
       intros. lia. 
       intros. reflexivity.

       intros. lia.
Qed.


 Lemma big_sum_sum'':forall n m a1 a2 b1 b2 (f: nat -> Matrix a1 a2)
 (g:nat->Matrix b1 b2),
 big_sum f n .+ big_sum g m =
 big_sum (fun i=> if i <?n then f i else g (i-n)) (n+m).
 Proof. intros. rewrite big_sum_sum'.
        f_equal. 
        apply big_sum_eq_bounded.
        intros. 
        apply Lt_n_i in H.
        rewrite H. reflexivity.
        apply big_sum_eq_bounded.
        intros. 
        assert(n + x >= n). lia.
        apply Lt_n_i_false in H0.
        rewrite H0. 
        rewrite add_comm.
        rewrite add_sub.
       reflexivity.
Qed.
 
 
 Lemma dstate_Separ_map2{s e:nat}: forall (mu1 mu2: list (cstate *qstate s e))  s0 e0 s1 e1 ,
 dstate_Separ mu1 s0 e0 s1 e1->
 dstate_Separ mu2 s0 e0 s1 e1->
 dstate_Separ (StateMap.Raw.map2 option_app mu1 mu2) s0 e0 s1 e1 .
 Proof. induction mu1; induction mu2; intros.
        simpl. intuition.
        destruct a.
        rewrite map2_nil_l.
        assumption.
        rewrite map2_nil_r.
        assumption.
        destruct a. 
        destruct a0. 
        simpl in *.
        inversion H; subst.
        inversion  H0; subst.
        destruct (Cstate_as_OT.compare c c0).
        econstructor; try assumption.
        
        apply H7. apply H8.
        reflexivity. intuition.

        econstructor; try assumption.
        
        assert(forall i : nat, WF_qstate ((fun i:nat =>
        if i<?n then q0_i i else q0_i0  (i-n)) i)).
        intros. bdestruct (i<?n). 
        apply H7. apply H9.
        apply H1. 
        assert(forall i : nat, WF_qstate ((fun i:nat =>
        if i<?n then q1_i i else q1_i0  (i-n)) i)).
        intros. bdestruct (i<?n). 
        apply H8. apply H10.
        apply H1. 
        assert(2^(e-s) =2 ^ (s1 - s) * 2 ^ (e- s1)).
        admit. destruct H1.
        rewrite big_sum_sum''.
        apply big_sum_eq_bounded.
        intros. 
        bdestruct (x<?n).
        reflexivity.
        reflexivity.

       apply IHmu1. intuition. intuition.

      econstructor; try assumption.
      apply H9. apply H10.
      reflexivity.
       apply IHmu2.
       apply H.
       intuition. 
Admitted.


Lemma dstate_qstate_eq_Separ{s e:nat}:forall (mu1 mu2: list(cstate * qstate s e))
s0 e0 s1 e1,
dstate_qstate_eq mu1 mu2 ->
dstate_Separ mu1 s0 e0 s1 e1->
dstate_Separ mu2 s0 e0 s1 e1.
Proof. induction mu1; intros. destruct mu2. intuition.
       destruct H. 
       destruct mu2. destruct a. destruct H.
       destruct a. destruct p. 
       simpl in H. destruct H. subst.
       inversion H0; subst.
       econstructor; try reflexivity.
       apply H7. apply H8.
       apply IHmu1. assumption.
       assumption.
Qed.

Lemma  super_0{ m n:nat}:  forall (M: Matrix m n) , 
super M Zero = Zero.
Proof. unfold super. intros. 
rewrite Mmult_0_r. rewrite Mmult_0_l.
reflexivity.     
Qed.



Lemma QInit_fun_sum{s' e':nat}: forall n s e (q: nat-> qstate s' e'), 
s'<=s/\s<=e/\e<=e'->
QInit_fun s e (big_sum q n) =
big_sum (fun i => QInit_fun s e (q i)) n .
Proof. induction n;  intros.
simpl.  unfold QInit_fun.
apply (@big_sum_0_bounded (Matrix (2 ^ (e' - s')) (2 ^ (e' - s')))).
intros.
assert(2^(e'-s')= (2^(s-s')) * (2^(e-s)) * (2^(e'-e))).
type_sovle'. destruct H1.
 rewrite (@Mmult_0_r (2^(e'-s'))  (2^(e'-s'))) .
rewrite Mmult_0_l. reflexivity.
simpl. rewrite <-IHn.
rewrite QInit_fun_plus. reflexivity.
assumption. assumption.
Qed.


Lemma QUnit_One_fun_sum{s' e':nat}: forall n s e U (q: nat-> qstate s' e'), 
s'<=s/\s<=e/\e<=e'->
QUnit_One_fun s e U (big_sum q n) =
big_sum (fun i => QUnit_One_fun s e U (q i)) n .
Proof. induction n;  intros.
simpl. unfold QUnit_One_fun. unfold q_update.
apply (@super_0 (2 ^ (e' - s')) (2 ^ (e' - s'))).
simpl. rewrite <-IHn.
symmetry.
apply QUnit_One_fun_plus. 
assumption. assumption.
Qed.  




Lemma QUnit_Ctrl_fun_sum{s' e':nat}: forall n s0 e0 s1 e1 U (q: nat-> qstate s' e'), 
s'<=s0/\ s0<=e0 /\ e0<=s1 /\ s1 <= e1 /\ e1 <=e'->
QUnit_Ctrl_fun s0 e0 s1 e1  U (big_sum q n) =
big_sum (fun i => QUnit_Ctrl_fun s0 e0 s1 e1  U (q i)) n .
Proof. induction n;  intros;
simpl. unfold QUnit_Ctrl_fun. unfold q_update.
apply (@super_0 (2 ^ (e' - s')) (2 ^ (e' - s'))).
rewrite <-IHn.
symmetry.
apply QUnit_Ctrl_fun_plus. 
assumption. assumption.
Qed.

Lemma QMeas_fun_sum{s' e':nat}: forall n s e j (q: nat-> qstate s' e'), 
s'<=s /\ s<=e /\ e <=e'->
QMeas_fun s e j (big_sum q n) =
big_sum (fun i => QMeas_fun s e j (q i)) n .
Proof. induction n;  intros.
simpl. unfold QMeas_fun . unfold q_update.
apply (@super_0 (2 ^ (e' - s')) (2 ^ (e' - s'))).
simpl. rewrite <-IHn.
symmetry.
apply QMeas_fun_plus. 
assumption. assumption.
Qed.


Lemma dstate_Separ_Qinit{s e:nat}: forall c (q:qstate s e) s0 e0 s1 e1 s' e',
dstate_Separ [(c, q)] s0 e0 s1 e1 ->
s=s0 /\s0<=s' /\ s'<=e'/\ e'<=e0 /\ e0=s1 /\ s1<=e1 /\
e1=e->
@dstate_Separ s e [(c, QInit_fun s' e' q)] s0 e0 s1 e1.
Proof.
intros.  inversion H; subst. clear H14. 
econstructor; try reflexivity.
assert(forall i : nat, @WF_qstate s s1 ((fun i=> QInit_fun s' e' (q0_i i)) i)).
intros. admit.
apply H1. apply H8.
rewrite (@QInit_fun_sum s e).
subst. 
apply big_sum_eq_bounded.
intros. apply (@QInit_fun_kron s s1 e).
apply WF_Mixed.  apply H8.
intuition.
intuition.
Admitted.


Lemma dstate_Separ_QUnit_One{s e:nat}: forall c (q:qstate s e) U s0 e0 s1 e1 s' e',
dstate_Separ [(c, q)] s0 e0 s1 e1 ->
s=s0 /\s0<=s' /\ s'<=e'/\ e'<=e0 /\ e0=s1 /\ s1<=e1 /\
e1=e->
@WF_Unitary (2^(e'-s')) U->
@dstate_Separ s e [(c, QUnit_One_fun s' e' U q)] s0 e0 s1 e1.
Proof.
intros.  inversion H; subst. clear H15. 
econstructor; try reflexivity.
assert(forall i : nat, @WF_qstate s s1 ((fun i=>QUnit_One_fun s' e' U (q0_i i)) i)).
intros. admit.
apply H2. apply H9.
rewrite (@QUnit_One_fun_sum s e).
subst. 
apply big_sum_eq_bounded.
intros. apply (@QUnit_One_fun_kron s s1 e).
apply H1. apply WF_Mixed. apply H9.
intuition.
intuition.
econstructor.
Admitted.


Lemma dstate_Separ_QUnit_Ctrl{s e:nat}: forall c (q:qstate s e)  
s0 e0 s1 e1 s0' e0' s1' e1' (U: nat -> Square (2 ^ (e1' - s1'))),
dstate_Separ [(c, q)] s0 e0 s1 e1 ->
(forall j, WF_Unitary (U j))->
s=s0 /\s0<=s0' /\ s0'<=e0'/\ e0'< s1' /\ s1'<=e1' /\e1'<=e0 /\ e0=s1 /\ s1<=e1 /\
e1=e->
@dstate_Separ s e [(c, QUnit_Ctrl_fun s0' e0' s1' e1' U q)] s0 e0 s1 e1.
Proof.
intros.  inversion H; subst. clear H15. 
econstructor; try reflexivity.
assert(forall i : nat, @WF_qstate s s1 ((fun i=>QUnit_Ctrl_fun s0' e0' s1' e1' U (q0_i i)) i)).
intros. admit.
apply H2. apply H9.
rewrite (@QUnit_Ctrl_fun_sum s e).
subst. 
apply big_sum_eq_bounded.
intros. 
admit.
intuition.
econstructor.
Admitted.


Lemma dstate_Separ_QMeas{s e:nat}: forall c (q:qstate s e)  
s0 e0 s1 e1 s' e' j,
dstate_Separ [(c, q)] s0 e0 s1 e1 ->
s=s0 /\s0<=s' /\ s'<=e' /\e'<=e0 /\ e0=s1 /\ s1<=e1 /\
e1=e->
(j<(2^(e'-s')))->
@dstate_Separ s e [(c, QMeas_fun s' e' j q)] s0 e0 s1 e1.
Proof.
intros. inversion H; subst. clear H15. 
econstructor; try reflexivity.
assert(forall i : nat, @WF_qstate s s1 ((fun i=>QMeas_fun s' e' j (q0_i i)) i)).
intros. admit.
apply H2. apply H9.
rewrite (@QMeas_fun_sum s e).
apply big_sum_eq_bounded.
intros. 
apply (@QMeas_fun_kron s s1 e).
assumption.
apply WF_Mixed. 
apply H9.

intuition.
intuition.
econstructor.
Admitted.




Lemma r3{s e:nat}: forall c s0 e0 s1 e1
(mu mu':list (cstate *qstate s e)) F ,
ceval_single c mu mu'-> 
dstate_Separ mu s0 e0 s1 e1->
NSet.Equal (NSet.inter (fst (Free_state F)) (fst (MVar c))) (NSet.empty)  ->
NSet.Subset (snd (MVar c)) (Qsys_to_Set s0 e0) ->
dstate_Separ mu' s0 e0 s1 e1 .
Proof.
induction c. 
-- {intros. apply ceval_skip_1 in H. subst. intuition. }
-- admit.
-- induction mu; intros.
  {inversion  H; subst. intuition.  }
   {destruct a0. inversion H; subst. clear H.
   apply dstate_Separ_map2. 
   apply dstate_qstate_eq_Separ with [(c,q)].
   simpl. intuition.
   inversion H0; subst.
   econstructor; try reflexivity.
   assumption. assumption. econstructor.
   apply IHmu with F. assumption.
   inversion H0; subst. assumption.
   assumption. assumption. }
--admit.
  { intros. inversion H; subst. intuition.
    apply IHc2 with mu1 F.
    assumption. 
    apply IHc1 with  ((sigma, rho) :: mu0) F.
    assumption.
    assumption.
    simpl in H1. rewrite inter_union_dist in H1.
    rewrite union_empty in H1. intuition.
    simpl in H2. apply subset_union in H2.
    intuition.
    simpl in H1. rewrite inter_union_dist in H1.
    rewrite union_empty in H1. intuition.
    simpl in H2. apply subset_union in H2.
    intuition.
   }
--{ induction mu; intros. inversion_clear H. intuition.
    inversion H; subst.
    apply dstate_Separ_map2. 
    apply IHc1 with  [(sigma, rho)] F.
    assumption. inversion H0; subst.
    econstructor; try reflexivity.
    assumption. assumption. econstructor.
    simpl in H1. rewrite inter_union_dist in H1.
    rewrite union_empty in H1. intuition.
    simpl in H2. apply subset_union in H2.
    intuition.
    apply IHmu with F.
    assumption.
    inversion H0; subst. intuition.
    assumption. assumption.
    apply dstate_Separ_map2. 
    apply IHc2 with [(sigma, rho)] F.
    assumption. 
    inversion H0; subst.
    econstructor; try reflexivity.
    assumption. assumption. econstructor.
    simpl in H1. rewrite inter_union_dist in H1.
    rewrite union_empty in H1. intuition.
    simpl in H2. apply subset_union in H2.
    intuition.
    apply IHmu with F.
    assumption.
    inversion H0; subst. intuition.
    assumption. assumption. }
-- admit. 

-- induction mu; intros.
{inversion  H; subst. intuition.  }
 {destruct a. inversion H; subst. clear H.
 apply dstate_Separ_map2. 
 simpl in H2.
 apply dstate_Separ_Qinit.
 inversion H0; subst.
    econstructor; try reflexivity.
    assumption. assumption. econstructor.
 admit.
 apply IHmu with F. assumption.
 inversion H0; subst. intuition.
 assumption. assumption. }

 -- induction mu; intros.
{inversion  H; subst. intuition.  }
 {destruct a. inversion H; subst. clear H.
  apply inj_pair2_eq_dec in H5.
  apply inj_pair2_eq_dec in H5.
  destruct H5.
 apply dstate_Separ_map2. 
 apply dstate_Separ_QUnit_One.
 inversion H0; subst.
    econstructor; try reflexivity.
    assumption. assumption. econstructor.
 admit. apply H11.
 apply IHmu with F. assumption.
 inversion H0; subst. intuition.
 assumption. assumption. }

 -- induction mu; intros.
 {inversion  H; subst. intuition.  }
  {destruct a. inversion H; subst. clear H.
   apply inj_pair2_eq_dec in H8.
   apply inj_pair2_eq_dec in H8.
   destruct H8.
  apply dstate_Separ_map2. 
  apply dstate_Separ_QUnit_Ctrl.
  inversion H0; subst.
  econstructor; try reflexivity.
  assumption. assumption. econstructor.
  assumption.
  admit.
  apply IHmu with F. assumption.
  inversion H0; subst. intuition.
  assumption. assumption.
  apply Nat.eq_dec. apply Nat.eq_dec.
   }

  -- induction mu; intros.
  {inversion  H; subst. intuition.  }
   {destruct a. inversion H; subst. clear H.
   apply dstate_Separ_map2. 
   admit.
   apply IHmu with F. assumption.
   inversion H0; subst.  intuition.
   assumption. assumption. }
Admitted.






Lemma PMtrace_Super_swap'{s e:nat}: forall l r s0 e0 (M: Square (2^(e0-s0))) (A:qstate s e) ,
s<=l /\l<=s0 /\ s0<=e0 /\ e0<=r /\ r<=e -> 
WF_Matrix M->
super ((I (2 ^ (s0-l)) ⊗ M ⊗ I (2 ^ (r-e0)))) (PMpar_trace A  l r) = 
@PMpar_trace s e (super (I (2 ^ (s0-s)) ⊗ M ⊗ I (2 ^ (e-e0))) A) l r.
Proof. intros. unfold super. repeat rewrite Ptrace_l_r'.  
       assert((2^(s0-l) * 2 ^ (e0-s0) * 2^(r-e0)) = 1 * (2 ^ (r- l)) * 1).
      rewrite mul_1_l. rewrite mul_1_r.
       type_sovle'. 
        destruct H1. rewrite Mmult_Msum_distr_l.
       rewrite Mmult_Msum_distr_r.
       apply big_sum_eq_bounded.  intros.  
       assert((2^(s0-l) * 2 ^ (e0-s0) * 2^(r-e0)) = 1 * (2 ^ (r- l)) * 1).
      rewrite mul_1_l. rewrite mul_1_r.
       type_sovle'. 
       destruct H2. 
       rewrite Mmult_Msum_distr_l.
       rewrite Mmult_Msum_distr_r.
       apply big_sum_eq_bounded.  intros. 
        rewrite Mmult_assoc_5.
        assert(2 ^ (s0 - s) * 2 ^ (e0 - s0) * 2 ^ (e - e0) = 2 ^ (l - s) * 2 ^ (r - l) * 2 ^ (e - r)).
        type_sovle'. destruct H3. 
        rewrite Mmult_assoc_5.
        f_equal.  f_equal.

        remember (I (2 ^ (s0 - l)) ⊗ M ⊗ I (2 ^ (r - e0))).
        remember (⟨ x ∣_ (l - s) ⊗ I (2 ^ (r - l))
        ⊗ ⟨ x0 ∣_ (e - r)).
        assert((2^(s0-l) * 2 ^ (e0-s0) * 2^(r-e0)) = (2 ^ (r- l))).
         type_sovle'. destruct H3. 
        apply Logic.eq_trans with ((I 1 ⊗ m ⊗ I 1) × m0).
        rewrite kron_1_l; auto_wf. rewrite kron_1_r. f_equal; try rewrite mul_1_l; try rewrite mul_1_r; type_sovle'.
        rewrite Heqm. auto_wf. 
        apply Logic.eq_trans with (m0
        × (I (2 ^ (l-s)) ⊗ m ⊗ I (2 ^ (e-r)))).
        rewrite Heqm. rewrite Heqm0.
      repeat rewrite kron_mixed_product. repeat rewrite Mmult_1_l; auto_wf.
      repeat rewrite Mmult_1_r; auto_wf.  f_equal; auto_wf.
      rewrite Heqm.  
      f_equal;  try rewrite mul_1_l; try rewrite mul_1_r; type_sovle'.
      rewrite Mmult_kron_5; auto_wf. 
      repeat rewrite id_kron. f_equal; type_sovle'.
      f_equal; type_sovle'. f_equal; type_sovle'.
      f_equal; type_sovle'.

      remember (∣ x ⟩_ (l - s) ⊗ I (2 ^ (r - l))
      ⊗ ∣ x0 ⟩_ (e - r)).
      remember ((I (2 ^ (s0 - l)) ⊗ M ⊗ I (2 ^ (r - e0)))).
      assert((2^(s0-l) * 2 ^ (e0-s0) * 2^(r-e0)) = (2 ^ (r- l))).
         type_sovle'. destruct H3. 
      apply Logic.eq_trans with (m× (I 1 ⊗ (m0) † ⊗ I 1)  ).
        rewrite kron_1_l; auto_wf. rewrite kron_1_r.
         f_equal; try rewrite mul_1_l; try rewrite mul_1_r; type_sovle'.
        rewrite Heqm0. auto_wf.
        apply Logic.eq_trans with ((I (2 ^ (l-s)) ⊗ m0 ⊗ I (2 ^ (e-r))) †
        × m). rewrite Heqm. rewrite Heqm0. 
        repeat rewrite kron_adjoint. repeat rewrite id_adjoint_eq.
      repeat rewrite kron_mixed_product. repeat rewrite Mmult_1_l; auto_wf.
      repeat rewrite Mmult_1_r; auto_wf.  f_equal; auto_wf.
      rewrite Heqm0.  
      f_equal;  try rewrite mul_1_l; try rewrite mul_1_r; type_sovle'.
      rewrite Mmult_kron_5; auto_wf. 
      repeat rewrite id_kron. f_equal; type_sovle'.
      f_equal; type_sovle'. f_equal; type_sovle'.
      f_equal; type_sovle'. f_equal; type_sovle'.
       intuition. intuition. 
Qed.
       

Lemma PMpar_trace_QInit{ s e:nat}: forall c (q:qstate s e) s' e' s0 e0 s1 e1,
dstate_Separ [(c, q)] s0 e0 s1 e1->
s=s0 /\s0<=s' /\ s'<=e'/\ e'<=e0 /\ e0=s1 /\ s1<=e1 /\
e1=e->
@PMpar_trace s e (QInit_fun s' e' q) s1 e1=
PMpar_trace q s1 e1.
Proof. intros. simpl in H. inversion H; subst.
clear H.
rewrite  (@QInit_fun_sum s e ).
repeat rewrite (big_sum_par_trace).
apply big_sum_eq_bounded.
intros.  destruct H0.
 destruct H1.
 destruct H2.
destruct H3. destruct H4.
destruct H5.
subst.  
rewrite (@QInit_fun_kron s s1 e).

repeat rewrite PMpar_trace_R; try reflexivity.
rewrite (PMpar_trace_r _ ((QInit_fun s' e' (q0_i x))) (q1_i x)); try reflexivity.
rewrite (PMpar_trace_r _ (q0_i x) (q1_i x)); try reflexivity.
rewrite QInit_trace. reflexivity.
intuition.
apply WF_Mixed. 
apply H7.
apply WF_Mixed. 
apply H7.
apply WF_Mixed. 
apply H8.
apply WF_kron; type_sovle'.
apply WF_Mixed. 
apply H7.
apply WF_Mixed. 
apply H8.
admit.
apply WF_Mixed. 
apply H8.
 admit.
 apply WF_kron; type_sovle'.
 apply WF_Mixed. 
 apply H7.
 apply WF_Mixed. 
 apply H8.
admit.
apply WF_Mixed. 
apply H8.

 intuition. intuition. intuition.
 intuition.
Admitted.


Lemma PMpar_trace_QUnit_one{ s e:nat}: forall c (q:qstate s e)  s' e' (U:Square (2^(e'-s'))) s0 e0 s1 e1,
dstate_Separ [(c, q)] s0 e0 s1 e1->
s=s0 /\s0<=s' /\ s'<=e'/\ e'<=e0 /\ e0=s1 /\ s1<=e1 /\
e1=e->
WF_Unitary U->
@PMpar_trace s e (QUnit_One_fun s' e' U q) s1 e1=
PMpar_trace q s1 e1.
Proof. intros. inversion H; subst. clear H.
rewrite  (@QUnit_One_fun_sum s e ).
repeat rewrite (big_sum_par_trace).
apply big_sum_eq_bounded.
intros.  destruct H0.
destruct H2. destruct H3.
destruct H4. destruct H5.
destruct H6. 
subst.  
rewrite (@QUnit_One_fun_kron s s1 e).
repeat rewrite PMpar_trace_R; try reflexivity.
rewrite (PMpar_trace_r _ ((QUnit_One_fun s' e' U (q0_i x))) (q1_i x)); try reflexivity.
rewrite (PMpar_trace_r _ (q0_i x) (q1_i x)); try reflexivity.
rewrite QUnit_One_trace. reflexivity.
intuition.
admit. apply H1. admit. admit. admit. 
 admit. admit. admit. admit. admit.
 admit. admit. 

 intuition. intuition. intuition.
 intuition.
Admitted.


Lemma PMpar_trace_QUnit_Ctrl{ s e:nat}: forall c (q:qstate s e)  s0' e0' s1' e1' (U:nat -> Square (2^(e1'-s1'))) s0 e0 s1 e1,
dstate_Separ [(c, q)] s0 e0 s1 e1->
s=s0 /\s0<=s0' /\ s0'<=e0'/\ e0'< s1' /\ s1'<=e1' /\e1'<=e0 /\ e0=s1 /\ s1<=e1 /\
e1=e ->
(forall j, WF_Unitary (U j))->
@PMpar_trace s e (QUnit_Ctrl_fun s0' e0' s1' e1' U q) s1 e1=
PMpar_trace q s1 e1.
Proof. intros. 
inversion H; subst. clear H.
rewrite  (@QUnit_Ctrl_fun_sum s e ).
repeat rewrite (big_sum_par_trace).
apply big_sum_eq_bounded.
intros.  destruct H0.
destruct H2. destruct H3.
destruct H4. destruct H5.
destruct H6. destruct H7.
destruct H10. 
subst.  
admit. 
 intuition. intuition. intuition.
Admitted.

(* 
Lemma PMpar_trace_QMeas{ s e:nat}: forall c (q:qstate s e)  s' e' i s0 e0 s1 e1,
dstate_Separ [(c, q)] s0 e0 s1 e1->
s=s0 /\s0<=s' /\ s'<=e'/\ e'<=e0 /\ e0=s1 /\ s1<=e1 /\
e1=e->
 (i <(2^(e'-s')))->
exists (p: R), and (0<p)%R
(PMpar_trace (QMeas_fun s' e' i q) s1 e1=
 p .* PMpar_trace q s1 e1).
Proof. intros. simpl in H. destruct H.
destruct H. destruct H. destruct H.
rewrite H. 
exists (
       fst (@trace  (2^(e-s)) ((QMeas_fun s' e' i q))) / fst (@trace (2^(e-s))  (q)))%R.
split. admit.
rewrite  (@QMeas_fun_sum s e ).
(* rewrite PMtrace_scale. *)
assert(2^(e-s)=(2^(e0-s0))* (2^(e1-s1))).
type_sovle'. destruct H3.
(* rewrite <-Mscale_Msum_distr_r. *)
repeat rewrite (big_sum_par_trace).
remember ((fst (trace (QMeas_fun s' e' i q)) / fst (trace q))%R).
rewrite (big_sum_eq_bounded   _ 
((fun i0 : nat => (@trace (2^(e0-s0)) (QMeas_fun s' e' i (x i0))) .* x0 i0))).
rewrite (big_sum_eq_bounded   ((fun i0 : nat => PMpar_trace (x i0 ⊗ x0 i0) s1 e1)) 
((fun i0 : nat => (@trace (2^(e0-s0)) ((x i0))) .* x0 i0))).
rewrite Mscale_Msum_distr_l

intros.  destruct H0.
destruct H4. destruct H5.
destruct H6. destruct H7.
destruct H8.
destruct H0. destruct H7. destruct H9.
rewrite (@QMeas_fun_kron s e0 e1).
remember (((fst (trace (QMeas_fun s' e' i q)) / fst (trace q))%R)).
assert((2^(e0-s))* (2^(e1-e0))= 2^(e1-s)).
type_sovle'. destruct H0.
rewrite <-Mscale_kron_dist_l.
repeat rewrite PMpar_trace_R; try reflexivity.
rewrite (PMpar_trace_r _ ((QMeas_fun s' e' i (x x2))) (x0 x2)); try reflexivity.
rewrite (PMpar_trace_r _ (r.*x x2) (x0 x2)); try reflexivity.
rewrite QMeas_fun. reflexivity.
intuition.
admit. apply H1. admit. admit. admit. 
 admit. admit. admit. admit. admit.
 admit. admit. 

 intuition. intuition. intuition.
 intuition.
Admitted. *)

Lemma big_app_seman{ s e:nat}: forall n (f:nat -> list(cstate * qstate s e)) F , 
(forall j, j<n -> (WF_dstate_aux (f j)) /\ State_eval_dstate F (f j))->
(forall i, i<n -> WF_dstate_aux (big_app f i)) ->
n>0->
State_eval_dstate F (big_app f n)  .
Proof. induction n;   intros. lia.
       destruct n. simpl. 
       rewrite map2_r_refl.
       apply H. lia.  
       simpl.
       apply d_seman_app_aux.
       assert(StateMap.Raw.map2 option_app (big_app f n) (f n)=
       big_app f (S n)).
       reflexivity. rewrite H2.
       apply H0. lia.
       apply H. lia. 
       apply IHn.
       intros. apply H.
       lia. intros. apply H0.
       lia. lia.
       apply H. lia. 
Qed.

Lemma State_eval_sum{ s e:nat}: forall n c (f:nat -> qstate s e) F , 
(forall j, j<n -> (WF_qstate (f j)) /\ State_eval F (c, (f j)))->
(forall i, i<n -> WF_qstate (@big_sum  (Matrix (2^(e-s)) (2^(e-s))) (M_is_monoid (2^(e-s)) (2^(e-s)))  f i)) ->
n>0->
State_eval F (c, @big_sum  (Matrix (2^(e-s)) (2^(e-s))) (M_is_monoid (2^(e-s)) (2^(e-s))) f n)  .
Proof.
induction n;   intros. lia.
       destruct n. simpl. 
       rewrite Mplus_0_l.
       apply H. lia.  
       simpl.
       apply State_eval_plus.
       assert(@Mplus  (2^(e-s))  (2^(e-s)) 
       (@big_sum  (Matrix (2^(e-s)) (2^(e-s))) _ f n) (f n)=
       @big_sum  (Matrix (2^(e-s)) (2^(e-s))) _ f (S n)).
       reflexivity.
       rewrite H2.
       apply H0. lia.
       apply H. lia. 
       apply IHn.
       intros. apply H.
       lia. intros. apply H0.
       lia. lia.
       apply H. lia.
Qed. 

Lemma QExp_eval_sub: forall (qs: QExp) s e c (q1 q2 q': qstate s e) ,
@Mplus (2^(e-s)) (2^(e-s)) q1  q2= q'->
State_eval qs (c, q')->
State_eval qs (c, q1) /\
State_eval qs (c, q2).
Proof. induction qs; intros.
       destruct H. 
      admit.
      destruct H.
      simpl in H0.
      destruct H0. destruct H0.
      apply (IHqs1 _ _ _  q1 q2) in H0 .
      apply (IHqs2 _ _ _  q1 q2) in H1 .
      
      simpl. split. 
      intuition. intuition. reflexivity.
      reflexivity. 
Admitted.



Lemma QExp_eval_sub': forall F s e c (q1 q2 q': qstate s e) ,
@Mplus (2^(e-s)) (2^(e-s)) q1  q2= q'->
State_eval F (c, q')->
State_eval F (c, q1) /\
State_eval F (c, q2).
Proof. induction F; intros.
       split;
       apply state_eq_Pure with (c,q');
       try reflexivity; try assumption. 
        
       apply QExp_eval_sub with q'.
       assumption.
       assumption.
      
      simpl in H0.
      destruct H0. destruct H1.
      apply (IHF1 _ _ _  q1 q2) in H1 .
      apply (IHF2 _ _ _  q1 q2) in H2 .
      
      simpl. split. 
      intuition. intuition. assumption. assumption.

      simpl in H0.
      destruct H0. 
      apply (IHF1 _ _ _  q1 q2) in H0 .
      apply (IHF2 _ _ _  q1 q2) in H1 .
      
      simpl. split. 
      intuition. intuition. assumption. assumption.
Qed.


Lemma State_eval_sub_sum{ s e:nat}: forall n c (f:nat -> qstate s e) F , 
(forall i, i<n -> WF_qstate (@big_sum  (Matrix (2^(e-s)) (2^(e-s))) (M_is_monoid (2^(e-s)) (2^(e-s)))  f i)) ->
State_eval F (c, @big_sum  (Matrix (2^(e-s)) (2^(e-s))) (M_is_monoid (2^(e-s)) (2^(e-s))) f n)->
(forall j, j<n -> State_eval F (c, (f j))).
Proof. induction n; intros. simpl in *. lia.
       simpl in H0.
       apply (QExp_eval_sub' F _ _ _ 
       (big_sum f n) (f n)) in H0.
       destruct H0.
       assert(j = n \/ j< n). lia. destruct H3.
       rewrite H3. assumption.
       apply IHn.
       intros.
       apply H. lia. assumption.
        lia.
        reflexivity.
Qed.

Fixpoint dstate_eq_qstate{s e:nat} (mu:list (cstate * qstate s e)) (q:qstate s e):=
match mu with 
|nil=> False
|(c1, q1)::mu' => and (exists p1:R, and (0<p1)%R (q1 = p1 .* q)) (dstate_eq_qstate mu' q)
end.

Definition cstate_eq c1 c2 (c:NSet.t) :=
        forall j, NSet.In j c-> c_find j c1 = c_find j c2.

Lemma  cstate_eq_union: forall c1 c2 x y,
cstate_eq c1 c2 (NSet.union x y)->
cstate_eq c1 c2 x /\ cstate_eq c1 c2 y .
Proof. unfold cstate_eq. intros.
      split. intros.
      apply H. 
      apply NSet.union_2.
      assumption.
      intros. 
      apply H.
      apply NSet.union_3.
      assumption.
       
Qed.



Lemma cstate_eq_a{ s e:nat}: forall c1 c2 (a:aexp) (q: qstate s e),
cstate_eq c1 c2 (Free_aexp a)->
aeval (c1, q) a=aeval (c2,q) a.
Proof. induction a; intros. reflexivity.
       unfold cstate_eq in H. simpl in H.
       simpl. apply H. 
       apply NSet.add_1.
       reflexivity.
       simpl in *. 
       apply cstate_eq_union in H.
       rewrite IHa1. rewrite IHa2.
       reflexivity. intuition.
       intuition. 
       simpl in *. 
       apply cstate_eq_union in H.
        rewrite IHa1. rewrite IHa2.
       reflexivity. intuition. intuition. 
       simpl in *. 
       apply cstate_eq_union in H.
        rewrite IHa1. rewrite IHa2.
       reflexivity. intuition. intuition.
       simpl in *. 
       apply cstate_eq_union in H.
        rewrite IHa1. rewrite IHa2.
       reflexivity. intuition. intuition.
       simpl in *. 
       apply cstate_eq_union in H.
        rewrite IHa1. rewrite IHa2.
       reflexivity. intuition. intuition.
       simpl in *. 
       apply cstate_eq_union in H.
        rewrite IHa1. rewrite IHa2.
       reflexivity. intuition. intuition.
       simpl in *. 
       apply cstate_eq_union in H.
        rewrite IHa1. rewrite IHa2.
       reflexivity. intuition. intuition.     
Qed.


Lemma cstate_eq_b{ s e:nat}: forall c1 c2 (b:bexp) (q: qstate s e),
cstate_eq c1 c2 (Free_bexp b)->
beval (c1, q) b=beval (c2,q) b.
Proof. induction b; intros. 
       reflexivity. reflexivity.
       simpl in *. 
       apply cstate_eq_union in H.
       rewrite (cstate_eq_a c1 c2 a1).
       rewrite (cstate_eq_a c1 c2 a2).
       reflexivity. intuition. intuition. 
       simpl in *. 
       apply cstate_eq_union in H.
       rewrite (cstate_eq_a c1 c2 a1).
       rewrite (cstate_eq_a c1 c2 a2).
       reflexivity. intuition. intuition.
       simpl in *. 
       apply cstate_eq_union in H.
       rewrite (cstate_eq_a c1 c2 a1).
       rewrite (cstate_eq_a c1 c2 a2).
       reflexivity. intuition. intuition.
       simpl in *. 
       apply cstate_eq_union in H.
       rewrite (cstate_eq_a c1 c2 a1).
       rewrite (cstate_eq_a c1 c2 a2).
       reflexivity. intuition. intuition.   
       simpl in *.
       rewrite IHb. reflexivity. assumption. 
       simpl in *. apply cstate_eq_union in H.
       rewrite IHb1. rewrite IHb2.
       reflexivity. intuition. intuition.   
Admitted.


Lemma cstate_eq_P{ s e:nat}: forall c1 c2 P (q: qstate s e),
cstate_eq c1 c2 (Free_pure P)->
State_eval P (c1, q)->
State_eval P (c2, q).
Proof. induction P; intros. 
       simpl. simpl in H0.
       rewrite<- (cstate_eq_b c1).
       assumption. assumption.
       simpl in *.
Admitted.


Fixpoint dstate_eq_cstate{s e:nat} (mu1 mu2:list (cstate * qstate s e)) c:=
match mu1 ,mu2 with 
|nil, nil=> True
|(c1, q1)::mu1', (c2,q2)::mu2' => and (cstate_eq c1 c2 c) (dstate_eq_cstate mu1' mu2' c)
|_, _ => False
end.

Lemma cstate_eq_d{s e:nat}: forall (mu1 mu2:list (cstate * qstate s e)) P,
dstate_eq_cstate mu1 mu2 (Free_pure P)->
State_eval_dstate P mu1 ->
State_eval_dstate P mu2.
Proof. induction mu1; induction mu2; intros. simpl in *. destruct H0.
       destruct a. simpl in *. destruct H.
       destruct a.
       simpl in *. destruct H.
       destruct mu2. 
       destruct a. destruct a0.
       econstructor.
       simpl in H.
       apply cstate_eq_P with c.
       intuition.
       simpl.
       rewrite (state_eq_Pure _  _ (c,q)).
       inversion_clear H0.
       assumption. reflexivity.
       econstructor.
       destruct a.
       destruct a0. 
       econstructor.
       simpl in H.
       apply cstate_eq_P with c.
       intuition.
       simpl.
       rewrite (state_eq_Pure _  _ (c,q)).
       inversion_clear H0.
       assumption.
       reflexivity.
       rewrite <-State_eval_dstate_Forall.
       apply IHmu1.
       simpl in H. 
       intuition. destruct mu1. simpl in *.
       destruct H. destruct H1.
       inversion_clear H0.
       rewrite State_eval_dstate_Forall.
       assumption. discriminate. discriminate.
Qed. 

Lemma cstate_eq_F{ s e:nat}: forall c1 c2 F (q: qstate s e),
cstate_eq c1 c2 (fst (Free_state F))->
State_eval F (c1, q)->
State_eval F (c2, q).
Proof. induction F; intros.
       apply cstate_eq_P with c1.
       assumption. assumption.
       apply qstate_eq_Qexp with (c1,q).
       reflexivity. assumption.
       simpl in *. 
       split. intuition.
       split. apply IHF1. 
       admit. intuition.
       apply IHF2. admit. intuition. 
       
Admitted.



(* Lemma dstate_qstate_eq'_F{ s e:nat}: forall (mu1 mu2:list (cstate * qstate s e)) (q:qstate s e) F,
dstate_eq_qstate mu1 q ->
dstate_eq_qstate mu2 q->
(dstate_eq_cstate mu1 mu2 (fst (Free_state F))) ->
State_eval_dstate F mu1->
State_eval_dstate F mu2.
Proof. induction mu1; intros. simpl in *. destruct H.
       destruct a. 
       simpl in *.
       destruct H. destruct H.
       destruct H.
       inversion_clear H2.
       rewrite H4 in H5.
       assert((c, x .* q)= s_scale x (c,q)).
       unfold s_scale. reflexivity.
       unfold qstate in H5.
       rewrite H2 in H5.
       rewrite <-s_seman_scale in H5.
       induction mu2.
       simpl in *. destruct H0.
       destruct mu2. 
       destruct a. 
       simpl in H0. 
       destruct H0. destruct H0.
       destruct H0. rewrite H8.
       econstructor.
       assert((c0, x0 .* q)= s_scale x0 (c0,q)).
       unfold s_scale. reflexivity.
       unfold qstate.
       rewrite H9. 
       rewrite <-s_seman_scale. 
       admit.  assumption.
       econstructor.
       simpl.
       destruct a. 
       econstructor. 
       simpl in H0. destruct H0.
       destruct H0. destruct H0.
       rewrite H8.
       assert((c0, x0 .* q)= s_scale x0 (c0,q)).
       unfold s_scale. reflexivity.
       unfold qstate.
       rewrite H9. 
       rewrite <-s_seman_scale.


       rewrite <-State_eval_dstate_Forall.
       apply IHmu2.
       simpl in H0. intuition.
       intros.
       apply H1 in H7.
       simpl in H7. simpl. inversion_clear H7.
       assumption.
       intuition. discriminate.
       assumption. 
       
Qed. *)


Lemma r10{ s e:nat}: forall c (q: qstate s e) s0 e0 s1 e1 s2 e2 i j F,
s1 <= s0 /\ s0 <= e0 /\ e0 <= e1 /\ s2 <= e2 ->
WF_qstate q->
dstate_Separ [(c, q)] s1 e1 s2 e2 ->
NSet.Subset (Qsys_to_Set s0 e0) (Qsys_to_Set s1 e1)->
NSet.Equal
(NSet.inter (fst (Free_state F))
(fst (MVar <{ i :=M [[s0 e0]] }>))) NSet.empty ->
State_eval F (c, PMpar_trace q s2 e2)->
State_eval F (c_update i j c, PMpar_trace (QMeas_fun s0 e0 j q) s2 e2).
Proof. intros c q s0 e0 s1 e1 s2 e2 i j F Hw. intros.  
simpl in *. 
inversion H0; subst.
clear H0. clear H17.
rewrite big_sum_par_trace in *.
rewrite (@QMeas_fun_sum s e).
rewrite big_sum_par_trace.
apply State_eval_sum.
intros. split.
apply WF_par_trace. intuition. 
admit.
assert(@State_eval s e F
(c, ((fun i : nat => 
@PMpar_trace s e
(@kron (2 ^ (s2 - s)) (2 ^ (s2 - s)) (2 ^ (e - s2)) (2 ^ (e - s2)) 
(q0_i i)  (q1_i i)) s2 e) j0))).
eapply (@State_eval_sub_sum s e n c 
((fun i : nat => 
@PMpar_trace s e
(@kron (2 ^ (s2 - s)) (2 ^ (s2 - s)) (2 ^ (e - s2)) (2 ^ (e - s2)) 
(q0_i i)  (q1_i i)) s2 e))).
intros.
admit. 
admit.
assumption.
simpl in *.
rewrite PMpar_trace_R in *; try reflexivity.
rewrite (PMpar_trace_r _ (q0_i j0 )  (q1_i j0)) in H4; try reflexivity.
rewrite QMeas_fun_kron.
rewrite (PMpar_trace_r _ (QMeas_fun s0 e0 j (q0_i j0))  (q1_i j0));try reflexivity.
admit.
admit.
apply WF_Mixed. apply H11.
admit.
admit.
apply WF_Mixed. apply H11.
intuition.
apply WF_Mixed. apply H10.
apply WF_Mixed. apply H11.
apply WF_kron; type_sovle'.
apply WF_Mixed. apply H10.
apply WF_Mixed. apply H11.
apply WF_kron; type_sovle'.
apply WF_Mixed. apply H10.
apply WF_Mixed. apply H11.
admit.
intros. admit. admit.
intuition.
intuition.
intuition.
Admitted.

Lemma d_par_trace_trace{s e:nat}: forall (l r : nat) (mu: list (cstate * qstate s e)),
s <= l /\ l <= r <= e -> 
WF_Matrix_dstate mu ->
 d_trace_aux mu =
 d_trace_aux (d_par_trace mu l r).
Proof. induction mu; intros. simpl. reflexivity.
      destruct a. simpl. unfold s_trace.
      simpl.  rewrite  Ptrace_trace.
      rewrite IHmu. reflexivity.
      intuition. inversion_clear H0. intuition.
      intuition. inversion_clear H0. 
       intuition.


       
Qed.


Lemma WF_Mixed_dstate{ s e: nat}: forall (mu : list (cstate * qstate s e)), 
WF_dstate_aux mu -> WF_Matrix_dstate mu.
Proof. induction mu; intros. econstructor.
      destruct a. inversion H; subst.
      econstructor. apply WF_Mixed.
      apply H2.
      apply IHmu.
      apply H3.       
Qed.

Lemma WF_d_par_trace: forall (s e l r : nat) (mu: list (cstate * qstate s e)),
s <= l /\ l <= r <= e -> WF_dstate_aux mu ->
 WF_dstate_aux (d_par_trace mu l r).
Proof. induction mu; intros. simpl. econstructor.
destruct a. simpl. econstructor.
unfold WF_state. simpl. apply WF_par_trace.
intuition. inversion_clear H0. assumption.
apply IHmu. intuition. inversion_clear H0.
assumption. assert((((c, PMpar_trace q l r) :: d_par_trace mu l r)=
d_par_trace ((c, q) :: mu) l r)).
simpl. reflexivity.
unfold state.
rewrite H1. 
rewrite <-d_par_trace_trace.
inversion_clear H0. assumption.
intuition.
apply WF_Mixed_dstate.
assumption.



       
Qed.




Lemma r4{s e:nat}: forall c s0 e0 s1 e1
(mu mu':list (cstate *qstate s e)) F ,
WF_dstate_aux mu ->
ceval_single c mu mu'-> 
dstate_Separ mu s0 e0 s1 e1->
NSet.Equal (NSet.inter (fst (Free_state F)) (fst (MVar c))) (NSet.empty)  ->
NSet.Subset (snd (MVar c)) (Qsys_to_Set s0 e0) ->
State_eval_dstate F (d_par_trace mu s1 e1) ->
State_eval_dstate F (d_par_trace mu' s1 e1).
Proof. induction c. 
-- {intros s0 e0 s1 e1 mu mu' F Hw. intros. apply ceval_skip_1 in H. subst. intuition. }
-- admit.
-- induction mu; intros mu' F Hw; intros. 
  {inversion  H; subst. intuition.  }
   {destruct a0. inversion H; subst. clear H.
   rewrite d_par_trace_map2.
   inversion_clear H3.
   destruct mu. inversion_clear H10.
   simpl.
   econstructor. 
   apply cstate_eq_F with c.
   simpl in H1. 
   unfold cstate_eq.
   intros. rewrite c_update_find_not.
   reflexivity.
   unfold not.
   intros. rewrite<-H5 in *.
   admit. assumption. 
   econstructor.
   apply d_seman_app_aux.
   apply WF_d_par_trace.
   admit. apply WF_state_dstate_aux.
   apply WF_state_eq with (c, q).
   reflexivity. inversion_clear Hw. assumption.
   apply WF_d_par_trace.
   admit. apply WF_ceval with <{ i := a }> (p :: mu).
   inversion_clear Hw. assumption.
   assumption. 
   simpl. econstructor.
   apply cstate_eq_F with c.
   simpl in H1. 
   unfold cstate_eq.
   intros. rewrite c_update_find_not.
   reflexivity.
   unfold not.
admit. assumption. econstructor.
apply IHmu. inversion_clear Hw. assumption. 
assumption. 
inversion H0; subst.   intuition.
assumption. assumption.
destruct p. simpl. assumption. } 
-- admit.
--{ intros s0 e0 s1 e1 mu mu' F Hw. intros. inversion H; subst. intuition.
    (* assert(State_eval_dstate F (d_par_trace mu1 s1 e1) ).
    apply IHc1 with s0 e0 ((sigma, rho) :: mu0).
    assumption. assumption.
    admit. admit.
    assumption. *)
   apply IHc2 with s0 e0 mu1.
   apply WF_ceval with c1 ((sigma, rho) :: mu0).
   assumption. assumption. 
   assumption. 
   apply r3 with c1 ((sigma, rho) :: mu0) F.
   assumption. assumption.
   simpl in H1. 
   rewrite inter_union_dist in H1.
   rewrite union_empty in H1. intuition.
   simpl in H2. 
   apply subset_union in H2.
   intuition. simpl in H1.
   rewrite inter_union_dist in H1.
   rewrite union_empty in H1. intuition.
   simpl in H2. 
   apply subset_union in H2.
   intuition.
   apply IHc1 with s0 e0  ((sigma, rho) :: mu0).
   assumption.
   assumption.
   assumption.
   simpl in H1.
   rewrite inter_union_dist in H1.
   rewrite union_empty in H1. intuition.
   simpl in H2. 
   apply subset_union in H2.
   intuition.
   assumption.
   }
   {induction mu; intros mu' F Hw; intros. inversion_clear H. intuition.
   destruct a. inversion H; subst; clear H;
   rewrite d_par_trace_map2;
   inversion_clear H3.
   destruct mu. inversion H12;subst.
   simpl. repeat rewrite map2_nil_r.
   apply IHc1 with s0 e0 [(c,q)].
   assumption. assumption. assumption.
   simpl in H1.
   rewrite inter_union_dist in H1.
   rewrite union_empty in H1. intuition.
   simpl in H2. 
   apply subset_union in H2.
   intuition.
   simpl. econstructor. assumption. 
   econstructor.  
   apply d_seman_app_aux.
   apply WF_d_par_trace.
   admit. apply WF_ceval  with c1 [(c, q)].
   apply WF_state_dstate_aux.
   inversion_clear Hw. assumption.
   assumption.
   apply WF_d_par_trace. admit.
   apply WF_ceval with <{ if b then c1 else c2 end }> (p :: mu).
   inversion_clear Hw.
   assumption. assumption.
   apply IHc1 with s0 e0 [(c,q)].
   apply WF_state_dstate_aux. 
   inversion_clear Hw. intuition. 
   assumption. inversion_clear H0; subst.
   econstructor; try reflexivity. assumption.
   assumption. econstructor.
   simpl in H1.
   rewrite inter_union_dist in H1.
   rewrite union_empty in H1. intuition.
   simpl in H2. 
   apply subset_union in H2.
   intuition.
   simpl. econstructor. assumption.
   econstructor.
   apply IHmu. inversion_clear Hw; intuition.
   assumption. inversion_clear H0. assumption.
   assumption.
   assumption.
   destruct p. 
   simpl. assumption.

   destruct mu. inversion H12;subst.
   simpl. repeat rewrite map2_nil_r.
   apply IHc2 with s0 e0 [(c,q)].
   assumption. assumption.
   assumption. 
   simpl in H1.
   rewrite inter_union_dist in H1.
   rewrite union_empty in H1. intuition.
   simpl in H2. 
   apply subset_union in H2.
   intuition.
   simpl. econstructor. assumption. 
   econstructor.  
   apply d_seman_app_aux.
   apply WF_d_par_trace.
   admit. apply WF_ceval  with c2 [(c, q)].
   apply WF_state_dstate_aux.
   inversion_clear Hw. assumption.
   assumption.
   apply WF_d_par_trace. admit.
   apply WF_ceval with <{ if b then c1 else c2 end }> (p :: mu).
   inversion_clear Hw.
   assumption. assumption.
   apply IHc2 with s0 e0 [(c,q)].
   apply WF_state_dstate_aux. 
   inversion_clear Hw. intuition. 
   assumption.
   inversion_clear H0; subst.
   econstructor; try reflexivity. assumption.
   assumption. econstructor. 
   simpl in H1.
   rewrite inter_union_dist in H1.
   rewrite union_empty in H1. intuition.
   simpl in H2. 
   apply subset_union in H2.
   intuition.
   simpl. econstructor. assumption.
   econstructor.
   apply IHmu. inversion_clear Hw.
   assumption. assumption.
   inversion_clear H0. assumption. 
   assumption.
   assumption.
   destruct p. 
   simpl. assumption. }
{ admit. }
{induction mu; intros mu' F Hw; intros.
{inversion  H; subst. intuition.  }
 {destruct a. inversion H; subst. clear H.
 rewrite d_par_trace_map2.
 inversion_clear H3.
 destruct mu. inversion_clear H11.
 simpl.
 econstructor. 
 rewrite (PMpar_trace_QInit c _ _ _ s1 e1).
 assumption. assumption.  admit. 
 econstructor.
 apply d_seman_app_aux.
 apply WF_d_par_trace.
 admit. apply WF_ceval  with <{ (s0 e0) :Q= 0 }>  [(c, q)]. 
 apply WF_state_dstate_aux.
 inversion_clear Hw. assumption.
 admit.
 apply WF_d_par_trace. admit.
 apply WF_ceval with <{ (s0 e0) :Q= 0 }> (p :: mu).
 inversion_clear Hw.
 assumption. assumption.

 simpl. econstructor. 
 rewrite (PMpar_trace_QInit c _ _ _ s1 e1).
 assumption. inversion H0; subst. econstructor; try reflexivity.
 assumption. assumption. econstructor.  
  admit. 
 econstructor.
apply IHmu. inversion_clear Hw. assumption. 
assumption. 
inversion H0; subst.  intuition.
assumption. assumption.
destruct p. simpl. assumption. }  }

{induction mu; intros mu' F Hw; intros.
{inversion  H; subst. intuition.  }
 {destruct a. inversion H; subst. clear H.
 apply inj_pair2_eq_dec in H6.
 apply inj_pair2_eq_dec in H6.
 destruct H6.
 rewrite d_par_trace_map2.
 inversion_clear H3.
 destruct mu. inversion_clear H13.
 simpl.
 econstructor. 
 rewrite (PMpar_trace_QUnit_one c _ _ _ _ s1 e1).
 assumption. assumption.  admit.
 assumption. 
 econstructor.
 apply d_seman_app_aux.
 apply WF_d_par_trace.
 admit. apply WF_ceval  with (QUnit_One s0 e0 U1)  [(c, q)]. 
 apply WF_state_dstate_aux.
 inversion_clear Hw. assumption.
 admit.
 apply WF_d_par_trace. admit.
 apply WF_ceval with (QUnit_One s0 e0 U1) (p :: mu).
 inversion_clear Hw.
 assumption. assumption.
 simpl. econstructor. 
 rewrite (PMpar_trace_QUnit_one c _ _ _ _ s1 e1).
 assumption. inversion H0; subst. econstructor; try reflexivity.
 assumption. assumption. econstructor.  admit.
 assumption.
 econstructor. 
apply IHmu. inversion_clear Hw. assumption.
assumption. 
inversion H0; subst. intuition.
assumption. assumption.
destruct p. simpl. assumption.
apply Nat.eq_dec. apply Nat.eq_dec. }  }


{induction mu; intros mu' F Hw; intros.
{inversion  H; subst. intuition.  }
 {destruct a. inversion H; subst. clear H.
 apply inj_pair2_eq_dec in H9.
 apply inj_pair2_eq_dec in H9.
 destruct H9.
 rewrite d_par_trace_map2.
 inversion_clear H3.
 destruct mu. inversion_clear H15.
 simpl.
 econstructor. 
 rewrite (PMpar_trace_QUnit_Ctrl c _ _ _ _ _ _  s2 e2).
 assumption. assumption.  admit.
 assumption. econstructor.
 apply d_seman_app_aux.
 apply WF_d_par_trace.
 admit. apply WF_ceval  with (QUnit_Ctrl s0 e0 s1 e1 U1)  [(c, q)]. 
 apply WF_state_dstate_aux.
 inversion_clear Hw. assumption.
 admit.
 apply WF_d_par_trace. admit.
 apply WF_ceval with (QUnit_Ctrl s0 e0 s1 e1 U1) (p :: mu).
 inversion_clear Hw.
 assumption. assumption. 
 simpl. econstructor.  
 rewrite (PMpar_trace_QUnit_Ctrl c _ _ _ _ _ _ s2 e2).
 assumption. inversion H0; subst. econstructor; try reflexivity.
 assumption. assumption. econstructor.  admit.
 assumption.
 econstructor.
apply IHmu. inversion_clear Hw; assumption.
assumption. 
inversion H0; subst. intuition.
assumption. assumption.
destruct p. simpl. assumption.
apply Nat.eq_dec. apply Nat.eq_dec. }  }

{induction mu; intros mu' F Hw; intros.
{inversion  H; subst. intuition.  }
 {destruct a. inversion H; subst. clear H.
 rewrite d_par_trace_map2.
 inversion_clear H3.
 destruct mu. inversion_clear H12.
 simpl. rewrite map2_nil_r.
 rewrite d_par_trace_app.
 apply big_app_seman.
 intros. split.
 apply WF_d_par_trace.   admit.
 admit.
 simpl. econstructor.
 apply r10 with s1 e1.
 admit. inversion_clear Hw. intuition. assumption. 
 simpl in *. assumption.
 assumption. assumption.
  econstructor.
  admit. apply pow_gt_0.
 apply d_seman_app_aux.
 apply WF_d_par_trace. 
 admit. apply WF_ceval  with <{ i :=M [[s0 e0]] }>  [(c, q)]. 
 apply WF_state_dstate_aux.
 inversion_clear Hw. assumption.
 admit.
 apply WF_d_par_trace. admit.
 apply WF_ceval with <{ i :=M [[s0 e0]] }> (p :: mu).
 inversion_clear Hw.
 assumption. assumption. 
 rewrite d_par_trace_app.
 apply big_app_seman.
 intros. split. apply WF_d_par_trace.
  admit. admit.
 simpl. econstructor.
 apply r10 with s1 e1.
 admit. inversion_clear Hw. assumption. inversion_clear H0; subst.
 econstructor; try reflexivity.
 assumption. assumption. econstructor. 
 simpl in *. assumption.
 assumption. assumption. 
econstructor.
 intros.
  admit.
  apply pow_gt_0. 
apply IHmu. inversion_clear Hw. assumption.
assumption. 
inversion  H0; subst. intuition.
assumption. assumption.
destruct p. simpl. assumption.
 }  }
Admitted.




Lemma State_dstate_free_eval{s e:nat}:forall  (mu: list (cstate * qstate s e)) (F: State_formula) s' e',
s<=s'/\ s'<=e' /\ e'<=e ->
s'<=(fst (Free_State F)) /\ (snd (Free_State F))<=e'->
WF_Matrix_dstate mu ->
State_eval_dstate F mu <-> 
State_eval_dstate F (d_par_trace mu s' e').
Proof. induction mu; intros. simpl. intuition.
       destruct mu; destruct a. 
       split; intros.
       inversion_clear H2. 
       econstructor.
       apply (State_free_eval _ (c, q)).  
       assumption. assumption. 
       inversion_clear H1. intuition.
       assumption. econstructor.
       
       inversion_clear H2.
       econstructor.
       apply (State_free_eval _ (c, q)) in H3.
       assumption. assumption. assumption.
       inversion_clear H1. intuition.
       econstructor.

       split; intros.
       inversion_clear H2.
       econstructor. 
       apply (State_free_eval _ (c, q)).  
       assumption. assumption. 
       inversion_clear H1. intuition.
       assumption.
       rewrite <-State_eval_dstate_Forall in H4. 
       rewrite (IHmu _ s' e') in H4.
       rewrite <-State_eval_dstate_Forall.
       apply H4. destruct p.  discriminate.
       assumption. assumption. 
       inversion_clear H1. intuition.
       discriminate. 
       
       econstructor. 
       inversion_clear H2.
       apply (State_free_eval _ (c, q)) in H3.  
       assumption. assumption. assumption. 
       inversion_clear H1. intuition.
       destruct p. 
       inversion_clear H2.
       rewrite <-State_eval_dstate_Forall. 
       rewrite (IHmu _ s' e').
       simpl. assumption. assumption.
       assumption.
       inversion_clear H1. intuition.
       discriminate.
Qed.


Lemma State_eval_odot:forall (s e : nat) (mu : list (cstate * qstate s e)) (F1 F2 : State_formula),
State_eval_dstate ((F1 ⊙ F2)) mu <->
State_eval_dstate F1 mu /\ State_eval_dstate F2 mu /\ 
NSet.Equal (NSet.inter (snd (Free_state F1))
         (snd (Free_state F2)))
     NSet.empty  .
Proof.
intros. split; intros; 
       induction mu; 
       simpl in H. destruct H.
       -destruct mu; destruct a; inversion_clear H; simpl;
        intuition.  
      -destruct H. destruct H. 
      -destruct a. destruct mu. simpl. econstructor. 
       destruct H. inversion_clear H. inversion_clear H0.
      split; inversion_clear H. intuition. intuition.  apply Forall_nil.
      simpl. econstructor.  destruct H. inversion_clear H.
      destruct H0.
      inversion_clear H. intuition.
      apply IHmu. destruct H. inversion_clear H. destruct H0.
      inversion_clear H. split. 
      intuition. intuition.  
Qed.

Lemma subset_trans:
forall x y z,
 NSet.Subset x y ->
 NSet.Subset y z ->
 NSet.Subset x z.
Proof. intros. unfold NSet.Subset in *.
       intros. intuition.
       
Qed.

Lemma Qsys_subset: 
forall r s e l  : nat,
s <=l /\ l <= r /\ r <= e
->NSet.Subset (Qsys_to_Set l r) (Qsys_to_Set s e).
Proof.
       unfold Qsys_to_Set. induction r; intros. 
      simpl. Search (NSet.empty). admit.
      simpl. 
      destruct H. destruct H0.
      assert(l=S r \/ l<> S r).
      apply Classical_Prop.classic.
      destruct H2.
      rewrite H2.
       assert(S r <? S r =false).
       admit.
       rewrite H3. admit.
       assert(l < S r).
       lia. apply Lt_n_i in H3. 
       rewrite H3.
       unfold NSet.Subset.
       intros.
       unfold NSet.Subset in IHr.
       assert(a= r \/ a<>r).
       apply Classical_Prop.classic.
       destruct H5. rewrite H5 in *.
       apply In_Qsys. lia.  
       lia. 
       assert(l = r \/ l<>r).  
       apply Classical_Prop.classic .
       destruct H6. rewrite H6 in *.
       admit.
       apply IHr with l.
       lia.
       apply NSet.add_3 in H4.
       assumption.
       lia.  
Admitted.






Lemma rule_f: forall  F1 F2 c s e (mu mu':list (cstate * qstate s e )) ,
Considered_Formula (F1 ⊙ F2) ->
WF_dstate_aux mu ->
State_eval_dstate (F1 ⊙ F2) mu->
ceval_single c mu mu'-> 
NSet.Equal (NSet.inter (fst (Free_state F2)) (fst (MVar c))) (NSet.empty) ->
NSet.Subset (snd (MVar c)) (Qsys_to_Set (fst (Free_State F1))  (snd  (Free_State F1)) ) ->
State_eval_dstate F2 mu'.
Proof. intros.
pose H. simpl in H. destruct H.
destruct a. destruct o. 

rewrite (State_dstate_free_eval _ _ (fst (Free_State (F2)))
(snd (Free_State (F2)))).
assert(d_par_trace mu' (fst (Free_State F2))
       (snd (Free_State F2))=
       d_par_trace (d_par_trace mu' (fst (Free_State (F1 ⊙ F2)))
       (snd (Free_State (F1 ⊙ F2)))) (fst (Free_State F2))
     (snd (Free_State F2))).
rewrite d_par_trace_assoc. reflexivity.
assert(s <= fst (Free_State (F1 ⊙ F2)) /\ snd (Free_State (F1 ⊙ F2)) <=
e).
apply dstate_eval_dom with mu. assumption.
split. intuition. 
split. simpl. 
apply min_le_iff.
right. intuition.
split. apply Considered_Formula_dom.
assumption. split. simpl. 
rewrite le_max. intuition. 
rewrite e0. apply Considered_Formula_dom.
assumption. intuition.
rewrite H.  
remember ((d_par_trace mu (fst (Free_State (F1 ⊙ F2)))
       (snd (Free_State (F1 ⊙ F2))))).
 apply r4 with c (fst (Free_State F1))
(snd (Free_State F1)) l.
rewrite Heql. apply WF_d_par_trace.
assert(s <= fst (Free_State (F1 ⊙ F2)) /\ snd (Free_State (F1 ⊙ F2)) <=
e).
apply dstate_eval_dom with mu. assumption.
split. intuition. split.
apply Considered_Formula_dom. assumption.
intuition. assumption. rewrite Heql. 
apply Par_trace_ceval_swap.
assert(s <= fst (Free_State (F1 ⊙ F2)) /\ snd (Free_State (F1 ⊙ F2)) <=
e).
apply dstate_eval_dom with mu. assumption.
split. intuition. 
split.
apply Considered_Formula_dom. assumption.
intuition.
simpl. rewrite le_min.
rewrite le_max.
apply subset_trans with 
(Qsys_to_Set (fst (Free_State F1)) (snd (Free_State F1))).
assumption. apply Qsys_subset.
split. intuition.
split. apply Considered_Formula_dom.
assumption. rewrite e0.
apply Considered_Formula_dom. assumption.
rewrite e0. apply Considered_Formula_dom.
assumption. rewrite<-e0.
apply Considered_Formula_dom. assumption.
apply WF_Mixed_dstate. assumption.
assumption.
rewrite Heql. apply r1.
intuition.
assumption.
assumption.
assumption.
assumption.
rewrite Heql.
assert(d_par_trace mu (fst (Free_State F2))
       (snd (Free_State F2))=
       d_par_trace (d_par_trace mu (fst (Free_State (F1 ⊙ F2)))
       (snd (Free_State (F1 ⊙ F2)))) (fst (Free_State F2))
     (snd (Free_State F2))).
rewrite d_par_trace_assoc.
reflexivity.
assert(s <= fst (Free_State (F1 ⊙ F2)) /\ snd (Free_State (F1 ⊙ F2)) <=
e).
apply dstate_eval_dom with mu. assumption.
split. intuition. 
split. simpl. 
apply min_le_iff.
right. intuition.
split. apply Considered_Formula_dom.
assumption. split. simpl. 
rewrite le_max. intuition. 
rewrite e0. apply Considered_Formula_dom.
assumption. intuition. 
rewrite <-H5.
rewrite State_eval_odot in H1.
rewrite <-State_dstate_free_eval.
intuition.
assert(s <= fst (Free_State (F2)) /\ snd (Free_State (F2)) <=
e).
apply dstate_eval_dom with mu.
intuition. 
split. intuition.
split.
apply Considered_Formula_dom.
assumption. 
intuition. intuition.
apply WF_Mixed_dstate. assumption.
assert(s <= fst (Free_State (F2)) /\ snd (Free_State (F2)) <=
e).
apply dstate_eval_dom with mu.
rewrite State_eval_odot in H1.
intuition. 
split. intuition.
split.
apply Considered_Formula_dom.
assumption. 
intuition. intuition.
intuition.
apply WF_Mixed_dstate.
apply WF_ceval with c mu. 
 assumption. assumption.






Admitted.




Theorem rule_qframe: forall (F1 F2 F3: State_formula) c,
Considered_Formula (F1 ⊙ F3)->
Considered_Formula (F2 ⊙ F3)->
         ({{F1}} c {{F2}}) /\  (NSet.Equal (NSet.inter (fst (Free_state F3)) (fst (MVar c))) (NSet.empty) )
         /\ (NSet.Subset (snd (MVar c)) (Qsys_to_Set (fst (Free_State F1))  (snd  (Free_State F1)) ) )
         ->  {{F1 ⊙ F3}} c {{F2 ⊙ F3}}.
Proof.  unfold hoare_triple.  intros F1 F2 F3 c Hc1 Hc2. intros. destruct H.
        assert(sat_Assert mu F1 -> sat_Assert mu' F2).
        apply H. assumption. 
        destruct mu as [mu IHmu].
        destruct mu' as [mu' IHmu'].
        inversion_clear H0. simpl in H6.
        repeat rewrite sat_Assert_to_State in *.
        inversion_clear H1.  simpl in *.
        econstructor. assumption. simpl in *.
        pose H7.
        rewrite State_eval_odot in s0.
        rewrite State_eval_odot.
        destruct s0. destruct H8.
        split. 
        assert(sat_Assert (StateMap.Build_slist IHmu') F2).
        apply H with (StateMap.Build_slist IHmu).
        apply E_com. assumption. assumption.
        assumption. rewrite sat_Assert_to_State.
        econstructor. assumption. assumption.
        rewrite sat_Assert_to_State in *.
        inversion_clear H10. assumption.
        split. apply rule_f  with F1 c mu.
        assumption. 
        assumption. assumption. assumption.
         intuition.  intuition.
         admit.
Admitted.







(* Lemma rule_f: forall  F1 F2 c n (mu mu':list (cstate * qstate n )) ,
State_eval_dstate (F1 ⊙ F2) mu->
ceval_single c mu mu'-> 
NSet.Subset (fst (MVar c)) (fst (Free_state F1))->
NSet.Subset (snd (MVar c)) (snd (Free_state F1))->
State_eval_dstate F2 mu'.
Proof. induction c. intros. 
-(*skip*) apply ceval_skip_1 in H0. rewrite <-H0.
  rewrite State_eval_odot in H.  intuition.
-admit.
-intros. inversion H0; subst.  assumption. *)
(* Lemma rule_f': forall a s e sigma (rho:qstate s e) i a',
NSet.Equal (NSet.inter (NSet.add i NSet.empty)
       ((Free_aexp a))) (NSet.empty) ->
 aeval 
  (c_update i (aeval (sigma, rho) a') sigma, rho) a =
  aeval 
  (sigma, rho) a .
Proof. induction a; intros.
       simpl. reflexivity.   
       simpl in *. 
       assert(i0<>i). admit.
       rewrite c_update_find_not.
       reflexivity. assumption.
       simpl in *. rewrite IHa1.
       rewrite IHa2. reflexivity.
       admit. admit.
       simpl in *. rewrite IHa1.
       rewrite IHa2. reflexivity.
       admit. admit.
       simpl in *. rewrite IHa1.
       rewrite IHa2. reflexivity.
       admit. admit.
       simpl in *. rewrite IHa1.
       rewrite IHa2. reflexivity.
       admit. admit.
       simpl in *. rewrite IHa1.
       rewrite IHa2. reflexivity.
       admit. admit.
       simpl in *. rewrite IHa1.
       rewrite IHa2. reflexivity.
       admit. admit.
       simpl in *. rewrite IHa1.
       rewrite IHa2. reflexivity.
       admit. admit.
Admitted.

Lemma rule_f_b: forall b s e sigma (rho:qstate s e) i a,
NSet.Equal (NSet.inter (NSet.add i NSet.empty)
       ((Free_bexp b))) (NSet.empty) ->
beval 
  (c_update i (aeval (sigma, rho) a) sigma, rho) b=
beval 
  (sigma, rho) b .
Proof. induction b; intros.
       simpl. reflexivity.
       simpl. reflexivity.   
       simpl in *. repeat rewrite rule_f'.
       reflexivity. admit. admit.
       simpl in *. repeat rewrite rule_f'.
       reflexivity. admit. admit.
       simpl in *. repeat rewrite rule_f'.
       reflexivity. admit. admit.
       simpl in *. repeat rewrite rule_f'.
       reflexivity. admit. admit.
       simpl in *.  rewrite IHb.
       reflexivity. assumption.
       simpl in *. rewrite IHb1. rewrite IHb2.
       reflexivity. admit. admit.
       simpl in *. rewrite IHb1. rewrite IHb2.
       reflexivity. admit. admit.
Admitted.

(* Lemma Free_map: forall (P:nat->Pure_formula) (x y:nat) ,
(Free_pure (P x))= (Free_pure (P y)).
Proof. induction P. simpl. intros. induction (P x); induction (P y).
       destruct b; destruct b0. reflexivity.

  
Qed. *)


Lemma rule_f'_p: forall  P s e sigma (rho:qstate s e) i a,
NSet.Equal (NSet.inter (NSet.add i NSet.empty)
       ((Free_pure P))) (NSet.empty) ->
Pure_eval P
  (c_update i (aeval (sigma, rho) a) sigma, rho)<->
Pure_eval P
  (sigma, rho) .
Proof. induction P; intros.
       simpl. rewrite rule_f_b. reflexivity.    
       assumption. admit. admit.
       split. 
       simpl in *. intros.
       remember (c_update i (aeval (sigma, rho) a) sigma).
       apply (IHP _ _ c rho i0 a0).
       assumption.
       rewrite Heqc. admit.
       intros.
       simpl in *.
       remember (c_update i (aeval (sigma, rho) a) sigma).
       apply (IHP _ _ c rho i0 a0) in H0.
Admitted.

Lemma rule_f_assn: forall  F s e sigma (rho:qstate s e) i a,
NSet.Equal (NSet.inter (fst (MVar <{ i := a }>)) (fst (Free_state F))) NSet.empty ->
State_eval F (c_update i (aeval (sigma, rho) a) sigma, rho) <-> State_eval F (sigma, rho) .
Proof. induction F; intros; simpl in *. 
       apply rule_f'_p. assumption. 
       admit.
Admitted. *)




(* Fixpoint QExp_dom (qs:QExp) :=
  match qs with 
  | QExp_s s e v => (s, e) 
  | QExp_t qs1 qs2 =>  (QExp_dom qs1) .+ (QExp_dom qs2)
  end .

Fixpoint QExp_vec (qs: QExp) (s e:nat) :=
  match qs with 
  | QExp_s s e v => v 
  | QExp_t qs1 qs2 =>  (QExp_vec qs1) .+ (QExp_vec qs2)
  end . *)

(* Lemma QExp_pure: forall (qs: QExp) s e c (q : qstate s e) ,
State_eval qs (c, q)->
exists (q': Density (2^(e-s))) (p:R), and (Pure_State q')
(q=p .* q').
Proof. induction qs. intros. 
       simpl in H. 
  
Qed.


Lemma QExp_eval_sub: forall (qs: QExp) s e c (q q': qstate s e) ,
q_subseq q q'->
State_eval qs (c, q')->
State_eval qs (c, q).
Proof. induction qs; intros.
      inversion_clear H. subst. intuition.
      admit.
      inversion_clear H. subst. intuition.
      destruct H1. subst.
      simpl in H0.
      destruct H0. destruct H.
      destruct H. destruct H.
      destruct H. destruct H.
      destruct H. 
      inversion H; subst.
      simpl.
Admitted.



Lemma QExp_eval_sub': forall F s e c (q q': qstate s e) ,
q_subseq q q'->
State_eval F (c, q')->
State_eval F (c, q).
Proof. induction F; intros.
       apply state_eq_Pure with (c,q').
       reflexivity. intuition.
       inversion_clear H.
       subst. intuition.
       destruct H1.  subst.
       induction qs.
       simpl in H0. 
       simpl.  
       split. intuition.
       split. intuition.
       split. intuition.
       rewrite <-PMtrace_scale in *.
       rewrite PMtrace_plus in *.
       rewrite Mscale_plus_distr_r in *.
       destruct H0. destruct H0.
       destruct H1. 
       admit. lia. lia.
       admit.

       

      



Lemma State_eval_sub: forall s e (mu mu': list (state s e)) F,
d_subseq mu mu'->
State_eval_dstate F mu'->
State_eval_dstate F mu.
Proof. induction mu.  intros. destruct mu'.
       simpl in H0. destruct H0.
       simpl in H. destruct H.
       intros. destruct mu'.
       destruct a.
       simpl in H. destruct H.
       destruct mu; destruct mu';
       destruct a; destruct s0.
       simpl in H. 
       simpl. econstructor.
       inversion_clear H0.
       admit. 
       
       econstructor.

       simpl in H. intuition.
       destruct s1.
       simpl in H. intuition.
       simpl. econstructor.
       admit.
       apply IHmu with (s2 :: mu').
       destruct s1. destruct s2.
       simpl in H. econstructor. intuition.
       split. intuition. intuition.
       inversion_clear H0. intuition.   
 Admitted. *)



(* Lemma rule_f_qinit_qs: forall  F1 F2 s' e' (st st': (cstate * qstate s' e' )) s e,
State_eval (F1 ⊙ F2) st->
ceval_single (QInit s e) [st] [st']-> 
NSet.Subset (snd (MVar (QInit s e))) (snd (Free_state F1))->
State_eval F1 st'.
Proof. induction qs. intros. 
       inversion H0; subst. inversion H8; subst.
       inversion_clear H8. injection H7.
       intros. rewrite <-H2.  clear H7. clear H2.


       assert(e < s0 \/ s> e0)%nat. admit.
       destruct H2.
       simpl in *. split. intuition.
       split. intuition.  
        admit.
        intros.
        simpl in *.
        split.  intuition.
        split. apply (IHqs1 F1  n st st' s e).
        split. admit. intuition.
        assumption. assumption.
        apply (IHqs2 F1  n st st' s e).
        split. admit. intuition.
        assumption. assumption.
Admitted. *)




(* Lemma rule_f_qinit: forall  F1 F2 F3 s' e' (st st': (cstate * qstate s' e' )) s e,
(forall (s0 e0: nat) (st st':(cstate * qstate s' e' )), 
State_eval F1 st -> 
ceval_single (QInit s e) [st] [st']-> 
State_eval F2 st') -> 
State_eval (F1 ⊙ F3) st->
ceval_single (QInit s e) [st] [st']-> 
NSet.Subset (snd (MVar (QInit s e))) (snd (Free_state F1))->
State_eval (F2 ⊙ F3) st'.
Proof. intros. inversion H0; subst. destruct st.
       destruct st'.  destruct H3.
       destruct H3. destruct H3. destruct H3.
       destruct H3. destruct H3. 
       inversion H3; subst. simpl in H10. 
       rewrite <-H10 in H1. simpl in H2.
       inversion H1; subst. inversion H13; subst.
       clear H13. injection H12. intros; subst.
       clear H12. simpl in H4. 
Admitted. *)

(* Inductive d_combin {s0 e0 s1 e1 s2 e2:nat}: (list (cstate * qstate s0 e0))-> (list (cstate * qstate s1 e1))-> (list (cstate * qstate s2 e2))-> Prop:=
|combin_nil: d_combin nil nil nil 
|combin_cons: forall sigma rho0  rho1  rho' mu0 mu1 mu',
              q_combin rho0 rho1 rho'->
              d_combin mu0 mu1 mu'->
               d_combin ((sigma, rho0)::mu0) ((sigma, rho1)::mu1) ((sigma, rho')::mu'). *)

(* Inductive q_combin{s0 e0 s1 e1 s2 e2}: (qstate s0 e0) -> (qstate s1 e1)-> (qstate s2 e2)->Prop:=
|combin_l: forall q0 q1, e0 = s1-> s0 = s2 -> e1 = e2 ->
            q_combin q0 q1 (@kron (2^(e0-s0)) (2^(e0-s0)) (2^(e1-s1))  
            (2^(e1-s1)) q0 q1)
|combin_r: forall q0 q1, e1 = s0-> s1= s2 -> e0 =e2 ->
            q_combin q0 q1 (@kron  (2^(e1-s1))  
            (2^(e1-s1)) (2^(e0-s0)) (2^(e0-s0)) q1 q0). *)

(* Inductive d_combin {s0 e0 s1 e1 s2 e2:nat}: (list (cstate * qstate s0 e0))-> (list (cstate * qstate s1 e1))-> (list (cstate * qstate s2 e2))-> Prop:=
|combin_nil: d_combin nil nil nil 
|combin_cons: forall sigma rho0  rho1  rho' mu0 mu1 mu',
      q_combin rho0 rho1 rho'->
      d_combin mu0 mu1 mu'->
        d_combin ((sigma, rho0)::mu0) ((sigma, rho1)::mu1) ((sigma, rho')::mu').

Fixpoint d_subseq{s e: nat} (mu0 mu1: list (cstate *qstate s e)): Prop:=
match mu0, mu1 with 
|nil , nil=> True
|(c0,q0)::mu0', (c1,q1)::(mu1')=>c0=c1 /\ q_subseq q0 q1 /\ d_subseq mu0' mu1'
|_, _=> False
end.

(* Lemma State_eval_combin: forall s e (mu:list(cstate * qstate s e)) (F1 F2:State_formula),
State_eval_dstate (F1 ⊙ F2) mu <->
(exists s0 e0 s1 e1 (mu0:list(cstate * qstate s0 e0)) (mu1:list(cstate * qstate s1 e1)), 
and (d_combin mu0 mu1 mu ) 
((State_eval_dstate F1 mu0 /\ State_eval_dstate F2 mu1)))
.
Proof. 
Admitted. *)


Lemma rule_6: forall c s e s0 e0 s1 e1
(q:qstate s0 e0) (q0:qstate s1 e1) (rho': qstate s e)
(x:list(cstate * qstate s0 e0))(x0:list(cstate * qstate s1 e1))
(x1:list(cstate * qstate s e)),
q_combin q q0 rho'->
d_combin x x0 x1 ->
exists (mu:list (cstate * qstate s e)),
d_combin (StateMap.Raw.map2 option_app [(c, q)] x)
    (StateMap.Raw.map2 option_app [(c, q0)] x0) mu.
Proof. 
induction x; intros. inversion_clear H0.
simpl. exists [(c, rho')].
econstructor. assumption. econstructor.
destruct a. 
inversion_clear H0.
simpl. destruct (Cstate_as_OT.compare c c0).
exists ((c,rho')::(c0,rho'0)::mu').
econstructor. assumption.
econstructor. assumption.
repeat rewrite map2_r_refl.
assumption.
inversion H; subst.
exists ((c,@kron (2^(s1-s)) (2^(s1-s))
(2^(e-s1)) (2^(e-s1)) (q .+ q1) (q0 .+ rho1))::mu').
apply (@combin_cons s s1 s1 e s e).
econstructor; try reflexivity.
repeat rewrite map2_r_refl.
assumption.
exists ((c,@kron  (2^(s0-s)) (2^(s0-s)) (2^(e-s0)) (2^(e-s0))
 (q0 .+ rho1) (q .+ q1))::mu').
apply (@combin_cons s0 e s s0 s e).
econstructor; try reflexivity.
repeat rewrite map2_r_refl.
assumption.
apply IHx in H2.
destruct H2.
exists ((c0,rho'0)::x2).
econstructor. 
assumption.
apply H0.
assumption.
Qed.

Lemma rule_7: forall s e s0 e0 s1 e1
(x mu1:list(cstate * qstate s0 e0))(x0 mu2:list(cstate * qstate s1 e1))
(x1 mu3:list(cstate * qstate s e)),
d_combin mu1 mu2 mu3->
d_combin x x0 x1 ->
exists (mu:list (cstate * qstate s e)),
d_combin (StateMap.Raw.map2 option_app mu1 x)
    (StateMap.Raw.map2 option_app mu2 x0) mu.
Proof. 
induction x; induction mu1; intros.
{ inversion_clear H0. inversion_clear H.
simpl. exists nil.
econstructor. }
{ destruct a. 
inversion_clear H0. inversion_clear H.
simpl. repeat rewrite map2_l_refl.
exists ((c,rho')::mu').
econstructor. assumption. assumption. }
{destruct a. 
inversion_clear H0. inversion_clear H.
simpl. repeat rewrite map2_r_refl.
exists ((c,rho')::mu').
econstructor. assumption. assumption. }
{destruct a0. destruct a.
inversion_clear H. inversion_clear H0. 
simpl. destruct (Cstate_as_OT.compare c c0).
assert (exists mu : list (cstate * qstate s e),
d_combin (StateMap.Raw.map2 option_app mu1 ((c0, q0) :: x))
(StateMap.Raw.map2 option_app mu4 ((c0, rho2) :: mu5)) mu ).
apply IHmu1 with ((c0, rho'0)::mu'0) mu'.
assumption. econstructor. assumption.
assumption. destruct H0.
exists ((c,rho')::x2).
econstructor. assumption.
assumption.

assert(exists mu'1 : list (cstate * qstate s e),
d_combin (StateMap.Raw.map2 option_app mu1 x)
(StateMap.Raw.map2 option_app mu4 mu5) mu'1).
apply IHx with mu'0 mu'.
assumption. assumption.
destruct H0.
inversion H1; subst.
exists ((c,@kron (2^(s1-s)) (2^(s1-s))
(2^(e-s1)) (2^(e-s1)) (q .+ q0) (rho1 .+ rho2))::x2).
apply (@combin_cons s s1 s1 e s e).
econstructor; try reflexivity.
assumption.
exists ((c,@kron  (2^(s0-s)) (2^(s0-s)) (2^(e-s0)) (2^(e-s0))
(rho1 .+ rho2)(q .+ q0) )::x2).
apply (@combin_cons s0 e s s0 s e).
econstructor; try reflexivity.
assumption.

assert (exists mu : list (cstate * qstate s e),
d_combin (StateMap.Raw.map2 option_app ((c, q)::mu1) x)
    (StateMap.Raw.map2 option_app ((c, rho1)::mu4) mu5) mu).
apply IHx with  mu'0 ((c, rho') ::mu').
econstructor. assumption.
assumption. assumption.
destruct H0. 
exists ((c0,rho'0)::x2).
econstructor.
assumption.
assumption. }
Qed.

Lemma q_combin_eq:forall s e s0 e0 s1 e1
(q:qstate s0 e0) (q0:qstate s1 e1) (rho rho': qstate s e),
q_combin q q0 rho->
q_combin q q0 rho'->
rho=rho'.
Proof. intros. inversion H; subst. 
       inversion H0; subst. reflexivity.
       assert(1=2^(s-s))%nat. rewrite Nat.sub_diag.
       rewrite pow_0_r. lia. unfold qstate. destruct H1.
       admit. 
       inversion H0; subst.
       admit.
       reflexivity.
Admitted.

Lemma d_combin_eq:forall s e s0 e0 s1 e1
(mu:list (state s0 e0)) (mu0: list (state s1 e1)) (mu1 mu2: list (state s e)),
d_combin mu mu0 mu1->
d_combin mu mu0 mu2->
mu1=mu2.
Proof. induction mu; intros. inversion H; subst. 
       inversion H0; subst. reflexivity.
       inversion H; subst.
       inversion H0; subst. f_equal.
       f_equal. apply q_combin_eq with 
       s0 e0 s1 e1 rho0 rho1; assumption.
       apply IHmu with mu4; assumption.
Qed.

Lemma q_subseq_eq:forall s e  (q q':qstate s e),
q=q'-> q_subseq q q'.
Proof. intros. subst. unfold q_subseq.
       left. reflexivity. 
Qed.

Lemma d_subseq_eq:forall s e (mu mu':list (state s e)),
mu=mu'-> d_subseq mu mu'.
Proof. induction mu; destruct mu'; intros.
      econstructor. destruct H. econstructor.
      destruct H. 
      destruct a. econstructor. reflexivity.
      split.
      apply q_subseq_eq. reflexivity.
      apply IHmu. reflexivity.
      injection H; intros; subst.
      destruct s0. 
      econstructor. reflexivity.
      split.  
      apply q_subseq_eq. reflexivity.
      apply IHmu. reflexivity.

Qed.

Lemma rule_three:  forall s e s0 e0 s1 e1
(x:list(cstate * qstate s0 e0))(x0:list(cstate * qstate s1 e1))
(q:qstate s0 e0) (q0:qstate s1 e1) (rho': qstate s e)
(mu'1 mu:list(cstate * qstate s e)) c ,
q_combin q q0 rho'->
d_combin x x0 mu'1->
(d_combin
  (StateMap.Raw.map2 option_app
     [(c,q)] x)
  (StateMap.Raw.map2 option_app
     [(c, q0)] x0) mu)
  -> d_subseq (StateMap.Raw.map2 option_app
  [(c,
    rho')] mu'1) mu.
Proof. induction x; intros.
--inversion H0; subst.  clear H0. simpl in H1. 
  simpl StateMap.Raw.map2. inversion_clear H1.
  inversion_clear H2. econstructor. reflexivity.
  split. 
  apply q_subseq_eq. apply q_combin_eq with s0
  e0 s1 e1 q q0. assumption. assumption. econstructor.
--destruct a. inversion H0; subst. clear H0.
  simpl in H1.  
  destruct (Cstate_as_OT.compare c c0);
  repeat rewrite map2_r_refl in H1.
  inversion_clear H1; inversion_clear H2;
  simpl; MC.elim_comp;
  econstructor. reflexivity.  split. apply q_subseq_eq.
  apply q_combin_eq with s0
  e0 s1 e1 q q0. assumption. assumption.
  econstructor. reflexivity.  split. 
  apply q_subseq_eq.
  apply q_combin_eq with s0
  e0 s1 e1 q1 rho1. assumption. assumption.
  rewrite map2_r_refl.
  apply d_subseq_eq.
  apply d_combin_eq with s0 e0 s1 e1 x mu1; assumption.

  inversion_clear H1. simpl. MC.elim_comp. 
  econstructor. reflexivity.  split. 
  inversion H0; subst. inversion H; subst.
  inversion H7; subst.
  repeat rewrite kron_plus_distr_l.
  repeat rewrite kron_plus_distr_r. unfold q_subseq.
  right.  
   admit. admit. admit. admit.
   rewrite map2_r_refl. 
   apply d_subseq_eq.
   apply d_combin_eq with s0 e0 s1 e1 x mu1; assumption.

  inversion_clear H1. simpl. MC.elim_comp.
  econstructor. reflexivity.  split.  apply q_subseq_eq.
  apply q_combin_eq with s0
  e0 s1 e1 q1 rho1. assumption. assumption.
  apply IHx with mu1 q q0. 
  assumption. assumption.
  apply H2.
Admitted.


Lemma rule_for:  forall s e s0 e0 s1 e1
(x mu1:list(cstate * qstate s0 e0))(x0 mu2:list(cstate * qstate s1 e1))
(mu3 mu'1 mu:list(cstate * qstate s e)),
d_combin mu1 mu2 mu3->
d_combin x x0 mu'1->
(d_combin (StateMap.Raw.map2 option_app
     mu1 x)
(StateMap.Raw.map2 option_app
   mu2 x0)mu)
-> d_subseq (StateMap.Raw.map2 option_app
  mu3 mu'1) mu.
Proof. induction x; induction mu1; intros.
--inversion H0; subst.  clear H0.
  inversion H; subst. clear H.
  simpl in H1. 
  simpl StateMap.Raw.map2. inversion_clear H1.
   econstructor. 
 { inversion H0; subst.  clear H0.
 inversion H; subst. clear H.
  simpl in H1. repeat rewrite map2_l_refl in H1.
  inversion H1; subst. clear H1.
  simpl. rewrite map2_l_refl. intuition. apply q_subseq_eq.
  apply q_combin_eq with s0 e0 s1 e1 rho0 rho1.
  intuition. intuition. apply d_subseq_eq.
  apply d_combin_eq with s0 e0 s1 e1 mu1 mu4.
  assumption. assumption. }
  { inversion H0; subst.  clear H0.
  inversion H; subst. clear H.
   simpl in H1. repeat rewrite map2_r_refl in H1.
   inversion H1; subst. clear H1.
   simpl. rewrite map2_r_refl. intuition. apply q_subseq_eq.
   apply q_combin_eq with s0 e0 s1 e1 rho0 rho1.
   intuition. intuition. apply d_subseq_eq.
   apply d_combin_eq with s0 e0 s1 e1 x mu1.
   assumption. assumption. }
   {destruct a0; destruct a. inversion H0; subst. clear H0.
   inversion H; subst. clear H.  simpl in H1.
  destruct (Cstate_as_OT.compare c c0);
  repeat rewrite map2_r_refl in H1;
  inversion_clear H1;
  simpl; MC.elim_comp;
  econstructor; try reflexivity. 
  split. apply q_subseq_eq.
  apply q_combin_eq with s0
  e0 s1 e1 q rho2. assumption. assumption.
  apply IHmu1 with ((c0, rho1) :: mu4) mu5.
  assumption.  econstructor.
  assumption. assumption.
  assumption.


  
  split.  inversion H7; subst.
  inversion H6; subst. inversion H; subst.
  repeat rewrite kron_plus_distr_l.
  repeat rewrite kron_plus_distr_r.
  unfold q_subseq.
   admit. admit. admit. admit.
   apply IHx with mu1 mu4 mu5.
   assumption. assumption.
   assumption.

   split. apply q_subseq_eq.
  apply q_combin_eq with s0
  e0 s1 e1 q0 rho1. assumption. assumption.
  repeat rewrite app_fix in *.
  apply IHx with  ((c,q)::mu1) mu4 ((c,rho2)::mu5) .
  econstructor. assumption.
  assumption. 
  assumption. assumption. }
Admitted.


Lemma q_subseq_trans:forall s e  (q0 q1 q2: qstate s e),
 q_subseq q0 q1->
 q_subseq q1 q2->
 q_subseq q0 q2. 
Proof. intros. unfold q_subseq in *.
       destruct H; destruct H0. 
       left. subst. reflexivity.
       destruct H0. 
       right. exists x. subst. reflexivity.
       destruct H.
       right. exists x. subst. reflexivity.
       destruct H. destruct H0.
       right.
       exists (x .+ x0).
       subst. rewrite Mplus_assoc.
       reflexivity.
Qed.

Lemma d_subseq_trans:forall s e (mu0 mu1 mu2:list (state s e)),
 d_subseq mu0 mu1->
 d_subseq mu1 mu2->
 d_subseq mu0 mu2. 
Proof.  induction mu0;destruct mu1; destruct mu2;
       intros.
      {assumption. }
      {destruct s0; intuition. }
      {destruct s0; intuition. }
      {destruct s0; intuition. }
      {destruct a; intuition. }
      {destruct s0; intuition. }
      {destruct s0; intuition. }
      {destruct a. destruct s0. destruct s1. simpl in *.
       split. destruct H. rewrite H. intuition.
       split. apply q_subseq_trans with  q0.
       intuition. intuition.
       apply IHmu0 with mu1; intuition.
        }
Qed.


Lemma d_subseq_map2: forall s e
(mu1 mu2 mu1' mu2':list (cstate *qstate s e)),
d_subseq mu1 mu1'-> 
d_subseq mu2 mu2'->
d_subseq (StateMap.Raw.map2 option_app mu1 mu2)
  (StateMap.Raw.map2 option_app mu1' mu2').
Proof. induction mu1; induction mu2; intros;
       destruct mu1'; destruct mu2';
       try destruct p; try destruct a; 
       try destruct a0; try intuition.
       simpl in *.
       repeat rewrite map2_r_refl.
       intuition.
       simpl in *. 
       repeat rewrite map2_l_refl.
       intuition.
       destruct p0. 
       simpl in *. destruct H. destruct H0.
       subst. 
       destruct (Cstate_as_OT.compare c c2).
       simpl. split. intuition.
       split. intuition.
      apply IHmu1. intuition. 
      simpl. intuition. 
      
     
      econstructor. reflexivity.
      split.  admit. 
      apply IHmu1. intuition.
      intuition. 
     
      simpl. 
      repeat rewrite app_fix.
      split. reflexivity.
      split. intuition.
      apply IHmu2.
      split. reflexivity.
      intuition. intuition.
Admitted. *)




(* Lemma d_q_eq_map2: forall s e
(mu1 mu2 mu1' mu2':list (cstate *qstate s e)),
qstate_eqdstate_ mu1 mu1'->
dstate_qstate_eq mu2 mu2'->
dstate_qstate_eq (StateMap.Raw.map2 option_app mu1 mu2)
  (StateMap.Raw.map2 option_app mu1' mu2').
Proof.   induction mu1; induction mu2; intros;
destruct mu1'; destruct mu2';
try destruct p; try destruct a; 
try destruct a0; try intuition.
simpl in *.
repeat rewrite map2_r_refl.
intuition.
simpl in *. 
repeat rewrite map2_l_refl.
intuition.
destruct p0. 
simpl in *. destruct H. destruct H0.
subst. 
destruct (Cstate_as_OT.compare c c2).
simpl. split. intuition.
apply IHmu1. intuition.
simpl. intuition.

simpl. split. intuition.
apply IHmu1. intuition. intuition.

split. reflexivity.
repeat rewrite app_fix in *.
apply IHmu2.
split. reflexivity.
intuition. intuition.
Qed.  *)
(* Local Open Scope nat_scope.
Lemma QInit_fun_sub{s' e':nat}: forall s e (q q': qstate s' e'), 
s'<=s/\s<=e/\e<=e'->
q_subseq q q'->
@q_subseq s' e' (QInit_fun s e q) (QInit_fun s e q').
Proof. intros. inversion_clear H0. subst.  
       apply q_subseq_eq. reflexivity.
      destruct H1. subst.
      rewrite <-QInit_fun_plus.
      unfold q_subseq. right.
      exists (QInit_fun s e x).
      reflexivity. intuition.
Qed.


Lemma QUnit_Ctrl_fun_sub{s' e':nat}: forall s0 e0 s1 e1 (q q0: qstate s' e') (U: nat-> Square (2^(e1-s1))), 
s'<=s0/\s0<=e0 /\ e0<=s1/\s1<=e1/\e1<=e'->
q_subseq q0 q->
q_subseq (QUnit_Ctrl_fun s0 e0 s1 e1 U q0) 
(QUnit_Ctrl_fun s0  e0 s1 e1 U q).
Proof. intros. inversion_clear H0. subst. 
apply q_subseq_eq. reflexivity.
destruct H1. subst.
rewrite <-QUnit_Ctrl_fun_plus.
unfold q_subseq. right.
exists (QUnit_Ctrl_fun s0 e0 s1 e1 U x).
reflexivity. intuition.
Qed.


Lemma QUnit_One_fun_sub{s' e':nat}: forall s e U (q q': qstate s' e'), 
s'<=s/\s<=e/\e<=e'->
q_subseq q q'->
@q_subseq s' e' (QUnit_One_fun s e U q) (QUnit_One_fun s e U q').
Proof. intros. inversion_clear H0. subst. 
       apply q_subseq_eq. reflexivity.
      destruct H1. subst.
      rewrite <-QUnit_One_fun_plus.
      unfold q_subseq. right.
      exists (QUnit_One_fun s e U x).
      reflexivity. intuition.
Qed.

Lemma QMeas_fun_sub{s' e':nat}: forall s e i (q q': qstate s' e'), 
s'<=s/\s<=e/\e<=e'->
q_subseq q q'->
@q_subseq s' e' (QMeas_fun s e i q) (QMeas_fun s e i q').
Proof. intros. inversion_clear H0. subst. 
       apply q_subseq_eq. reflexivity.
      destruct H1. subst.
      rewrite <-QMeas_fun_plus.
      unfold q_subseq. right.
      exists (QMeas_fun s e i x).
      reflexivity. intuition.
Qed. *)

(* Lemma rule_two: forall c s0 e0 s1 e1 
(mu1:list (cstate *qstate s0 e0))
(mu2:list (cstate *qstate s1 e1))
s e
(mu0 mu mu':list (cstate *qstate s e)) F ,
ceval_single c mu mu'-> 
d_combin mu1 mu2 mu0  ->
d_subseq mu mu0 ->
NSet.inter (fst (Free_state F)) (fst (MVar c)) = NSet.empty ->
NSet.Subset (snd (MVar c)) (Qsys_to_Set s0 e0) ->
State_eval_dstate F mu2 ->
(exists (mu1' :list (cstate *qstate s0 e0))
( mu2': list (cstate *qstate s1 e1))
( mu'': list (cstate *qstate s e)), and 
(ceval_single c mu1 mu1')
(State_eval_dstate F mu2' /\
d_combin mu1' mu2' mu''  /\
 d_subseq mu' mu'')).
Proof. induction c. 
-- induction mu1; intros. 
   {inversion  H0; subst. 
   exists nil. exists nil. exists nil. 
   split. apply E_nil. destruct H4. }
    { destruct a. 
    inversion H0; subst. clear H0.
    assert(ceval_single <{ skip }> (mu'0) (mu'0)).
    apply ceval_skip. 
    assert(exists  (mu1' : list (cstate * qstate s0 e0)) 
    (mu2' : list (cstate * qstate s1 e1)) 
    (mu'' :  list (cstate * qstate s e)),
    and (ceval_single <{ skip }> mu1 mu1') 
    (State_eval_dstate F mu2' /\
    d_combin mu1' mu2' mu'' /\ d_subseq mu'0 mu'')).
    apply (IHmu1 _ _ _ _ _ _ _ H0 H11). apply d_subseq_eq.
    reflexivity. assumption. assumption. admit.
    destruct H5. destruct H5. destruct H5. 
    destruct H5. apply ceval_skip_1 in H5.
    subst.
    exists (((c, q) :: x)). exists (((c, rho1) :: x0)).
    exists ((c, rho')::x1).
    split.  apply E_Skip. split. simpl.
    econstructor. inversion_clear H4. assumption.
    admit.
    split. econstructor.  intuition.  intuition.
    apply ceval_skip_1 in H. rewrite <-H. 
    apply d_subseq_trans with ((c, rho') :: mu'0).
    assumption. simpl. split. reflexivity.
    split. apply q_subseq_eq. reflexivity.
    intuition.
     }
-- admit.
--induction mu1; intros.
  {inversion  H0; subst. 
   exists nil. exists nil. exists nil.
   split. econstructor. destruct H4. }
   {destruct a0. inversion H0; subst. clear H0.
    destruct mu. simpl in H1. intuition.
    destruct p. inversion H; subst. simpl in H1.
    destruct H1. subst. 
  assert(exists
  (mu1' : list (cstate * qstate s0 e0)) 
  (mu2' : list (cstate * qstate s1 e1)) 
  (mu'' : list  (cstate * qstate s e)),
  (and (ceval_single <{ i := a }> mu1 mu1') 
   (State_eval_dstate F mu2'/\
   d_combin mu1' mu2' mu'' /\ d_subseq mu'1 mu''))).
  apply (IHmu1 _ _ _ _ _ _ _ H12 H11). intuition.
  assumption. assumption. admit. 
  destruct H0. destruct H0. destruct H0.
  exists (StateMap.Raw.map2 option_app 
  [(c_update i (aeval (c,q) a) c, q)] x).
  exists (StateMap.Raw.map2 option_app 
  [(c_update i (aeval (c,rho1) a) c,rho1)] x0).
  assert(exists (mu'': list (cstate *qstate s e)),
  d_combin
  (StateMap.Raw.map2 option_app
     [(c_update i (aeval (c, q) a) c, q)] x)
  (StateMap.Raw.map2 option_app
     [(c_update i (aeval (c, q) a) c, rho1)] x0) mu'').
  apply rule_6 with  (rho') x1. assumption. intuition. 
   destruct H5. exists x2. 
  split. apply E_Asgn. intuition.
  split. admit.
  split. rewrite (state_eq_aexp (c, rho1) (c,q)).
  intuition. reflexivity. 
  apply d_subseq_trans with 
  ((StateMap.Raw.map2 option_app
  [(c_update i (aeval (c, q) a) c, rho')] x1)).
  apply d_subseq_map2. simpl.
  rewrite (state_eq_aexp (c, q0) (c, q)).
  intuition. reflexivity. intuition.  
  apply rule_three with s0 e0 s1 e1 x x0 q rho1.
  assumption. intuition. assumption. } 
 --admit.
 --intros. destruct mu1; intros.
   { inversion  H0; subst.
     exists nil. exists nil. exists nil. 
     split; econstructor. destruct H4. 
     destruct H4. }
   { inversion H0; subst. clear H0.
     destruct mu. intuition.
     destruct p.   inversion H; subst.
      simpl in H1. destruct H1. destruct H0.
assert(exists
(mu1' : list (cstate * qstate s0 e0)) 
(mu2' : list (cstate * qstate s1 e1))
(mu'' : list (cstate * qstate s e)),
(and (ceval_single c1 (((c, rho0) :: mu1)) mu1') 
 (State_eval_dstate F mu2'  /\
 d_combin mu1' mu2' mu''  /\ d_subseq mu2 mu''))).
apply IHc1 with ((c, rho1) :: mu4) ((c, rho') :: mu'0) (((c, q) :: mu)) .
intuition. econstructor.  intuition.
intuition. simpl. split. reflexivity. apply H1.
admit.
admit. assumption.  
destruct H0. destruct H0. destruct H0.
assert( exists
(mu1' : list (cstate * qstate s0 e0)) 
(mu2' : list (cstate * qstate s1 e1))
(mu'' : list (cstate * qstate s e)),
(and (ceval_single c2 x mu1') 
 (State_eval_dstate F mu2' /\
 d_combin mu1' mu2' mu'' /\ d_subseq mu' mu'' ))).
 apply IHc2 with x0 x1 mu2. intuition. intuition.
 intuition. admit. admit. intuition.
 destruct H5. destruct H5. destruct H5.
 exists x2. exists x3. exists x4. split.
  apply E_Seq with x. 
  intuition. intuition. intuition. }

--induction mu1; intros.
{inversion  H0; subst. 
 exists nil. exists nil. exists nil.
 split. econstructor. destruct H4.
  } 
 { destruct a. inversion H0; subst. clear H0.
  destruct mu. simpl in H1. intuition.
  destruct p. inversion H; subst; simpl in H1.
  destruct H1; subst.
   {assert(exists
  (mu1' : list (cstate * qstate s0 e0)) 
  (mu2' : list (cstate * qstate s1 e1)) 
  (mu''0 : list  (cstate * qstate s e)),
  (and (ceval_single <{ if b then c1 else c2 end }> mu1 mu1') 
   (State_eval_dstate F mu2' /\
   d_combin mu1' mu2' mu''0 /\ d_subseq mu'' mu''0))).
  apply (IHmu1 _ _ _ _ _ _ _ H14 H11). intuition.
   assumption. assumption. admit.
  destruct H0. destruct H0. destruct H0.
  assert(exists
  (mu1' : list (cstate * qstate s0 e0)) 
  (mu2' : list (cstate * qstate s1 e1)) 
  (mu''0 : list  (cstate * qstate s e)),
  (and (ceval_single c1 [(c,q)] mu1') 
   (State_eval_dstate F mu2' /\
   d_combin mu1' mu2' mu''0 /\ d_subseq mu'1 mu''0))).
   apply IHc1 with [(c, rho1)] [(c,rho')] [(c,q0)]. intuition.
   econstructor. intuition. econstructor.
   simpl. intuition. admit. admit. simpl.
   econstructor. inversion_clear H4. assumption.
   econstructor.
   destruct H5. destruct H5. destruct H5. 
  exists (StateMap.Raw.map2 option_app 
  x2 x).
  exists (StateMap.Raw.map2 option_app 
  x3 x0).
  assert(exists (mu'': list (cstate *qstate s e)),
  d_combin (StateMap.Raw.map2 option_app x2 x)
  (StateMap.Raw.map2 option_app x3 x0) mu'').
  apply rule_7 with x1 x4. intuition. intuition.
   destruct H6. exists x5. 
   split. apply E_IF_true.
  rewrite (state_eq_bexp _ (c, q0)). intuition.
  reflexivity. intuition.
   intuition.
   split. admit.
   split. intuition. 
  apply d_subseq_trans with 
  ((StateMap.Raw.map2 option_app x4 x1)).
  apply d_subseq_map2. intuition. intuition. 
  apply rule_for with s0 e0 s1 e1 x x2 x0 x3.
  intuition. intuition. assumption. 
 }
 { admit. }
}
--admit.
--induction mu1; intros.
{inversion  H0; subst. 
 exists nil. exists nil. exists nil.
 split. econstructor. destruct H4. }
 {destruct a. inversion H0; subst. clear H0.
  destruct mu. simpl in H1. intuition.
  destruct p. inversion H; subst. simpl in H1. 
  destruct H1; subst.
assert(exists
(mu1' : list (cstate * qstate s0 e0)) 
(mu2' : list (cstate * qstate s1 e1)) 
(mu'' : list  (cstate * qstate s2 e2)),
(and (ceval_single <{ (s e) :Q= 0 }> mu1 mu1') 
 (State_eval_dstate F mu2' /\
 d_combin mu1' mu2' mu'' /\ d_subseq mu'1 mu''))).
apply (IHmu1 _ _ _ _ _ _ _ H13 H11). intuition.
assumption. assumption. admit. 
destruct H0. destruct H0. destruct H0.
exists (StateMap.Raw.map2 option_app 
[(c,(QInit_fun s e q))] x).
exists (StateMap.Raw.map2 option_app 
[(c,rho1)] x0).
assert(exists (mu'': list (cstate *qstate s2 e2)),
d_combin
(StateMap.Raw.map2 option_app
[(c,(QInit_fun s e q))] x)
(StateMap.Raw.map2 option_app
[(c,rho1)]  x0) mu'').
inversion H10; subst.
apply (rule_6 _ s2 e2 s2 s1 s1 e2 _ _ 
 (@kron (2^(s1-s2)) (2^(s1-s2)) (2^(e2-s1))
 (2^(e2-s1)) (QInit_fun s e q) rho1)_ _ x1).
apply combin_l; econstructor. intuition. 
apply (rule_6 _ s2 e2 s0 e2 s2 s0 _ _ 
 (@kron (2^(s0-s2))
 (2^(s0-s2)) (2^(e2-s0)) (2^(e2-s0))  rho1 (QInit_fun s e q) )_ _ x1).
apply combin_r; econstructor. intuition.
destruct H5. exists x2. 
split. apply E_Qinit. 
simpl in H2. admit.  intuition.
split. apply d_seman_app_aux. admit. admit.
simpl. econstructor. inversion_clear H4. assumption.
econstructor. intuition. 
split. 
intuition.  
inversion H10; subst.
apply d_subseq_trans with 
((StateMap.Raw.map2 option_app
[(c,(@kron (2^(s1-s2)) (2^(s1-s2)) (2^(e2-s1))
(2^(e2-s1)) (QInit_fun s e q) rho1) )] x1)).
apply d_subseq_map2.
simpl. split. reflexivity. split.
apply q_subseq_trans with ((@QInit_fun s2 e2 s e 
(@kron (2^(s1-s2)) (2^(s1-s2)) (2^(e2-s1))
(2^(e2-s1)) q rho1))).
apply QInit_fun_sub. intuition. intuition.
apply q_subseq_eq. 
apply QInit_fun_kron. 
admit. admit. intuition. intuition.
apply (rule_three s2 e2 s2 s1 s1 e2 x x0 (QInit_fun s e q) rho1).
econstructor; reflexivity.  intuition. assumption. 
apply d_subseq_trans with 
((StateMap.Raw.map2 option_app
[(c,(@kron (2^(s0-s2))
(2^(s0-s2)) (2^(e2-s0)) (2^(e2-s0))  rho1 (QInit_fun s e q) ) )] x1)).
apply d_subseq_map2.
simpl. split. reflexivity. split.
apply q_subseq_trans with ((@QInit_fun s2 e2 s e 
(@kron (2^(s0-s2))
 (2^(s0-s2)) (2^(e2-s0)) (2^(e2-s0))  rho1 q ))).
apply QInit_fun_sub. intuition. intuition.
apply q_subseq_eq. admit. 
 intuition. intuition.
apply (rule_three s2 e2 s0 e2 s2 s0 x x0 (QInit_fun s e q) rho1).
econstructor; reflexivity.  intuition. assumption. 
}

--induction mu1; intros.
{inversion  H0; subst. 
 exists nil. exists nil. exists nil.
 split. econstructor. destruct H4. }
 {destruct a. inversion H0; subst. clear H0.
  destruct mu. simpl in H1. intuition.
  destruct p. inversion H; subst. simpl in H1.
  destruct H1; subst.
  apply inj_pair2_eq_dec in H6.
  apply inj_pair2_eq_dec in H6.
  subst. 
assert(exists
(mu1' : list (cstate * qstate s0 e0)) 
(mu2' : list (cstate * qstate s1 e1)) 
(mu'' : list  (cstate * qstate s2 e2)),
(and (ceval_single (QUnit_One s e U) mu1 mu1') 
 (State_eval_dstate F mu2' /\
 d_combin mu1' mu2' mu'' /\ d_subseq mu'1 mu''))).
apply (IHmu1 _ _ _ _ _ _ _ H15 H11). intuition.
assumption. assumption.  admit.
destruct H0. destruct H0. destruct H0.
exists (StateMap.Raw.map2 option_app 
[(c,(QUnit_One_fun s e U q))] x).
exists (StateMap.Raw.map2 option_app 
[(c,rho1)] x0).
assert(exists (mu'': list (cstate *qstate s2 e2)),
d_combin
(StateMap.Raw.map2 option_app
[(c,(QUnit_One_fun s e U q))] x)
(StateMap.Raw.map2 option_app
[(c,rho1)]  x0) mu'').
apply (rule_6 _ s2 e2 s0 e0 s1 e1 _ _ 
 (@kron (2^(e0-s0)) (2^(e0-s0)) (2^(e1-s1))
 (2^(e1-s1)) (QUnit_One_fun s e U q) rho1)_ _ x1).
  admit. intuition. 
 destruct H5. exists x2. 
split. apply E_Qunit_One.  
simpl in H2. admit.  intuition.
intuition.
split. admit. 
split. 
intuition. 
apply d_subseq_trans with 
((StateMap.Raw.map2 option_app
[(c,(@kron (2^(e0-s0)) (2^(e0-s0)) (2^(e1-s1))
(2^(e1-s1)) (QUnit_One_fun s e U q) rho1) )] x1)).
apply d_subseq_map2.
simpl. split. reflexivity. split. 
admit. intuition. intuition. 
apply (rule_three s2 e2 s0 e0 s1 e1 x x0 (QUnit_One_fun s e U q) rho1).
admit. intuition. assumption. 
apply Nat.eq_dec. apply Nat.eq_dec. }

--induction mu1; intros.
{inversion  H0; subst. 
 exists nil. exists nil. exists nil.
 split. econstructor. destruct H4. }
 {destruct a. inversion H0; subst. clear H0.
  destruct mu. simpl in H1. intuition.
  destruct p. inversion H; subst. simpl in H1.
  destruct H1; subst.
  apply inj_pair2_eq_dec in H9.
  apply inj_pair2_eq_dec in H9.
  subst. 
assert(exists
(mu1' : list (cstate * qstate s2 e2)) 
(mu2' : list (cstate * qstate s3 e3)) 
(mu'' : list  (cstate * qstate s e)),
(and (ceval_single (QUnit_Ctrl s0 e0 s1 e1 U) mu1 mu1') 
 (State_eval_dstate F mu2' /\
 d_combin mu1' mu2' mu'' /\ d_subseq mu'1 mu''))).
apply (IHmu1 _ _ _ _ _ _ _ H17 H11). intuition.
assumption. assumption. admit. 
destruct H0. destruct H0. destruct H0.
exists (StateMap.Raw.map2 option_app 
[(c,(QUnit_Ctrl_fun s0 e0 s1 e1 U q))] x).
exists (StateMap.Raw.map2 option_app 
[(c,rho1)] x0).
assert(exists (mu'': list (cstate *qstate s e)),
d_combin
(StateMap.Raw.map2 option_app
[(c,(QUnit_Ctrl_fun s0 e0 s1 e1 U q))] x)
(StateMap.Raw.map2 option_app
[(c,rho1)]  x0) mu'').
apply (rule_6 _ s e s2 e2 s3 e3 _ _ 
 (@kron (2^(e2-s2)) (2^(e2-s2)) (2^(e3-s3))
 (2^(e3-s3)) (QUnit_Ctrl_fun s0 e0 s1 e1 U q)
  rho1)_ _ x1).
  admit. intuition. 
 destruct H5. exists x2. 
split. apply E_QUnit_Ctrl.  
simpl in H2. admit.  intuition.
intuition.
split. admit.
split. 
intuition. 
apply d_subseq_trans with 
((StateMap.Raw.map2 option_app
[(c,(@kron (2^(e2-s2)) (2^(e2-s2)) (2^(e3-s3))
(2^(e3-s3)) (QUnit_Ctrl_fun s0 e0 s1 e1 U q) rho1) )] x1)).
apply d_subseq_map2.
simpl. split. reflexivity.
split.
admit. intuition. intuition. 
apply (rule_three s e s2 e2 s3 e3 x x0 (QUnit_Ctrl_fun s0 e0 s1 e1 U q) rho1).
admit. intuition. assumption.
apply Nat.eq_dec. apply Nat.eq_dec. }

--induction mu1; intros.
{inversion  H0; subst. 
 exists nil. exists nil. exists nil.
 split. econstructor. destruct H4. }
 {destruct a. inversion H0; subst. clear H0.
  destruct mu. simpl in H1. intuition.
  destruct p. inversion H; subst. simpl in H1.
  destruct H1; subst.
assert(exists
(mu1' : list (cstate * qstate s0 e0)) 
(mu2' : list (cstate * qstate s1 e1)) 
(mu'' : list  (cstate * qstate s2 e2)),
(and (ceval_single (QMeas i s e ) mu1 mu1') 
 (State_eval_dstate F mu2' /\
 d_combin mu1' mu2' mu'' /\ d_subseq mu'1 mu''))).
apply (IHmu1 _ _ _ _ _ _ _ H14 H11). intuition.
assumption. assumption. admit. 
destruct H0. destruct H0. destruct H0.
exists (StateMap.Raw.map2 option_app 
(big_app (fun j : nat => [(c_update i j c, QMeas_fun s e j q)])
          (2 ^ (e - s))) x).
exists (StateMap.Raw.map2 option_app 
(big_app (fun j : nat => [(c_update i j c, rho1)])
          (2 ^ (e - s))) x0).
assert(exists (mu'': list (cstate *qstate s2 e2)),
d_combin
(StateMap.Raw.map2 option_app
(big_app (fun j : nat => [(c_update i j c, QMeas_fun s e j q)])
          (2 ^ (e - s))) x)
(StateMap.Raw.map2 option_app
(big_app (fun j : nat => [(c_update i j c, rho1)])
(2 ^ (e - s))) x0) mu'').
apply (rule_7 s2 e2 s0 e0 s1 e1 _ _  _ _
 x1 (big_app
(fun j : nat =>
 [(c_update i j c, @kron (2^(e0-s0)) (2^(e0-s0)) (2^(e1-s1))
 (2^(e1-s1)) (QMeas_fun s e j q) rho1 )])
(2 ^ (e - s))) ). 
  admit. intuition. 
 destruct H5. exists x2. 
split. apply E_Meas.   
simpl in H2. admit.  intuition.
split. admit.
split. 
intuition. 
apply d_subseq_trans with 
((StateMap.Raw.map2 option_app
(big_app
(fun j : nat =>
 [(c_update i j c, @kron (2^(e0-s0)) (2^(e0-s0)) (2^(e1-s1))
 (2^(e1-s1)) (QMeas_fun s e j q) rho1 )])
(2 ^ (e - s))) x1)).
apply d_subseq_map2. 
admit. intuition. 
apply (rule_for s2 e2 s0 e0 s1 e1 x (big_app (fun j : nat => [(c_update i j c, QMeas_fun s e j q)])
(2 ^ (e - s))) x0 (big_app (fun j : nat => [(c_update i j c, rho1)]) (2 ^ (e - s)))).
admit. intuition. assumption. }
Admitted.

 *)


(* Lemma QExp_eval_sub: forall (qs: QExp) s e c (q q': qstate s e) ,
q_subseq q q'->
State_eval qs (c, q')->
State_eval qs (c, q).
Proof. Admitted.



Lemma QExp_eval_sub: forall F s e c (q q': qstate s e) ,
q_subseq q q'->
State_eval F (c, q')->
State_eval F (c, q).
Proof. induction F; intros.
       apply state_eq_Pure with (c,q').
       reflexivity. intuition.
       inversion_clear H.
       subst. intuition.
       destruct H1.  subst.
       induction qs.
       simpl in H0. 
       simpl.  
       split. intuition.
       split. intuition.
       split. intuition.
       rewrite <-PMtrace_scale in *.
       rewrite PMtrace_plus in *.
       rewrite Mscale_plus_distr_r in *.
       destruct H0. destruct H0.
       destruct H1. 
       admit. lia. lia.
       

      



Lemma State_eval_sub: forall s e (mu mu': list (state s e)) F,
d_subseq mu mu'->
State_eval_dstate F mu'->
State_eval_dstate F mu.
Proof. induction mu.  intros. destruct mu'.
       simpl in H0. destruct H0.
       simpl in H. destruct H.
       intros. destruct mu'.
       destruct a.
       simpl in H. destruct H.
       destruct mu; destruct mu';
       destruct a; destruct s0.
       simpl in H. 
       simpl. econstructor.
       inversion_clear H0.
       admit. 
       
       econstructor.

       simpl in H. intuition.
       destruct s1.
       simpl in H. intuition.
       simpl. econstructor.
       admit.
       apply IHmu with (s2 :: mu').
       destruct s1. destruct s2.
       simpl in H. econstructor. intuition.
       split. intuition. intuition.
       inversion_clear H0. intuition.   
 Admitted. *)







(* Lemma QExp_eval_pure: forall qs s e c (q: qstate s e) ,
QExp_eval qs (c, q)->
exists (p:R) (φ: Vector (2^((snd (Free_QExp' qs))-(fst (Free_QExp' qs))))),
p .* (@PMpar_trace s e q ((fst (Free_QExp' qs))) (((snd (Free_QExp' qs)))) )
= φ  × φ†.
Proof. induction qs; intros. 
       simpl in H. 
       exists ((R1 / Cmod (@trace (2^(e0-s0)) q))%R).
       exists v.
       simpl. 
       rewrite PMtrace_scale.
       unfold outer_product in H.
       intuition.
       simpl QExp_eval in H.  
       destruct H. 
       destruct H0.
       apply IHqs1 in H0.
       apply IHqs2 in H1.
       destruct H0.
       destruct H0.
       destruct H1.
       destruct H1.
Admitted. *)








(* Lemma Mixed_pure: forall {n:nat} (ρ1 ρ2: Density n), 
Mixed_State ρ1 ->
Mixed_State ρ2 ->

Par_Pure_State (ρ1 .+  ρ2) ->
exists (p1 p2:R),  and ( and (0<p1)%R  (0<p2)%R) 
(ρ1 = p1 .* (ρ1 .+  ρ2) 
/\ ρ2 = p2 .* (ρ1 .+  ρ2)) .
Proof. 
Admitted. *)








(* Lemma seman_eq_two{s e:nat}: forall F1 F2  c (q:qstate s e),
Considered_Formula (F1 ⊙ F2) ->
WF_qstate q->
State_eval (F1 ⊙ F2) (c, q) -> 
exists 
(q1:qstate (fst (Free_State F1)) (snd (Free_State F1)))
(q2:qstate (fst (Free_State F2)) (snd (Free_State F2))), 
and (WF_qstate q1  /\ WF_qstate q2)
 ((s<= (fst (Free_State (F1 ⊙ F2))) /\ (snd (Free_State (F1 ⊙ F2))) <=e)
/\ ((State_eval F1 (c, q1) /\ State_eval F2 (c, q2))  /\
(q_combin q1 q2 (@PMpar_trace s e q (fst (Free_State (F1 ⊙ F2))) (snd (Free_State (F1 ⊙ F2))))))).
Proof. intros F1 F2 c q H Hw. 
       exists ((C1/ (@trace (2^(e-s)) q) .* (PMpar_trace q (fst (Free_State F1)) (snd (Free_State F1))))).
       exists (PMpar_trace q (fst (Free_State F2)) (snd (Free_State F2))).
       split. 
       split. rewrite <-(Ptrace_trace _ _  _ ((fst (Free_State F1)))
       ((snd (Free_State F1)))).
       unfold WF_qstate.
       split. admit.
       apply Considered_Formula_dom.
       apply H.  admit. apply WF_Mixed. apply Hw.
       apply WF_par_trace.
       admit. assumption.
       split. admit.
       split. admit.
       simpl in H. 
       destruct H. destruct H1. 
       destruct H2.
       simpl. 
       pose H2.
       rewrite <-Nat.eqb_eq in e0.
       rewrite e0. simpl. rewrite H2.
       (* assert((PMpar_trace q (fst (Free_State F1)) (fst (Free_State F2))) = 
              PMpar_trace (PMpar_trace q (fst (Free_State F1)) (snd (Free_State F2))) (fst (Free_State F1)) (fst (Free_State F2))). *)
       rewrite  <-(PMpar_trace_assoc _ (fst (Free_State F1)) (snd (Free_State F2)) (fst (Free_State F1)) (fst (Free_State F2))).
       rewrite  <-(PMpar_trace_assoc _ (fst (Free_State F1)) (snd (Free_State F2)) (fst (Free_State F2)) (snd (Free_State F2))).
       remember ((fst (Free_State F1))) as s'.
       remember ((fst (Free_State F2))) as x.
       remember ((snd (Free_State F2))) as e'.
       remember (PMpar_trace q s' e').
       assert((@trace (2^(e'-s')) q0) .* q0 =
       @kron (2^(x-s')) (2^(x-s')) (2^(e'-x))  (2^(e'-x)) (PMpar_trace q0 s' x) (PMpar_trace q0 x e') ).
       apply Odot_Sepear'. 
       rewrite Heqs'. rewrite Heqx. rewrite Heqe'.
       split. rewrite <-Heqx. rewrite<- H2.
       apply Considered_Formula_dom. apply H.
       apply Considered_Formula_dom. apply H1.
       rewrite Heqq0. apply WF_par_trace.
       rewrite Heqs'. rewrite Heqe'.
       admit. assumption. 
       admit.  
       assert( q0 =@kron (2^(x-s')) (2^(x-s')) (2^(e'-x))  (2^(e'-x)) (C1 / (@trace (2^(e'-s')) q0) .* (PMpar_trace q0 s' x)) (PMpar_trace q0 x e') ).
       rewrite Mscale_kron_dist_l.
       rewrite <-H3.
       rewrite Cdiv_unfold.
       rewrite Cmult_1_l.
       rewrite Mscale_assoc.
       rewrite Cinv_l.
       rewrite Mscale_1_l.
       reflexivity.
       admit. 
       assert((@trace (2^(e'-s')) q0) = (@trace (2^(e-s)) q)).
       rewrite Heqq0. 
       rewrite Ptrace_trace.
       reflexivity. 
       rewrite Heqs'. rewrite Heqe'. admit. 
       apply WF_Mixed. apply Hw.
       rewrite <-H5.
       remember ((C1 / (@trace (2^(e'-s')) q0) .* (PMpar_trace q0 s' x))).
       remember ((PMpar_trace q0 x e')).
       rewrite H4.
       apply combin_l; try reflexivity.

       split. admit.
       split. rewrite <-H2. apply Considered_Formula_dom.
       assumption.
       split. apply Considered_Formula_dom. 
       assumption. intuition. admit.

       split. admit.
       split. intuition. 
       split. rewrite<-H2. apply Considered_Formula_dom.
       assumption.
       split. apply Considered_Formula_dom. assumption.
       admit.

      
Admitted.


Lemma seman_eq_two'{s e:nat}: forall F1 F2  c (q:qstate s e),
Considered_Formula (F1 ⊙ F2) ->
@WF_Matrix  (2^(e-s)) (2^(e-s)) q->
(exists (s0 e0 s1 e1 s2 e2: nat)
(q1:qstate s0 e0)
(q2:qstate s1 e1), and (s<=s2 /\ e2 <= e)
( (State_eval F1 (c, q1) /\ State_eval F2 (c, q2))  /\
(q_combin q1 q2 (@PMpar_trace s e q s2 e2)))) 
-> State_eval (F1 ⊙ F2) (c, q).
Proof. intros.  
       destruct H1.
       destruct H1.
       destruct H1.
       destruct H1.
       destruct H1.
       destruct H1.
       destruct H1.
       destruct H1.
       destruct H1.
       destruct H2.
       inversion H3; subst.

       simpl. split. 
       admit.

       split.
       rewrite (State_free_eval _ _ x3 x1).
       simpl. 
       assert(PMpar_trace q x3 x1 = 
       PMpar_trace (PMpar_trace q x3 x4) x3 x1).
       rewrite PMpar_trace_assoc.
       reflexivity. admit.
       rewrite H5.
       rewrite PMpar_trace_L.
       rewrite <-H4.
       rewrite (PMpar_trace_l x1 x5 x6).
      admit.
      admit. admit.
      rewrite H4.  admit.
      reflexivity.
      admit. admit.
      admit.
      admit.
      admit.

      rewrite (State_free_eval _ _ x1 x4).
      simpl. 
      assert(PMpar_trace q x1 x4 = 
      PMpar_trace (PMpar_trace q x3 x4) x1 x4).
      rewrite PMpar_trace_assoc.
      reflexivity. admit.
      rewrite H5.
      rewrite PMpar_trace_R.
      rewrite <-H4.
      rewrite (PMpar_trace_r x1 x5 x6).
     admit.
     admit. admit.
     rewrite H4.  admit.
     reflexivity. reflexivity.
     admit. admit.
     admit.
     admit.
     

     simpl. split. 
       admit.

       split.
       rewrite (State_free_eval _ _ x x4).
       simpl. 
       assert(PMpar_trace q x x4 = 
       PMpar_trace (PMpar_trace q x3 x4) x x4).
       rewrite PMpar_trace_assoc.
       reflexivity. admit.
       rewrite H5.
       rewrite PMpar_trace_R.
       rewrite <-H4.
       rewrite (PMpar_trace_r x x6 x5).
      admit.
      admit. admit.
      rewrite H4.  admit.
      reflexivity. reflexivity.
      admit. admit.
      admit.
      admit.

      rewrite (State_free_eval _ _ x3 x).
      simpl. 
      assert(PMpar_trace q x3 x = 
      PMpar_trace (PMpar_trace q x3 x4) x3 x).
      rewrite PMpar_trace_assoc.
      reflexivity. admit.
      rewrite H5.
      rewrite PMpar_trace_L.
      rewrite <-H4.
      rewrite (PMpar_trace_l x x6 x5).
     admit.
     admit. admit.
     rewrite H4.  admit.
     reflexivity. 
     admit. admit.
     admit.
     admit.
     admit.
Admitted.



Lemma seman_eq_three{s e:nat}: forall  (mu: list (cstate * qstate s e)) F1 F2,
WF_dstate_aux mu ->
Considered_Formula (F1 ⊙ F2) ->
State_eval_dstate (F1 ⊙ F2) mu -> 
exists 
(mu0:list(cstate * qstate (fst (Free_State F1)) (snd (Free_State F1)))) 
(mu1:list(cstate * qstate (fst (Free_State F2)) (snd (Free_State F2)))),
 and  (WF_dstate_aux mu0 /\ WF_dstate_aux mu1)
 (and (s<= (fst (Free_State (F1 ⊙ F2))) /\ (snd (Free_State (F1 ⊙ F2))) <=e)
 ((d_combin mu0 mu1 (d_par_trace mu (fst (Free_State (F1 ⊙ F2))) (snd (Free_State (F1 ⊙ F2)))))
  /\ ((State_eval_dstate F1 mu0 /\ State_eval_dstate F2 mu1)))).
Proof. induction mu;  intros F1 F2 Hw; intros.
       destruct H0.
       destruct mu. 
       inversion H0; subst.
       destruct a.
       apply seman_eq_two in H3.
       destruct H3.  destruct H1.
       destruct H1. destruct H1.
       exists [(c,x)]. exists [(c,x0)].
       split. split. 
       apply WF_state_dstate_aux. 
       apply H1. apply WF_state_dstate_aux.
       apply H3. 
       split. intuition.  
       split. econstructor. intuition.
       econstructor. simpl. intuition. 
       intuition. inversion_clear Hw. intuition. 
        assert(exists
        (mu0 : list
                 (cstate *
                  qstate (fst (Free_State F1))
                    (snd (Free_State F1)))) 
      (mu1 : list
               (cstate *
                qstate (fst (Free_State F2)) (snd (Free_State F2)))),
         and ( WF_dstate_aux mu0 /\ WF_dstate_aux mu1)
        (and (s <= fst (Free_State (F1 ⊙ F2)) /\
          snd (Free_State (F1 ⊙ F2)) <= e) 
         (d_combin mu0 mu1
           (d_par_trace (p :: mu) (fst (Free_State (F1 ⊙ F2)))
              (snd (Free_State (F1 ⊙ F2)))) /\
         State_eval_dstate F1 mu0 /\ State_eval_dstate F2 mu1))).
       apply IHmu. inversion_clear Hw. assumption. intuition. inversion_clear H0.
       apply State_eval_dstate_Forall. discriminate.
       intuition.
       destruct H1. destruct H1.
       destruct H1. 
       destruct a. destruct p. 
       assert(exists 
       (q1:qstate (fst (Free_State F1)) (snd (Free_State F1)))
       (q2:qstate (fst (Free_State F2)) (snd (Free_State F2))), 
       and (WF_qstate q1 /\ WF_qstate q2)
        ((s<= (fst (Free_State (F1 ⊙ F2))) /\ (snd (Free_State (F1 ⊙ F2))) <=e)
       /\ ((State_eval F1 (c, q1) /\ State_eval F2 (c, q2))  /\
       (q_combin q1 q2 (@PMpar_trace s e q (fst (Free_State (F1 ⊙ F2))) (snd (Free_State (F1 ⊙ F2)))))))).
       apply seman_eq_two. intuition.
       inversion_clear Hw. intuition.
       inversion_clear H0. intuition.
       destruct H3. destruct H3.
       destruct H3. 
       exists ((c,x1)::x). exists ((c,x2)::x0).
       split. split. econstructor.
       intuition. intuition.
       admit.
       econstructor. intuition.
       intuition. 
       admit.
       split. intuition. 
       split. econstructor.  intuition.
       apply H2. 
       split. econstructor. intuition.
       destruct x. econstructor.
       apply H2. econstructor. intuition.
       destruct x0. econstructor. 
       apply H2. 
Admitted.










Lemma seman_eq_three'{s e:nat}: forall  (mu: list (cstate * qstate s e)) F1 F2,
WF_Matrix_dstate mu ->
Considered_Formula (F1 ⊙ F2) ->
(exists (s0 e0 s1 e1 s2 e2: nat)
(mu0:list(cstate * qstate s0 e0)) 
(mu1:list(cstate * qstate s1 e1)),
 (and (s<= s2 /\ e2 <=e)
 ((d_combin mu0 mu1 (d_par_trace mu s2 e2))
  /\ ((State_eval_dstate F1 mu0 /\ State_eval_dstate F2 mu1)))))
  -> State_eval_dstate (F1 ⊙ F2) mu.
Proof.
       
induction mu;  intros F1 F2 Hw; intros.
destruct H0. 
destruct H0. 
destruct H0. destruct H0.
destruct H0. destruct H0.
destruct H0. destruct H0.
destruct H0. 
destruct H1. inversion H1; subst.
destruct H2. destruct H2.
destruct H0. destruct H0.
destruct H0. destruct H0.
destruct H0. destruct H0.
destruct H0. destruct H0.
destruct H0.  destruct H1.
destruct mu. 
destruct a.  inversion H1; subst.
simpl d_par_trace in *.
inversion H9; subst. 
econstructor.
apply seman_eq_two'.
intuition. simpl in Hw. intuition.  
exists x. exists x0.
exists x1. exists x2.
exists x3. exists x4.
exists rho0. exists rho1.
split. intuition.
destruct H2. inversion_clear H2.
inversion_clear H3.
split. intuition. intuition. econstructor.
destruct a. destruct p.  
inversion H1; subst. clear H1.
inversion H9; subst. clear H9.
econstructor.
apply seman_eq_two'.
intuition. simpl in Hw. intuition. 
exists x. exists x0.
exists x1. exists x2.
exists x3. exists x4.
exists rho0. exists rho1.
split. intuition.
destruct H2. inversion_clear H1.
inversion_clear H2.
split. intuition. intuition.
apply IHmu.
simpl in Hw. simpl. intuition.
intuition.
exists x. exists x0.
exists x1. exists x2.
exists x3. exists x4.
exists ((c0,rho2)::mu2).
exists ((c0,rho3)::mu3).
split. intuition. 
split. econstructor. intuition.
intuition. 
destruct H2. inversion_clear H1.
inversion_clear H2.
split. intuition. intuition. 
Qed.







Lemma QExp_eval_sub: forall (qs: QExp) s e c (q q': qstate s e) ,
WF_qstate q ->
WF_qstate q'->
q_subseq q q'->
State_eval qs (c, q')->
State_eval qs (c, q).
Proof. induction qs; intros.
      inversion_clear H1. subst. intuition.
      destruct H3. subst.
      simpl in *.  
      split. intuition.
      split. intuition.
      split. intuition.
      rewrite <-PMtrace_scale in *.
      rewrite PMtrace_plus in *.
      rewrite Mscale_plus_distr_r in *.
      destruct H2. destruct H2.
      destruct H3. unfold outer_product in H4.
      remember ((R1 / Cmod (trace (q .+ x)))%R .* PMpar_trace q s e).
      remember ((R1 / Cmod (trace (q .+ x)))%R .* PMpar_trace x s e).
      apply (ParDensityO.Mixed_pure m m0) in H4.
      destruct H4. destruct H4. 
      subst. destruct H4.   
      admit. rewrite Heqm.
      apply Mixed_State_scale.   admit.
      admit. rewrite Heqm0.
      apply Mixed_State_scale.   admit.
      admit. 
      rewrite Heqm. rewrite Heqm0.
      rewrite <-Mscale_plus_distr_r.
      rewrite <-PMtrace_plus.
      rewrite <-(Ptrace_trace s0 e0 (q .+ x) s e).
      apply Mixed_State_aux_to01. admit.
      intuition. apply WF_Mixed. apply H0.
      admit. 
      simpl in *.
      split. intuition.
      split. apply IHqs1 with (q').
     intuition. intuition. intuition.
     intuition.
     apply IHqs2 with q'.
     intuition. intuition.
     intuition. intuition.
Admitted.

Lemma State_eval_sub: forall F s e c (q q': qstate s e) ,
WF_qstate q ->
WF_qstate q' ->
q_subseq q q'->
State_eval F (c, q')->
State_eval F (c, q).
Proof. induction F; intros.
       apply state_eq_Pure with (c,q').
       reflexivity. intuition.
       apply QExp_eval_sub with q'.
       intuition. intuition. intuition.
       intuition.
       simpl in *.
       split. intuition.
       split. apply IHF1 with (q').
      intuition. intuition. intuition.
      intuition.
      apply IHF2 with q'.
      intuition. intuition. intuition.
      intuition.
      simpl in *.
       split. apply IHF1 with (q').
      intuition. intuition.
      intuition. intuition.
      apply IHF2 with q'.
      intuition. intuition.
      intuition. intuition.
Qed.



Lemma State_eval_sub': forall s e (mu mu': list (state s e)) F,
WF_dstate_aux mu ->
WF_dstate_aux mu'->
d_subseq mu mu'->
State_eval_dstate F mu'->
State_eval_dstate F mu.
Proof.
induction mu.  intros. destruct mu'.
       destruct H2.
       simpl in H1. destruct H1.  
       intros. destruct mu'.
       destruct a.
       simpl in H1. destruct H1.
       destruct mu; destruct mu';
       destruct a; destruct s0.
       simpl in H1. 
       simpl. econstructor.
       inversion_clear H2.
       apply State_eval_sub with q0.
       inversion_clear H. intuition.
       inversion_clear H0. intuition.
       intuition. destruct H1. subst.
       intuition. 
       
       econstructor.

       simpl in H1. intuition.
       destruct s1.
       simpl in H1. intuition.
       simpl. econstructor.
       destruct H1. subst.
       apply State_eval_sub with q0.
       inversion_clear H. intuition.
       inversion_clear H0. intuition.
       intuition. 
       inversion_clear H2. intuition.
       apply IHmu with (s2 :: mu').
       inversion_clear H. assumption.
       inversion_clear H0. assumption.
       simpl in H1. intuition.
       destruct s1. destruct s2.
       simpl in H2. 
       inversion_clear H2. intuition.
Qed.

(* Lemma State_eval_combin: forall s e (mu:list(cstate * qstate s e)) (F1 F2:State_formula),
(exists s0 e0 s1 e1 (mu0:list(cstate * qstate s0 e0)) (mu1:list(cstate * qstate s1 e1)), 
and (d_combin mu0 mu1 mu ) 
((State_eval_dstate F1 mu0 /\ State_eval_dstate F2 mu1)))
-> State_eval_dstate (F1 ⊙ F2) mu.
Proof. 
induction mu; intros. destruct H. destruct H.
destruct H. destruct H. destruct H.
destruct H. destruct H. inversion H; subst.
destruct H0. destruct H0.

simpl. 
econstructor.

Admitted. *) *)


       



(* 
Lemma rule':  forall c (F1 F2:State_formula),
(forall (s e : nat) (mu mu' : dstate s e),
ceval c mu mu' -> sat_Assert mu F1 -> sat_Assert mu' F2)
->
(forall (s0 e0 : nat) (mu0 mu'0 : list (cstate * qstate s0 e0)),
Sorted (StateMap.Raw.PX.ltk (elt:=qstate s0 e0)) mu0->
WF_dstate_aux mu0 ->
ceval_single c mu0 mu'0 ->
State_eval_dstate F1 mu0 -> State_eval_dstate F2 mu'0).
Proof. intros.   
       assert(Sorted (StateMap.Raw.PX.ltk (elt:=qstate s0 e0)) mu'0
       ).
       apply ceval_sorted with c mu0.
       assumption.
       assumption.
       assert(sat_Assert (StateMap.Build_slist H4) F2).
       apply H with (StateMap.Build_slist H0).
       econstructor.
       intuition.
       apply WF_ceval with c mu0.
        intuition. intuition.
        intuition.
        rewrite sat_Assert_to_State.
        econstructor.
        assumption.
        assumption.
        rewrite sat_Assert_to_State in H5.
        inversion_clear H5.
        assumption.
Qed.



Lemma subset_trans:
forall x y z,
 NSet.Subset x y ->
 NSet.Subset y z ->
 NSet.Subset x z.
Proof. intros. unfold NSet.Subset in *.
       intros. intuition.
       
Qed.
 *)







      


        




(* Theorem rule_qframe_aux: forall (c : com) (F1 F2 F3 : State_formula)
(s e : nat) ( mu mu' :list (cstate *qstate s e)),
Considered_Formula ((F1 ⊙ F3))->
Considered_Formula ((F2 ⊙ F3))->
Sorted (StateMap.Raw.PX.ltk (elt:=qstate s e)) mu->
WF_dstate_aux mu ->
(forall (s e : nat) (mu mu' : dstate s e),
    ceval c mu mu' -> sat_Assert mu F1 -> sat_Assert mu' F2)->
NSet.inter (fst (Free_state F3)) (fst (MVar c)) = NSet.empty ->
NSet.Subset (snd (MVar c)) (Qsys_to_Set (fst (Free_State F1))  (snd  (Free_State F1)) ) ->
ceval_single c mu mu' ->
State_eval_dstate (F1 ⊙ F3) mu ->
State_eval_dstate (F2 ⊙ F3) mu'.
Proof.  induction mu; intros mu' Hc1 Hc2 Hs Hw; intros.
         simpl in *. destruct H3.
       inversion_clear H3. destruct mu.
       destruct a. 
       apply (ceval_4  c _ _ _ mu') in Hs.
       destruct Hs. destruct H3. destruct H3.
       destruct H6. inversion H6; subst. 
       rewrite map2_nil_r.
       apply seman_eq_two in H4.
       remember ((PMpar_trace q (fst (Free_State (F1 ⊙ F3)))
       (snd (Free_State (F1 ⊙ F3))))).
       remember (d_par_trace x (fst (Free_State (F1 ⊙ F3)))
       (snd (Free_State (F1 ⊙ F3)))).
       destruct H4. destruct H4. destruct H4.
       assert(exists
       (mu1' : list (cstate * qstate (fst (Free_State F1))
       (snd (Free_State F1)))) 
     (mu2' : list (cstate * qstate (fst (Free_State F3))
     (snd (Free_State F3)))) 
     (mu'' : list (cstate * qstate (fst (Free_State (F1 ⊙ F3)))
     (snd (Free_State (F1 ⊙ F3))))),
       and (ceval_single c [(c0,x0)] mu1')
       (State_eval_dstate F3 mu2' /\
       d_combin mu1' mu2' mu'' /\ d_subseq l mu'')).
       apply rule_two with [(c0,x1)] [(c0, q0)] [(c0, q0)].
       rewrite Heql. 
       rewrite Heqq0.
       assert([(c0,
       PMpar_trace q (fst (Free_State (F1 ⊙ F3)))
         (snd (Free_State (F1 ⊙ F3))))]=
      d_par_trace [(c0, q)] (fst (Free_State (F1 ⊙ F3)))
      (snd (Free_State (F1 ⊙ F3)))).
      reflexivity. rewrite H8.
       apply Par_trace_ceval_swap.
       split. intuition.
       split. apply Considered_Formula_dom.
       assumption. intuition.
       apply subset_trans with (Qsys_to_Set (fst (Free_State F1)) (snd (Free_State F1))).
       assumption.
       admit. admit.
       intuition.
       econstructor. intuition.
      econstructor. apply d_subseq_eq.
      reflexivity. assumption.
      assumption.
      econstructor. intuition. econstructor.
      destruct H8. destruct H8. destruct H8.
      assert(State_eval_dstate (F2 ⊙ F3) l).
      apply State_eval_sub' with x4.
      admit. admit. 
      intuition. apply seman_eq_three'.
      admit.
      intuition. 
      exists  (fst (Free_State F1)).
      exists  (snd (Free_State F1)).
      exists (fst (Free_State F3)).
      exists  (snd (Free_State F3)).
      exists (fst (Free_State (F1 ⊙ F3))).
      exists (snd (Free_State (F1 ⊙ F3))).
      (* exists (fst (Free_State F1)). exists (snd (Free_State F1)).
       exists (fst (Free_State (F3))). exists (snd (Free_State (F3))). *)
      exists x2. exists x3. split. intuition.
      split. 
      rewrite (d_par_trace_refl ((fst (Free_State (F1 ⊙ F3))))  ((snd (Free_State (F1 ⊙ F3)))) x4).
      intuition. intuition. admit.
      split. 
     
      apply rule' with c F1 [(c0, x0)].
      intros. apply H with mu. intuition.
      assumption.
      apply Sorted_cons.
      apply Sorted_nil. apply HdRel_nil.
      admit. intuition. 
      econstructor. intuition.
      econstructor.
       intuition.
       
      apply (State_dstate_free_eval 
      _ _ (fst (Free_State (F1 ⊙ F3))) (snd (Free_State (F1 ⊙ F3)))).
      split. intuition.
      split. apply Considered_Formula_dom.
      assumption. intuition.
      admit. admit. subst. apply H9.
      intuition. intuition. 
      destruct a. destruct p.  
      inversion Hs; subst.
       apply (ceval_4  c _ _ _ mu') in Hs.
       destruct Hs. destruct H3. destruct H3.
       destruct H6. subst. 
       apply seman_eq_two in H4.
       remember ((PMpar_trace q (fst (Free_State (F1 ⊙ F3)))
       (snd (Free_State (F1 ⊙ F3))))).
       remember ((d_par_trace x (fst (Free_State (F1 ⊙ F3)))
       (snd (Free_State (F1 ⊙ F3))))). 
       apply d_seman_app_aux.
       apply WF_ceval with c [(c0, q)].
       inversion_clear Hw. apply WF_state_dstate_aux. intuition.
       intuition. 
       apply WF_ceval with c ((c1, q0) :: mu).
       inversion_clear Hw. intuition.
       intuition.
       destruct H4. destruct H4. destruct H4. 
       assert(exists
       (mu1' : list (cstate * qstate (fst (Free_State F1)) (snd (Free_State F1)))) 
     (mu2' : list (cstate * qstate (fst (Free_State F3)) (snd (Free_State F3)))) 
     (mu'' : list (cstate * qstate (fst (Free_State (F1 ⊙ F3)))
     (snd (Free_State (F1 ⊙ F3))))),
       and (ceval_single c [(c0,x1)] mu1' )
       (State_eval_dstate F3 mu2' /\
       d_combin mu1' mu2' mu'' /\ d_subseq l mu'')).
       apply rule_two with [(c0,x2)] [(c0, q1)] [(c0, q1)].
       rewrite Heql. 
       rewrite Heqq1.
       assert([(c0,
       PMpar_trace q (fst (Free_State (F1 ⊙ F3)))
         (snd (Free_State (F1 ⊙ F3))))]=
      d_par_trace [(c0, q)] (fst (Free_State (F1 ⊙ F3)))
      (snd (Free_State (F1 ⊙ F3)))).
      reflexivity. rewrite H10.
       apply Par_trace_ceval_swap.
       split. 
       intuition. split.
       apply Considered_Formula_dom.
       assumption. intuition.
       apply subset_trans with 
       ((Qsys_to_Set (fst (Free_State F1)) (snd (Free_State F1)))).
       assumption.
       admit. admit.
       intuition.
       econstructor. intuition. econstructor. apply d_subseq_eq.
      reflexivity. assumption.
       assumption.
      econstructor. intuition. econstructor.
      assert(State_eval_dstate (F2 ⊙ F3) l).
      destruct H10. destruct H10. destruct H10.
      apply State_eval_sub' with x5.
      admit. admit.
      intuition. apply seman_eq_three'.
      admit.
      intuition. 
      exists (fst (Free_State F1)). exists (snd (Free_State F1)). 
      exists (fst (Free_State F3)). exists (snd (Free_State F3)).
      exists (fst (Free_State (F1 ⊙ F3))).
      exists (snd (Free_State (F1 ⊙ F3))). 
      exists x3. exists x4. split.
      intuition. split.  
      rewrite d_par_trace_refl. 
      intuition. intuition. admit.
      split. 

      apply rule' with c F1 [(c0, x1)].
      intros. apply H with mu0. intuition.
      assumption.
      apply Sorted_cons.
      apply Sorted_nil. apply HdRel_nil.
      admit. intuition. 
      econstructor. intuition.
      econstructor.
       intuition.
      
      apply (State_dstate_free_eval 
      _ _ (fst (Free_State (F1 ⊙ F3))) (snd (Free_State (F1 ⊙ F3)))).
      split. 
      intuition.
      split. apply Considered_Formula_dom.
      assumption.
      intuition.
      admit. 
      admit. subst. intuition. apply IHmu.
      intuition. intuition.
      assumption. inversion_clear Hw.
      assumption. apply H.
      intuition. intuition.
      intuition. apply H5. 
      intuition. intuition.
Admitted.




Theorem rule_qframe: forall (F1 F2 F3: State_formula) c,
         Considered_Formula ((F1 ⊙ F3))->
         Considered_Formula ((F2 ⊙ F3))->
         ({{F1}} c {{F2}}) /\ 
          (NSet.inter (fst (Free_state F3)) (fst (MVar c)) =NSet.empty) 
         /\ NSet.Subset (snd (MVar c)) (snd (Free_state F1))
         ->  {{F1 ⊙ F3}} c {{F2 ⊙ F3}}.
Proof. unfold hoare_triple. intros F1 F2 F3 c. intros Hc1 Hc2 H.
       intros s e (mu ,IHmu) (mu', IHmu');
       intros. inversion_clear H0. simpl in H4.
       rewrite sat_Assert_to_State in *.
       inversion_clear H1. econstructor.
       intuition. simpl in H5. apply rule_qframe_aux with c F1 mu.
       intuition. intuition.  intuition. intuition.
       destruct H. assumption.
       intuition. intuition. assumption.
       assumption.
Qed. *)

              



(* Inductive derivable : Assertion -> com -> Assertion-> Type :=
  | H_Skip : forall D,
      derivable D <{skip}> D
  | H_Asgn : forall D X a,
      derivable (Assn_sub X a D) <{X := a}> D
  | H_Seq : forall P Q R c1 c2,
      derivable Q c2 R -> derivable P c1 Q -> derivable P <{c1;c2}> R
  | H_conseq: forall (P P' Q Q': Assertion) c,
      derivable P' c Q' -> (P ->> P') -> (Q'->> Q) -> derivable P c Q
  | H_conj: forall (F1 F1' F2 F2': State_formula) c,
     derivable F1 c F1' -> derivable F2 c F2' -> derivable (F1 /\ F2) c (F1' /\ F2')
  | H_If: forall (F1 F1' F2 F2': State_formula) (c1 c2:com) (b:bexp) (p:R),
      0<p<1->
     derivable (F1 /\ b) c1 (F1') -> derivable (F2 /\ (BNot b)) c2 (F2')
  -> derivable (APro [(p, (F1 /\ b)) ; ((1 - p), (F2 /\ (BNot b)))])
                <{if b then c1 else c2 end}>
                (APro [(p, F1') ; ((1 - p), F2')])
  |H_while: forall F0 F1 (b:bexp) (c:com),
         derivable (F0 /\ (b)) c (ANpro[(F0 /\ b); (F1/\ (BNot b))])
      -> derivable (ANpro[(F0 /\ b); (F1/\ (BNot b))])
                   <{while b do c end}>
                   (F1 /\ (BNot b))
  | H_sum': forall (nF1 nF2:npro_formula) p_n  c,
                    (Forall (fun x=> x<>0%R) p_n)->
                    length nF1 = length p_n -> 
                    (big_hoare nF1 nF2 c)
        -> derivable (npro_to_pro_formula nF1 p_n) c
                    (npro_to_pro_formula nF2 p_n)
  | H_Init: forall s e , derivable (BTrue) <{( s e ) :Q= 0}> ((QExp_s s e  (Vec (2^(e-s)) 0)))
  | H_QUnit: forall s' e' s e (U: Square (2^(e'-s'))) (v: Vector (2^(e-s))), (s<=s')%nat /\ (e' <=e)%nat ->WF_Matrix v->
             derivable   (QExp_s s  e  (U_v s' e' s e U† v)) (QUnit_One s' e' U) (QExp_s s  e  v)
  | H_QMeas: forall s' e' s e (v: Vector (2^(e-s))) x (P :nat-> (Pure_formula)),
             (s<=s')%nat /\ (e'<=e)%nat->(norm v = 1)%R -> WF_Matrix v->
   derivable ((QExp_s  s  e  v) /\ big_Sand (fun i:nat => (Assn_sub_P x i (P i))) (2^(e'-s')) )
             (QMeas x s' e')
             (big_pOplus (fun i:nat=> (@norm (2^(e-s)) ((U_v s' e' s e (∣ i ⟩_ (e'-s') × ⟨ i ∣_ (e'-s')) v))) ^ 2)%R
   (fun i:nat=> SAnd ((P i))  (QExp_s  s  e ((R1 / ( (@norm (2^(e-s)) ((U_v s' e' s e (∣ i ⟩_ (e'-s') × ⟨ i ∣_ (e'-s')) v)))))%R.* 
   (U_v s' e' s e (∣ i ⟩_ (e'-s') × ⟨ i ∣_ (e'-s')) v)))) (2^(e'-s')))
  | H_Absurd: forall D c, derivable (BFalse) c D
  | H_QFrame: forall (F1 F2 F3: State_formula) c,
  (NSet.inter (fst (Free_state F3)) (fst (MVar c)) = NSet.empty /\
   NSet.Subset (snd (MVar c)) (snd (Free_state F1))) ->
   derivable F1 c F2
  ->derivable (F1 ⊙ F3) c (F2 ⊙ F3).

  (* Theorem rule_qframe: forall c (F1 F2 F3: State_formula) ,
          derivable F1 c F2 ->
         (NSet.inter (fst (Free_state F3)) (fst (MVar c)) =NSet.empty) 
         /\ (NSet.inter (snd (Free_state F3)) (snd (MVar c)) =NSet.empty) 
         ->  {{F1 ⊙ F3}} c {{F2 ⊙ F3}}.
Proof.  unfold hoare_triple. induction c; intros;
        inversion_clear H1.
     --admit.
     --admit.
     -- admit.
     -- admit.
     --inversion H.
       F1 F2 F3 c. intros H.
       intros s e (mu ,IHmu). induction mu; intros (mu', IHmu');
       intros. destruct H. destruct H2.
       inversion_clear H1. inversion_clear H4.
       inversion_clear H1. simpl in H5. destruct H5. 
       constructor. constructor. constructor.
       admit. destruct mu. 
      inversion_clear H0. simpl in H4.
      simpl. inversion_clear H1. 
      inversion_clear H0. inversion_clear H1.
      destruct a.
      inversion H4;subst;   simpl in H5.
        simpl. admit.  admit. inversion H10; subst.
        rewrite map2_nil. rewrite map2_l_refl.
        simpl. admit.
        inversion H12; subst.
        rewrite map2_nil. rewrite map2_l_refl.
        simpl. 
destruct H5. destruct H1.  
destruct H1. destruct H1.
destruct H1. destruct H1. 
destruct H1. inversion H1;subst.
simpl in H.
exists s. exists x1. exists x1. existn.
exists (fst x3, q_update ((I (2 ^ (s' - s)) ⊗ U ⊗ I (2 ^ (x1 - e')))) (snd x3)).
exists (fst x3, q_update (I (2 ^ (e - x1))) (snd x4)).
split. admit. split. admit. split. admit.
split. admit. admit.


exists s. exists x. exists x. existn.
exists((fst x3, q_update ((I (2 ^ (s' - x)) ⊗ U ⊗ I (2 ^ (e - e')))) (snd x3))).
exists ((fst x3, q_update ((I (2 ^ (x - s)))) (snd x4))).

 split.   admit. 
 split. admit. split. admit.
 split. admit. admit. *)



  Theorem  soundness: forall F1 F2 c,
   derivable F1 c F2 -> {{F1}} c {{F2}} .
  Proof. intros. induction H. 
  -- apply rule_skip.
  -- apply QRule_Q_L.rule_assgn.
  --apply rule_seq with Q. assumption. assumption.
  --apply rule_conseq with P' Q'. assumption. assumption. assumption.
  --apply rule_conj. assumption. assumption.
  -- apply rule_cond. assumption. split.  assumption.
      assumption.
  -- apply rule_while. assumption. 
  --apply rule_sum. assumption. assumption. assumption.
  --apply rule_QInit.
  --apply rule_QUnit_One; assumption.
  --apply rule_QMeas; assumption.
  --admit.
  --  unfold hoare_triple. induction c; intros;
  inversion_clear H1.
--admit.
--admit.
-- admit.
-- admit.
  Qed.
  
   *)

(* Theorem rule_qframe: forall (F1 F2 F3: State_formula) c,
         ({{F1}} c {{F2}}) /\  (NSet.inter (fst (Free_state F3)) (fst (MVar c)) =NSet.empty) 
         /\ (NSet.inter (snd (Free_state F3)) (snd (MVar c)) =NSet.empty) 
         ->  {{F1 ⊙ F3}} c {{F2 ⊙ F3}}.
Proof. unfold hoare_triple. intros F1 F2 F3 c. intros H.
       intros s e (mu ,IHmu). induction mu; intros (mu', IHmu');
       intros. destruct H. destruct H2.
       inversion_clear H1. inversion_clear H4.
       inversion_clear H1. simpl in H5. destruct H5. 
       constructor. constructor. constructor.
       admit. destruct mu. 
      inversion_clear H0. simpl in H4.
      simpl. inversion_clear H1. 
      inversion_clear H0. inversion_clear H1.
      destruct a.
      inversion H4;subst;   simpl in H5.
        simpl. admit.  admit. inversion H10; subst.
        rewrite map2_nil. rewrite map2_l_refl.
        simpl. admit.
        inversion H12; subst.
        rewrite map2_nil. rewrite map2_l_refl.
        simpl. 
destruct H5. destruct H1.  
destruct H1. destruct H1.
destruct H1. destruct H1. 
destruct H1. inversion H1;subst.
simpl in H.
exists s. exists x1. exists x1. existn.
exists (fst x3, q_update ((I (2 ^ (s' - s)) ⊗ U ⊗ I (2 ^ (x1 - e')))) (snd x3)).
exists (fst x3, q_update (I (2 ^ (e - x1))) (snd x4)).
split. admit. split. admit. split. admit.
split. admit. admit.


exists s. exists x. exists x. existn.
exists((fst x3, q_update ((I (2 ^ (s' - x)) ⊗ U ⊗ I (2 ^ (e - e')))) (snd x3))).
exists ((fst x3, q_update ((I (2 ^ (x - s)))) (snd x4))).

 split.   admit. 
 split. admit. split. admit.
 split. admit. admit.


 inversion H12; subst.
 rewrite map2_nil. rewrite map2_l_refl.
 simpl.  
destruct H5. destruct H1.  
destruct H1. destruct H1.
destruct H1. destruct H1. 
destruct H1. inversion H1;subst.
simpl in H. admit. admit. admit.









      
Admitted.   *)


(* Theorem rule_qframe_aux: forall (c : com) (F1 F2 F3 : State_formula)
(s e : nat) ( mu mu' :list (cstate *qstate s e)),
(forall (s e : nat) (mu mu' : list (cstate *qstate s e)),
 ceval_single c mu mu' -> State_eval_dstate  F1 mu -> State_eval_dstate  F2 mu')->
NSet.inter (fst (Free_state F3)) (fst (MVar c)) = NSet.empty ->
NSet.Subset (snd (MVar c)) (snd (Free_state F1)) ->
ceval_single c mu mu' ->
State_eval_dstate (F1 ⊙ F3) mu ->
State_eval_dstate (F2 ⊙ F3) mu'.
Proof. induction c; intros.
--admit.
--admit.
--admit.
--admit.
--inversion H2; subst. admit.
   apply IHc2 with F1 mu1.


--assert (ceval_single <{ abort }>
[(fst x3, snd x3)] []). apply E_Abort. 
apply H in H4. simpl in H4. destruct H4. 
simpl. admit.

assert (ceval_single <{ abort }>
[(fst x3, snd x3)] []). apply E_Abort. 
apply H in H4. simpl in H4. destruct H4. 
simpl. admit.

--inversion H8; subst.  rewrite map2_nil. rewrite map2_l_refl.
simpl. exists s. exists x1. exists x1. existn.
exists ((c_update i (aeval (fst x3, snd x3 ) a)
(fst x3), snd x3)). 
exists (c_update i (aeval (fst x3,snd x4) a)
(fst x3), snd x4). split. admit.
split. admit. split. admit. split. 
assert( ceval_single <{ i := a }>
[(fst x3, snd x3)]
(StateMap.Raw.map2 option_app
   [(c_update i
       (aeval (fst x3, snd x3) a)
       (fst x3), snd x3)] [])). apply E_Asgn.
apply E_nil. rewrite map2_nil in H4. rewrite map2_l_refl in H4.
simpl in H4. apply H in H4. simpl in H4. intuition.
simpl. admit.  admit.

inversion H8; subst.  rewrite map2_nil. rewrite map2_l_refl.
simpl. exists x. existn. exists s. exists x.
exists ((c_update i (aeval (fst x3, snd x3 ) a)
(fst x3), snd x3)). 
exists (c_update i (aeval (fst x3,snd x4) a)
(fst x3), snd x4).
 split. admit.
split. admit. split. admit. split. 
assert( ceval_single <{ i := a }>
[(fst x3, snd x3)]
(StateMap.Raw.map2 option_app
   [(c_update i
       (aeval (fst x3, snd x3) a)
       (fst x3), snd x3)] [])). apply E_Asgn.
apply E_nil. rewrite map2_nil in H4. rewrite map2_l_refl in H4.
simpl in H4. apply H in H4. simpl in H4. intuition.
simpl. admit.  admit.

--admit. admit.

--admit. admit.
   admit. admit.
-- admit. admit.
   admit. admit.
(* --inversion H8; subst.  rewrite map2_nil. rewrite map2_l_refl.
simpl. exists s. exists x1. exists x1. existn.
exists (fst x3, q_update ((I (2 ^ (s' - s)) ⊗ U ⊗ I (2 ^ (x1 - e')))) (snd x3)).
exists (fst x3, q_update (I (2 ^ (e - x1))) (snd x4)).
split. admit. split. admit. split. admit.
split. admit. admit. *)
Admitted. *)
(* 

Theorem rule_qframe: forall (F1 F2 F3: State_formula) c,
         ({{F1}} c {{F2}}) /\  (NSet.inter (fst (Free_state F3)) (fst (MVar c)) =NSet.empty) 
         /\ (NSet.inter (snd (Free_state F3)) (snd (MVar c)) =NSet.empty) 
         ->  {{F1 ⊙ F3}} c {{F2 ⊙ F3}}.
Proof.  unfold hoare_triple.  intros. destruct H.
        assert(sat_Assert mu F1 -> sat_Assert mu' F2).
        apply H. assumption. 
        destruct mu as [mu IHmu].
        destruct mu' as [mu' IHmu'].
        inversion_clear H0. simpl in H5.
        repeat rewrite sat_Assert_to_State in *.
        inversion_clear H1.  simpl in *.
        econstructor. assumption. simpl in *.
        inversion_clear H3.  
        simpl in H6.
        rewrite State_eval_odot in *.
        destruct H6. destruct H6.
        split. 
        assert(sat_Assert (StateMap.Build_slist IHmu') F2).
        apply H with (StateMap.Build_slist IHmu).
        apply E_com. assumption. assumption.
        assumption. rewrite sat_Assert_to_State.
        econstructor. assumption. assumption.
        rewrite sat_Assert_to_State in *.
        inversion_clear H8. assumption.
        split. apply rule_f with c mu.
        assumption. assumption. 
        assumption. admit.
Admitted. *)