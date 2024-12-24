Require Import Reals.
Require Import Coquelicot.Complex.
Require Import Strings.String.
Require Import Lists.List.
Require Import Coq.Init.Datatypes.
From Coq Require Import Bool.Bool.
From Coq Require Import Lia.
From Coq Require Import Init.Nat.


From Quan Require Import Matrix.
From Quan Require Import Quantum.
From Quan Require Import Basic.
From Quan Require Import QState.
From Quan Require Import Mixed_State.

Delimit Scope C_scope with C.
Local Open Scope C_scope.


Local Open Scope nat_scope. 

(*---------------------------Partial Trace--------------------------*)

Local Open Scope matrix_scope.

Definition R_reduced{s e:nat} (M: qstate s e) (l:nat) : qstate l e:=
  let f:= (fun i=>  let v_i:= (∣ i ⟩_ (2^(l-s))) in  
  ((v_i†) ⊗ (I (2^(e-l)))) ×  M ×  ((v_i) ⊗ (I (2^(e-l))))) in
  big_sum  f (2^(l-s)).

Definition L_reduced{s e:nat} (M: qstate s e ) (r:nat) : qstate s r:=
    let f:= (fun i=>  let v_i:= (∣ i ⟩_ (2^(e-r))) in  
    ((I (2^(r-s)))  ⊗ (v_i†)   ×  M × ((I (2^(r-s))) ⊗ v_i))) in
    big_sum  f (2^(e-r)).

Definition Reduced{s e:nat} (M: qstate s e) (l:nat) (r:nat): qstate l r:=
    R_reduced (L_reduced M r) l.

Ltac type_sovle:=
try (repeat rewrite  <-Nat.pow_add_r;  rewrite Nat.mul_1_r ; f_equal ; lia).

Ltac type_sovle':=
try (repeat rewrite  <-Nat.pow_add_r;  f_equal ; lia).

(*WF Reduced*)
Lemma WF_L_reduced{s e:nat}: forall (q:qstate s e)  r,
s<=r/\r<=e->
@WF_Matrix (2^(e-s)) (2^(e-s)) q->
@WF_Matrix  (2^(r-s)) (2^(r-s)) (L_reduced q r).
Proof. intros. 
       unfold L_reduced.
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

Lemma WF_R_reduced{s e:nat}: forall (q:qstate s e)  l,
s<=l/\l<=e->
@WF_Matrix (2^(e-s)) (2^(e-s)) q->
@WF_Matrix  (2^(e-l)) (2^(e-l)) (R_reduced q l).
Proof. intros. 
       unfold R_reduced.
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
    
    
Lemma WF_Reduced{s e:nat}: forall (q:qstate s e)  l r,
s<=l/\l<=r<=e->
@WF_Matrix (2^(e-s)) (2^(e-s)) q->
@WF_Matrix  (2^(r-l)) (2^(r-l)) (Reduced q l r).
Proof. intros. unfold Reduced. apply WF_R_reduced. lia. 
       apply WF_L_reduced. lia. assumption.
Qed. 

(*Reduced trace*)
Lemma Ptrace_l_r{ s e:nat}: forall (A:qstate s e) l r,
Reduced A  l r = big_sum (fun i : nat => big_sum
    (fun i0 : nat => ⟨ i ∣_ (2^(l-s)) ⊗ I (2 ^ (r-l))
    × (I (2 ^ (r - s)) ⊗ ⟨ i0 ∣_ (2^(e-r)) × A × (I (2 ^ (r - s)) ⊗ ∣ i0 ⟩_ (2^(e-r))))
    × (∣ i ⟩_ (2^(l-s)) ⊗ I (2 ^ (r-l)))) 
    (2 ^ (e-r))) (2 ^ (l-s)). 
Proof. unfold Reduced. unfold L_reduced.
unfold R_reduced; intros. apply big_sum_eq.  
apply functional_extensionality. intros.
rewrite (@Mmult_Msum_distr_l  (2 ^ (l-s) * 2 ^ (r-l)) (2 ^ (l-s) * 2 ^ (r-l))).
 rewrite Mmult_Msum_distr_r.
reflexivity.
Qed.

Lemma Mmult_assoc_5: forall {m n o p q r:nat} (A: Matrix m n) 
(B: Matrix n o) (C: Matrix o p) (D: Matrix p q) (E: Matrix q r), 
A × (B × C × D) × E= (A × B) × C × (D × E).
Proof. intros. repeat rewrite <-Mmult_assoc. reflexivity.  
Qed.


Lemma Ptrace_l_r' {s e:nat}: forall (A:qstate s e) l r,
s<=l /\ l<=r ->
Reduced A l r =big_sum (fun i : nat => big_sum
   (fun j: nat => (⟨ i ∣_ (2^(l-s)) ⊗ I (2 ^ (r-l)) ⊗ ⟨ j ∣_ (2^(e-r))) 
                   × A ×  
                  (∣ i ⟩_ (2^(l-s)) ⊗ I (2 ^ (r-l)) ⊗ ∣ j ⟩_ (2^(e-r)))) (2 ^ (e-r))) (2 ^ (l-s)).
Proof. intros. rewrite Ptrace_l_r. 
       apply big_sum_eq_bounded. intros. 
       apply big_sum_eq_bounded. intros.
       assert(2 ^ (l-s) * 2 ^ (r-l) = 2^(r-s) * 1)%nat.
       type_sovle.
       destruct H2. rewrite Mmult_assoc_5. 
       f_equal; type_sovle'; type_sovle. 
       f_equal; type_sovle'; type_sovle. 
       apply eq_trans with ((⟨ x ∣_ (2^(l-s)) ⊗ I (2 ^ (r-l)) ⊗ I 1) 
       × ((I (2 ^ (l-s))) ⊗ (I (2 ^ (r-l))) ⊗ ⟨ x0 ∣_ (2^(e-r)))).
       f_equal;  type_sovle'; type_sovle.   
       rewrite kron_1_r. reflexivity. 
       rewrite id_kron. f_equal; type_sovle; type_sovle'.
       f_equal; type_sovle'.
       repeat rewrite kron_mixed_product.
       repeat rewrite Mmult_1_r. repeat rewrite Mmult_1_l.
       reflexivity. auto_wf. auto_wf. auto_wf.

       apply eq_trans with (((I (2 ^ (l-s))) ⊗ (I (2 ^ (r-l))) ⊗ ∣ x0 ⟩_ (2^(e-r))) 
       × (∣ x ⟩_ (2^(l-s)) ⊗ I (2 ^ (r-l)) ⊗ I 1)).
       f_equal;  type_sovle; type_sovle'.
       rewrite id_kron. f_equal; type_sovle; type_sovle'.
       f_equal; type_sovle'.
       rewrite kron_1_r. reflexivity.  
       repeat rewrite kron_mixed_product.
       repeat rewrite Mmult_1_r. repeat rewrite Mmult_1_l.
       reflexivity. auto_wf. auto_wf. auto_wf.
Qed.


Local Open Scope nat_scope.
Lemma  big_sum_trace: forall n (f:nat-> Square n) n0, 
trace (big_sum  f  n0)= big_sum (fun i:nat => trace (f i)) n0.
Proof. intros. induction n0. simpl. apply Zero_trace. 
    simpl. rewrite trace_plus_dist. f_equal. assumption. Qed.

Lemma  Reduced_trace: forall s e (A:qstate s e) l r,
s <= l/\ l<=r /\ r<=e-> @WF_Matrix (2^(e-s)) (2^(e-s)) A->
@trace (2^(r-l)) (Reduced A  l r) = @trace (2^(e-s)) A.
Proof. intros. rewrite Ptrace_l_r'.
   assert(2^(r-l)=1 * 2 ^ (r-l) * 1) . lia.
   destruct H1. rewrite big_sum_trace.
   rewrite (big_sum_eq_bounded  _ ((fun i : nat =>
   trace (big_sum
      (fun j : nat =>
        ( (∣ i ⟩_ (2^(l-s)) × ⟨ i ∣_ (2^(l-s))) ⊗ I (2 ^ (r-l)) ⊗  (∣ j ⟩_ (2^(e-r))  × ⟨ j ∣_ (2^(e-r))) × A))
        (2 ^ (e-r)))))).
    rewrite <-big_sum_trace. 
    assert(2^(e-s) = 2^(l-s) * 2^(r-l) * (2^(e-r))); type_sovle'. 
    f_equal; type_sovle'.
     (* destruct H2. *)
    rewrite (big_sum_eq_bounded  _ ((fun i : nat =>
    @Mmult (2^(e-s)) (2^(e-s)) (2^(e-s)) ( (∣ i ⟩_ (2^(l-s)) × ⟨ i ∣_ (2^(l-s))) ⊗   I (2 ^ (r-l))
    ⊗  (big_sum
      (fun j : nat => (∣ j ⟩_ (2^(e-r)) × ⟨ j ∣_ (2^(e-r))) ) 
      (2 ^ (e-r)) ))  A ))  ). destruct H1.
    repeat rewrite <-@Mmult_Msum_distr_r. repeat rewrite <-kron_Msum_distr_r.
     repeat rewrite big_sum_I. repeat rewrite id_kron.
    assert(2^(l-s) * 2^(r-l) * (2^(e-r))= 2^(e-s)). type_sovle'.
    destruct H1.
    rewrite Mmult_1_l. reflexivity. assumption.
    intros.  rewrite kron_Msum_distr_l.
    assert(2^(e-s) = 2^(l-s) * 2^(r-l) * (2^(e-r))); type_sovle'.  
     destruct H3.
    rewrite Mmult_Msum_distr_r. reflexivity.
    intros. repeat  rewrite big_sum_trace. apply big_sum_eq_bounded.
    intros. rewrite trace_mult.   
    rewrite <-Mmult_assoc. 
    apply Logic.eq_trans with (trace
    (∣ x ⟩_ (2^(l-s)) ⊗ I (2 ^ (r-l)) ⊗ ∣ x0 ⟩_ (2^(e-r))
     × (⟨ x ∣_ (2^(l-s)) ⊗ I (2 ^ (r-l)) ⊗ ⟨ x0 ∣_ (2^(e-r))) × A)).
     f_equal. f_equal. f_equal; try lia.
    repeat rewrite kron_mixed_product. 
    rewrite Mmult_1_r.  reflexivity.
    auto_wf. intuition.
Qed.


(*WF_qstate Reduced*)
Local Open Scope nat_scope.
Lemma WF_qstate_Reduced: forall s e l r (q:qstate s e),
s<=l/\l<=r/\r<=e->
WF_qstate q->
WF_qstate (Reduced q l r).
Proof. intros. unfold WF_qstate in *.
       destruct H0.  split. 
       apply nz_Mixed_State_aux_to_nz_Mix_State.
      split.  
      rewrite Ptrace_l_r'.
      remember ((fun i : nat =>
      big_sum
        (fun j : nat =>
         ⟨ i ∣_ (2^(l - s)) ⊗ I (2 ^ (r - l)) ⊗ ⟨ j ∣_ (2^(e - r)) × q
         × (∣ i ⟩_ (2^(l - s)) ⊗ I (2 ^ (r - l)) ⊗ ∣ j ⟩_ (2^(e - r))))
        (2 ^ (e - r)))).
      
      assert(2 ^ (r - l) = 1 * 2 ^ (r - l) * 1).
      lia. rewrite <-H2.
      
      apply nz_Mixed_State_aux_big_sum.
      apply Nat.pow_nonzero. lia. 
      intros.  rewrite NZ_Mixed_State_aux_equiv'.  
      assert( m i = Zero \/ m i<> Zero).
      apply Classical_Prop.classic.
      destruct H4.
      right. assumption.  
      left.  rewrite Heqm. rewrite <-H2.
      apply nz_Mixed_State_aux_big_sum.
      apply Nat.pow_nonzero. lia.
      intros. 
      remember (⟨ i ∣_ (2^(l - s)) ⊗ I (2 ^ (r - l)) ⊗ ⟨ i0 ∣_ (2^(e - r))).
      remember ((∣ i ⟩_ (2^(l - s)) ⊗ I (2 ^ (r - l)) ⊗ ∣ i0 ⟩_ (2^(e - r))) ).
      assert ((@Mmult ( 2 ^ (r - l) )
      (2 ^ (l - s) * 2 ^ (r - l) * 2 ^ (e - r))
         (2 ^ (r - l) )
      (@Mmult ( 2 ^ (r - l) )
      (2 ^ (l - s) * 2 ^ (r - l) * 2 ^ (e - r))
      (2 ^ (l - s) * 2 ^ (r - l) * 2 ^ (e - r))
         m0
         q) m1 )=super  m0  q  ). unfold super.
      f_equal; try lia. rewrite Heqm1.
      rewrite Heqm0. repeat rewrite kron_adjoint.
      rewrite id_adjoint_eq. repeat rewrite adjoint_involutive.
      reflexivity. rewrite H6.
      rewrite NZ_Mixed_State_aux_equiv'. 
         assert( m0 × q × (m0) † = Zero \/ m0 × q × (m0) † <> Zero).
         apply Classical_Prop.classic.
        destruct H7. right.  
        assumption.
        left. 
        assert(2 ^ (r - l) = 1 * 2 ^ (r - l) * 1).
        lia. rewrite <-H8.
        apply nz_mixed_super_aux.
        rewrite Heqm0. auto_wf. 
        apply nz_Mixed_State_aux_to_nz_Mix_State.
        assert((2 ^ (e - s))= (2 ^ (l - s) * 2 ^ (r - l) * 2 ^ (e - r))).
        type_sovle'. destruct H9.
        assumption. unfold super. assumption.
        apply big_sum_not_0.
        intros. 
        rewrite Heqm in H4.
        assumption.
        apply big_sum_not_0.
        assert(Reduced q l r = 
        big_sum m (2 ^ (l - s))).
        rewrite Ptrace_l_r'.
        rewrite Heqm. reflexivity.
        lia. 
        rewrite Nat.mul_1_l in H3.
        rewrite Nat.mul_1_r in H3.
        rewrite <-H3. 
        intro. 
        assert(Cmod (@trace (2^(r-l)) (Reduced q l r)) = Cmod ((@trace (2^(r-l)) Zero))) .
        rewrite H4. reflexivity.
        rewrite Zero_trace in H5. 
        rewrite Reduced_trace in H5. rewrite Cmod_0 in H5. 
        apply nz_mixed_state_Cmod_1 in H0.
        rewrite H5 in H0. 
        lra. lia.  auto_wf.
        lia. 
      rewrite Reduced_trace.
      apply nz_mixed_state_Cmod_1. assumption.
      lia. auto_wf. lia.
Qed.

(* properties*)
Lemma Reduced_Zero{s' e'}: forall l r,
@Reduced s' e' Zero l r = Zero.
Proof. unfold Reduced.  intros.
unfold R_reduced. 
apply (@big_sum_0_bounded (Matrix (2^(e'-s')) (2^(e'-s')))).
intros. 
unfold L_reduced.
rewrite  (@big_sum_0_bounded (Matrix (2^(e'-s')) (2^(e'-s')))).
Msimpl. reflexivity.
intros. Msimpl. reflexivity.
Qed.

Lemma Reduced_tensor_l{s e:nat} : forall r (M1:qstate s r) (M2:qstate r e) (M3:qstate s e),
@WF_Matrix (2^(r-s))  ((2^(r-s))) M1-> @WF_Matrix (2^(e-r))  ((2^(e-r))) M2-> 
@WF_Matrix  (2^(e-s))  ((2^(e-s ))) M3->
M3= @kron (2^(r-s))  ((2^(r-s))) (2^(e-r))  ((2^(e-r))) M1 M2
-> L_reduced M3 r= (@trace (2^(e-r)) M2) .*  M1.
Proof. intros.  unfold L_reduced. rewrite H2.
assert(forall i:nat, i< (2^(e-r)) -> (I (2 ^ (r-s)) ⊗ (Base_vec (2^(e-r)) i) †) × (M1 ⊗ M2)
× (I (2 ^ (r-s)) ⊗ Base_vec (2^(e-r)) i) =(M1) 
⊗ ((M2 i i) .* I 1)).
intros. repeat rewrite kron_mixed_product.
rewrite Mmult_1_l. rewrite Mmult_1_r.  rewrite base_inner_M.
reflexivity. 
assumption. assumption.
assumption. assumption. apply big_sum_eq_bounded in H3.
rewrite H3. rewrite <- kron_Msum_distr_l. 
rewrite <- big_sum_Mscale_r.
 unfold trace. rewrite Mscale_kron_dist_r.
 rewrite kron_1_r. reflexivity.
Qed.

Lemma Reduced_tensor_r{s e:nat} :  forall l (M1:qstate s l) (M2:qstate l e) (M3:qstate s e),
@WF_Matrix (2^(l-s))  ((2^(l-s))) M1-> @WF_Matrix (2^(e-l))  ((2^(e-l))) M2-> 
@WF_Matrix  (2^(e-s))  ((2^(e-s ))) M3->
M3= @kron (2^(l-s))  ((2^(l-s))) (2^(e-l))  ((2^(e-l))) M1 M2
-> R_reduced M3 l= (@trace (2^(l-s)) M1) .*  M2.
Proof. intros.  unfold R_reduced. rewrite H2.
assert(forall i:nat, i< (2^(l-s)) -> (Base_vec (2 ^ (l-s)) i) †
⊗ I (2 ^ (e-l))
× (M1 ⊗ M2)
× (Base_vec (2 ^ (l-s)) i
   ⊗ I (2 ^ (e - l)))  =  
((M1 i i) .* I 1) ⊗ (M2) ).
intros. repeat rewrite kron_mixed_product.
rewrite Mmult_1_l. rewrite Mmult_1_r. rewrite base_inner_M.
reflexivity. assumption. assumption.
assumption. assumption. apply big_sum_eq_bounded in H3.
rewrite H3. rewrite <- kron_Msum_distr_r. 
rewrite <- big_sum_Mscale_r. 
 unfold trace. rewrite Mscale_kron_dist_l.
 rewrite kron_1_l. reflexivity. assumption.
 Qed.
 
   
Lemma R_reduced_scale: forall s e l c (M:qstate s e),
(@scale (2^(e-l)) (2^(e-l)) c (R_reduced M l))=
(@R_reduced s e (scale c  M) l ) .
Proof. intros. unfold R_reduced.
assert(forall i:nat, i< (2^(l-s))->
(∣ i ⟩_ (2^(l-s)) † ⊗ I (2 ^ (e - l)) × (c .* M)
× (∣ i ⟩_ (2^(l-s)) ⊗ I (2 ^ (e - l)))) =
(c .*(∣ i ⟩_ (2^(l-s)) † ⊗ I (2 ^ (e - l)) ×  M
× (∣ i ⟩_ (2^(l-s)) ⊗ I (2 ^ (e - l)))))) .
intros. remember (∣ i ⟩_ (2^(l-s)) † ⊗ I (2 ^ (e - l))) as A.
rewrite (Mscale_mult_dist_r _ _ _ c A M).
rewrite (Mscale_mult_dist_l _ _ _ c (A × M) _).
reflexivity.
assert( big_sum
(fun i : nat =>
 ⟨ i ∣_ (2^(l - s)) ⊗ I (2 ^ (e - l)) × (@scale (Nat.pow (S (S O)) (sub e s))
 (Nat.pow (S (S O)) (sub e s)) c M)
 × (∣ i ⟩_ (2^(l - s)) ⊗ I (2 ^ (e - l))))
(2 ^ (l - s))= 
big_sum
(fun i : nat =>
 ⟨ i ∣_ (2^(l - s)) ⊗ I (2 ^ (e - l)) × (@scale
 (mul (Nat.pow (S (S O)) (sub l s))
    (Nat.pow (S (S O)) (sub e l)))
 (mul (Nat.pow (S (S O)) (sub l s))
    (Nat.pow (S (S O)) (sub e l)))
 c M)
 × (∣ i ⟩_ (2^(l - s)) ⊗ I (2 ^ (e - l))))
(2 ^ (l - s))). f_equal.
rewrite H0. 
apply big_sum_eq_bounded in H.
rewrite H. 
rewrite Mscale_Msum_distr_r. reflexivity. 
Qed.


Locate plus_assoc.
(*l是左边的维数， m是右边的维数*)
Local Open Scope nat_scope.

Lemma  minus_S: forall (n l:nat), n- (S l)=n-l-1 .
Proof. induction n. reflexivity.
      induction l. 
 rewrite Nat.sub_0_r.
 reflexivity.
simpl. apply IHn.
Qed.

Lemma  minus_assoc: forall (n l m: nat), n-l-m=n-m-l .
Proof.
induction n.
reflexivity.
induction l. 
rewrite Nat.sub_0_r.
intros. 
rewrite Nat.sub_0_r.  reflexivity.
induction m.
rewrite Nat.sub_0_r.
rewrite Nat.sub_0_r. reflexivity.
simpl.
rewrite minus_S. rewrite (minus_S (n-m) (l)).
assert(n-l-m=n-m-l).
apply IHn. rewrite H. reflexivity.
Qed.


Lemma L_reduced_scale: forall s e r c (M:qstate s e) , 
(@scale (2^(r-s)) (2^(r-s)) c (@L_reduced s e M r))=
(@L_reduced s e ( scale c  M) r ).
Proof. intros.   unfold L_reduced.
assert(forall i:nat, (i< (2^(e-r)))%nat->
(I (2 ^ (r-s)) ⊗ ⟨ i ∣_ (2^(e-r)) ×  (c.* M)
      × (I (2 ^ (r-s)) ⊗ ∣ i ⟩_ (2^(e-r))) ) =
(c .* (I (2 ^ (r-s)) ⊗ ⟨ i ∣_ (2^(e-r)) × M
× (I (2 ^ (r-s)) ⊗ ∣ i ⟩_ (2^(e-r)))) )) .
intros. remember (I (2 ^ (r-s)) ⊗ ⟨ i ∣_ (2^(e-r))) as A.
rewrite (Mscale_mult_dist_r _ _ _ c A M).
rewrite (Mscale_mult_dist_l _ _ _ c (A × M) _).
reflexivity.
assert( big_sum
(fun i : nat =>
  I (2 ^ (r - s)) ⊗ ⟨ i ∣_ (2^(e - r))  × 
 (@scale (Nat.pow (S (S O)) (sub e s))
 (Nat.pow (S (S O)) (sub e s)) c M)
 × ( I (2 ^ (r - s)) ⊗  ∣ i ⟩_ (2^(e - r)) ))
(2 ^ (e- r))= 
big_sum
(fun i : nat =>
I (2 ^ (r - s)) ⊗ ⟨ i ∣_ (2^(e - r))  × (@scale
 (mul (Nat.pow (S (S O)) (sub r s))
    (Nat.pow (S (S O)) (sub e r)))
 (mul (Nat.pow (S (S O)) (sub r s))
    (Nat.pow (S (S O)) (sub e r)))
 c M)
 × ( I (2 ^ (r - s)) ⊗  ∣ i ⟩_ (2^(e - r)) ))
(2 ^ (e-r))). f_equal.
rewrite H0.
apply big_sum_eq_bounded in H.
rewrite H. 
rewrite  Mscale_Msum_distr_r. reflexivity. 
Qed.

Local Open Scope nat_scope.
Lemma R_reduced_plus: forall s e l (M N:qstate s e) , 
((@R_reduced s e (M .+ N) l ))=
(@R_reduced s e (M) l  ) .+  ((@R_reduced s e (N) l  )).
Proof. intros.   unfold R_reduced. 
      rewrite (big_sum_eq_bounded 
      (fun i : nat =>
    ⟨ i ∣_ (2^(l-s)) ⊗ I (2 ^ (e - l)) × (M .+ N)
    × (∣ i ⟩_ (2^(l-s)) ⊗ I (2 ^ (e - l))))  
      (fun i : nat =>
      (⟨ i ∣_ (2^(l-s)) ⊗ I (2 ^ (e - l)) × M 
      × (∣ i ⟩_ (2^(l-s)) ⊗ I (2 ^ (e - l))) ) .+ 
      (⟨ i ∣_ (2^(l-s)) ⊗ I (2 ^ (e - l)) × N 
      × (∣ i ⟩_ (2^(l-s)) ⊗ I (2 ^ (e - l))) )
      )). assert(2^(e-l) =1*2^(e-l)).
      rewrite Nat.mul_1_l. reflexivity. destruct H.
      apply (@Msum_plus _ (2^(e-s)) (2^(e-s))).
      intros. 
    rewrite Mmult_plus_distr_l.
    rewrite Mmult_plus_distr_r. 
    reflexivity. 
Qed.

Lemma L_reduced_plus: forall s e l   (M N:qstate s e) ,
((@L_reduced s e (M .+ N) l ))=
(@L_reduced s e (M) l  ) .+  ((@L_reduced s e (N) l )).
Proof. intros.   unfold L_reduced.
rewrite (big_sum_eq_bounded 
(fun i : nat =>
    I (2 ^ (l-s)) ⊗ ⟨ i ∣_ (2^(e-l)) × (M .+ N)
    × (I (2 ^ (l-s)) ⊗ ∣ i ⟩_ (2^(e-l))))  
(fun i : nat =>
I (2 ^ (l-s)) ⊗ ⟨ i ∣_ (2^(e-l)) × M
× (I (2 ^ (l-s)) ⊗ ∣ i ⟩_ (2^(e-l))) .+ 
I (2 ^ (l-s)) ⊗ ⟨ i ∣_ (2^(e-l)) × N
× (I (2 ^ (l-s)) ⊗ ∣ i ⟩_ (2^(e-l)))
)). assert(2^(l-s) =2^(l-s)*1). type_sovle.
 destruct H. apply (@Msum_plus _ (2^(l-s)) (2^(l-s))).  intros.
rewrite Mmult_plus_distr_l.
rewrite Mmult_plus_distr_r. 
reflexivity. 
Qed.

Lemma Reduced_scale: forall s e l r c (M:qstate s e) , 
(@scale (2^(r-l)) (2^(r-l)) c (@Reduced s e M l r))=
(@Reduced s e ( scale c  M) l r ) .
Proof. intros. unfold Reduced. rewrite R_reduced_scale.
rewrite L_reduced_scale. reflexivity.
Qed.

Lemma Reduced_plus: forall s e l r  (M N:qstate s e) ,
((@Reduced s e (M .+ N) l r))=
(@Reduced s e (M) l r ) .+  ((@Reduced s e (N) l r )).
Proof. intros. unfold Reduced. rewrite L_reduced_plus.
rewrite R_reduced_plus. reflexivity. 
Qed.


Lemma big_sum_Reduced{ s e: nat}: forall n (f:nat-> Square (2^(e-s)) ) l r ,
s<=l/\l<=r/\ r<=e->
Reduced (big_sum f n) l r=
big_sum (fun i :nat =>Reduced (f i) l r ) n .
Proof. induction n; intros; simpl. 
      apply Reduced_Zero.  
      unfold qstate in *.
      rewrite Reduced_plus.
      rewrite <-IHn. reflexivity. assumption.
Qed.


Local Open Scope nat_scope.
Lemma L_reduced_assoc{ s e :nat}: forall (q:qstate s e) r r',
s<=r' /\ r'<=r /\ r<=e->
L_reduced (L_reduced q r)  r'=
L_reduced q  r'.
Proof. intros. unfold L_reduced.
       
       rewrite (big_sum_eq_bounded  
       _ ((fun i : nat =>
        big_sum
           (fun i0 : nat =>
            I (2 ^ (r' - s)) ⊗ ⟨ i ∣_ (2^(r - r')) ⊗ ⟨ i0 ∣_ (2^(e - r)) × q
            × ((I (2 ^ (r' - s)) ⊗ ∣ i ⟩_ (2^(r - r'))) ⊗ ∣ i0 ⟩_ (2^(e - r))))
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
      assert( ∣ x / 2 ^ (e - r) ⟩_ (2^(r - r'))
      ⊗ ∣ x mod 2 ^ (e - r) ⟩_ (2^(e - r)) =
      ∣ x ⟩_ (2^(r - r' + (e - r)))).
      rewrite Nat.pow_add_r.
      apply (base_kron x (2^(r-r')) (2^(e-r))).
      assert(adjoint (∣ x / 2 ^ (e - r) ⟩_ (2^(r - r'))
      ⊗ ∣ x mod 2 ^ (e - r) ⟩_ (2^(e - r)))=
      adjoint (∣ x ⟩_ (r - r' + (e - r)))).
      rewrite H2. reflexivity.
      rewrite kron_adjoint in H3.
      assumption.
      apply WF_adjoint.
      apply WF_base. 
      apply Nat.div_lt_upper_bound.
      apply Nat.pow_nonzero. lia. 
      assert(2 ^ (e - r) * 2 ^ (r - r') = 2^(e-r')).
      type_sovle'. rewrite H1. assumption.
     apply WF_adjoint.
     apply WF_base.
     apply Nat.mod_bound_pos.
     lia. apply pow_gt_0.
      rewrite kron_assoc; auto_wf.
      f_equal; type_sovle'.
      apply base_kron.
      apply WF_base. 
      apply Nat.div_lt_upper_bound.
      apply Nat.pow_nonzero. lia. 
      assert(2 ^ (e - r) * 2 ^ (r - r') = 2^(e-r')).
      type_sovle'. rewrite H1. assumption.
      
     apply WF_base.   apply Nat.mod_bound_pos.
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
       apply Logic.eq_trans with (I (2 ^ (r' - s)) ⊗ ⟨ x ∣_ (2^(r - r'))
       ⊗ I 1 × (I (2 ^ (r' - s)) ⊗ I (2^(r-r')) ⊗ ⟨ x0 ∣_ (2^(e - r))) × q
       × (I (2 ^ (r' - s)) ⊗ I (2^(r - r')) ⊗ ∣ x0 ⟩_ (2^(e - r))
          × (I (2 ^ (r' - s)) ⊗ ∣ x ⟩_ (2^(r - r')) ⊗ I 1 ))).
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

Lemma R_reduced_assoc{ s e :nat}: forall (q:qstate s e) l l',
s<=l /\ l<=l' /\ l'<=e->
R_reduced (R_reduced q l)  l'=
R_reduced q  l'.
Proof. intros. unfold R_reduced.
       
       rewrite (big_sum_eq_bounded  
       _ ((fun i : nat =>
        big_sum
           (fun i0 : nat =>
             (⟨ i0 ∣_ (2^(l-s)) ⊗ ⟨ i ∣_ (2^(l' - l)) ⊗  I (2 ^ (e - l')) ) × q
            × ((  ∣ i0 ⟩_ (2^(l- s))) ⊗ ∣ i ⟩_ (2^(l' - l)) ⊗ (I (2 ^ (e-l'))  )))
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
      assert(∣ x / 2 ^ (l' - l) ⟩_ (2^(l - s))
      ⊗ ∣ x mod 2 ^ (l' - l) ⟩_ (2^(l' - l))=
      ∣ x ⟩_ (2^(l - s + (l' - l)))).
      rewrite Nat.pow_add_r.
      apply (base_kron x (2 ^ (l - s)) (2 ^ (l' - l))).
      assert(adjoint ( ∣ x / 2 ^ (l' - l) ⟩_ (2^(l - s))
      ⊗ ∣ x mod 2 ^ (l' - l) ⟩_ (2^(l' - l)))=
      adjoint (∣ x ⟩_ (2^(l - s + (l' - l))))).
      rewrite H2. reflexivity.
      rewrite kron_adjoint in H3.
      apply H3.
      f_equal; type_sovle'.
      apply base_kron.
      assert(2^(l'-l) * 2^(e-l')=1 * 2^(e-l)).
      rewrite Nat.mul_1_l. 
      type_sovle'. destruct H0.
      intros.
      rewrite Mmult_Msum_distr_l.
      rewrite Mmult_Msum_distr_r.
      apply big_sum_eq_bounded.
      intros. 
      rewrite Mmult_assoc_5.
      apply Logic.eq_trans with ( I 1  ⊗ ⟨ x ∣_ (2^(l'-l)) ⊗  I (2 ^ (e-l')) 
      × ( ⟨ x0 ∣_ (2^(l- s)) ⊗ I (2 ^ (l'-l)) ⊗ I (2^(e-l')) ) × q
      × ( ∣ x0 ⟩_ (2^(l - s)) ⊗ I (2 ^ (l' - l)) ⊗ I (2^(e - l')) 
      × (I 1 ⊗ ∣ x ⟩_ (2^(l'- l)) ⊗  I (2 ^ (e- l'))  ))).
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

Lemma Reduced_comm{ s e :nat}: forall (q:qstate s e) l r ,
s<=l /\ l<=r /\ r<=e->
R_reduced (L_reduced q r) l=
L_reduced (R_reduced q l) r.
Proof. intros. unfold R_reduced. 
       unfold L_reduced.
       rewrite (big_sum_eq_bounded 
       _ ((fun i : nat =>
      big_sum
      (fun i0 : nat =>
      ⟨ i ∣_ (2^(l - s)) ⊗ I (2 ^ (r - l)) ⊗ ⟨ i0 ∣_ (2^(e - r)) × q
      × ((∣ i ⟩_ (2^(l - s)) ⊗ I (2 ^ (r - l))) ⊗ ∣ i0 ⟩_ (2^(e - r))))
      (2 ^ (e - r))))).
      
      rewrite (big_sum_eq_bounded 
      (fun i : nat =>
      I (2 ^ (r - l)) ⊗ ⟨ i ∣_ (2^(e - r))
      × big_sum
       (fun i0 : nat =>
        ⟨ i0 ∣_ (2^(l - s)) ⊗ I (2 ^ (e - l)) × q
        × (∣ i0 ⟩_ (2^(l - s)) ⊗ I (2 ^ (e - l))))
       (2 ^ (l - s)) × (I (2 ^ (r - l)) ⊗ ∣ i ⟩_ (2^(e - r))))
      ((fun i : nat =>
     big_sum
     (fun i0 : nat =>
     ⟨ i0 ∣_ (2^(l - s)) ⊗ I (2 ^ (r - l)) ⊗ ⟨ i∣_ (2^(e - r)) × q
     × ((∣ i0 ⟩_ (2^(l - s)) ⊗ I (2 ^ (r - l))) ⊗ ∣ i ⟩_ (2^(e - r))))
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
       apply Logic.eq_trans with ( I 1 ⊗ I (2 ^ (r - l)) ⊗ ⟨ x ∣_ (2^(e - r))
        × ( ⟨ x0 ∣_ (2^(l - s)) ⊗ I (2 ^ (r- l)) ⊗ I (2^(e-r)) ) × q
       ×  ( ∣ x0 ⟩_ (2^(l - s)) ⊗ I (2 ^ (r - l)) ⊗ I (2^(e - r)) 
          × (  I 1  ⊗ I (2 ^ (r - l)) ⊗ ∣ x ⟩_ (2^(e - r))  ))).
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
       apply Logic.eq_trans with ( ⟨ x ∣_ (2^(l - s )) ⊗ I (2 ^ (r - l))  ⊗ I 1
        × ( I (2 ^ ( l- s)) ⊗ I (2^ (r - l)) ⊗ ⟨ x0 ∣_ (2^(e - r)) ) × q
        ×  (  I (2 ^ (l- s)) ⊗ I (2^(r - l)) ⊗ ∣ x0 ⟩_ (2^(e - r))
        × ( ∣ x ⟩_ (2^(l - s)) ⊗ I (2 ^ (r - l)) ⊗ I 1 ))).
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



Lemma Reduced_assoc{ s e :nat}: forall (q:qstate s e) l r l' r',
s<=l /\ l<=l' /\l' <=r' /\  r'<=r /\ r<=e->
Reduced (Reduced q l r) l' r'=
Reduced q l' r'.
Proof. intros. unfold Reduced. 
       rewrite Reduced_comm; try lia.
       rewrite R_reduced_assoc; try lia.
       rewrite Reduced_comm; try lia.
       rewrite L_reduced_assoc; try lia.
       rewrite Reduced_comm; try lia.
       reflexivity. 
Qed. 



Lemma R_reduced_refl{s e : nat}: forall (l : nat) (q : qstate s e),
l = s -> @WF_Matrix  (2^(e-s)) (2^(e-s)) q  -> 
R_reduced q l = q.
Proof. intros. subst. unfold R_reduced. 
       rewrite Nat.sub_diag.  
       simpl. rewrite Mplus_0_l.
       rewrite base_I. rewrite id_adjoint_eq.
       rewrite kron_1_l; auto_wf.
       repeat rewrite Nat.add_0_r.
       repeat rewrite Nat.mul_1_r.
       repeat rewrite Mmult_1_l; auto_wf.
       repeat rewrite Mmult_1_r; auto_wf.
       reflexivity.   
Qed.

Lemma L_reduced_refl{s e : nat}: forall (r : nat) (q : qstate s e),
 r=e -> @WF_Matrix  (2^(e-s)) (2^(e-s)) q  -> 
L_reduced q r = q.
Proof. intros. subst. unfold L_reduced. 
       rewrite Nat.sub_diag.  
       simpl. rewrite Mplus_0_l.
       rewrite base_I. rewrite id_adjoint_eq.
       rewrite kron_1_r; auto_wf.
       repeat rewrite Nat.add_0_r.
       repeat rewrite Nat.mul_1_r.
       repeat rewrite Mmult_1_l; auto_wf.
       repeat rewrite Mmult_1_r; auto_wf.
       reflexivity.   
Qed.


Lemma Reduced_refl{s e:nat}: forall l r (q: qstate s e),
l=s/\r=e-> @WF_Matrix (2^(e-s)) (2^(e-s)) q->
Reduced q l r=q.
Proof. intros. destruct H. subst.
       unfold Reduced. 
       rewrite L_reduced_refl; try reflexivity; try assumption.
       rewrite R_reduced_refl; try reflexivity; assumption.
Qed.



Lemma Reduced_L {s e : nat}: forall (l r : nat) (q : qstate s e),
s=l/\ l<=r/\r<=e -> @WF_Matrix  (2^(e-s)) (2^(e-s)) q  -> 
Reduced q l r = L_reduced q r.
Proof. intros. destruct H. subst. unfold Reduced. 
       rewrite R_reduced_refl. 
       reflexivity. reflexivity.
       apply WF_L_reduced.
       assumption. assumption. 
Qed.

Lemma Reduced_R {s e : nat}: forall (l r : nat) (q : qstate s e),
r=e -> @WF_Matrix  (2^(e-s)) (2^(e-s)) q  -> 
Reduced q l r = R_reduced q l.
Proof. intros.  subst. unfold Reduced. 
       rewrite L_reduced_refl. 
       reflexivity. reflexivity.
       assumption. 
Qed.


Fixpoint d_reduced{ s e: nat} (mu:list (cstate * qstate s e)) l r :=
       match mu with 
       | nil => nil 
       | (c, q)::mu' =>(c, Reduced q l r):: (d_reduced mu' l r)
       end.
     



Lemma d_reduced_assoc{ s e :nat}: forall (mu: list (cstate *qstate s e)) l r l' r',
s<=l /\ l<=l' /\l' <=r' /\  r'<=r /\ r<=e->
d_reduced (d_reduced mu l r) l' r'=
d_reduced mu l' r'.
Proof. induction mu; intros.
simpl. reflexivity.
destruct a. 
simpl. f_equal.
rewrite Reduced_assoc. reflexivity.
intuition. apply IHmu. intuition. 
Qed. 



Lemma d_reduced_refl{s e:nat}: forall l r (mu: list (cstate * qstate s e)),
l=s/\r=e-> WF_Matrix_dstate mu->
d_reduced mu l r=mu.
Proof. induction mu; intros. simpl. reflexivity.
        destruct a. 
      simpl in *. f_equal. 
      f_equal. apply Reduced_refl.
      intuition. intuition.
      apply IHmu. intuition. intuition.
Qed.

Lemma d_reduced_map2{s e :nat}: forall (mu1 mu2: list (cstate *qstate s e)) l r,
(d_reduced (StateMap.Raw.map2 option_app mu1 mu2) l r)=
( (StateMap.Raw.map2 option_app (d_reduced mu1 l r ) (d_reduced mu2 l r))).
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
       simpl. unfold q_plus. rewrite Reduced_plus.
       rewrite IHmu1.
       reflexivity.
       simpl. rewrite IHmu2.
       reflexivity.
Qed.

Lemma d_reduced_trace{s e:nat}: forall (l r : nat) (mu: list (cstate * qstate s e)),
s <= l /\ l <= r <= e -> 
WF_Matrix_dstate mu ->
 d_trace_aux mu =
 d_trace_aux (d_reduced mu l r).
Proof. induction mu; intros. simpl. reflexivity.
      destruct a. simpl. unfold s_trace.
      simpl. unfold q_trace.  rewrite  Reduced_trace.
      rewrite IHmu. reflexivity.
      intuition. inversion_clear H0. intuition.
      intuition. inversion_clear H0. 
       intuition.  
Qed.


Lemma WF_d_reduced: forall (s e l r : nat) (mu: list (cstate * qstate s e)),
s <= l /\ l <= r <= e -> WF_dstate_aux mu ->
 WF_dstate_aux (d_reduced mu l r).
Proof. induction mu; intros. simpl. econstructor.
destruct a. simpl. econstructor.
unfold WF_state. simpl. apply WF_qstate_Reduced.
intuition. inversion_clear H0. assumption.
apply IHmu. intuition. inversion_clear H0.
assumption. assert((((c, Reduced q l r) :: d_reduced mu l r)=
d_reduced ((c, q) :: mu) l r)).
simpl. reflexivity.
unfold state.
rewrite H1. 
rewrite <-d_reduced_trace.
inversion_clear H0. assumption.
intuition.
apply WF_NZ_Mixed_dstate.
assumption.
 
Qed.

Import Sorted.
Lemma d_reduced_sort{s e:nat}:forall (mu: list (state s e)) l r,
Sorted (StateMap.Raw.PX.ltk (elt:=qstate s e)) mu->
Sorted (StateMap.Raw.PX.ltk (elt:=qstate s e)) (d_reduced mu l r).
Proof. induction mu; intros. simpl. econstructor.
inversion_clear H. 
destruct a. simpl. econstructor . 
apply IHmu. assumption.
destruct mu. simpl in *. econstructor.
destruct s0. 
simpl. econstructor.  inversion_clear H1.
unfold StateMap.Raw.PX.ltk in *. simpl in *.
assumption.
Qed.