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
From Quan Require Import QState_L.


Delimit Scope C_scope with C.
Local Open Scope C_scope.


Local Open Scope nat_scope.
Definition Vec(n:nat) (i:nat): Vector n := 
    fun x y => match x, y with 
            | j, 0 => if j=?i then C1 else C0
            | _, _ => C0
            end.

Notation "∣ i ⟩_ n " := (Vec (2^n) i) (at level 0) :matrix_scope.
Notation "⟨ i ∣_ n " := (adjoint (Vec (2^n) i)) (at level 0) :matrix_scope.
Check ∣ 2 ⟩_ 4. 

Lemma Lt_n_i: forall n i , i<n -> i<?n=true.
Proof. 
induction n; destruct i. lia. lia.  intuition.
intros.
 simpl. intros. apply IHn. lia. 
Qed.

Lemma Neq_i_j: forall i j,  i <> j -> i =? j=false.
Proof. 
 induction i; induction j. lia. simpl. reflexivity.
 simpl. reflexivity. simpl. intros.   apply IHi. lia. 
Qed.

Lemma Vec_e_i: forall n i, i < n -> Vec n i = @e_i n i.
Proof. intros. prep_matrix_equality. 
       destruct x; destruct y; unfold e_i; simpl;
       destruct i.
       { rewrite Lt_n_i.  reflexivity.  assumption. }
       { rewrite Lt_n_i. reflexivity. lia.  }
       { rewrite Lt_n_i. reflexivity. lia. }  
       { rewrite Lt_n_i. reflexivity. lia. }
       simpl. reflexivity.
       bdestruct (x =? i). destruct H0.
       { rewrite Lt_n_i.  reflexivity.  assumption. }
       simpl.
       reflexivity.
       simpl. reflexivity.
       bdestruct (x =? i). destruct H0.
       { rewrite Lt_n_i.  reflexivity.  assumption.  }
       simpl. reflexivity.      
Qed.


Lemma  Vec1: forall (n i x:nat), x <> i -> Vec n i x 0= C0.
  Proof. intros. simpl Vec. bdestruct (x=?i). unfold not in H. intuition.
  reflexivity.   
 Qed.

 Lemma WF_vec: forall n i, i < n -> WF_Matrix (Vec n i) .
 Proof. intros. 
      unfold WF_Matrix. intros.
      destruct i. intuition. intuition.
      intuition. unfold Vec. destruct y. bdestruct(x=?0). intuition.
      reflexivity. reflexivity.   unfold Vec. destruct y. intuition.
      reflexivity. unfold Vec. destruct y. bdestruct(x=?S i). intuition.
      reflexivity. reflexivity.
 Qed.

 #[export]Hint Resolve WF_vec: wf_db.

 Definition vector_to_C (c: C): Vector 1 :=  c .* I 1.

Coercion vector_to_C : C >-> Vector .

Lemma matrix_0_0:forall c, (c .* I 1) 0 0= c.
Proof. intros. rewrite Mscale_1_r.  simpl. reflexivity. Qed.
 Require Import Coq.Structures.OrderedTypeEx.
 Lemma  big_sum_i: forall (f:nat-> C) (n i:nat), 
 (forall y, y <> i -> f y = C0)-> ( i < n -> big_sum f n= f i).
 Proof.  intros. apply big_sum_unique. exists i. auto. Qed.

 Local Open Scope C_scope.
 Lemma Vec_inner_r: forall (n i:nat) (V:Vector n),
 WF_Matrix V-> i< n -> V† × Vec n i=(V i 0)^* .* I 1.
Proof. intros.   prep_matrix_equality.  
    bdestruct (y=?0).  unfold Mmult. rewrite H1. 
      assert( (Σ
      (fun y0 : nat =>
       ((V) † x y0 * Vec n i y0 0)%C)
      n )= ((V) † x  i) * (Vec n i i 0)%C).
      try rewrite (big_sum_i (fun y0 : nat =>
      (V) † x y0 * Vec n i y0 0) n i). 
      reflexivity.  intros. simpl. unfold not in H1.  bdestruct (y0=?i).
      intuition. intuition. rewrite Cmult_0_r. reflexivity. assumption.
      rewrite H2. simpl. bdestruct (i=?i).  rewrite Cmult_1_r.
      destruct x. 
      rewrite  matrix_0_0. unfold adjoint.  reflexivity. 
      assert (WF_Matrix V †). apply WF_adjoint. assumption.
      assert (WF_Matrix ((V i 0) ^* .* I 1)). apply WF_scale. apply WF_I.
      unfold WF_Matrix in H4. 
      unfold WF_Matrix in H5. rewrite H4. rewrite H5. reflexivity.
      intuition. intuition. intuition. 
      assert (WF_Matrix ((V i 0) ^* .* I 1)). apply WF_scale. apply WF_I.
      assert (WF_Matrix ((V) † × Vec n i)). apply WF_mult. apply WF_adjoint. assumption.
      apply WF_vec. apply H0. unfold WF_Matrix in H2. 
      unfold WF_Matrix in H3. intuition. rewrite H2. rewrite H3. reflexivity.
      right. intuition. right. intuition.
Qed.

Lemma Vec_inner_l: forall (n i:nat) (V:Vector n), 
WF_Matrix V -> i< n -> (Vec n i)† ×  V =(V i 0) .* I 1.
Proof. intros. assert(V† × Vec n i=(V i 0)^* .* I 1). 
apply Vec_inner_r. assumption. assumption.
apply Madjoint_simplify in H1.  rewrite Mmult_adjoint in H1.
rewrite Mscale_adj in H1. rewrite adjoint_involutive in H1.
rewrite id_adjoint_eq in H1. rewrite Cconj_involutive in H1.
assumption.
Qed.

Lemma C1_Conj: Coquelicot.Complex.Cconj C1=C1.
Proof. 
    unfold Coquelicot.Complex.Cconj.  unfold C1. simpl. rewrite Ropp_0. reflexivity.
Qed.
      
Lemma C0_Conj: Coquelicot.Complex.Cconj C0=C0.
Proof. 
    unfold Coquelicot.Complex.Cconj.  simpl. rewrite Ropp_0. reflexivity.
Qed.   

Lemma Vec_inner_M{n:nat}: forall (M: Square n) (i:nat), 
  WF_Matrix M-> 
  i<n -> (Vec n i)† × M × (Vec n i) = (M i i) .* I 1.
Proof . intros. prep_matrix_equality.
    assert ((Vec n i) † × M = (M † × (Vec n i) )†).
    rewrite Mmult_adjoint. rewrite adjoint_involutive.
    reflexivity. rewrite H1.
    rewrite Vec_inner_r.  
    unfold Mmult. 
    assert(Σ
    (fun y0 : nat =>
      (M) † i y0 * Vec n i y0 0)
    n= (M) † i i * Vec n i i 0 ).
      apply (big_sum_i (fun y0 : nat =>
      (M) † i y0 * Vec n i y0 0) n i). 
      intros. simpl. unfold not in H1.  bdestruct (y0=?i).
      intuition. rewrite Cmult_0_r. reflexivity.
      intuition. rewrite H2. 
      unfold adjoint. rewrite Cmult_conj. 
      rewrite Cconj_involutive.
      simpl Vec. bdestruct(i=?i). 
      rewrite C1_Conj.
      rewrite Cmult_1_r. 
      reflexivity.
      intuition.
      apply WF_mult. apply WF_adjoint. assumption.
      apply WF_vec.
      assumption.
      intuition.
  Qed.

  Lemma big_sum_Mscale_r : forall (n : nat) (M: Square n) (f:nat->C) n', 
    big_sum f n' .*  M = big_sum (fun x => f x .* M) n'.
Proof. intros. induction n'.
       simpl. rewrite Mscale_0_l. reflexivity.
       simpl. rewrite Mscale_plus_distr_l.
       rewrite IHn'. reflexivity.
Qed.

Lemma  trace_base:forall (n:nat) (M:Square n),
WF_Matrix M->
big_sum (fun i:nat => (Vec n i)† × M × (Vec n i)) n  = (trace M) .* I 1.
       Proof. intros. remember ((fun i : nat => (M i i) .* I 1)).
       rewrite (big_sum_eq_bounded _ m _). 
       rewrite Heqm. unfold trace. 
       rewrite big_sum_Mscale_r.  reflexivity. 
       intros. rewrite Vec_inner_M. rewrite Heqm. reflexivity. 
       apply H. assumption.
       Qed.
Lemma Vec_inner_0{n:nat}:forall i j :nat,
i<>j-> i<(2^n) -> j<(2^n)->
(⟨ i ∣_ (n) × ∣ j ⟩_ (n))=C0 .* I 1.
Proof. intros. rewrite Vec_inner_l. simpl.
       rewrite Neq_i_j. reflexivity.
       assumption. auto_wf. assumption. 
Qed.

Lemma Vec_inner_1: forall i n,
(i<(2^n))%nat->
⟨ i ∣_ (n) × ∣ i ⟩_ (n) = I 1.
Proof. intros. rewrite Vec_inner_l. simpl.
       bdestruct (i=?i). rewrite Mscale_1_l.
       reflexivity. lia. auto_wf. assumption. 
Qed.

Local Open Scope nat_scope.
Lemma base_1:forall n x,
x<n->
(x / n) = 0 .
Proof. Admitted.

Lemma base_3:forall n x,
x>=n-> x< 2*n->
(x / n) = 1.
Proof. Admitted.

Lemma base_2:forall n x,
x<n-> 
(x mod n) = x .
Proof.  Admitted.

Lemma base_4:forall n x,
x>=n-> x< 2*n->
(x mod n) = x - n .
Proof.  Admitted.

Lemma div_1:forall y,
y/1=y .
Proof. induction y. simpl. reflexivity.
       simpl. simpl in IHy. Admitted.

 Lemma mod_1:forall y,
y mod 1=0 . Proof. Admitted.

Lemma qubit0_Vec_kron:forall n i,
i<(2^n)->
kron (Vec 2 0) (Vec (2^(n)) i) = (Vec (2^(n+1)) i).
Proof. intros. prep_matrix_equality. unfold kron.
       rewrite div_1. rewrite mod_1.
       bdestruct (x<?(2^n)).
       rewrite base_1. rewrite base_2. 
       destruct y. simpl. rewrite Cmult_1_l.
       reflexivity. 
       simpl. rewrite Cmult_0_l. reflexivity.
       assumption. assumption.
       bdestruct (x<?(2^(n+1))).
       rewrite base_3. rewrite base_4.
       destruct y. simpl. rewrite Cmult_0_l.
       admit. simpl. rewrite Cmult_0_l. reflexivity.
       assumption. assert(2 ^ (n + 1)=2 * 2 ^ n). 
      rewrite Nat.pow_add_r. rewrite Nat.mul_comm.
      f_equal.  rewrite <-H2. assumption.
      assumption. assert(2 ^ (n + 1)=2 * 2 ^ n). 
      rewrite Nat.pow_add_r. rewrite Nat.mul_comm.
      f_equal.  rewrite <-H2. assumption.
Admitted.

Lemma qubit1_Vec_kron:forall n i,
i<(2^n)->
kron (Vec 2 1) (Vec (2^(n)) i) = (Vec (2^(n+1)) (i+2^n)).
Proof. intros. prep_matrix_equality. unfold kron.
       rewrite div_1. rewrite mod_1.
       bdestruct (x<?(2^n)).
       rewrite base_1. rewrite base_2. 
       destruct y. simpl. rewrite Cmult_0_l.
       admit.
       simpl. rewrite Cmult_0_l. reflexivity.
       assumption. assumption.
       bdestruct (x<?(2^(n+1))).
       rewrite base_3. rewrite base_4.
       destruct y. simpl. rewrite Cmult_1_l.
       admit. simpl. rewrite Cmult_0_l. reflexivity.
       assumption. assert(2 ^ (n + 1)=2 * 2 ^ n). 
      rewrite Nat.pow_add_r. rewrite Nat.mul_comm.
      f_equal.  rewrite <-H2. assumption.
      assumption. assert(2 ^ (n + 1)=2 * 2 ^ n). 
      rewrite Nat.pow_add_r. rewrite Nat.mul_comm.
      f_equal.  rewrite <-H2. assumption.
Admitted.



Require Import QState_L.
Lemma  big_sum_trace: forall n (f:nat-> Square n) n0, 
trace (big_sum  f  n0)= big_sum (fun i:nat => trace (f i)) n0.
Proof. intros. induction n0. simpl. apply Zero_trace. 
    simpl. rewrite trace_plus_dist. f_equal. assumption. Qed.

(*---------------------------Partial Trace--------------------------*)

Local Open Scope matrix_scope.
(*右*)
(* Definition PMRpar_trace_aux {n:nat} (M: Square (2^n)) : Square (2^(n-1)):=
  ⟨0∣ ⊗ (I (2^(n-1))) ×  M ×  ∣0⟩ ⊗ (I (2^(n-1))) .+ ⟨1∣ ⊗ (I (2^(n-1))) × M × ∣1⟩ ⊗ (I (2^(n-1))).

Definition PMLpar_trace_aux {n:nat} (M: Square (2^n)) : Square (2^(n-1)):=
(((I (2^(n-1)))  ⊗ ⟨0∣)  ×  M × ((I (2^(n-1))) ⊗ ∣0⟩)) .+  (((I (2^(n-1))) ⊗ ⟨1∣ ) × M ×  ((I (2^(n-1))) ⊗ ∣1⟩)). *)

Definition PMRpar_trace{s e:nat} (M: qstate s e) (l:nat) : qstate l e:=
  let f:= (fun i=>  let v_i:= (Vec (2^(l-s)) i) in  
  ((v_i†) ⊗ (I (2^(e-l)))) ×  M ×  ((v_i) ⊗ (I (2^(e-l))))) in
  big_sum  f (2^(l-s)).

Definition PMLpar_trace{s e:nat} (M: qstate s e ) (r:nat) : qstate s r:=
    let f:= (fun i=>  let v_i:= (Vec (2^(e-r)) i) in  
    ((I (2^(r-s)))  ⊗ (v_i†)   ×  M × ((I (2^(r-s))) ⊗ v_i))) in
    big_sum  f (2^(e-r)).

Definition PMpar_trace{s e:nat} (M: qstate s e) (l:nat) (r:nat): qstate l r:=
    PMRpar_trace (PMLpar_trace M r) l.

Lemma Ptrace_l_r{ s e:nat}: forall (A:qstate s e) l r,
PMpar_trace A  l r = big_sum (fun i : nat => big_sum
    (fun i0 : nat => ⟨ i ∣_ (l-s) ⊗ I (2 ^ (r-l))
    × (I (2 ^ (r - s)) ⊗ ⟨ i0 ∣_ (e-r) × A × (I (2 ^ (r - s)) ⊗ ∣ i0 ⟩_ (e-r)))
    × (∣ i ⟩_ (l-s) ⊗ I (2 ^ (r-l)))) 
    (2 ^ (e-r))) (2 ^ (l-s)). 
Proof. unfold PMpar_trace. unfold PMLpar_trace.
unfold PMRpar_trace; intros. apply big_sum_eq.  
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

(* Ltac type_sovle:=
  try (rewrite <-Nat.pow_add_r; rewrite Nat.mul_1_r;  f_equal;
  rewrite Nat.add_comm; rewrite Nat.sub_add; [reflexivity|assumption]);
  try (repeat rewrite Nat.mul_1_l; repeat rewrite Nat.mul_1_r; reflexivity);
  try ( repeat rewrite <-Nat.pow_add_r; f_equal; f_equal;
  rewrite Nat.add_comm; rewrite Nat.sub_add; [reflexivity|assumption]);
  try (repeat rewrite <-Nat.pow_add_r; f_equal; rewrite Nat.add_comm; rewrite Nat.sub_add;
  [reflexivity|assumption]);
  try (repeat rewrite <-Nat.pow_add_r; f_equal;  rewrite Nat.sub_add;
  [reflexivity|assumption]);
  try (rewrite <-Nat.pow_add_r; rewrite Nat.mul_1_r; f_equal;
  try lia ). *)

Ltac type_sovle:=
    try (repeat rewrite  <-Nat.pow_add_r;  rewrite Nat.mul_1_r ; f_equal ; lia).

    Ltac type_sovle':=
    try (repeat rewrite  <-Nat.pow_add_r;  f_equal ; lia).
Lemma Ptrace_l_r' {s e:nat}: forall (A:qstate s e) l r,
s<=l /\ l<=r ->
PMpar_trace A l r =big_sum (fun i : nat => big_sum
   (fun j: nat => (⟨ i ∣_ (l-s) ⊗ I (2 ^ (r-l)) ⊗ ⟨ j ∣_ (e-r)) 
                   × A ×  
                  (∣ i ⟩_ (l-s) ⊗ I (2 ^ (r-l)) ⊗ ∣ j ⟩_ (e-r))) (2 ^ (e-r))) (2 ^ (l-s)).
Proof. intros. rewrite Ptrace_l_r. 
       apply big_sum_eq_bounded. intros. 
       apply big_sum_eq_bounded. intros.
       assert(2 ^ (l-s) * 2 ^ (r-l) = 2^(r-s) * 1)%nat.
       type_sovle.
       destruct H2. rewrite Mmult_assoc_5. 
       f_equal; type_sovle'; type_sovle. 
       f_equal; type_sovle'; type_sovle. 
       apply eq_trans with ((⟨ x ∣_ (l-s) ⊗ I (2 ^ (r-l)) ⊗ I 1) 
       × ((I (2 ^ (l-s))) ⊗ (I (2 ^ (r-l))) ⊗ ⟨ x0 ∣_ (e-r))).
       f_equal;  type_sovle'; type_sovle.   
       rewrite kron_1_r. reflexivity. 
       rewrite id_kron. f_equal; type_sovle; type_sovle'.
       f_equal; type_sovle'.
       repeat rewrite kron_mixed_product.
       repeat rewrite Mmult_1_r. repeat rewrite Mmult_1_l.
       reflexivity. auto_wf. auto_wf. auto_wf.

       apply eq_trans with (((I (2 ^ (l-s))) ⊗ (I (2 ^ (r-l))) ⊗ ∣ x0 ⟩_ (e-r)) 
       × (∣ x ⟩_ (l-s) ⊗ I (2 ^ (r-l)) ⊗ I 1)).
       f_equal;  type_sovle; type_sovle'.
       rewrite id_kron. f_equal; type_sovle; type_sovle'.
       f_equal; type_sovle'.
       rewrite kron_1_r. reflexivity.  
       repeat rewrite kron_mixed_product.
       repeat rewrite Mmult_1_r. repeat rewrite Mmult_1_l.
       reflexivity. auto_wf. auto_wf. auto_wf.
Qed.

Lemma PMpar_trace_l{s e:nat} : forall r (M1:qstate s r) (M2:qstate r e) (M3:qstate s e),
@WF_Matrix (2^(r-s))  ((2^(r-s))) M1-> @WF_Matrix (2^(e-r))  ((2^(e-r))) M2-> 
@WF_Matrix  (2^(e-s))  ((2^(e-s ))) M3->
M3= @kron (2^(r-s))  ((2^(r-s))) (2^(e-r))  ((2^(e-r))) M1 M2
-> PMLpar_trace M3 r= (@trace (2^(e-r)) M2) .*  M1.
Proof. intros.  unfold PMLpar_trace. rewrite H2.
assert(forall i:nat, i< (2^(e-r)) -> (I (2 ^ (r-s)) ⊗ (Vec (2^(e-r)) i) †) × (M1 ⊗ M2)
× (I (2 ^ (r-s)) ⊗ Vec (2^(e-r)) i) =(M1) 
⊗ ((M2 i i) .* I 1)).
intros. repeat rewrite kron_mixed_product.
rewrite Mmult_1_l. rewrite Mmult_1_r.  rewrite Vec_inner_M.
reflexivity. 
assumption. assumption.
assumption. assumption. apply big_sum_eq_bounded in H3.
rewrite H3. rewrite <- kron_Msum_distr_l. 
rewrite <- big_sum_Mscale_r.
 unfold trace. rewrite Mscale_kron_dist_r.
 rewrite kron_1_r. reflexivity.
Qed.

Lemma PMpar_trace_r{s e:nat} :  forall l (M1:qstate s l) (M2:qstate l e) (M3:qstate s e),
@WF_Matrix (2^(l-s))  ((2^(l-s))) M1-> @WF_Matrix (2^(e-l))  ((2^(e-l))) M2-> 
@WF_Matrix  (2^(e-s))  ((2^(e-s ))) M3->
M3= @kron (2^(l-s))  ((2^(l-s))) (2^(e-l))  ((2^(e-l))) M1 M2
-> PMRpar_trace M3 l= (@trace (2^(l-s)) M1) .*  M2.
Proof. intros.  unfold PMRpar_trace. rewrite H2.
assert(forall i:nat, i< (2^(l-s)) -> (Vec (2 ^ (l-s)) i) †
⊗ I (2 ^ (e-l))
× (M1 ⊗ M2)
× (Vec (2 ^ (l-s)) i
   ⊗ I (2 ^ (e - l)))  =  
((M1 i i) .* I 1) ⊗ (M2) ).
intros. repeat rewrite kron_mixed_product.
rewrite Mmult_1_l. rewrite Mmult_1_r. rewrite Vec_inner_M.
reflexivity. assumption. assumption.
assumption. assumption. apply big_sum_eq_bounded in H3.
rewrite H3. rewrite <- kron_Msum_distr_r. 
rewrite <- big_sum_Mscale_r. 
 unfold trace. rewrite Mscale_kron_dist_l.
 rewrite kron_1_l. reflexivity. assumption.
 Qed.
 
   
Lemma R_trace_scale: forall s e l c (M:qstate s e),
(@scale (2^(e-l)) (2^(e-l)) c (PMRpar_trace M l))=
(@PMRpar_trace s e (scale c  M) l ) .
Proof. intros. unfold PMRpar_trace.
assert(forall i:nat, i< (2^(l-s))->
((Vec (2 ^ (l-s)) i) † ⊗ I (2 ^ (e - l)) × (c .* M)
× (Vec (2 ^ (l-s)) i ⊗ I (2 ^ (e - l)))) =
(c .*((Vec (2 ^ (l-s)) i) † ⊗ I (2 ^ (e - l)) ×  M
× (Vec (2 ^ (l-s)) i ⊗ I (2 ^ (e - l)))))) .
intros. remember ((Vec (2 ^ (l-s)) i) † ⊗ I (2 ^ (e - l))) as A.
rewrite (Mscale_mult_dist_r _ _ _ c A M).
rewrite (Mscale_mult_dist_l _ _ _ c (A × M) _).
reflexivity.
assert( big_sum
(fun i : nat =>
 ⟨ i ∣_ (l - s) ⊗ I (2 ^ (e - l)) × (@scale (Nat.pow (S (S O)) (sub e s))
 (Nat.pow (S (S O)) (sub e s)) c M)
 × (∣ i ⟩_ (l - s) ⊗ I (2 ^ (e - l))))
(2 ^ (l - s))= 
big_sum
(fun i : nat =>
 ⟨ i ∣_ (l - s) ⊗ I (2 ^ (e - l)) × (@scale
 (mul (Nat.pow (S (S O)) (sub l s))
    (Nat.pow (S (S O)) (sub e l)))
 (mul (Nat.pow (S (S O)) (sub l s))
    (Nat.pow (S (S O)) (sub e l)))
 c M)
 × (∣ i ⟩_ (l - s) ⊗ I (2 ^ (e - l))))
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


 (* Lemma PMpar_trace_m{s e:nat} : forall l r (M1:qstate s e) (M2:Square (2^(l))) (M3:Square (2^(n-l-m))) (M4: (Square (2^m)))(H1:m<=n) (H2:l<=n-m),
 WF_Matrix M1-> WF_Matrix M2-> WF_Matrix M3-> WF_Matrix M4->
 M1= M2 ⊗ M3 ⊗ M4
 -> PMpar_trace M1 l m= (@trace (2^(l)) M2) * (@trace (2^(m)) M4).*  M3.
 Proof. intros. unfold PMpar_trace.
      rewrite H5.  
        rewrite (PMpar_trace_l m _ (M2 ⊗ M3) M4 ).
        rewrite <- R_trace_scale.
        rewrite (PMpar_trace_r l _ M2 M3 ).
        rewrite Mscale_assoc. rewrite Cmult_comm. reflexivity.
        apply WF_kron.
        rewrite <- Nat.pow_add_r.
        Local Open Scope nat_scope.
        assert ((l + (n - l - m))=(n-m)).
        assert((n-l-m)=(n-m-l)).
        apply minus_assoc.
        rewrite H6. rewrite Nat.add_comm.
        rewrite Nat.sub_add.
        reflexivity. assumption.
        rewrite H6. reflexivity.
        rewrite <- Nat.pow_add_r.
        Local Open Scope nat_scope.
        assert ((l + (n - l - m))=(n-m)).
        assert((n-l-m)=(n-m-l)).
        apply minus_assoc.
        rewrite H6. rewrite Nat.add_comm.
        rewrite Nat.sub_add.
        reflexivity. assumption.
        rewrite H6. reflexivity.
        assumption. assumption. assumption.
        unfold WF_Matrix in H3.
        unfold WF_Matrix.
        assert((n-l-m)=(n-m-l)).
        apply minus_assoc.
        rewrite <-H6.
        apply H3.
        unfold "⊗".
        assert((n-l-m)=(n-m-l)).
        apply minus_assoc.
        rewrite <-H6.
        reflexivity.
        rewrite <- H5.
        assumption.

        apply WF_kron.
        rewrite <- Nat.pow_add_r.
        Local Open Scope nat_scope.
        assert ((l + (n - l - m))=(n-m)).
        assert((n-l-m)=(n-m-l)).
        apply minus_assoc.
        rewrite H6. rewrite Nat.add_comm.
        rewrite Nat.sub_add.
        reflexivity. assumption.
        rewrite H6. reflexivity.
        rewrite <- Nat.pow_add_r.
        Local Open Scope nat_scope.
        assert ((l + (n - l - m))=(n-m)).
        assert((n-l-m)=(n-m-l)).
        apply minus_assoc.
        rewrite H6. rewrite Nat.add_comm.
        rewrite Nat.sub_add.
        reflexivity. assumption.
        rewrite H6. reflexivity.
        assumption. assumption. assumption.
        reflexivity.
Qed. *)

Lemma L_trace_scale: forall s e r c (M:qstate s e) , 
(@scale (2^(r-s)) (2^(r-s)) c (@PMLpar_trace s e M r))=
(@PMLpar_trace s e ( scale c  M) r ).
Proof. intros.   unfold PMLpar_trace.
assert(forall i:nat, (i< (2^(e-r)))%nat->
(I (2 ^ (r-s)) ⊗ ⟨ i ∣_ (e-r) ×  (c.* M)
      × (I (2 ^ (r-s)) ⊗ ∣ i ⟩_ (e-r)) ) =
(c .* (I (2 ^ (r-s)) ⊗ ⟨ i ∣_ (e-r) × M
× (I (2 ^ (r-s)) ⊗ ∣ i ⟩_ (e-r))) )) .
intros. remember (I (2 ^ (r-s)) ⊗ ⟨ i ∣_ (e-r)) as A.
rewrite (Mscale_mult_dist_r _ _ _ c A M).
rewrite (Mscale_mult_dist_l _ _ _ c (A × M) _).
reflexivity.
assert( big_sum
(fun i : nat =>
  I (2 ^ (r - s)) ⊗ ⟨ i ∣_ (e - r)  × 
 (@scale (Nat.pow (S (S O)) (sub e s))
 (Nat.pow (S (S O)) (sub e s)) c M)
 × ( I (2 ^ (r - s)) ⊗  ∣ i ⟩_ (e - r) ))
(2 ^ (e- r))= 
big_sum
(fun i : nat =>
I (2 ^ (r - s)) ⊗ ⟨ i ∣_ (e - r)  × (@scale
 (mul (Nat.pow (S (S O)) (sub r s))
    (Nat.pow (S (S O)) (sub e r)))
 (mul (Nat.pow (S (S O)) (sub r s))
    (Nat.pow (S (S O)) (sub e r)))
 c M)
 × ( I (2 ^ (r - s)) ⊗  ∣ i ⟩_ (e - r) ))
(2 ^ (e-r))). f_equal.
rewrite H0.
apply big_sum_eq_bounded in H.
rewrite H. 
rewrite  Mscale_Msum_distr_r. reflexivity. 
Qed.

Local Open Scope nat_scope.
Lemma R_trace_plus: forall s e l (M N:qstate s e) , 
((@PMRpar_trace s e (M .+ N) l ))=
(@PMRpar_trace s e (M) l  ) .+  ((@PMRpar_trace s e (N) l  )).
Proof. intros.   unfold PMRpar_trace. 
      rewrite (big_sum_eq_bounded 
      (fun i : nat =>
    ⟨ i ∣_ (l-s) ⊗ I (2 ^ (e - l)) × (M .+ N)
    × (∣ i ⟩_ (l-s) ⊗ I (2 ^ (e - l))))  
      (fun i : nat =>
      (⟨ i ∣_ (l-s) ⊗ I (2 ^ (e - l)) × M 
      × (∣ i ⟩_ (l-s) ⊗ I (2 ^ (e - l))) ) .+ 
      (⟨ i ∣_ (l-s) ⊗ I (2 ^ (e - l)) × N 
      × (∣ i ⟩_ (l-s) ⊗ I (2 ^ (e - l))) )
      )). assert(2^(e-l) =1*2^(e-l)).
      rewrite Nat.mul_1_l. reflexivity. destruct H.
      apply (@Msum_plus _ (2^(e-s)) (2^(e-s))).
      intros. 
    rewrite Mmult_plus_distr_l.
    rewrite Mmult_plus_distr_r. 
    reflexivity. 
Qed.

Lemma L_trace_plus: forall s e l   (M N:qstate s e) ,
((@PMLpar_trace s e (M .+ N) l ))=
(@PMLpar_trace s e (M) l  ) .+  ((@PMLpar_trace s e (N) l )).
Proof. intros.   unfold PMLpar_trace.
rewrite (big_sum_eq_bounded 
(fun i : nat =>
    I (2 ^ (l-s)) ⊗ ⟨ i ∣_ (e-l) × (M .+ N)
    × (I (2 ^ (l-s)) ⊗ ∣ i ⟩_ (e-l)))  
(fun i : nat =>
I (2 ^ (l-s)) ⊗ ⟨ i ∣_ (e-l) × M
× (I (2 ^ (l-s)) ⊗ ∣ i ⟩_ (e-l)) .+ 
I (2 ^ (l-s)) ⊗ ⟨ i ∣_ (e-l) × N
× (I (2 ^ (l-s)) ⊗ ∣ i ⟩_ (e-l))
)). assert(2^(l-s) =2^(l-s)*1). type_sovle.
 destruct H. apply (@Msum_plus _ (2^(l-s)) (2^(l-s))).  intros.
rewrite Mmult_plus_distr_l.
rewrite Mmult_plus_distr_r. 
reflexivity. 
Qed.

Lemma PMtrace_scale: forall s e l r c (M:qstate s e) , 
(@scale (2^(r-l)) (2^(r-l)) c (@PMpar_trace s e M l r))=
(@PMpar_trace s e ( scale c  M) l r ) .
Proof. intros. unfold PMpar_trace. rewrite R_trace_scale.
rewrite L_trace_scale. reflexivity.
Qed.

Lemma PMtrace_plus: forall s e l r  (M N:qstate s e) ,
((@PMpar_trace s e (M .+ N) l r))=
(@PMpar_trace s e (M) l r ) .+  ((@PMpar_trace s e (N) l r )).
Proof. intros. unfold PMpar_trace. rewrite L_trace_plus.
rewrite R_trace_plus. reflexivity. 
Qed.

Require Import ParDensityO.

Local Open Scope nat_scope.
Lemma WF_par_trace: forall s e l r (q:qstate s e),
s<=l/\l<=r/\r<=e->
WF_qstate q->
WF_qstate (PMpar_trace q l r).
Proof. intros. unfold WF_qstate in *.
      destruct H0.  split.
       induction H0.
       rewrite <-PMtrace_scale.
       econstructor.  assumption.
       destruct H2. 
       destruct H2. rewrite H3.
       rewrite Ptrace_l_r'.
       admit. lia.
       rewrite PMtrace_plus.
       repeat rewrite <-PMtrace_scale.
       econstructor; try assumption.
       lia. 
Admitted.
