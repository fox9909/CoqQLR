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


Lemma big_sum_0_R : forall n,
(Σ (fun _ :nat =>0%R ) n)= 0%R. 
Proof. 
intros.
  induction n.
  - reflexivity.
  - simpl. remember (Σ (fun _ : nat => 0%R) n) as f.
  rewrite IHn.   
  rewrite Cplus_0_r. easy.
Qed.       

Lemma  Zero_trace: forall n, @trace n Zero=C0.
Proof. intros. unfold Zero.  unfold trace.
 apply (big_sum_0_R n). 
Qed.

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

Definition PMRpar_trace{n:nat} (M: Square (2^n)) (l:nat) : Square  (2^(n-l)):=
  let f:= (fun i=>  let v_i:= (Vec (2^l) i) in  
  ((v_i†) ⊗ (I (2^(n-l)))) ×  M ×  ((v_i) ⊗ (I (2^(n-l))))) in
  big_sum  f (2^l).

Definition PMLpar_trace{n:nat} (M: Square (2^n)) (l:nat) : Square  (2^(n-l)):=
    let f:= (fun i=>  let v_i:= (Vec (2^l) i) in  
    ((I (2^(n-l)))  ⊗ (v_i†)   ×  M × ((I (2^(n-l))) ⊗ v_i))) in
    big_sum  f (2^l).

Definition PMpar_trace{n:nat} (M: Square (2^n)) (l:nat) (m:nat):=
    PMRpar_trace (PMLpar_trace M m) l.

Lemma Ptrace_l_r: forall  n (A:Square (2^n)) s e,
s<=n-e->
PMpar_trace A  s e = big_sum (fun i : nat => big_sum
    (fun i0 : nat => ⟨ i ∣_ (s) ⊗ I (2 ^ (n - e - s))
    × (I (2 ^ (n - e)) ⊗ ⟨ i0 ∣_ (e) × A × (I (2 ^ (n - e)) ⊗ ∣ i0 ⟩_ (e)))
    × (∣ i ⟩_ (s) ⊗ I (2 ^ (n - e - s)))) 
    (2 ^ e)) (2 ^ s). 
Proof. unfold PMpar_trace. unfold PMLpar_trace.
unfold PMRpar_trace; intros. apply big_sum_eq.  
apply functional_extensionality. intros.  
assert(2^(n-e)*1 = 2 ^ s * 2 ^ (n - e - s)).
rewrite <-Nat.pow_add_r. rewrite Nat.mul_1_r. f_equal.
rewrite Nat.add_comm. rewrite Nat.sub_add. reflexivity.
assumption. destruct H0.   
rewrite  Mmult_Msum_distr_l. rewrite Mmult_Msum_distr_r.
reflexivity.
Qed.

Lemma Mmult_assoc_5: forall {m n o p q r:nat} (A: Matrix m n) 
(B: Matrix n o) (C: Matrix o p) (D: Matrix p q) (E: Matrix q r), 
A × (B × C × D) × E= (A × B) × C × (D × E).
Proof. intros. repeat rewrite <-Mmult_assoc. reflexivity.  
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
  [reflexivity|assumption]).



Lemma Ptrace_l_r': forall  n (A:Square (2^n)) s e,
s<=n-e->
PMpar_trace A  s e =big_sum (fun i : nat => big_sum
   (fun j: nat => (⟨ i ∣_ (s) ⊗ I (2 ^ (n- e - s)) ⊗ ⟨ j ∣_ (e)) 
                   × A ×  
                  (∣ i ⟩_ (s) ⊗ I (2 ^ (n- e - s)) ⊗ ∣ j ⟩_ (e))) (2 ^ e)) (2 ^ s).
Proof. intros. rewrite Ptrace_l_r. 
       apply big_sum_eq_bounded. intros. 
       apply big_sum_eq_bounded. intros.
       assert(( Init.Nat.mul (2 ^ s)  (2 ^ (n - e - s)))%nat= Init.Nat.mul (2 ^ (n - e)) 1).
       type_sovle. destruct H2. rewrite Mmult_assoc_5. 
       f_equal; type_sovle.   
       f_equal; type_sovle.  
       apply eq_trans with ((⟨ x ∣_ (s) ⊗ I (2 ^ (n - e - s)) ⊗ I 1) 
       × ((I (2 ^ s)) ⊗ (I (2 ^ (n - e - s))) ⊗ ⟨ x0 ∣_ (e))).
       f_equal.  type_sovle. type_sovle. type_sovle.  
       rewrite kron_1_r. reflexivity. 
       rewrite id_kron. f_equal; type_sovle. 
       repeat rewrite kron_mixed_product.
       repeat rewrite Mmult_1_r. repeat rewrite Mmult_1_l.
       reflexivity. auto_wf. auto_wf. auto_wf.

       apply eq_trans with (((I (2 ^ s)) ⊗ (I (2 ^ (n - e - s))) ⊗ ∣ x0 ⟩_ (e)) 
       × (∣ x ⟩_ (s) ⊗ I (2 ^ (n - e - s)) ⊗ I 1)).
       f_equal.  type_sovle. type_sovle. type_sovle.  
       rewrite id_kron. f_equal; type_sovle.
       rewrite kron_1_r. reflexivity.  
       repeat rewrite kron_mixed_product.
       repeat rewrite Mmult_1_r. repeat rewrite Mmult_1_l.
       reflexivity. auto_wf. auto_wf. auto_wf.
       assumption.
Qed.

Lemma PMpar_trace_l{n:nat} : forall l (M1:Square (2^n)) (M2:Square (2^(n-l))) (M3:Square (2^(l))),
WF_Matrix M1-> WF_Matrix M2-> WF_Matrix M3->
M1= M2⊗ M3
-> PMLpar_trace M1 l= (@trace (2^(l)) M3) .*  M2.
Proof. intros.  unfold PMLpar_trace. rewrite H2.
assert(forall i:nat, i< (2^(l)) -> (I (2 ^ (n - l)) ⊗ (Vec (2^l) i) †) × (M2 ⊗ M3)
× (I (2 ^ (n - l)) ⊗ Vec (2^l) i) =(M2) 
⊗ ((M3 i i) .* I 1)).
intros. repeat rewrite kron_mixed_product.
rewrite Mmult_1_l. rewrite Mmult_1_r.  rewrite Vec_inner_M.
reflexivity. assumption. assumption.
assumption. assumption. apply big_sum_eq_bounded in H3.
rewrite H3. rewrite <- kron_Msum_distr_l. 
rewrite <- big_sum_Mscale_r.
 unfold trace. rewrite Mscale_kron_dist_r.
 rewrite kron_1_r. reflexivity.
Qed.

Lemma PMpar_trace_r{n:nat} : forall l (M1:Square (2^n)) (M2:Square (2^(l))) (M3:Square (2^(n-l))),
WF_Matrix M1-> WF_Matrix M2-> WF_Matrix M3->
M1= M2⊗ M3
-> PMRpar_trace M1 l= (@trace (2^(l)) M2) .*  M3.
Proof. intros.  unfold PMRpar_trace. rewrite H2.
assert(forall i:nat, i< (2^(l)) -> (Vec (2 ^ l) i) †
⊗ I (2 ^ (n - l))
× (M2 ⊗ M3)
× (Vec (2 ^ l) i
   ⊗ I (2 ^ (n - l)))  =  
((M2 i i) .* I 1) ⊗ (M3) ).
intros. repeat rewrite kron_mixed_product.
rewrite Mmult_1_l. rewrite Mmult_1_r. rewrite Vec_inner_M.
reflexivity. assumption. assumption.
assumption. assumption. apply big_sum_eq_bounded in H3.
rewrite H3. rewrite <- kron_Msum_distr_r. 
rewrite <- big_sum_Mscale_r. 
 unfold trace. rewrite Mscale_kron_dist_l.
 rewrite kron_1_l. reflexivity. assumption.
 Qed.
 
   
Lemma R_trace_scale: forall n l c (M:Square (2^n)) , 
(scale c (@PMRpar_trace n M l))=
(@PMRpar_trace n ( scale c  M) l ) .
Proof. intros. unfold PMRpar_trace.
assert(forall i:nat, i< (2^(l))->
((Vec (2 ^ l) i) † ⊗ I (2 ^ (n - l)) × (c .* M)
× (Vec (2 ^ l) i ⊗ I (2 ^ (n - l)))) =
(c .*((Vec (2 ^ l) i) † ⊗ I (2 ^ (n - l)) ×  M
× (Vec (2 ^ l) i ⊗ I (2 ^ (n - l)))))) .
intros. remember ((Vec (2 ^ l) i) † ⊗ I (2 ^ (n - l))) as A.
rewrite (Mscale_mult_dist_r _ _ _ c A M).
rewrite (Mscale_mult_dist_l _ _ _ c (A × M) _).
reflexivity.
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


 Lemma PMpar_trace_m{n:nat} : forall l m (M1:Square (2^n)) (M2:Square (2^(l))) (M3:Square (2^(n-l-m))) (M4: (Square (2^m)))(H1:m<=n) (H2:l<=n-m),
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
Qed.

Lemma L_trace_scale: forall n l c (M:Square (2^n)) , 
(scale c (@PMLpar_trace n M l))=
(@PMLpar_trace n ( scale c  M) l ) .
Proof. intros.   unfold PMLpar_trace. 
assert(forall i:nat, (i< (2^(l)))%nat->
(I (2 ^ (n - l)) ⊗ ⟨ i ∣_ (l) ×  (c.* M)
      × (I (2 ^ (n - l)) ⊗ ∣ i ⟩_ (l)) ) =
(c .* (I (2 ^ (n - l)) ⊗ ⟨ i ∣_ (l) × M
× (I (2 ^ (n - l)) ⊗ ∣ i ⟩_ (l))) )) .
intros. remember (I (2 ^ (n - l)) ⊗ ⟨ i ∣_ (l)) as A.
rewrite (Mscale_mult_dist_r _ _ _ c A M).
rewrite (Mscale_mult_dist_l _ _ _ c (A × M) _).
reflexivity. 
apply big_sum_eq_bounded in H.
rewrite H. 
rewrite  Mscale_Msum_distr_r. reflexivity. 
Qed.

Local Open Scope nat_scope.
Lemma R_trace_plus: forall n l   (M N:Square (2^n)) , 
l<=n->
((@PMRpar_trace n (M .+ N) l ))=
(@PMRpar_trace n (M) l  ) .+  ((@PMRpar_trace n (N) l  )).
Proof. intros.   unfold PMRpar_trace. 
      rewrite (big_sum_eq_bounded 
      (fun i : nat =>
    ⟨ i ∣_ (l) ⊗ I (2 ^ (n - l)) × (M .+ N)
    × (∣ i ⟩_ (l) ⊗ I (2 ^ (n - l))))  
      (fun i : nat =>
      (⟨ i ∣_ (l) ⊗ I (2 ^ (n - l)) × M 
      × (∣ i ⟩_ (l) ⊗ I (2 ^ (n - l))) ) .+ 
      (⟨ i ∣_ (l) ⊗ I (2 ^ (n - l)) × N 
      × (∣ i ⟩_ (l) ⊗ I (2 ^ (n - l))) )
      )). assert(2^(n-l) =1*2^(n-l)).
      rewrite Nat.mul_1_l. reflexivity. destruct H0.
      apply Msum_plus.  intros.
      assert(2 ^ l * 2 ^ (n - l)= 2 ^ n).
      type_sovle. destruct H1.
    rewrite Mmult_plus_distr_l.
    rewrite Mmult_plus_distr_r. 
    reflexivity. 
Qed.

Lemma L_trace_plus: forall n l   (M N:Square (2^n)) ,
l<=n-> 
((@PMLpar_trace n (M .+ N) l ))=
(@PMLpar_trace n (M) l  ) .+  ((@PMLpar_trace n (N) l )).
Proof. intros.   unfold PMLpar_trace.
rewrite (big_sum_eq_bounded 
(fun i : nat =>
    I (2 ^ (n - l)) ⊗ ⟨ i ∣_ (l) × (M .+ N)
    × (I (2 ^ (n - l)) ⊗ ∣ i ⟩_ (l)))  
(fun i : nat =>
I (2 ^ (n - l)) ⊗ ⟨ i ∣_ (l) × M
× (I (2 ^ (n - l)) ⊗ ∣ i ⟩_ (l)) .+ 
I (2 ^ (n - l)) ⊗ ⟨ i ∣_ (l) × N
× (I (2 ^ (n - l)) ⊗ ∣ i ⟩_ (l))
)). assert(2^(n-l) =2^(n-l)*1). type_sovle.
 destruct H0. apply Msum_plus.  intros.
assert(2 ^ (n-l) * 2 ^ l= 2 ^ n). 
type_sovle. destruct H1.
rewrite Mmult_plus_distr_l.
rewrite Mmult_plus_distr_r. 
reflexivity. 
Qed.

Lemma PMtrace_scale: forall n l m c (M:Square (2^n)) , 
(scale c (@PMpar_trace n M l m))=
(@PMpar_trace n ( scale c  M) l m ) .
Proof. intros. unfold PMpar_trace. rewrite R_trace_scale.
rewrite L_trace_scale. reflexivity.
Qed.

Lemma PMtrace_plus: forall n l m  (M N:Square (2^n)) ,
m<=n->l<=n-m-> 
((@PMpar_trace n (M .+ N) l m))=
(@PMpar_trace n (M) l m ) .+  ((@PMpar_trace n (N) l m )).
Proof. intros. unfold PMpar_trace. rewrite L_trace_plus.
rewrite R_trace_plus. reflexivity. intuition. intuition.
Qed.
    

