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

Lemma  Vec0: forall (n i x:nat), x = i -> Vec n i x 0= C1.
Proof. intros. simpl Vec. bdestruct (x=?i).
reflexivity. lia.   
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
(* Lemma base_1:forall n x,
x<n->
(x / n) = 0 .
Proof. Search(Nat.div). Admitted. *)

Lemma base_3:forall n x,
x>=n-> x< 2*n->
(x / n) = 1.
Proof. intros.  
       symmetry. 
       apply (Nat.div_unique x n 1 (x-n)).
       apply lt_le_trans with (2 * n - n).
       simpl. lia. simpl. lia. lia.
Qed.

(* Lemma base_2:forall n x,
x<n-> 
(x mod n) = x .
Proof.  Admitted. *)

Lemma base_4:forall n x,
x>=n-> x< 2*n->
(x mod n) = x - n .
Proof. intros. symmetry. 
       apply (Nat.mod_unique x n 1 (x-n)).
        lia. lia.   
Qed.

(* Lemma div_1:forall y,
y/1=y .
Proof. induction y. simpl. reflexivity.
       simpl. simpl in IHy. Admitted. *)

 (* Lemma mod_1:forall y,
y mod 1=0 . Proof. Admitted. *)

Lemma qubit0_Vec_kron:forall n i,
i<(2^n)->
kron (Vec 2 0) (Vec (2^(n)) i) = (Vec (2^(n+1)) i).
Proof. intros. prep_matrix_equality. unfold kron.
       rewrite Nat.div_1_r. rewrite Nat.mod_1_r.
       bdestruct (x<?(2^n)).
       rewrite Nat.div_small. rewrite Nat.mod_small. 
       destruct y. simpl. rewrite Cmult_1_l.
       reflexivity. 
       simpl. rewrite Cmult_0_l. reflexivity.
       assumption. assumption.
       bdestruct (x<?(2^(n+1))).
       rewrite base_3. rewrite base_4.
       destruct y. simpl. rewrite Cmult_0_l.
       bdestruct (x=? i). destruct H2. lia. reflexivity.
       simpl. rewrite Cmult_0_l. reflexivity.
       assumption. assert(2 ^ (n + 1)=2 * 2 ^ n). 
      rewrite Nat.pow_add_r. rewrite Nat.mul_comm.
      f_equal.  rewrite <-H2. assumption.
      assumption. assert(2 ^ (n + 1)=2 * 2 ^ n). 
      rewrite Nat.pow_add_r. rewrite Nat.mul_comm.
      f_equal.  rewrite <-H2. assumption.
      unfold Vec.
      simpl. destruct y. bdestruct (x=?i).
      destruct H2. lia. 
      assert(x/2^n >= 2^n / 2^n). 
      apply Nat.div_le_mono. lia. lia.
      rewrite Nat.div_same in H3. 
      bdestruct (x / 2 ^ n =? 0). rewrite H4 in *.
      lia. rewrite Cmult_0_l. reflexivity. lia.
      rewrite Cmult_0_l. reflexivity.  
Qed.

Lemma qubit1_Vec_kron:forall n i,
i<(2^n)->
kron (Vec 2 1) (Vec (2^(n)) i) = (Vec (2^(n+1)) (i+2^n)).
Proof. intros. prep_matrix_equality. unfold kron.
       rewrite Nat.div_1_r. rewrite Nat.mod_1_r.
       bdestruct (x<?(2^n)).
       rewrite Nat.div_small. rewrite Nat.mod_small. 
       destruct y. simpl. rewrite Cmult_0_l.
       bdestruct (x =? i + 2 ^ n). rewrite H1 in *.
       lia. reflexivity.
       simpl. rewrite Cmult_0_l. reflexivity.
       assumption. assumption.
       bdestruct (x<?(2^(n+1))).
       rewrite base_3. rewrite base_4.
       destruct y. simpl. rewrite Cmult_1_l.
       bdestruct (x - 2 ^ n =? i). 
       rewrite <-H2. rewrite Nat.sub_add. 
       rewrite Nat.eqb_refl. reflexivity. lia.
       bdestruct (x =? i + 2 ^ n). rewrite H3 in *.
       lia. reflexivity.
       simpl. rewrite Cmult_0_l. reflexivity.
       assumption. assert(2 ^ (n + 1)=2 * 2 ^ n). 
      rewrite Nat.pow_add_r. rewrite Nat.mul_comm.
      f_equal.  rewrite <-H2. assumption.
      assumption. assert(2 ^ (n + 1)=2 * 2 ^ n). 
      rewrite Nat.pow_add_r. rewrite Nat.mul_comm.
      f_equal.  rewrite <-H2. assumption.
      simpl. unfold Vec. simpl. destruct y.
      bdestruct (x =? i + 2 ^ n). rewrite H2.
      assert(i + 2 ^ n= i+ 1* 2^n). lia. rewrite H3.
      rewrite Nat.div_add. rewrite Nat.mod_add.
      rewrite Nat.mod_small. rewrite Nat.div_small.
      simpl. rewrite Nat.eqb_refl. rewrite Cmult_1_l. reflexivity.
      lia. lia. lia. lia. 
      bdestruct (x / 2 ^ n =? 1). 
      bdestruct (x mod 2 ^ n =? i).
      assert(x= 2^n * (x / 2 ^ n)+ x mod 2 ^ n ).
      apply Nat.div_mod_eq. rewrite H3 in H5. 
      rewrite H4 in H5. rewrite Nat.mul_1_r in H5.
      rewrite Nat.add_comm in H5. lia.
       rewrite Cmult_0_r. reflexivity.
      rewrite Cmult_0_l. reflexivity. 
      rewrite Cmult_0_l. reflexivity.
Qed.



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



Lemma big_sum_x_y{n:nat}: forall (f:nat-> Matrix n n) x y n_0,
big_sum f n_0 x y= big_sum (fun i=> (f i) x y) n_0 .
Proof. induction n_0. simpl. unfold Zero. reflexivity.
      simpl. unfold Mplus. f_equal. intuition.
  
Qed.

Lemma pow_gt_0: forall n ,
2^ n >0 .
Proof. induction n. simpl. lia.
      simpl. rewrite Nat.add_0_r. 
      lia.
Qed.


Lemma big_sum_I_i: forall n i, 
i< n -> Vec n i ×  (adjoint (Vec n i)) =
fun x y => if (x =? i) && (y =? i) && (x<? n) then C1 else C0.
Proof. intros. prep_matrix_equality. unfold Mmult.
      simpl. rewrite Cplus_0_l. 
      bdestruct((x =? i)).  simpl.
      bdestruct((y =? i)).  simpl.
      bdestruct(x<? n). simpl.
      unfold adjoint. rewrite Vec0. 
      rewrite Cconj_R.
      rewrite Cmult_1_l. reflexivity.
      assumption. intuition.
      unfold adjoint. rewrite Vec1. 
      rewrite Cconj_R.
      rewrite Cmult_0_r. reflexivity.
      assumption. simpl. 
      rewrite Cmult_0_l. reflexivity.
Qed.

Lemma  big_sum_I: forall n,
big_sum (fun i : nat => ∣ i ⟩_ n × ⟨ i ∣_ n)
    (2 ^ n)= I (2^n).
Proof. intros. 
       rewrite (big_sum_eq_bounded  _
        (fun i=> fun x y => if (x =? i) && (y =? i) && (x<? 2^n) then C1 else C0)).
        prep_matrix_equality.
        rewrite big_sum_x_y.
        unfold I.  destruct x; destruct y.
        rewrite (big_sum_unique  C1).
        simpl. assert(0 <? 2 ^ n = true). 
        rewrite Lt_n_i. reflexivity. apply pow_gt_0.
        rewrite H. reflexivity.
        exists 0. split. apply pow_gt_0.
        split. simpl. rewrite Lt_n_i.  reflexivity.
        apply pow_gt_0. intros.
        assert((0 =? x')=false). rewrite Neq_i_j.
        reflexivity. assumption. rewrite H1.
        simpl. reflexivity.
        rewrite big_sum_0. simpl. reflexivity.
        intros. destruct x. simpl. reflexivity. 
        simpl. reflexivity. 
        rewrite big_sum_0. simpl. reflexivity.
        intros. destruct x0. simpl. reflexivity. 
        simpl. bdestruct ((x =? x0) ); reflexivity. 
       simpl. bdestruct (x =? y). simpl. 
       bdestruct (S x <? 2 ^ n). 
       rewrite (big_sum_unique  C1).
        simpl. assert(0 <? 2 ^ n = true). 
        rewrite Lt_n_i. reflexivity. apply pow_gt_0.
        reflexivity.
        exists (S x). split. assumption.
        split.  rewrite Nat.eqb_refl. rewrite H. rewrite Nat.eqb_refl.
        simpl. reflexivity. 
        intros. destruct x'. simpl. reflexivity. 
        simpl.  rewrite Neq_i_j.  rewrite Neq_i_j. reflexivity.
        rewrite <-H. lia. lia.
        rewrite big_sum_0. simpl. reflexivity.
        intros. destruct x0. simpl. reflexivity. 
        simpl. bdestruct ((x =? x0)); bdestruct ((y =? x0));
         reflexivity.
        simpl. 
        rewrite big_sum_0. simpl. reflexivity.
        intros. destruct x0. simpl. reflexivity. 
        simpl.  bdestruct ((x =? x0)); bdestruct ((y =? x0));
        bdestruct ((S x <? 2 ^ n)); try lia; 
         reflexivity.
         intros. apply big_sum_I_i. assumption.
Qed.


Lemma  Ptrace_trace: forall s e (A:qstate s e) l r,
s <= l/\ l<=r /\ r<=e-> @WF_Matrix (2^(e-s)) (2^(e-s)) A->
@trace (2^(r-l)) (PMpar_trace A  l r) = @trace (2^(e-s)) A.
Proof. intros. rewrite Ptrace_l_r'.
   assert(2^(r-l)=1 * 2 ^ (r-l) * 1) . lia.
   destruct H1. rewrite big_sum_trace.
   rewrite (big_sum_eq_bounded  _ ((fun i : nat =>
   trace (big_sum
      (fun j : nat =>
        ( (∣ i ⟩_ (l-s) × ⟨ i ∣_ (l-s)) ⊗ I (2 ^ (r-l)) ⊗  (∣ j ⟩_ (e-r)  × ⟨ j ∣_ (e-r)) × A))
        (2 ^ (e-r)))))).
    rewrite <-big_sum_trace. 
    assert(2^(e-s) = 2^(l-s) * 2^(r-l) * (2^(e-r))); type_sovle'. 
    f_equal; type_sovle'.
     (* destruct H2. *)
    rewrite (big_sum_eq_bounded  _ ((fun i : nat =>
    @Mmult (2^(e-s)) (2^(e-s)) (2^(e-s)) ( (∣ i ⟩_ (l-s) × ⟨ i ∣_ (l-s)) ⊗   I (2 ^ (r-l))
    ⊗  (big_sum
      (fun j : nat => (∣ j ⟩_ (e-r) × ⟨ j ∣_ (e-r)) ) 
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
    intros. rewrite trace_mult'.   
    rewrite <-Mmult_assoc. 
    apply Logic.eq_trans with (trace
    (∣ x ⟩_ (l-s) ⊗ I (2 ^ (r-l)) ⊗ ∣ x0 ⟩_ (e-r)
     × (⟨ x ∣_ (l-s) ⊗ I (2 ^ (r-l)) ⊗ ⟨ x0 ∣_ (e-r)) × A)).
     f_equal. f_equal. f_equal; try lia.
    repeat rewrite kron_mixed_product. 
    rewrite Mmult_1_r.  reflexivity.
    auto_wf. intuition.
Qed.


Lemma big_sum_not_0{n:nat}:forall (f:nat-> Square n) n0,
(big_sum f n0) <> Zero ->
(exists i:nat, (i<n0)%nat /\   (f i) <> Zero).
Proof. induction n0; intros H0. simpl in *. destruct H0. reflexivity.
      assert(big_sum f n0 = Zero \/ big_sum f n0 <> Zero).
      apply Classical_Prop.classic. destruct H.
      simpl in H0. rewrite H in H0. rewrite Mplus_0_l in H0.
      exists n0. split. lia. assumption.
       assert(exists i : nat, i < n0 /\ f i <> Zero).
       apply IHn0.  assumption. 
       destruct H1. exists x. split. lia. intuition. 
Qed.


Lemma Mixed_State_aux_big_sum{n:nat}:forall (f:nat-> Square n) n0,
(n0<>0)%nat->
(forall i:nat, (i<n0)%nat ->  Mixed_State_aux (f i) \/ ((f i) =Zero))->
(exists i:nat, (i<n0)%nat /\   (f i) <> Zero)->
Mixed_State_aux (big_sum f n0) .
Proof. induction n0; intros. simpl. intuition. 
       simpl. destruct n0.  simpl. rewrite Mplus_0_l.
       destruct H1. destruct H1. assert(x =0). lia.
       rewrite H3 in H2. 
       assert(Mixed_State_aux (f 0) \/ f 0 = Zero).
       apply H0. lia. destruct H4. assumption.
       rewrite H4 in H2. destruct H2. reflexivity.
       assert (((f (S n0)) = Zero) \/  (f (S n0)) <> Zero).
       apply Classical_Prop.classic. destruct H2.
       rewrite H2. rewrite Mplus_0_r.
       apply IHn0. lia. 
     intros. apply H0. lia.  
     destruct H1.   destruct H1.
     exists x. split. bdestruct (x =? S n0).
     rewrite H4 in *. rewrite H2 in H3. destruct H3. reflexivity.
     lia. assumption.
     assert (((big_sum f (S n0))= Zero) \/  (big_sum f (S n0)) <> Zero).
     apply Classical_Prop.classic. destruct H3.
     rewrite H3. rewrite Mplus_0_l. 
     assert(Mixed_State_aux (f (S n0)) \/ f (S n0) = Zero).
     apply H0. lia. destruct H4. assumption.
     rewrite H4 in H2. destruct H2. reflexivity.
     apply Mix_S_aux. 
     apply IHn0. lia. intros. apply H0. lia.
     apply big_sum_not_0 in H3. assumption. 
     assert(Mixed_State_aux (f (S n0)) \/ f (S n0) = Zero).
     apply H0. lia. destruct H4. assumption.
     rewrite H4 in H2. destruct H2. reflexivity.
Qed.

Local Open Scope nat_scope.
Lemma Vector_State_snd_0: forall n (x: Vector (n)),
WF_Matrix x->
(snd (((x) † × x) 0%nat 0%nat)= 0)%R.
 Proof.  intros.  simpl. unfold adjoint. unfold Mmult. 
 apply big_sum_snd_0.  intros.  rewrite  Cmult_comm.
 apply Cmult_conj_real.  
Qed.
         
Lemma matrix_0_0_rev:forall (x: Vector 1), 
WF_Matrix x->
(x  0 0) .* I 1= x.
Proof. intros.   assert(WF_Matrix (x 0 0 .* I 1)).
apply WF_scale. apply WF_I.   prep_matrix_equality. bdestruct (x0=?0).
bdestruct (y=?0). rewrite H2. rewrite H1. unfold scale.
unfold I.  simpl. rewrite Cmult_1_r. reflexivity.
rewrite H1. unfold WF_Matrix in *.   
  rewrite (H _ y).   rewrite (H0 _ y). reflexivity.
  right. lia. right. lia.  unfold WF_Matrix in *.    
  rewrite (H _ y).   rewrite (H0 _ y). reflexivity.
  left. lia. left. lia.
  Qed.     

Lemma inner_eq: forall n (x: Vector (n)),
WF_Matrix x->
((x) † × x) = ((norm x) * (norm x))%R .* I 1
 .
Proof. intros. unfold norm. rewrite sqrt_sqrt. unfold inner_product.
     rewrite <-(matrix_0_0_rev ((x) † × x)) at 1.
      unfold RtoC.  f_equal. 
      destruct (((x) † × x) 0 0)  eqn:E. 
      simpl.  f_equal. assert(r0= snd (((x) † × x) 0 0)).
      rewrite E. simpl. reflexivity. rewrite H0.
     apply Vector_State_snd_0. assumption.
     apply WF_mult.
     apply WF_adjoint. assumption. assumption.   
      apply inner_product_ge_0.
       
  
Qed.


Local Open Scope R_scope.
Lemma Vector_Mix_State{n:nat} : forall (x: Vector (n)),
WF_Matrix x-> x <> Zero->
Mixed_State_aux (x × (x) †).
Proof. intros. assert(x= ( (norm x))%R .* ( (R1 / ( (norm x)))%R .* x )).
          rewrite Mscale_assoc. rewrite Rdiv_unfold.
          rewrite Rmult_1_l. rewrite Cmult_comm. 
          rewrite RtoC_mult. 
          rewrite Rinv_l.
          rewrite Mscale_1_l. reflexivity.
          unfold not. intros.
          apply norm_zero_iff_zero in H1. rewrite H1 in H0.
          destruct H0. reflexivity. assumption.
          rewrite H1. rewrite Mscale_mult_dist_l.
          rewrite Mscale_adj.   rewrite Mscale_mult_dist_r.
          remember ( (norm x)). rewrite Mscale_assoc.
          rewrite Cconj_R. 
          rewrite RtoC_mult. 
          apply Pure_S_aux. 
          assert(0<=r). rewrite Heqr.
          apply norm_ge_0 . assert(0<r).   destruct H2.  
          assumption. rewrite Heqr in H2. 
          symmetry in H2.
          apply norm_zero_iff_zero in H2. rewrite H2 in H0.
          destruct H0. reflexivity.  
          assumption. apply Rmult_gt_0_compat.
          assumption. assumption.    
          unfold Pure_State. exists (((R1 / r)%R .* x)).
          split. unfold Pure_State_Vector. split. apply WF_scale.
          assumption.
           rewrite Mscale_adj. rewrite Mscale_mult_dist_r.
          rewrite Cconj_R. rewrite Mscale_mult_dist_l.
          rewrite inner_eq. 
          rewrite Heqr.  
          rewrite Rdiv_unfold. rewrite Rmult_1_l.
          repeat rewrite Mscale_assoc. 
          repeat rewrite RtoC_mult. 
          rewrite <-Rmult_assoc . 
          rewrite (Rmult_assoc  _ (/ norm x) _).
          assert((norm x<> 0)%R). 
          unfold not. intros.
          apply norm_zero_iff_zero in H2. rewrite H2 in H0.
          destruct H0. reflexivity. assumption.  
          rewrite Rinv_l. rewrite Rmult_1_r. 
          rewrite  Rinv_l. rewrite Mscale_1_l. reflexivity.
          assumption. assumption. assumption. reflexivity.
Qed.

Lemma mixed_super_aux : forall {m n} (M : Matrix m n) (ρ: Matrix n n), 
WF_Matrix M->
   Mixed_State_aux ρ ->
    (super M ρ) <> Zero ->
   Mixed_State_aux  (super M ρ).
  Proof.
  intros m n M ρ Hw H1 H2.
  induction H1.
  + unfold super. rewrite Mscale_mult_dist_r.
    rewrite Mscale_mult_dist_l.
    apply Mixed_State_scale_aux. 
    destruct H0. destruct H0. rewrite H1.
    rewrite Mmult_assoc. rewrite Mmult_assoc.
     rewrite <-(Mmult_assoc M ). rewrite <-Mmult_adjoint.
     apply Vector_Mix_State.
     destruct H0.  
     auto_wf. rewrite H1 in *. unfold super in H2.
    rewrite Mscale_mult_dist_r in H2.
    rewrite Mscale_mult_dist_l in H2.
    rewrite Mmult_assoc in H2. rewrite Mmult_assoc in H2.
    rewrite <-(Mmult_assoc M ) in H2 .
    rewrite <-Mmult_adjoint in H2.
    intro. rewrite H3 in H2. 
    rewrite Mmult_0_l in H2.
    rewrite Mscale_0_r in H2. destruct H2. reflexivity.
    assumption.
  + unfold  super in *.
    rewrite Mmult_plus_distr_l in *.
    rewrite Mmult_plus_distr_r in *.
    assert(M × ρ1 × (M) †  = Zero \/ M × ρ1 × (M) †  <> Zero).
    apply Classical_Prop.classic.
    assert(M × ρ2 × (M) †  = Zero \/ M × ρ2 × (M) †  <> Zero).
    apply Classical_Prop.classic.
    destruct H. rewrite H in *. destruct H0.
    rewrite H0 in *. 
    rewrite Mplus_0_l in *. destruct H2. reflexivity.
    rewrite Mplus_0_l. apply IHMixed_State_aux2.
    assumption. destruct H0.
    rewrite H0. rewrite Mplus_0_r. 
    apply IHMixed_State_aux1. assumption.
    apply Mix_S_aux; trivial.
    apply IHMixed_State_aux1. assumption.
    apply IHMixed_State_aux2. assumption.

Qed.


Local Open Scope nat_scope.
Lemma Mix_par_trace: forall s e l r (q:qstate s e),
s<=l/\l<=r/\r<=e->
WF_qstate q->
WF_qstate (PMpar_trace q l r).
Proof. intros. unfold WF_qstate in *.
      destruct H0.  split.
      apply Mixed_State_aux_to_Mix_State.
      split.  
      rewrite Ptrace_l_r'.
      remember ((fun i : nat =>
      big_sum
        (fun j : nat =>
         ⟨ i ∣_ (l - s) ⊗ I (2 ^ (r - l)) ⊗ ⟨ j ∣_ (e - r) × q
         × (∣ i ⟩_ (l - s) ⊗ I (2 ^ (r - l)) ⊗ ∣ j ⟩_ (e - r)))
        (2 ^ (e - r)))).
      
      assert(2 ^ (r - l) = 1 * 2 ^ (r - l) * 1).
      lia. rewrite <-H2.
      
      apply Mixed_State_aux_big_sum.
      apply Nat.pow_nonzero. lia. 
      intros.
      assert( m i = Zero \/ m i<> Zero).
      apply Classical_Prop.classic.
      destruct H4. right. assumption. 
      left.  rewrite Heqm. rewrite <-H2.
      apply Mixed_State_aux_big_sum.
      apply Nat.pow_nonzero. lia.
      intros. 
      remember (⟨ i ∣_ (l - s) ⊗ I (2 ^ (r - l)) ⊗ ⟨ i0 ∣_ (e - r)).
      remember ((∣ i ⟩_ (l - s) ⊗ I (2 ^ (r - l)) ⊗ ∣ i0 ⟩_ (e - r)) ).
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
         assert( m0 × q × (m0) † = Zero \/ m0 × q × (m0) † <> Zero).
         apply Classical_Prop.classic.
        destruct H7. right.  
        assumption.
        left. 
        assert(2 ^ (r - l) = 1 * 2 ^ (r - l) * 1).
        lia. rewrite <-H8.
        apply mixed_super_aux.
        rewrite Heqm0. auto_wf. 
        apply Mixed_State_aux_to_Mix_State.
        assert((2 ^ (e - s))= (2 ^ (l - s) * 2 ^ (r - l) * 2 ^ (e - r))).
        type_sovle'. destruct H9.
        assumption. unfold super. assumption.
        apply big_sum_not_0.
        intros. 
        rewrite Heqm in H4.
        assumption.
        apply big_sum_not_0.
        assert(PMpar_trace q l r = 
        big_sum m (2 ^ (l - s))).
        rewrite Ptrace_l_r'.
        rewrite Heqm. reflexivity.
        lia. 
        rewrite Nat.mul_1_l in H3.
        rewrite Nat.mul_1_r in H3.
        rewrite <-H3. 
        intro. 
        assert(Cmod (@trace (2^(r-l)) (PMpar_trace q l r)) = Cmod ((@trace (2^(r-l)) Zero))) .
        rewrite H4. reflexivity.
        rewrite Zero_trace in H5. 
        rewrite Ptrace_trace in H5. rewrite Cmod_0 in H5. 
        apply mixed_state_Cmod_1 in H0.
        rewrite H5 in H0. 
        lra. lia. 
        apply WF_Mixed. assumption. lia. 
      rewrite Ptrace_trace.
      apply mixed_state_Cmod_1. assumption.
      lia. apply WF_Mixed. assumption. lia.
Qed.

Local Open Scope nat_scope.
Lemma nat_eq_mod_div: forall a b c, a=b <-> 
(a / c = b/c) /\ (a mod c = b mod c) .
Proof. intros. intuition. 
       rewrite (Nat.div_mod_eq a c).
       rewrite (Nat.div_mod_eq b c).
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
      apply Nat.div_lt_upper_bound.
      apply Nat.pow_nonzero. lia. 
      assert(2 ^ (e - r) * 2 ^ (r - r') = 2^(e-r')).
      type_sovle'. rewrite H1. assumption.
     apply WF_adjoint.
     apply WF_vec.
     apply Nat.mod_bound_pos.
     lia. apply pow_gt_0.
      rewrite kron_assoc; auto_wf.
      f_equal; type_sovle'.
      apply Vec_kron.
      apply WF_vec. 
      apply Nat.div_lt_upper_bound.
      apply Nat.pow_nonzero. lia. 
      assert(2 ^ (e - r) * 2 ^ (r - r') = 2^(e-r')).
      type_sovle'. rewrite H1. assumption.
      
     apply WF_vec.   apply Nat.mod_bound_pos.
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


Lemma WF_PMpar_trace{s e:nat}: forall (q:qstate s e)  l r,
s<=l/\l<=r<=e->
@WF_Matrix (2^(e-s)) (2^(e-s)) q->
@WF_Matrix  (2^(r-l)) (2^(r-l)) (PMpar_trace q l r).
Proof. intros. unfold PMpar_trace. apply WF_PMRpar_trace. lia. 
      apply WF_PMLpar_trace. lia. assumption.
Qed. 


Lemma Vec_I: ((Vec 1 0)= I 1).
Proof. prep_matrix_equality. 
unfold Vec. unfold I.
destruct  x.
destruct y. simpl. reflexivity.
simpl. reflexivity. 
destruct y. simpl. reflexivity.
simpl.    assert((S x <? 1)=false).
rewrite Nat.ltb_ge. lia. rewrite H.
bdestruct (x=?y); simpl; reflexivity.
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


Lemma PMpar_trace_refl{s e:nat}: forall l r (q: qstate s e),
l=s/\r=e-> @WF_Matrix (2^(e-s)) (2^(e-s)) q->
PMpar_trace q l r=q.
Proof. intros. destruct H. subst.
       unfold PMpar_trace. 
       rewrite PMLpar_trace_refl; try reflexivity; try assumption.
       rewrite PMRpar_trace_refl; try reflexivity; assumption.
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



Fixpoint WF_Matrix_dstate { s e:nat} (mu: list (cstate * qstate s e)) :=
  match mu with 
  |nil => True 
  | (c,q)::mu' => and (@WF_Matrix (2^(e-s)) (2^(e-s)) q)  (WF_Matrix_dstate mu') 
  end.


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