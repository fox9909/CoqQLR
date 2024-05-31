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

(*---------------------------Partial Trace--------------------------*)

Local Open Scope matrix_scope.
(*右*)
Definition PMRpar_trace_aux {n:nat} (M: Square (2^n)) : Square (2^(n-1)):=
  ⟨0∣ ⊗ (I (2^(n-1))) ×  M ×  ∣0⟩ ⊗ (I (2^(n-1))) .+ ⟨1∣ ⊗ (I (2^(n-1))) × M × ∣1⟩ ⊗ (I (2^(n-1))).

Definition PMLpar_trace_aux {n:nat} (M: Square (2^n)) : Square (2^(n-1)):=
(((I (2^(n-1)))  ⊗ ⟨0∣)  ×  M × ((I (2^(n-1))) ⊗ ∣0⟩)) .+  (((I (2^(n-1))) ⊗ ⟨1∣ ) × M ×  ((I (2^(n-1))) ⊗ ∣1⟩)).

Definition PMRpar_trace{n:nat} (M: Square (2^n)) (l:nat) : Square  (2^(n-l)):=
  let f:= (fun i=>  let v_i:= (Vec (2^l) i) in  
  ((v_i†) ⊗ (I (2^(n-l)))) ×  M ×  ((v_i) ⊗ (I (2^(n-l))))) in
  big_sum  f (2^l).

Definition PMLpar_trace{n:nat} (M: Square (2^n)) (l:nat) : Square  (2^(n-l)):=
    let f:= (fun i=>  let v_i:= (Vec (2^l) i) in  
    ((I (2^(n-l)))  ⊗ (v_i†)   ×  M × ((I (2^(n-l))) ⊗ v_i))) in
    big_sum  f (2^l).

Definition vector_to_C (c: C): Vector 1 :=  c .* I 1.

Coercion vector_to_C : C >-> Vector .

Lemma matrix_0_0:forall c, (c .* I 1) 0 0= c.
Proof. intros. rewrite Mscale_1_r.  simpl. reflexivity. Qed.

 Lemma inner1{n:nat}: forall (M: Square 2), 
WF_Matrix M ->⟨0∣ × M × ∣0⟩ = (M 0 0) .* I 1.
Proof . intros. prep_matrix_equality.
        bdestruct (x <? 2); bdestruct (y <? 2) ;
        assert(H': WF_Matrix (M 0 0 .* I 1));
        try apply WF_scale; try apply WF_I1;
        unfold Mmult; 
        destruct x; destruct y; simpl; unfold "⟨0∣";
        unfold qubit0; rewrite Cmult_0_r;
        repeat rewrite Cplus_0_l;
        repeat rewrite Cplus_0_r;
        unfold "^*"; simpl; rewrite Ropp_0;
        repeat rewrite Cmult_1_r;
        try rewrite Cmult_1_l;
        rewrite Cmult_0_l;
        try rewrite Cplus_0_r;
        simpl; try rewrite matrix_0_0; try 
        reflexivity; try rewrite Cmult_0_r;
        try rewrite Cplus_0_l; try rewrite Cmult_0_l;
        unfold WF_Matrix in H;
        rewrite H'; try reflexivity. try right. try intuition.
        left. intuition. right. intuition. simpl.
        right. intuition.
        left. intuition.
        right. intuition.
        left. intuition.
        left. intuition.
        left. intuition.
        right. intuition.
        left. intuition. 
        left. intuition.
      Qed.

      
Lemma inner2{n:nat}: forall (M: Square 2), 
      WF_Matrix M ->⟨1∣ × M × ∣1⟩ = (M 1 1) .* I 1.
      Proof . intros. prep_matrix_equality.
              bdestruct (x <? 2); bdestruct (y <? 2) ;
              assert(H': WF_Matrix (M 1 1 .* I 1));
              try apply WF_scale; try apply WF_I1;
              unfold Mmult; 
              destruct x; destruct y; simpl; unfold "⟨0∣";
              unfold qubit0; rewrite Cmult_0_r;
              repeat rewrite Cplus_0_l;
              repeat rewrite Cplus_0_r;
              unfold "^*"; simpl; rewrite Ropp_0;
              repeat rewrite Cmult_1_r;
              try rewrite Cmult_1_l;
              rewrite Cmult_0_l;
              try rewrite Cplus_0_r;
              simpl; try rewrite matrix_0_0; try 
              reflexivity; try rewrite Cmult_0_r;
              try rewrite Cplus_0_l; try rewrite Cmult_0_l;
              unfold WF_Matrix in H;  try rewrite H';
              try reflexivity. right. intuition.
              left. intuition. right. intuition. simpl.
              right. intuition.
              left. intuition.
              right. intuition.
              left. intuition.
              left. intuition.
              left. intuition.
              right. intuition.
              left. intuition. 
              left. intuition.
            Qed.

Require Import Coq.Structures.OrderedTypeEx.
Lemma  big_sum_i_0: forall (f:nat-> C) (n i:nat), 
(forall y, y <> i -> f y = C0)-> (0 <= i< n -> big_sum f n= f i).
Proof. intros. induction n. intuition.
      simpl.  bdestruct (i=?n). rewrite H1 in H. 
      assert (forall y : nat,
      y < n -> f y = C0). intros. assert (y<> n). apply (Nat_as_OT.lt_not_eq).
      apply H2. apply H. apply H3. 
      rewrite big_sum_0_bounded. rewrite <- H1. rewrite Cplus_0_l. reflexivity.
      assumption. rewrite H. rewrite Cplus_0_r. apply IHn. intuition.
      intuition.
Qed.


Local Open Scope C_scope.
Lemma inner3: forall (n i:nat) (V:Vector n),
 WF_Matrix V->0 <= i< n -> V† × Vec n i=(V i 0)^* .* I 1.
Proof. intros.   prep_matrix_equality.  
    bdestruct (y=?0).  unfold Mmult. rewrite H1. 
      assert( (Σ
      (fun y0 : nat =>
       ((V) † x y0 * Vec n i y0 0)%C)
      n )= ((V) † x  i) * (Vec n i i 0)%C).
      try rewrite (big_sum_i_0 (fun y0 : nat =>
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
      


Local Open Scope C_scope.
Lemma inner4: forall (n i:nat) (V:Vector n), 
WF_Matrix V -> 0 <= i< n -> (Vec n i)† ×  V =(V i 0) .* I 1.
Proof. intros. assert(V† × Vec n i=(V i 0)^* .* I 1). 
apply inner3. assumption. assumption.
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

Lemma inner'{n:nat}: forall (M: Square n) (i:nat), 
  WF_Matrix M-> 
  i<n -> (Vec n i)† × M × (Vec n i) = (M i i) .* I 1.
Proof . intros. prep_matrix_equality.
    assert ((Vec n i) † × M = (M † × (Vec n i) )†).
    rewrite Mmult_adjoint. rewrite adjoint_involutive.
    reflexivity. rewrite H1.
    rewrite inner3.  
    unfold Mmult. 
    assert(Σ
    (fun y0 : nat =>
      (M) † i y0 * Vec n i y0 0)
    n= (M) † i i * Vec n i i 0 ).
      apply (big_sum_i_0 (fun y0 : nat =>
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

         
Lemma kron1{n:nat} : forall (M: Square 2), 
WF_Matrix M ->
⟨0∣ × M × ∣0⟩ .+ ⟨1∣ × M × ∣1⟩ = (@trace 2 M) .* I 1.
Proof. intros.    prep_matrix_equality.
      unfold trace. simpl. 
      rewrite (@inner1 2 M).
      rewrite (@inner2 2 M).
      destruct x ; destruct y;
      assert(H': WF_Matrix (M 1 1 .* I 1));
      try apply WF_scale; try apply WF_I1;
      assert(H'': WF_Matrix (M 0 0 .* I 1));
      try apply WF_scale; try apply WF_I1;
      rewrite Cplus_0_l;
      unfold ".+"; repeat rewrite matrix_0_0;
      try rewrite Mscale_plus_distr_l;
      try reflexivity;
      rewrite H'; try rewrite Cplus_0_r;
      try rewrite H''.
      assumption. assumption.
Qed.


Lemma trace1{n:nat} : forall (A:Square (2^n)) (B:Square (2^(n-1))) (C:Square 2),
WF_Matrix A-> WF_Matrix B-> WF_Matrix C->
A= B ⊗ C
-> PMLpar_trace_aux A = (@trace 2 C) .*  B.
Proof.  intros.  unfold PMLpar_trace_aux. rewrite  H2.
       repeat rewrite kron_mixed_product.
       rewrite Mmult_1_l. rewrite Mmult_1_r.  
       rewrite <- kron_plus_distr_l.   
       rewrite (@kron1 2 C). rewrite Mscale_kron_dist_r.
       rewrite kron_1_r. reflexivity. assumption. assumption. assumption.
Qed.

(* Lemma big_sum_kron_l : forall (n1 n2 m1 m2:nat) (M: Matrix n1 n2) (f:nat-> Matrix m1 m2) n', 
    M ⊗ big_sum f n' = big_sum (fun x => M ⊗ f x) n'.
Proof. intros. induction n'.
       simpl. rewrite kron_0_r. reflexivity.
       simpl. rewrite kron_plus_distr_l.
       rewrite IHn'. reflexivity.
Qed.

Lemma big_sum_kron_r : forall (n1 n2 m1 m2:nat) (M: Matrix n1 n2) (f:nat-> Matrix m1 m2) n', 
    big_sum f n'  ⊗  M = big_sum (fun x => f x ⊗ M) n'.
Proof. intros. induction n'.
       simpl. rewrite kron_0_l. reflexivity.
       simpl. rewrite kron_plus_distr_r.
       rewrite IHn'. reflexivity.
Qed. *)

Lemma big_sum_Mscale_r : forall (n : nat) (M: Square n) (f:nat->C) n', 
    big_sum f n' .*  M = big_sum (fun x => f x .* M) n'.
Proof. intros. induction n'.
       simpl. rewrite Mscale_0_l. reflexivity.
       simpl. rewrite Mscale_plus_distr_l.
       rewrite IHn'. reflexivity.
Qed.

Lemma trace'{n:nat} : forall l (M1:Square (2^n)) (M2:Square (2^(n-l))) (M3:Square (2^(l))),
WF_Matrix M1-> WF_Matrix M2-> WF_Matrix M3->
M1= M2⊗ M3
-> PMLpar_trace M1 l= (@trace (2^(l)) M3) .*  M2.
Proof. intros.  unfold PMLpar_trace. rewrite H2.
assert(forall i:nat, i< (2^(l)) -> (I (2 ^ (n - l)) ⊗ (Vec (2^l) i) †) × (M2 ⊗ M3)
× (I (2 ^ (n - l)) ⊗ Vec (2^l) i) =(M2) 
⊗ ((M3 i i) .* I 1)).
intros. repeat rewrite kron_mixed_product.
rewrite Mmult_1_l. rewrite Mmult_1_r. rewrite inner'.
reflexivity. assumption. assumption.
assumption. assumption. apply big_sum_eq_bounded in H3.
rewrite H3. rewrite <- kron_Msum_distr_l. 
rewrite <- big_sum_Mscale_r.
 unfold trace. rewrite Mscale_kron_dist_r.
 rewrite kron_1_r. reflexivity.
Qed.

Lemma trace''{n:nat} : forall l (M1:Square (2^n)) (M2:Square (2^(l))) (M3:Square (2^(n-l))),
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
rewrite Mmult_1_l. rewrite Mmult_1_r. rewrite inner'.
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
Definition PMpar_trace{n:nat} (M: Square (2^n)) (l:nat) (m:nat):=
   PMRpar_trace (PMLpar_trace M m) l.

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


 Lemma trace'''{n:nat} : forall l m (M1:Square (2^n)) (M2:Square (2^(l))) (M3:Square (2^(n-l-m))) (M4: (Square (2^m)))(H1:m<=n) (H2:l<=n-m),
 WF_Matrix M1-> WF_Matrix M2-> WF_Matrix M3-> WF_Matrix M4->
 M1= M2 ⊗ M3 ⊗ M4
 -> PMpar_trace M1 l m= (@trace (2^(l)) M2) * (@trace (2^(m)) M4).*  M3.
 Proof. intros. unfold PMpar_trace.
      rewrite H5.  
        rewrite (trace' m _ (M2 ⊗ M3) M4 ).
        rewrite <- R_trace_scale.
        rewrite (trace'' l _ M2 M3 ).
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

Notation "∣ i ⟩_ n " := (Vec (2^n) i) (at level 0) :matrix_scope.
Notation "⟨ i ∣_ n " := (adjoint (Vec (2^n) i)) (at level 0) :matrix_scope.
Check ∣ 2 ⟩_ 4.


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

#[export]Hint Resolve WF_vec: wf_db.

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


Lemma  trace_base:forall (n:nat) (M:Square n),
WF_Matrix M->
big_sum (fun i:nat => (Vec n i)† × M × (Vec n i)) n  = (trace M) .* I 1.
       Proof. intros. remember ((fun i : nat => (M i i) .* I 1)).
       rewrite (big_sum_eq_bounded _ m _). 
       rewrite Heqm. unfold trace. 
       rewrite big_sum_Mscale_r.  reflexivity. 
       intros. rewrite inner'. rewrite Heqm. reflexivity. 
       apply H. assumption.
       Qed.


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
    

