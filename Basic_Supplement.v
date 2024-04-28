Require Import Reals.
Require Import Coquelicot.Complex.
Require Import Strings.String.
Require Import Lists.List.
Require Import Coq.Init.Datatypes.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import Lia.



From Quan Require Import Matrix.
From Quan Require Import Quantum.



Delimit Scope C_scope with C.
Local Open Scope C_scope.

(* Require Import Coq.Structures.OrderedTypeEx.
Require Import Coq.MSets.MSetWeakList.
Require Import Coq.FSets.FSetList.

Module SSet := FSetList.Make String_as_OT.

Definition CSet:=SSet.t.

Module NSet := FSetList.Make Nat_as_OT.
Definition QSet:=NSet.t.

Local Open Scope nat_scope.
(* Inductive Qsys:Type := 
|Q_unit (n m:nat): Qsys. *)


(* 下标从1开始*)
Fixpoint Qsys_to_Set (n m :nat)(l:QSet): QSet:=
  if n<?m then 
 (match m with 
  | O => l 
  | S m' => (NSet.add m' (Qsys_to_Set n (m') l)) 
  end) 
  else l . *)
   


Fixpoint ismemberN (a : nat) (L : list nat) : bool :=
match L with
| nil => false
| x :: t => if a=?x then true else ismemberN a t
end.

Fixpoint interN (L1 L2 : list nat) : list nat :=
match L1 with
| nil => nil
| x :: t => if ismemberN x L2 then  x :: interN t L2
            else interN t L2
end.


Lemma interN_nil: forall l:list nat, interN l nil = nil.
Proof.
  induction l as [|l IHl].
  -simpl. reflexivity.
  -simpl. auto.
Qed.

Local Open Scope string_scope.
Fixpoint ismemberS (a : string) (L : list string) : bool :=
match L with
| nil => false
| x :: t => if a=?x then true else ismemberS a t
end.

Fixpoint interS (L1 L2 : list string) : list string :=
match L1 with
| nil => nil
| x :: t => if ismemberS x L2 then  x :: interS t L2
            else interS t L2
end.

Lemma interS_nil: forall l:list string, interS l nil = nil.
Proof.
  induction l as [|l IHl].
  -simpl. reflexivity.
  -simpl. auto.
Qed.


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


Definition PMRpar_trace'{n:nat} (M: Square (2^n)) (l:nat) : Square  (2^(n-l)):=
  let f:= (fun i=>  let v_i:= (Vec (2^l) i) in  
  ((v_i†) ⊗ (I (2^(n-l)))) ×  M ×  ((v_i) ⊗ (I (2^(n-l))))) in
  big_sum  f (2^l).

Definition PMlpar_trace'{n:nat} (M: Square (2^n)) (l:nat) : Square  (2^(n-l)):=
    let f:= (fun i=>  let v_i:= (Vec (2^l) i) in  
    ((I (2^(n-l)))  ⊗ (v_i†)   ×  M × ((I (2^(n-l))) ⊗ v_i))) in
    big_sum  f (2^l).
    

(* Fixpoint PMRpar_trace{n:nat} (M: Square (2^n)) (i:nat): Square  (2^(n-i)):=
  match i with
  |0 => M 
  |S i'=> PMRpar_trace (PMRpar_trace_aux M) i' 
  end. *)

Definition PMLpar_trace_aux {n:nat} (M: Square (2^n)) : Square (2^(n-1)):=
     (((I (2^(n-1)))  ⊗ ⟨0∣)  ×  M × ((I (2^(n-1))) ⊗ ∣0⟩)) .+  (((I (2^(n-1))) ⊗ ⟨1∣ ) × M ×  ((I (2^(n-1))) ⊗ ∣1⟩)).
  
(* Fixpoint PMLpar_trace{n:nat} (M: Square (2^n)) (i:nat): Square  (2^(n-i)):=
    match i with
    |0 => M 
    |S i'=> PMLpar_trace (PMLpar_trace_aux M) i' 
    end. *)

Definition vector_to_C (c: C): Vector 1 :=  c .* I 1.

Coercion vector_to_C : C >-> Vector .

(* Local Open Scope R_scope.
Lemma Rmult_1_l : forall r:R, r * 0 = r.
Proof. rewrite Rmult_1_l *)
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
Lemma inner3: forall (n i:nat) (V:Vector n), WF_Matrix V->0 <= i< n -> V† × Vec n i=(V i 0)^* .* I 1.
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
Lemma inner4: forall (n i:nat) (V:Vector n), WF_Matrix V -> 0 <= i< n -> (Vec n i)† ×  V =(V i 0) .* I 1.
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
  i<n 
  -> (Vec n i)† × M × (Vec n i) = (M i i) .* I 1.
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

Lemma big_sum_kron_l : forall (n1 n2 m1 m2:nat) (M: Matrix n1 n2) (f:nat-> Matrix m1 m2) n', 
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
Qed.

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
-> PMlpar_trace' M1 l= (@trace (2^(l)) M3) .*  M2.
Proof. intros.  unfold PMlpar_trace'. rewrite H2.
assert(forall i:nat, i< (2^(l)) -> (I (2 ^ (n - l)) ⊗ (Vec (2^l) i) †) × (M2 ⊗ M3)
× (I (2 ^ (n - l)) ⊗ Vec (2^l) i) =(M2) 
⊗ ((M3 i i) .* I 1)).
intros. repeat rewrite kron_mixed_product.
rewrite Mmult_1_l. rewrite Mmult_1_r. rewrite inner'.
reflexivity. assumption. assumption.
assumption. assumption. apply big_sum_eq_bounded in H3.
rewrite H3. rewrite <- big_sum_kron_l. 
rewrite <- big_sum_Mscale_r.
 unfold trace. rewrite Mscale_kron_dist_r.
 rewrite kron_1_r. reflexivity.
Qed.

Lemma trace''{n:nat} : forall l (M1:Square (2^n)) (M2:Square (2^(l))) (M3:Square (2^(n-l))),
WF_Matrix M1-> WF_Matrix M2-> WF_Matrix M3->
M1= M2⊗ M3
-> PMRpar_trace' M1 l= (@trace (2^(l)) M2) .*  M3.
Proof. intros.  unfold PMRpar_trace'. rewrite H2.
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
rewrite H3. rewrite <- big_sum_kron_r. 
rewrite <- big_sum_Mscale_r. 
 unfold trace. rewrite Mscale_kron_dist_l.
 rewrite kron_1_l. reflexivity. assumption.
 Qed.

 Lemma big_sum_Mscale_l : forall m (c:C) (f:nat-> Square m)  n, 
    (scale c (big_sum f n)) = (big_sum (fun x =>  scale c (f x)) n).
   Proof.
   intros.
   induction n; simpl. 
   + apply Mscale_0_r.
   + rewrite <- IHn.
   rewrite Mscale_plus_distr_r.
   reflexivity.
   Qed.
 
   
    Lemma R_trace_scale: forall n l c (M:Square (2^n)) , 
    (scale c (@PMRpar_trace' n M l))=
   (@PMRpar_trace' n ( scale c  M) l ) .
   Proof. intros. unfold PMRpar_trace'.
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
   rewrite <- big_sum_Mscale_l. reflexivity. 
  Qed.


  Locate plus_assoc.
(*l是左边的维数， m是右边的维数*)
Definition PMpar_trace{n:nat} (M: Square (2^n)) (l:nat) (m:nat):=
   PMRpar_trace' (PMlpar_trace' M m) l.

Local Open Scope nat_scope.

Lemma  minus_S: forall (n l:nat), n- (S l)=n-l-1 .
Proof. induction n. reflexivity.
      induction l. 
 rewrite <-minus_n_O.
 reflexivity.
simpl. apply IHn.
Qed.

Lemma  minus_assoc: forall (n l m: nat), n-l-m=n-m-l .
Proof.
induction n.
reflexivity.
induction l. 
rewrite <-minus_n_O.
intros. 
rewrite <- (minus_n_O (S n - m)). reflexivity.
induction m.
rewrite <-minus_n_O.
rewrite <- minus_n_O. reflexivity.
simpl.
rewrite minus_S. rewrite (minus_S (n-m) (l)).
assert(n-l-m=n-m-l).
apply IHn. rewrite H. reflexivity.
Qed.

(* Local Open Scope R_scope.
Lemma minus_plus_assoc: forall (n l m:R), n+(l-m)=n+l-m.
Proof. induction n. 
       intros. reflexivity.
       intros. simpl plus. 
       rewrite IHn.  *)

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
        rewrite <- pow_add_r.
        Local Open Scope nat_scope.
        assert ((l + (n - l - m))=(n-m)).
        assert((n-l-m)=(n-m-l)).
        apply minus_assoc.
        rewrite H6.
        rewrite le_plus_minus_r.
        reflexivity. assumption.
        rewrite H6. reflexivity.
        rewrite <- pow_add_r.
        Local Open Scope nat_scope.
        assert ((l + (n - l - m))=(n-m)).
        assert((n-l-m)=(n-m-l)).
        apply minus_assoc.
        rewrite H6.
        rewrite le_plus_minus_r.
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
        rewrite <- pow_add_r.
        Local Open Scope nat_scope.
        assert ((l + (n - l - m))=(n-m)).
        assert((n-l-m)=(n-m-l)).
        apply minus_assoc.
        rewrite H6.
        rewrite le_plus_minus_r.
        reflexivity. assumption.
        rewrite H6. reflexivity.
        rewrite <- pow_add_r.
        Local Open Scope nat_scope.
        assert ((l + (n - l - m))=(n-m)).
        assert((n-l-m)=(n-m-l)).
        apply minus_assoc.
        rewrite H6.
        rewrite le_plus_minus_r.
        reflexivity. assumption.
        rewrite H6. reflexivity.
        assumption. assumption. assumption.
        reflexivity.
Qed.



