Require Import Reals.
Require Import Strings.String.
Require Import Lists.List.
Require Import Coquelicot.Complex.
Require Import Coq.Init.Datatypes.
From Coq Require Import Bool.Bool.
From Coq Require Import Lia.
From Coq Require Import Init.Nat.


Require Import Psatz.
Require Import Reals.
From Quan Require Export VecSet.
From Quan Require Export Matrix.
From Quan Require Export Quantum.
From Quan Require Export Complex.


Definition Vec(n:nat) (i:nat): Vector n := 
    fun x y => match x, y with 
            | j, 0 => if j=?i then C1 else C0
            | _, _ => C0
            end.

Notation "∣ i ⟩_ n " := (Vec (2^n) i) (at level 0) :matrix_scope.
Notation "⟨ i ∣_ n " := (adjoint (Vec (2^n) i)) (at level 0) :matrix_scope.

Local Open Scope nat_scope.
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

Lemma Lt_n_i: forall n i , i<n -> i<?n=true.
Proof. 
induction n; destruct i. lia. lia.  intuition.
intros.
simpl. intros. apply IHn. lia. 
Qed.

Lemma  Vec1: forall (n i x:nat), x = i -> Vec n i x 0= C1.
Proof. intros. simpl Vec. bdestruct (x=?i).
reflexivity. lia.   
Qed.

Lemma  Vec0: forall (n i x:nat), x <> i -> Vec n i x 0= C0.
  Proof. intros. simpl Vec. bdestruct (x=?i). unfold not in H. intuition.
  reflexivity.   
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
       rewrite Vec1. rewrite Cmult_1_r.
       reflexivity. reflexivity.
       intros. unfold scale.
       rewrite Vec0. rewrite Cmult_0_r.
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


Definition c_to_Vector1 (c: C): Vector 1 :=  c .* I 1.
Coercion c_to_Vector1 : C >-> Vector .

Lemma matrix_0_0:forall c, (c .* I 1) 0 0= c.
Proof. intros. rewrite Mscale_1_r.  simpl. reflexivity. Qed.

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
big_sum (fun i:nat => (Vec n i)† × M × (Vec n i)) n  = (trace M).
       Proof. intros. remember ((fun i : nat => (M i i) .* I 1)).
       rewrite (big_sum_eq_bounded _ m _). 
       rewrite Heqm. unfold trace. unfold c_to_Vector1.
       rewrite big_sum_Mscale_r.  reflexivity. 
       intros. rewrite Vec_inner_M. rewrite Heqm. reflexivity. 
       apply H. assumption.
       Qed.

Lemma Vec_inner_0{n:nat}:forall i j :nat,
i<>j-> i<(2^n) -> j<(2^n)->
(⟨ i ∣_ (n) × ∣ j ⟩_ (n))= C0.
Proof. intros. rewrite Vec_inner_l. simpl.
       rewrite Neq_i_j. reflexivity.
       assumption. auto_wf. assumption. 
Qed.

Lemma Vec_inner_1: forall i n,
(i<(2^n))%nat->
⟨ i ∣_ (n) × ∣ i ⟩_ (n) = C1.
Proof. intros. rewrite Vec_inner_l. simpl.
       bdestruct (i=?i). unfold c_to_Vector1.  rewrite Mscale_1_l.
       reflexivity. lia. auto_wf. assumption. 
Qed.

Local Open Scope nat_scope.
Search (Nat.div).
Lemma base_3:forall n x,
x>=n-> x< 2*n-> (x / n) = 1.
Proof. intros.  
       symmetry. 
       apply (Nat.div_unique x n 1 (x-n)).
       apply Nat.lt_le_trans with (2 * n - n).
       simpl. lia. simpl. lia. lia.
Qed.

Lemma base_4:forall n x,
x>=n-> x< 2*n->
(x mod n) = x - n .
Proof. intros. symmetry. 
       apply (Nat.mod_unique x n 1 (x-n)).
        lia. lia.   
Qed.

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


Local Open Scope C_scope.
Lemma fst_plus: forall (c1 c2: C),
 fst(c1 + c2)= (fst c1 + fst c2)%R.
Proof. intros. destruct c1. destruct c2.
      simpl. reflexivity.
Qed.

Lemma fst_mult: forall (r: R) (c: C),
 fst(r * c)= (r * fst c)%R.
Proof. intros. destruct c. 
      simpl. rewrite Rmult_0_l.
      rewrite Rminus_0_r. reflexivity.
  
Qed.


Lemma trace_mult: forall (n:nat) (A B :Square n),
trace(Mmult A B) =trace (Mmult B A).
Proof. intros. unfold trace. unfold Mmult. 
       rewrite big_sum_swap_order. 
       apply big_sum_eq. apply functional_extensionality.
       intros. apply big_sum_eq. apply functional_extensionality.
       intros.
apply Cmult_comm. 
Qed.

Lemma trace_mult': forall (m n:nat) (A:Matrix m n) (B:Matrix n m),
  trace(Mmult A B) =trace (Mmult B A).
  Proof. intros. unfold trace. unfold Mmult. 
         rewrite big_sum_swap_order. 
         apply big_sum_eq. apply functional_extensionality.
         intros. apply big_sum_eq. apply functional_extensionality.
         intros.
  apply Cmult_comm. 
  Qed.


  Lemma trace_mult_Unitary{n:nat}: forall (A B:Square n) ,
 WF_Unitary A -> WF_Matrix B-> trace B=trace (A × B ×  A†).
Proof. intros. rewrite trace_mult. rewrite<-Mmult_assoc. 
destruct H. rewrite H1. rewrite Mmult_1_l. reflexivity.
assumption. 
Qed.


  Lemma inner_trace: forall n (x: Vector (n)),
WF_Matrix x->
 ((norm x) * (norm x))%R = (fst (trace (x × x †))).
Proof. intros. unfold norm. rewrite sqrt_sqrt. 
f_equal. unfold inner_product. rewrite trace_mult'.  unfold trace.
simpl. rewrite Cplus_0_l.  reflexivity. apply inner_product_ge_0.
Qed. 

Lemma trace_vector: forall (m n:Vector 1), 
 (trace (m × n)) = (trace m) * (trace n).
Proof. intros. unfold trace.  unfold Mmult. 
       simpl. repeat rewrite Cplus_0_l.
       reflexivity.
Qed.



Lemma Zero_opp{ m n:nat}: forall m n (A B:Matrix m n),
A .+ (Mopp A) = Zero.
Proof. intros. prep_matrix_equality.
       unfold Mplus. unfold Mopp.
       unfold scale. rewrite<-Copp_mult_distr_l.
       rewrite Cmult_1_l.
       rewrite Cplus_opp_r. reflexivity.
Qed.

Lemma scale_Zero{m n:nat}: forall c (M:Matrix m n),
c .* M = Zero ->
c<>C0 ->
M = Zero.
Proof. intros. unfold scale in H. 
       unfold Zero in *.
      prep_matrix_equality.
      assert((fun x y : nat => c * M x y) x y=
      c * (M x y)). reflexivity.
      assert(c * (M x y)= C0).
      rewrite H in H1. symmetry. assumption. 
      apply Cmult_integral in H2.
      destruct H2. rewrite H2 in H0. destruct H0.
      reflexivity. assumption.
Qed.


Lemma big_sum_Cconj: forall (f: nat->C) n,
Cconj (big_sum f n)=big_sum (fun x=> Cconj (f x) ) n.
Proof. induction n; simpl. rewrite Cconj_0.
       reflexivity. rewrite Cconj_plus_distr.
       rewrite IHn. reflexivity.
  
Qed.


Lemma  trace_adj{  n:nat}:forall ( A: Square n),
trace (A)=Cconj (trace (adjoint A)) .
Proof. intros.   unfold trace. unfold adjoint.
rewrite big_sum_Cconj. apply big_sum_eq_bounded. intros.
      rewrite Cconj_involutive. reflexivity.
Qed.

Lemma inner_trace'{n:nat}: forall (x x0: Vector n), 
trace ((x0) † × x)= inner_product x0 x.
Proof. intros. unfold trace. unfold inner_product.
      simpl. rewrite Cplus_0_l. reflexivity. 
Qed.


Lemma trace_vector_mult{n}: forall (x x0:Vector n),
Cmod (trace (x × ((x) † × x0 × (x0) †)))=
(Cmod ⟨ x0, x ⟩ * Cmod ⟨ x0, x ⟩)%R.
Proof. intros.  rewrite trace_mult'. 
rewrite Mmult_assoc.
rewrite trace_vector.
rewrite trace_mult'.
rewrite trace_adj.
rewrite Cmod_mult.
rewrite  Cmod_Cconj.
rewrite Mmult_adjoint.
rewrite adjoint_involutive.
rewrite trace_mult'.
rewrite inner_trace'. reflexivity.
Qed.



Lemma  trace_I: trace (I 1) = C1.
Proof. unfold trace. simpl.  
      unfold I. simpl. rewrite Cplus_0_l.
      reflexivity.
       
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
      unfold adjoint. rewrite Vec1. 
      rewrite Cconj_R.
      rewrite Cmult_1_l. reflexivity.
      assumption. intuition.
      unfold adjoint. rewrite Vec0. 
      rewrite Cconj_R.
      rewrite Cmult_0_r. reflexivity.
      assumption. simpl. 
      rewrite Cmult_0_l. reflexivity.
Qed.

Lemma  big_sum_I: forall n,
big_sum (fun i : nat => ∣ i ⟩_ n × ⟨ i ∣_ n) (2 ^ n)= I (2^n).
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


Local Open Scope nat_scope.
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