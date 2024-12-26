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

Definition Base_vec(n:nat) (i:nat): Vector n := 
    fun x y => match x, y with 
            | j, 0 => if j=?i then C1 else C0
            | _, _ => C0
            end.

Notation "∣ i ⟩_ n " := (Base_vec n i) (at level 0) :matrix_scope.
Notation "⟨ i ∣_ n " := (adjoint (Base_vec n i)) (at level 0) :matrix_scope.

Local Open Scope nat_scope.
Lemma WF_base: forall n i, i < n -> WF_Matrix (∣ i ⟩_ n) .
Proof. intros. 
     unfold WF_Matrix. intros.
     destruct i. intuition. intuition.
     intuition. unfold Base_vec. destruct y. bdestruct(x=?0). intuition.
     reflexivity. reflexivity.   unfold Base_vec. destruct y. intuition.
     reflexivity. unfold Base_vec. destruct y. bdestruct(x=?S i). intuition.
     reflexivity. reflexivity.
Qed.
#[export]Hint Resolve WF_base: wf_db.

Lemma base_qubit0: Base_vec 2 0= qubit0. Proof. unfold Base_vec. solve_matrix. Qed. 
Lemma  base_qubit1: Base_vec 2 1= qubit1. Proof. unfold Base_vec. solve_matrix. Qed. 
#[export] Hint Rewrite @norm_scale @base_qubit0 @base_qubit1  using (auto 100 with wf_db) : M_db.


Lemma base_I: ((∣ 0 ⟩_ 1)= I 1).
Proof. prep_matrix_equality. 
unfold Base_vec. unfold I.
destruct  x.
destruct y. simpl. reflexivity.
simpl. reflexivity. 
destruct y. simpl. reflexivity.
simpl.    assert((S x <? 1)=false).
rewrite Nat.ltb_ge. lia. rewrite H.
bdestruct (x=?y); simpl; reflexivity.
Qed.

Lemma Lt_n_i: forall n i , i<n -> i<?n=true.
Proof. induction n; destruct i. lia. lia.  intuition.
intros. simpl. intros. apply IHn. lia. 
Qed.

Lemma  base1: forall (n i x:nat), x = i -> ∣ i ⟩_ n x 0= C1.
Proof. intros. simpl Base_vec. bdestruct (x=?i).
reflexivity. lia.   
Qed.

Lemma  base0: forall (n i x:nat), x <> i -> ∣ i ⟩_ n x 0= C0.
Proof. intros. simpl Base_vec. bdestruct (x=?i). unfold not in H. intuition.
reflexivity.   
Qed.

Lemma base_decom{ n:nat}: forall (v:Vector n),
WF_Matrix v ->
v= big_sum (fun i:nat=> (v i 0) .* (∣ i ⟩_ n)) n.
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
       rewrite base1. rewrite Cmult_1_r.
       reflexivity. reflexivity.
       intros. unfold scale.
       rewrite base0. rewrite Cmult_0_r.
       reflexivity. assumption.
       rewrite H.
       rewrite Msum_Csum.
       rewrite big_sum_0_bounded.
       reflexivity.
       intros.
       unfold scale.
       assert(WF_Matrix (Base_vec n x0)).
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
       assert(WF_Matrix (Base_vec n x0)).
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

Lemma base_e_i: forall n i, i < n -> ∣ i ⟩_ n = @e_i n i.
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

Local Open Scope nat_scope.
Lemma c_to_Vector1_refl:forall c, (c_to_Vector1 c) 0 0= c.
Proof. intros. unfold c_to_Vector1. unfold scale.
       unfold I. simpl. Csimpl .   reflexivity. Qed.

Lemma WF_c_to_Vector1: forall c, WF_Matrix (c_to_Vector1 c).
Proof. intros. unfold c_to_Vector1. auto_wf. Qed.
#[export] Hint Resolve WF_c_to_Vector1 : wf_db.

#[export] Hint Rewrite Rinv_l Rinv_1 : R_db.

Lemma matrix_0_0:forall c, (c .* I 1) 0 0= c.
Proof. intros. rewrite Mscale_1_r.  simpl. reflexivity. Qed.

Lemma matrix_0_0_rev:forall (x: Vector 1), 
WF_Matrix x-> (x  0 0) .* I 1= x.
Proof. 
       intros.   assert(WF_Matrix (x 0 0 .* I 1)).
       apply WF_scale. apply WF_I.   prep_matrix_equality. bdestruct (x0=?0).
       bdestruct (y=?0). rewrite H2. rewrite H1. unfold scale.
       unfold I.  simpl. rewrite Cmult_1_r. reflexivity.
       rewrite H1. unfold WF_Matrix in *.   
       rewrite (H _ y).   rewrite (H0 _ y). reflexivity.
       right. lia. right. lia.  unfold WF_Matrix in *.    
       rewrite (H _ y).   rewrite (H0 _ y). reflexivity.
       left. lia. left. lia.
Qed.     

  
(* Require Import Coq.Structures.OrderedTypeEx. *)
Local Open Scope nat_scope.
Lemma  big_sum_i: forall (f:nat-> C) (n i:nat), 
(forall y, y <> i -> f y = C0)-> ( i < n -> big_sum f n= f i).
Proof.  intros. apply big_sum_unique. exists i. auto. Qed.

Local Open Scope C_scope.
Lemma base_inner_r: forall (n i:nat) (V:Vector n),
 WF_Matrix V-> i< n -> V† × ∣ i ⟩_ n =(V i 0)^* .* I 1.
Proof. intros.   prep_matrix_equality.  
      bdestruct (y=?0).  unfold Mmult. rewrite H1. 
      assert( (Σ
      (fun y0 : nat =>
       ((V) † x y0 * ∣ i ⟩_ n y0 0)%C)
      n )= ((V) † x  i) * (∣ i ⟩_ n i 0)%C).
      try rewrite (big_sum_i (fun y0 : nat =>
      (V) † x y0 * ∣ i ⟩_ n y0 0) n i). 
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
      assert (WF_Matrix ((V) † × ∣ i ⟩_ n)). apply WF_mult. apply WF_adjoint. assumption.
      apply WF_base. apply H0. unfold WF_Matrix in H2. 
      unfold WF_Matrix in H3. intuition. rewrite H2. rewrite H3. reflexivity.
      right. intuition. right. intuition.
Qed.

Lemma base_inner_l: forall (n i:nat) (V:Vector n), 
WF_Matrix V -> i< n -> (∣ i ⟩_ n)† ×  V =(V i 0) .* I 1.
Proof. intros. assert(V† × ∣ i ⟩_ n=(V i 0)^* .* I 1). 
apply base_inner_r. assumption. assumption.
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

Lemma base_inner_M{n:nat}: forall (M: Square n) (i:nat), 
  WF_Matrix M-> 
  i<n -> (∣ i ⟩_ n)† × M × (∣ i ⟩_ n) = (M i i) .* I 1.
Proof . intros. prep_matrix_equality.
    assert ((∣ i ⟩_ n) † × M = (M † × (∣ i ⟩_ n) )†).
    rewrite Mmult_adjoint. rewrite adjoint_involutive.
    reflexivity. rewrite H1.
    rewrite base_inner_r.  
    unfold Mmult. 
    assert(Σ  (fun y0 : nat => (M) † i y0 * ∣ i ⟩_ n y0 0) n = (M) † i i * ∣ i ⟩_ n i 0 ).
    apply (big_sum_i (fun y0 : nat =>  (M) † i y0 * ∣ i ⟩_ n y0 0) n i). 
      intros. simpl. unfold not in H1.  bdestruct (y0=?i).
      intuition. rewrite Cmult_0_r. reflexivity.
      intuition. rewrite H2. 
      unfold adjoint. rewrite Cmult_conj. 
      rewrite Cconj_involutive.
      simpl Base_vec. bdestruct(i=?i). 
      rewrite C1_Conj.
      rewrite Cmult_1_r. 
      reflexivity.
      intuition.
      apply WF_mult. apply WF_adjoint. assumption.
      apply WF_base.
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
WF_Matrix M-> big_sum (fun i:nat => (∣ i ⟩_ n)† × M × (∣ i ⟩_ n)) n  = (trace M).
Proof. intros. remember ((fun i : nat => (M i i) .* I 1)).
rewrite (big_sum_eq_bounded _ m _). 
rewrite Heqm. unfold trace. unfold c_to_Vector1.
rewrite big_sum_Mscale_r.  reflexivity. 
intros. rewrite base_inner_M. rewrite Heqm. reflexivity. 
apply H. assumption.
Qed.

Lemma base_inner_0{n:nat}:forall i j :nat,
i<>j-> i<n -> j<n->
(⟨ i ∣_ (n) × ∣ j ⟩_ (n))= C0.
Proof. intros. rewrite base_inner_l. simpl.
       rewrite Neq_i_j. reflexivity.
       assumption. auto_wf. assumption. 
Qed.

Lemma base_inner_1: forall i n,
(i<n)%nat->
⟨ i ∣_ (n) × ∣ i ⟩_ (n) = C1.
Proof. intros. rewrite base_inner_l. simpl.
       bdestruct (i=?i). unfold c_to_Vector1.  rewrite Mscale_1_l.
       reflexivity. lia. auto_wf. assumption. 
Qed.

Lemma inner_trace'{n:nat}: forall (x x0: Vector n), 
trace ((x0) † × x)= inner_product x0 x.
Proof. intros. unfold trace. unfold inner_product.
      simpl. rewrite Cplus_0_l. reflexivity. 
Qed.

Lemma  trace_I: trace (I 1) = C1.
Proof. unfold trace. simpl.  
      unfold I. simpl. rewrite Cplus_0_l.
      reflexivity.
Qed.

Local Open Scope R_scope.
Lemma norm_base_1: forall n x, (x<n)%nat ->norm (∣ x ⟩_ (n))=1 .
Proof. intros.  unfold norm.   rewrite <-inner_trace'. rewrite base_inner_1.
       unfold c_to_Vector1. Msimpl. 
       rewrite trace_I. simpl. rewrite sqrt_1. reflexivity. assumption.
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


Lemma base_kron: forall x m n,
∣ x / n ⟩_ (m) ⊗ ∣ x mod n ⟩_ (n) =
Base_vec (m*n) x.
Proof. intros.
prep_matrix_equality.
       unfold kron.
       destruct y.
       simpl. 
       bdestruct (x0=?x).
       subst.
       assert((x / n =? x / n) = true ).
       rewrite Nat.eqb_eq. reflexivity.
       rewrite H. clear H. 
       assert((x mod n =? x mod n) = true ).
       rewrite Nat.eqb_eq. reflexivity.
       rewrite H.
       apply Cmult_1_l.
       rewrite (nat_neq_mod_div _ _ n) in H.
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

Local Open Scope nat_scope.
Lemma big_sum_I_i: forall n i, 
i< n -> ∣ i ⟩_ n ×  (adjoint (∣ i ⟩_ n)) =
fun x y => if (x =? i) && (y =? i) && (x<? n) then C1 else C0.
Proof. intros. prep_matrix_equality. unfold Mmult.
      simpl. rewrite Cplus_0_l. 
      bdestruct((x =? i)).  simpl.
      bdestruct((y =? i)).  simpl.
      bdestruct(x<? n). simpl.
      unfold adjoint. rewrite base1. 
      rewrite Cconj_R.
      rewrite Cmult_1_l. reflexivity.
      assumption. intuition.
      unfold adjoint. rewrite base0. 
      rewrite Cconj_R.
      rewrite Cmult_0_r. reflexivity.
      assumption. simpl. 
      rewrite Cmult_0_l. reflexivity.
Qed.

Lemma big_sum_x_y{n:nat}: forall (f:nat-> Matrix n n) x y n_0,
big_sum f n_0 x y= big_sum (fun i=> (f i) x y) n_0 .
Proof. induction n_0. simpl. unfold Zero. reflexivity.
      simpl. unfold Mplus. f_equal. intuition.
Qed.

Local Open Scope nat_scope.
Lemma pow_gt_0: forall n:nat ,
(2^ n >0)%nat .
Proof. induction n. simpl. lia.
      simpl. rewrite Nat.add_0_r. 
      lia.
Qed.

Lemma  big_sum_I: forall n,
big_sum (fun i : nat => ∣ i ⟩_ (2^n) × ⟨ i ∣_ (2^n)) (2^n)= I (2^n).
Proof. intros. 
       rewrite (big_sum_eq_bounded  _
        (fun i=> fun x y => if (x =? i) && (y =? i) && (x<? 2^n) then C1 else C0)).
        prep_matrix_equality.
        rewrite big_sum_x_y.
        unfold I.  destruct x; destruct y.
        rewrite (big_sum_unique  C1).
        simpl. assert(0 <? 2^ n = true). 
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

Lemma qubit0_base_kron:forall n i,
i<(2^n)->
kron (∣ 0 ⟩_ 2) (∣ i ⟩_ (2^n)) = (∣ i ⟩_ (2^(n+1))).
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
      unfold Base_vec.
      simpl. destruct y. bdestruct (x=?i).
      destruct H2. lia. 
      assert(x/2^n >= 2^n / 2^n). 
      apply Nat.div_le_mono. lia. lia.
      rewrite Nat.div_same in H3. 
      bdestruct (x / 2 ^ n =? 0). rewrite H4 in *.
      lia. rewrite Cmult_0_l. reflexivity. lia.
      rewrite Cmult_0_l. reflexivity.  
Qed.

Lemma qubit1_base_kron:forall n i,
i<(2^n)->
kron (∣ 1 ⟩_ 2) (∣ i ⟩_ (2^n)) = (∣ i+2^n ⟩_ (2^(n+1))).
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
      simpl. unfold Base_vec. simpl. destruct y.
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



(* 
 *)






(* Local Open Scope C_scope.


Lemma fst_mult: forall (r: R) (c: C),
 fst(r * c)= (r * fst c)%R.
Proof. intros. destruct c. 
      simpl. rewrite Rmult_0_l.
      rewrite Rminus_0_r. reflexivity.
Qed. *)


(* Lemma trace_mult: forall (n:nat) (A B :Square n),
trace(Mmult A B) =trace (Mmult B A).
Proof. intros. unfold trace. unfold Mmult. 
       rewrite big_sum_swap_order. 
       apply big_sum_eq. apply functional_extensionality.
       intros. apply big_sum_eq. apply functional_extensionality.
       intros.
apply Cmult_comm. 
Qed. *)

(*trace*)
(* 







 *)


(*  *)

(*  *)

(* 


 *)





(*  *)








