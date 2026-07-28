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
From Coq Require Import Psatz.

Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Arith.Peano_dec.

From Quan Require Import Matrix.
From Quan Require Import Quantum.
From Quan Require Import Mixed_State.
From Quan Require Import QState_L.
From Quan Require Import QIMP_L.
From Quan Require Import QAssert_L.
From Quan Require Import Reduced.
From Quan Require Import QRule_Q_L.
From Quan Require Import QRule_E_L.
From Quan Require Import QRule_I_L.
From Quan Require Import QSepar.
From Quan Require Import QFrame.
From Quan Require Import addM.
Import Basic. Import Ceval_Prop.


Local Open Scope com_scope.
Local Open Scope rule_scope.
Local Open Scope assert_scope.
Local Open Scope matrix_scope.
Local Open Scope nat_scope.




 

(*----------------------------------Definition-------------------------*)
Parameter p: nat->nat->R.
Hypothesis p_pos : forall a b, (0 < p a b < 1)%R.
Hypothesis p_sum1 :
  (p 0 0 + p 0 1 + p 1 0 + p 1 1 = 1)%R.

Definition cnot_on_one (i : nat) : Square (2 ^ 1) :=
  if i =? 0 then I 2 else σx.

(*表示对第l个block块的纯化*)
Definition sa (l : nat) : nat := 4 * l.
Definition sb (l : nat) : nat := 4 * l + 1.
Definition ta (l : nat) : nat := 4 * l + 2.
Definition tb (l : nat) : nat := 4 * l + 3.

Definition cx (l : nat) : nat := 3 * l.
Definition cy (l : nat) : nat := 3 * l + 1.
Definition cv (l : nat) : nat := 3 * l + 2.

Definition Purify (l : nat) : com :=
  <{ cnot_on_one [[(sa l) (S (sa l))]] [[(ta l) (S (ta l))]];
     cnot_on_one [[(sb l) (S (sb l))]] [[(tb l) (S (tb l))]];
     (cx l) :=M [[(ta l) (S (ta l))]];
     (cy l) :=M [[(tb l) (S (tb l))]];
     if (AId (cx l)) = (AId (cy l)) then
       (cv l) := 1
     else
       (cv l) := 0
     end }>.


Definition Purify_0123 : com := Purify 0.


Definition bit (n : nat) : nat := n mod 2.

Definition bit_xor (m n : nat) : nat :=
  bit (bit m + bit n).

Definition Bell (a b : nat) : Vector 4 :=
  / √ 2 .* big_sum (fun z => ((-C1) ^ (bit b * z) .* ((∣ z ⟩_ 2) ⊗ (∣ bit_xor z a ⟩_ 2)))) 2.


(*给定一个i表示局部分支编号，返回对应的a,b,c,d的值*)
  Definition idx_a (i : nat) : nat := bit (i / 8).
  Definition idx_b (i : nat) : nat := bit (i / 4).
  Definition idx_c (i : nat) : nat := bit (i / 2).
  Definition idx_d (i : nat) : nat := bit i.


(*给定一个i表示局部分支编号，返回w_i即对应的概率系数*)
Definition D_in_weight_i (p : nat -> nat -> R) (i : nat) : R :=
    (p (idx_a i) (idx_b i) * p (idx_c i) (idx_d i))%R.

(*给定一个i表示局部分支编号，和 l 表示第几个block块，返回在该分支下lblock块对应的输入状态*)
Definition D_in_branch_i (l i: nat)  : State_formula :=
    SQuan (QExp_s (sa l) (S (sb l)) (Bell (idx_a i) (idx_b i))) ⊙
    SQuan (QExp_s (ta l) (S (tb l)) (Bell (idx_c i) (idx_d i))).


Definition one_if_eq (a c : nat) : nat :=
  if Nat.eqb (bit a) (bit c) then 1 else 0.

(*给定一个i表示局部分支编号，和 l 表示第几个block块，返回在该分支下lblock块对应的输出状态*)
Definition D_out_branch_i (l i : nat) : State_formula :=
    SQuan (QExp_s (sa l) (S (sb l)) (Bell (idx_a i) (bit_xor (idx_b i) (idx_d i)))) /\s
    SPure (BEq (AId (cv l)) (one_if_eq (idx_a i) (idx_c i))).


Definition eta_l (eta l : nat) : nat :=
    (eta / 16 ^ l) mod 16.

Fixpoint big_prod_R (f : nat -> R) (m : nat) : R :=
    match m with
    | 0 => 1%R
    | S m' => (big_prod_R f m' * f m')%R
    end.

(*一共有m个分支，给定一个eta表示分支编号，返回对应的概率系数*)
Definition D_m_in_weight (p : nat -> nat -> R) (m eta : nat) : R :=
    big_prod_R
      (fun l => D_in_weight_i p (eta_l eta l))
      m.


Fixpoint big_odot (F : nat -> State_formula) (m : nat) : State_formula :=
    match m with
    | 0 => BTrue
    | S m' => F m' ⊙ big_odot F m'
    end.

(*一共有m个分支，给定一个eta表示分支编号，返回对应的分支输入状态*)
 Definition D_m_in_branch (m eta: nat) : State_formula :=
    big_odot
      (fun l => D_in_branch_i l (eta_l eta l))
      m.

(*一共有m个分支，给定一个eta表示分支编号，返回对应的分支输出状态*)
Definition D_m_out_branch (m eta: nat) : State_formula :=
  big_odot (fun l => D_out_branch_i l (eta_l eta l)) m. 

Definition D_m_in (p : nat -> nat -> R) (m:nat): pro_formula :=
    big_pOplus (D_m_in_weight p m) (D_m_in_branch m) (16^m).

Definition D_m_out (p : nat -> nat -> R) (m:nat): pro_formula :=
    big_pOplus (D_m_in_weight p m) (D_m_out_branch m) (16^m).

(*针对单个block分支*)
Definition D_post_q (p : nat -> nat -> R) (a k : nat) : R :=
  (p (bit a) 0%nat * p (bit a) (bit k) +
   p (bit a) 1%nat * p (bit a) (bit (1 + bit k)))%R.

Definition p_succ (p : nat -> nat -> R) : R :=
  ((p 0%nat 0%nat + p 0%nat 1%nat) *
   (p 0%nat 0%nat + p 0%nat 1%nat) +
   (p 1%nat 0%nat + p 1%nat 1%nat) *
   (p 1%nat 0%nat + p 1%nat 1%nat))%R.

Definition p_fail (p : nat -> nat -> R) : R :=
  (1 - p_succ p)%R.

Definition out_a (i : nat) : nat := bit (i / 2).
Definition out_k (i : nat) : nat := bit i.

Definition D_post_weight (p : nat -> nat -> R) (i : nat) : R :=
  D_post_q p (out_a i) (out_k i).

Definition D_post_branch (i : nat) : State_formula :=
  (BEq (AId ((cv 0))) 1) /\s
  SQuan (QExp_s 0 2 (Bell (out_a i) (out_k i))).

Definition D_post (p : nat -> nat -> R) : pro_formula :=
  big_pOplus (D_post_weight p) D_post_branch 4 ++
  [(p_fail p, SPure (BEq (AId ((cv 0))) 0))].


(*--------------------------辅助的引理---------------------------------------*)

Lemma bit_id : forall n, bit (bit n) = bit n.
  Proof.
    intros n.
    unfold bit.
    rewrite Nat.mod_mod by lia.
    reflexivity.
  Qed.

   Lemma bit_xor_0_l : forall n, bit_xor 0 n = bit n.
  Proof.
    intros n.
    unfold bit_xor.
    change (bit 0) with 0%nat.
    rewrite Nat.add_0_l.
    apply bit_id.
  Qed.

    Lemma bit_xor_0_r : forall n, bit_xor  n 0 = bit n.
  Proof.
    intros n.
    unfold bit_xor.
    change (bit 0) with 0%nat.
    rewrite Nat.add_0_r.
    apply bit_id.
  Qed.

Lemma bit_xor_1_l : forall n, bit_xor 1 n = bit (S (bit n)).
  Proof.
    intros n.
    unfold bit_xor.
    simpl.
    unfold bit at 1.
    simpl.
    reflexivity.
Qed.

Lemma bit_xor_assoc : forall a b c, bit_xor (bit_xor a b) c = bit_xor a (bit_xor b c).
Proof.
intros a b c. unfold bit_xor. unfold bit. 
repeat rewrite<-Nat.add_mod; try lia.   
replace (((a + b) mod 2 + c) mod 2) with (((a + b) + c) mod 2).
rewrite <-add_assoc. rewrite Nat.add_mod; try lia. rewrite (Nat.add_mod a); try lia. rewrite Nat.mod_mod; try lia.
rewrite Nat.add_mod; try lia. symmetry. rewrite (Nat.add_mod ((a + b) mod 2)); try lia. rewrite Nat.mod_mod; try lia.
Qed.

Lemma bit_xor_com : forall a b, bit_xor  a b = bit_xor b a.
Proof.
intros a b. unfold bit_xor. unfold bit. 
repeat rewrite<-Nat.add_mod; try lia.
rewrite Nat.add_comm. reflexivity.   
Qed.

Lemma bit_xor_eq_0 : forall a b,
    bit a = a ->
    bit b = b ->
    a = b ->
    bit_xor a b = 0.
Proof.
    intros a b Ha Hb Heq.
    subst b.
    assert (Ha01 : a = 0 \/ a = 1).
    {
      rewrite <- Ha.
      unfold bit.
      pose proof (Nat.mod_upper_bound a 2 ltac:(lia)).
      lia.
    }
    destruct Ha01; subst; reflexivity.
Qed.

Lemma bit_xor_neq_1 : forall a b,
    bit a = a ->
    bit b = b ->
    a <> b ->
    bit_xor a b = 1.
Proof.
    intros a b Ha Hb Hneq.
    assert (Ha01 : a = 0 \/ a = 1).
    {
      unfold bit in Ha.
      rewrite <- Ha.
      pose proof (Nat.mod_upper_bound a 2 ltac:(lia)).
      lia.
    }
    assert (Hb01 : b = 0 \/ b = 1).
    {
      unfold bit in Hb.
      rewrite <- Hb.
      pose proof (Nat.mod_upper_bound b 2 ltac:(lia)).
      lia.
    }
    destruct Ha01; destruct Hb01; subst; try contradiction; reflexivity.
Qed.

 Lemma bit_xor_bit : forall a b,
    bit (bit_xor a b) = bit_xor a b.
  Proof.
    intros a b.
    unfold bit_xor.
    apply bit_id.
  Qed.
  
  Lemma idx_d_bit : forall i,
    bit (idx_d i) = idx_d i.
  Proof.
    intros i.
    unfold idx_d.
    apply bit_id.
  Qed.


  Theorem rule_cond_classic': forall (F1 F2:State_formula) (c1 c2:com) (b:bexp), WF_formula F2->
        ({{F1 /\s (b)}} c1 {{F2 }} /\ {{F1 /\s ((BNot b) )}} c2 {{F2 }})
     -> ({{F1 }}
        if b then c1 else c2 end
        {{F2}}).
Proof. intros F1 F2 c1 c2 b H'. intros.  
assert(F1 ->> ANpro [F1 /\s b ; F1 /\s (BNot b)]). 
rule_solve. 
assert(StateMap.this mu=[] \/ StateMap.this mu <>[]).
apply Classical_Prop.classic. destruct H4.
apply sat_Assert_empty. simpl. split. econstructor;simpl. auto.
econstructor; simpl; auto; econstructor. discriminate. assumption.

apply sat_State_Npro; try  assumption. simpl. auto.

intros. apply H2 in H5. simpl in *. destruct (beval (x, d_find x mu) b); simpl;[left|right]; auto.
assert(({{F1 /\s b}} c1 {{F2}}) /\ ({{F1 /\s <{ ~ b }>}} c2 {{F2}})).
split; try apply H. 
unfold hoare_triple. intros. apply H0 in H3. apply sat_Npro_Pro in H3. destruct H3.
pose (rule_cond F1 F2 F1 F2 c1 c2 b x). eapply h in H1. destruct H3. 
eapply H1 in H4; try apply H2; apply rule_Oplus in H4; simpl in *.
apply (@sat_NPro_State' ) in H4.  try assumption. lra.
destruct H. unfold hoare_triple in *. 
econstructor; simpl.  auto. econstructor. simpl. auto.
econstructor.
Qed.

Lemma SAnd_assoc_r :
    forall F1 F2 F3,
      (F1 /\s (F2 /\s F3)) ->>
      ((F1 /\s F2) /\s F3).
  Proof.
    intros. rule_solve.  Qed. 


Theorem rule_sum_fun:
  forall (F1 F2 : nat -> State_formula) (c : com) (p_n : nat -> R) n,
    (forall i, i < n -> (0 < p_n i)%R) ->
    (forall i, i < n -> WF_formula (F2 i)) ->
    (forall i, i < n -> {{F1 i}} c {{F2 i}}) ->
    {{big_pOplus p_n F1 n}} c {{big_pOplus p_n F2 n}}.
Proof.
  intros F1 F2 c p_n n Hpos Hwf Htriple.
  rewrite <- (pro_npro_swap (big_pOplus p_n F1 n)).
  rewrite <- (pro_npro_swap (big_pOplus p_n F2 n)).
  rewrite big_pOplus_get_pro.
  rewrite big_pOplus_get_npro.
  rewrite big_pOplus_get_pro.
  rewrite big_pOplus_get_npro.
  repeat rewrite <- fun_to_list_big_Oplus_eq.
  eapply rule_sum.
  - apply Forall_fun_to_list. exact Hpos.
  - repeat rewrite fun_to_list_length. reflexivity.
  - apply Forall_fun_to_list. exact Hwf.
  - apply Forall_two_forall. exact Htriple.
Qed.


Theorem rule_OdotCon :
    forall F1 F2 F3 F4 : State_formula,
      NSet.Equal
        (NSet.inter (snd (Free_state F3)) (snd (Free_state F4)))
        NSet.empty ->
      (F1 ->> F3) ->
      (F2 ->> F4) ->
      (F1 ⊙ F2) ->> (F3 ⊙ F4).
  Proof. unfold assert_implies.
    intros F1 F2 F3 F4 Hdisj H13 H24 s e mu Hsat.
    rewrite sat_assert_odot in Hsat.
    rewrite sat_assert_odot.
    destruct Hsat as [HF1 Hsat].
    destruct Hsat as [HF2 _].
    split.
    - apply H13. exact HF1.
    - split.
      + apply H24. exact HF2.
      + exact Hdisj.
  Qed.

Theorem rule_Odot_swap_left : forall A B C : State_formula,
  A ⊙ (B ⊙ C) ->> B ⊙ (A ⊙ C).
Proof.    
  unfold assert_implies. 
  intros A B C s e mu Hsat.
  rewrite sat_assert_odot in Hsat.
  destruct Hsat as [HA Hsat].
  destruct Hsat as [HBC HA_BC].
  rewrite sat_assert_odot in HBC.
  destruct HBC as [HB HBC].
  destruct HBC as [HC HB_C].
  rewrite sat_assert_odot.
  split.
  - exact HB.
  - split.
    + rewrite sat_assert_odot.
      split.
      * exact HA.
      * split.
        -- exact HC.
        -- simpl in HA_BC.
           rewrite inter_union_dist in HA_BC.
           apply union_empty in HA_BC.
           destruct HA_BC as [_ HA_C].
           exact HA_C.
    + simpl.
      rewrite inter_union_dist.
      apply union_empty.
      split.
      * simpl in HA_BC.
        rewrite inter_union_dist in HA_BC.
        apply union_empty in HA_BC.
        destruct HA_BC as [HA_B _].
        rewrite inter_comm.
        exact HA_B.
      * exact HB_C.
Qed.

Theorem rule_Odot_swap_pair_frame : forall A B C : State_formula,
  (A ⊙ B) ⊙ C ->> (B ⊙ A) ⊙ C.
Proof.
  unfold assert_implies.
  intros A B C s e mu Hsat.
  rewrite sat_assert_odot in Hsat.
  destruct Hsat as [HAB Hsat].
  destruct Hsat as [HC HAB_C].
  rewrite sat_assert_odot in HAB.
  destruct HAB as [HA HAB].
  destruct HAB as [HB HA_B].
  rewrite sat_assert_odot.
  split.
  - rewrite sat_assert_odot.
    split.
    + exact HB.
    + split.
      * exact HA.
      * rewrite inter_comm. exact HA_B.
  - split.
    + exact HC.
    + simpl in HAB_C.
      rewrite inter_comm in HAB_C.
      rewrite inter_union_dist in HAB_C.
      apply union_empty in HAB_C.
      destruct HAB_C as [HA_C HB_C].
      simpl.
      rewrite inter_comm.
      rewrite inter_union_dist.
      apply union_empty.
      split.
      * exact HB_C.
      * exact HA_C.
Qed.

Lemma big_odot_q_in_index : forall (F : nat -> State_formula) n q,
  NSet.In q (snd (Free_state (big_odot F n))) ->
  exists i, i < n /\ NSet.In q (snd (Free_state (F i))).
Proof.
  intros F n.
  induction n; intros q Hq.
  - simpl in Hq. apply In_empty in Hq. contradiction.
  - simpl in Hq.
    apply NSet.union_1 in Hq.
    destruct Hq as [Hq | Hq].
    + exists n. split; [lia | exact Hq].
    + apply IHn in Hq.
      destruct Hq as [i Hq].
      destruct Hq as [Hi Hq].
      exists i. split; [lia | exact Hq].
Qed.

Lemma big_odot_qframe_disjoint_step :
  forall (F2 : State_formula) (F3 : nat -> State_formula) n,
    (forall i, i < S n ->
      NSet.Equal
        (NSet.inter (snd (Free_state F2)) (snd (Free_state (F3 i))))
        NSet.empty) ->
    (forall i j, i < S n -> j < S n -> i <> j ->
      NSet.Equal
        (NSet.inter (snd (Free_state (F3 i))) (snd (Free_state (F3 j))))
        NSet.empty) ->
    NSet.Equal
      (NSet.inter
        (snd (Free_state (big_odot F3 n ⊙ F2)))
        (snd (Free_state (F3 n))))
      NSet.empty.
Proof.
  intros F2 F3 n HF2 Hpair.
  unfold NSet.Equal.
  intros q; split; intros Hq.
  - apply NSet.inter_1 in Hq as Hleft.
    apply NSet.inter_2 in Hq as Hcur.
    simpl in Hleft.
    apply NSet.union_1 in Hleft.
    destruct Hleft as [Hprev | HF2q].
    + apply big_odot_q_in_index in Hprev.
      destruct Hprev as [i Hprev].
      destruct Hprev as [Hi Hprev].
      pose proof (Hpair i n ltac:(lia) ltac:(lia) ltac:(lia)) as Hdisj.
      unfold NSet.Equal in Hdisj.
      assert (NSet.In q (NSet.inter (snd (Free_state (F3 i))) (snd (Free_state (F3 n))))).
      { apply NSet.inter_3; assumption. }
      apply Hdisj in H. apply In_empty in H. contradiction.
    + pose proof (HF2 n ltac:(lia)) as Hdisj.
      unfold NSet.Equal in Hdisj.
      assert (NSet.In q (NSet.inter (snd (Free_state F2)) (snd (Free_state (F3 n))))).
      { apply NSet.inter_3; assumption. }
      apply Hdisj in H. apply In_empty in H. contradiction.
  - apply In_empty in Hq. contradiction.
Qed.

Theorem rule_qframe_big_odot' :
  forall (F1 F2 : State_formula) (F3 : nat -> State_formula) c n,
    (forall i, i < n ->
      NSet.Equal
        (NSet.inter (snd (Free_state F2)) (snd (Free_state (F3 i))))
        NSet.empty) ->
    (forall i j, i < n -> j < n -> i <> j ->
      NSet.Equal
        (NSet.inter (snd (Free_state (F3 i))) (snd (Free_state (F3 j))))
        NSet.empty) ->
    (forall i, i < n -> Considered_Formula (F3 i)) ->
    {{ F1 }} c {{ F2 }} ->
    (forall i, i < n ->
      NSet.Equal
        (NSet.inter (fst (Free_state (F3 i))) (fst (MVar c)))
        NSet.empty) ->
    (forall i, i < n ->
      snd (option_free (Free_State (F3 i))) <=
        option_nat (NSet.min_elt (snd (MVar c))) \/
      option_nat (NSet.max_elt (snd (MVar c))) <
        fst (option_free (Free_State (F3 i)))) ->
    {{ big_odot F3 n ⊙ F1 }} c {{ big_odot F3 n ⊙ F2 }}.
Proof.
  intros F1 F2 F3 c n.
  induction n.
  - intros HF2 Hpair Hcons Htriple Hc Hside.
    simpl.
    eapply rule_conseq.
    + apply Htriple.
    + eapply implies_trans.
      * apply rule_OdotC.
      * apply rule_OdotE.
    + eapply implies_trans.
      * apply rule_OdotE.
      * apply rule_OdotC.
  - intros HF2 Hpair Hcons Htriple Hc Hside.
    simpl.
    eapply rule_conseq.
    + eapply rule_qframe'.
      * eapply (big_odot_qframe_disjoint_step F2 F3 n).
        -- intros i Hi. apply HF2. lia.
        -- intros i j Hi Hj Hij. apply Hpair; lia.
      * apply Hcons. lia.
      * split.
        -- apply IHn.
           ++ intros i Hi. apply HF2. lia.
           ++ intros i j Hi Hj Hij. apply Hpair; lia.
           ++ intros i Hi. apply Hcons. lia.
           ++ exact Htriple.
           ++ intros i Hi. apply Hc. lia.
           ++ intros i Hi. apply Hside. lia.
        -- split.
           ++ apply Hc. lia.
           ++ apply Hside. lia.
    + apply rule_OdotA.
    + apply rule_OdotA.
Qed.
(*-------------------------单个分支正确性证明： {𝐺_i^(𝓁)} 𝐏𝐮𝐫𝐢𝐟𝐲 ^(𝓁) {𝐻_i^(𝓁)}, l 表示第几个block块, i表示对应的局部分支编号---------------------------*)

(*------1: Bell 态经过第一个 CNOT 后的状态变化---------*)
Definition Purify_after_cnot_a_vec (i : nat) : Vector 16 :=
    (/ 2)%R .* @big_sum (Matrix 16 1) _
      (fun z =>
        @big_sum (Matrix 16 1) _
          (fun w =>
            (((-C1) ^ (idx_b i * z)) *
             ((-C1) ^ (idx_d i * w))) .*
            (∣ z ⟩_ 2 ⊗
             ∣ bit_xor z (idx_a i) ⟩_ 2 ⊗
             ∣ bit_xor w z ⟩_ 2 ⊗
             ∣ bit_xor w (idx_c i) ⟩_ 2))
          2)
      2.

Definition Purify_after_cnot_a (l i : nat) : State_formula :=
  SQuan (QExp_s (sa l) (S (tb l)) (Purify_after_cnot_a_vec i)).

Definition Purify_before_cnot_a_join (l i : nat) : State_formula :=
  SQuan (QExp_s (sa l) (S (tb l)) (Bell (idx_a i) (idx_b i) ⊗ Bell (idx_c i) (idx_d i))).

Definition Purify_after_cnot_a_raw (l i : nat) : State_formula :=
  SQuan (QExp_s (sa l) (S (tb l)) (@UCtrl_v (sa l) (S (sa l)) (ta l) (S (ta l))
        (sa l) (S (tb l)) cnot_on_one
        (Bell (idx_a i) (idx_b i) ⊗ Bell (idx_c i) (idx_d i)))).

Ltac purify_wf_1 :=
    try match goal with
    | H : ?m = _ |- WF_Matrix ?m => try rewrite H
    end;
     try apply WF_kron; try auto_wf; try apply WF_base; unfold bit; 
    try apply Nat.mod_upper_bound; 
    try lia.


Lemma Purify_after_cnot_a_vec_eq : forall l i,
  UCtrl_v (sa l) (S (sa l)) (ta l) (S (ta l))
    (sa l) (S (tb l)) cnot_on_one
    (Bell (idx_a i) (idx_b i) ⊗ Bell (idx_c i) (idx_d i))
  = Purify_after_cnot_a_vec i.
Proof.
  (* CNOT_{s_a(l) -> t_a(l)} ( |β_{a_i,b_i}>_s ⊗ |β_{c_i,d_i}>_t )  =
     1/2 · Σ_{z=0}^{1} Σ_{w=0}^{1} (-1)^{b_i z + d_i w} | z, z ⊕ a_i, w ⊕ z, w ⊕ c_i >.
   *)
  intros l i.
  unfold Purify_after_cnot_a_vec, Bell.
  unfold UCtrl_v.
  replace (S (sa l) - sa l)%nat with 1%nat by lia.
  replace (sa l - sa l)%nat with 0%nat by lia.
  replace (S (tb l) - S (sa l))%nat with 3%nat by (unfold sa, tb; lia).
  replace (ta l - sa l)%nat with 2%nat by (unfold sa, ta; lia).
  replace (S (tb l) - S (ta l))%nat with 1%nat by (unfold ta, tb; lia).
     
  repeat rewrite Mscale_kron_dist_r.
  repeat rewrite Mscale_kron_dist_l.
  repeat rewrite Mscale_assoc. 
   
  assert(16=(2 ^ (S (tb l) - sa l))). unfold tb. unfold sa. 
  replace (S (4 * l + 3) - 4 * l) with 4 by lia.
  reflexivity. destruct H. 
  rewrite (Mscale_mult_dist_r). f_equal.  

  rewrite <- RtoC_inv by apply sqrt2_neq_0.
  rewrite <- RtoC_mult. f_equal.
  field_simplify; try apply sqrt2_neq_0. simpl.
  rewrite <-Rmult_assoc.
  rewrite sqrt_def; lra.

  rewrite kron_Msum_distr_r.  
  rewrite Mmult_Msum_distr_l. 
  apply big_sum_eq_bounded. intros. 
  rewrite kron_Msum_distr_l.  
  rewrite Mmult_Msum_distr_l.  
  apply big_sum_eq_bounded. intros.
  rewrite Mscale_kron_dist_l.
    rewrite Mscale_kron_dist_r. 
    rewrite Mscale_assoc. 
    rewrite Mscale_mult_dist_r. 
    f_equal. replace (bit (idx_b i)) with ((idx_b i)) by (unfold idx_b; symmetry;  apply bit_id ). 
    replace (bit (idx_d i)) with ((idx_d i)) by (unfold idx_d; symmetry;  apply bit_id ).  reflexivity.  simpl. rewrite Mplus_0_l. 
   repeat  rewrite kron_1_l; [ | auto_wf  |auto_wf].  
   rewrite Mmult_plus_distr_r. 
   unfold cnot_on_one. simpl.

   replace ((Nat.pow (S (S O)) match ta l return nat with
                                               | O => S (ta l)
                                               | S l0 => sub (ta l) l0
                                               end)) with (2).
  replace ((2 + (2 + (2 + (2 + 0)))) ) with (4*2) by lia.
                          
   replace ((I 4 ⊗ I 2 ⊗ I 2)) with ((I 2 ⊗ I 8)); [ | repeat rewrite id_kron; try reflexivity].
    
   replace ((I 4 ⊗ σx ⊗ I 2)) with ((I 2 ⊗ (I 2 ⊗  σx ⊗ I 2))); [ | try repeat rewrite <-kron_assoc; auto_wf; try rewrite id_kron; try reflexivity ] .
   replace (16) with (2*8); try reflexivity. repeat rewrite kron_mixed_product. 
   repeat rewrite Mmult_1_r; [ | auto_wf | auto_wf | auto_wf ]. repeat rewrite Mmult_1_l; [ | auto_wf  ].
   
    replace (4) with (2*2); try reflexivity. replace (1) with (1*1) by reflexivity.

 rewrite (kron_assoc (Base_vec 2 x)); [ | auto_wf | purify_wf_1 | purify_wf_1 ].
  repeat rewrite kron_mixed_product. 
   rewrite Mmult_1_l. rewrite kron_assoc; [ | auto_wf | auto_wf | auto_wf ]. repeat rewrite Mmult_assoc.
    simpl.
  
    replace (8) with (2*(2*2)) by reflexivity. replace (1) with (1*(1*1)) by reflexivity.

   repeat  rewrite kron_mixed_product. simpl. repeat rewrite Mmult_1_l; [|try apply WF_base;
  unfold bit; try apply Nat.mod_upper_bound; try lia | try apply WF_base;
  unfold bit; try apply Nat.mod_upper_bound; try lia] .  
   assert(x=0 \/ x=1) . lia. destruct H1; rewrite H1; Msimpl; rewrite <-base_qubit0; rewrite <-base_qubit1;
  try simpl; try rewrite base_inner_1; try rewrite  base_inner_0; unfold c_to_Vector1; Msimpl; try lia. rewrite bit_xor_0_r. 
  replace (bit x0) with (x0).    repeat rewrite kron_assoc; purify_wf_1. reflexivity. unfold bit; rewrite Nat.mod_small by lia; reflexivity.
   repeat rewrite kron_assoc; purify_wf_1. f_equal. f_equal.
   f_equal.  assert(x0=0 \/ x0=1) . lia. destruct H2; rewrite H2;   solve_matrix. purify_wf_1. purify_wf_1.

  replace (match ta l with
           | 0 => S (ta l)
           | S l0 => ta l - l0
           end) with 1.
  - reflexivity.
  - unfold ta.
    replace (4 * l + 2) with (S (4 * l + 1)) by lia. lia.  

Qed.

Lemma Purify_branch_cnot_a_correct : forall l i,
  {{ D_in_branch_i l i }}
    <{ cnot_on_one [[(sa l) (S (sa l))]] [[(ta l) (S (ta l))]] }>
  {{ Purify_after_cnot_a l i }}.
Proof.
  intros l i.
  eapply rule_conseq
    with (P' := Purify_before_cnot_a_join l i)
         (Q' := Purify_after_cnot_a_raw l i).
  - (* 使用 QUnit_Ctrl 规则处理第一个 CNOT。 *)
    unfold Purify_before_cnot_a_join.
    unfold Purify_after_cnot_a_raw.
    apply rule_QUnit_Ctrl.
    unfold sa, ta, tb. lia.
  - (* 将两个 Bell pair 的分离断言合并成一个 4-qubit 断言。 *)
    unfold D_in_branch_i.
    unfold Purify_before_cnot_a_join.
    eapply implies_trans.
    + apply rule_odotT.
    + replace (S (sb l)) with (ta l) by (unfold sb, ta; lia).
      replace (Bell (idx_a i) (idx_b i) ⊗ Bell (idx_c i) (idx_d i))
        with (@kron (2 ^ (ta l - sa l)) 1 (2 ^ (S (tb l) - ta l)) 1
          (Bell (idx_a i) (idx_b i)) (Bell (idx_c i) (idx_d i))).
      apply rule_Separ.
      replace (ta l - sa l) with 2 by (unfold sa, ta; lia).
      replace (S (tb l) - ta l) with 2 by (unfold ta, tb; lia).
      reflexivity.
  - (* 用矩阵计算等式把 QUnit_Ctrl 的 raw 后置改写成定义好的中间断言。 *)
    unfold Purify_after_cnot_a_raw.
    unfold Purify_after_cnot_a.
    rewrite Purify_after_cnot_a_vec_eq.
    apply implies_refl.
Qed.

(*------1: 状态经过第二个 CNOT 后的状态变化---------*)
Definition Purify_after_cnot_ab_vec (i : nat) : Vector 16 :=
    (/ 2)%R .* @big_sum (Matrix 16 1) _
      (fun z =>
        @big_sum (Matrix 16 1) _
          (fun w =>
            (((-C1) ^ (idx_b i * z)) *
             ((-C1) ^ (idx_d i * w))) .*
            (∣ z ⟩_ 2 ⊗
             ∣ bit_xor z (idx_a i) ⟩_ 2 ⊗
             ∣ bit_xor w z ⟩_ 2 ⊗
             ∣ bit_xor (bit_xor w z) (bit_xor (idx_a i) (idx_c i)) ⟩_ 2))
          2)
      2.

Definition Purify_after_cnot_ab_join (l i : nat) : State_formula :=
  SQuan (QExp_s (sa l) (S (tb l)) (Purify_after_cnot_ab_vec i)).

Definition Purify_after_cnot_ab_raw (l i : nat) : State_formula :=
  SQuan (QExp_s (sa l) (S (tb l))
        (@UCtrl_v (sb l) (S (sb l)) (tb l) (S (tb l))
        (sa l) (S (tb l)) cnot_on_one
        (Purify_after_cnot_a_vec i))).

Definition Purify_after_cnot_ab (l i : nat) : State_formula :=
  SQuan
    (QExp_s (sa l) (S (sb l))
      (Bell (idx_a i) (bit_xor (idx_b i) (idx_d i)))) ⊙
  SQuan
    (QExp_s (ta l) (S (tb l))
      (Bell (bit_xor (idx_a i) (idx_c i)) (idx_d i))).


Lemma Purify_after_cnot_ab_vec_raw_eq : forall l i,
  UCtrl_v (sb l) (S (sb l)) (tb l) (S (tb l))
    (sa l) (S (tb l)) cnot_on_one
    (Purify_after_cnot_a_vec i)
  = Purify_after_cnot_ab_vec i.
Proof. 
  (* 第二个 CNOT 的矩阵计算，CNOT_{s_b(l) -> t_b(l)}
    (Purify_after_cnot_a_vec(i) ) = Purify_after_cnot_ab_vec(i）。内部分支显示变化如下：|z, z xor a, w xor z, w xor c>
              ↦ |z, z xor a, w xor z, w xor z xor a xor c>. *)
    intros. 
    unfold UCtrl_v. 
    replace (S (sb l) - sb l)%nat with 1%nat by lia.
    replace (sb l - sa l)%nat with 1%nat; [ | unfold sa; unfold sb; try lia].
    replace (S (tb l) - S (sb l))%nat with 2%nat by (unfold sb, tb; lia).
    replace (tb l - sa l)%nat with 3%nat by (unfold sa, tb; lia).
    replace (S (tb l) - S (tb l))%nat with 0%nat by (lia). 
    unfold Purify_after_cnot_a_vec.
    unfold Purify_after_cnot_ab_vec.
    assert(16=(2 ^ (S (tb l) - sa l))). unfold tb. unfold sa. 
  replace (S (4 * l + 3) - 4 * l) with 4 by lia.
  reflexivity. destruct H. 
  rewrite (Mscale_mult_dist_r). f_equal.    
    rewrite Mmult_Msum_distr_l. 
    apply big_sum_eq_bounded. intros.
    rewrite Mmult_Msum_distr_l. 
    apply big_sum_eq_bounded. intros.
     rewrite Mscale_mult_dist_r. f_equal. 

     simpl. rewrite Mplus_0_l. 
   repeat  rewrite kron_1_r. 
   rewrite Mmult_plus_distr_r. 
   unfold cnot_on_one. simpl. 

   replace ((Nat.pow (S (S O)) match tb l return nat with
                                               | O => S (tb l)
                                               | S l0 => sub (tb l) l0
                                               end)) with (2).
replace ((2 + (2 + (2 + (2 + 0)))) ) with (4*2) by lia.
                          
   replace ((I 8 ⊗ I 2) ) with ((I 2 ⊗ I 2 ⊗ I 2 ⊗ I 2 )); [ | repeat rewrite id_kron; try reflexivity].
   replace ((I 4) ) with ((I 2 ⊗ I 2 )); [ | repeat rewrite id_kron; try reflexivity].
   
    
   replace ((I 8 ⊗ σx)) with ((I 2 ⊗ I 2 ⊗ (I 2 ⊗ σx))); [ | try repeat rewrite <-kron_assoc; auto_wf; try repeat  rewrite id_kron; try reflexivity ] .
   replace (4) with (2*2); try reflexivity. 
    repeat rewrite kron_assoc; try auto_wf. 
   replace (S (S (S (S (S (S (S (S (S (S (S (S (2 * 2))))))))))))) with (2*(2*(2*2))); try reflexivity. repeat rewrite kron_mixed_product. 
   repeat rewrite Mmult_1_r; [  | auto_wf | auto_wf | auto_wf ]. repeat rewrite Mmult_1_l; [ | auto_wf  ].

  remember ((Base_vec 2 0 × adjoint (Base_vec 2 0))). 
  remember (I 2 ⊗ (Base_vec 2 0 × adjoint (Base_vec 2 0))).
  remember (Base_vec 2 (bit_xor x (idx_a i))). 
  remember (Base_vec 2 (bit_xor x0 x)).
  remember (Base_vec 2 (bit_xor x0 (idx_c i))). 
  remember (Base_vec 2 x). 
  remember (Base_vec 2 1). 

   assert (m4 ⊗ m1 ⊗ m2 ⊗ m3= (@kron (S (S (S (S (mul (S (S O)) (S (S O))))))) (S O) (S (S O)) (S O)
           (@kron (mul (S (S O)) (S (S O))) (S O) (S (S O)) (S O) (@kron (S (S O)) (S O) (S (S O)) (S O) m4 m1) m2) m3)).
  reflexivity. rewrite <- H1.  repeat  rewrite (kron_assoc ); try apply WF_kron; try reflexivity; try auto_wf; try purify_wf_1.

 replace ((@kron (S (S O)) (S (S O)) (mul (S (S O)) (S (S O))) (mul (S (S O)) (S (S O))) m
         (@kron (S (S O)) (S (S O)) (S (S O)) (S (S O)) (I (S (S O))) (I (S (S O)))))) with ((m ⊗ (I 2 ⊗ I 2))) by reflexivity.
    
   assert((@Mmult (mul (S (S O)) (mul (S (S O)) (mul (S (S O)) (S (S O)))))(mul (S (S O)) (mul (S (S O)) (mul (S (S O)) (S (S O))))) (S O) (I 2 ⊗ (m ⊗ (I 2 ⊗ I 2)))
        (m4 ⊗ (m1 ⊗ (m2 ⊗ m3))))= I 2 ⊗ (m ⊗ (I 2 ⊗ I 2)) × (m4 ⊗ ((m1 ⊗ (m2 ⊗ m3)))) ). reflexivity. rewrite H2.
           
   assert((@Mmult (mul (S (S O)) (mul (S (S O)) (mul (S (S O)) (S (S O)))))
        (mul (S (S O)) (mul (S (S O)) (mul (S (S O)) (S (S O))))) (S O) (I 2 ⊗ (m5 × (m5) † ⊗ (I 2 ⊗ σx)))
        (m4 ⊗ (m1 ⊗ (m2 ⊗ m3))))= (I 2 ⊗ (m5 × (m5) † ⊗ (I 2 ⊗ σx))) × (m4 ⊗ ((m1 ⊗ (m2 ⊗ m3)))) ). reflexivity. rewrite H3.


    repeat rewrite kron_mixed_product. rewrite Heqm. rewrite Heqm1. rewrite Heqm2.  rewrite Heqm3. rewrite Heqm4.  rewrite Heqm5. 

     repeat  rewrite Mmult_1_l; try auto_wf; [ | purify_wf_1 | purify_wf_1 ].

   assert((bit_xor x (idx_a i))=0 \/ (bit_xor x (idx_a i))=1).
   assert (bit_xor x (idx_a i)<2). unfold bit_xor. unfold bit.
   apply Nat.mod_upper_bound. lia. lia. 
  
   destruct H4; rewrite H4; Msimpl; repeat  rewrite Mmult_assoc; rewrite <-base_qubit0; rewrite <-base_qubit1;
  try simpl; try rewrite base_inner_1; try rewrite  base_inner_0; unfold c_to_Vector1; Msimpl; try lia.   
  replace ((bit_xor (bit_xor x0 x) (bit_xor (idx_a i) (idx_c i)))) with (bit_xor x0 (idx_c i)). repeat rewrite kron_assoc; try apply WF_kron; try auto_wf; 
  try apply WF_base; unfold bit; try apply Nat.mod_upper_bound; try lia. reflexivity. 
  
  rewrite bit_xor_assoc. f_equal. rewrite<- bit_xor_assoc.
  rewrite H4. rewrite bit_xor_0_l. unfold idx_c. rewrite bit_id. reflexivity. 
 
   repeat rewrite kron_assoc; purify_wf_1. f_equal. f_equal.
   f_equal. replace ((bit_xor (bit_xor x0 x) (bit_xor (idx_a i) (idx_c i)))) with (bit_xor (bit_xor x0 (idx_c i)) 1). 
   
   assert((bit_xor x0 (idx_c i))=0 \/ (bit_xor x0 (idx_c i)=1)).
    assert (bit_xor x0 (idx_c i)<2). unfold bit_xor. unfold bit.
   apply Nat.mod_upper_bound. lia. lia.
   
    destruct H5; rewrite H5;  solve_matrix.   
    
    rewrite bit_xor_com. rewrite bit_xor_assoc.
    rewrite <- (bit_xor_assoc x). rewrite H4. 
    repeat rewrite <- bit_xor_assoc. f_equal. 
      rewrite bit_xor_com. reflexivity.

  replace (match tb l with
           | 0 => S (tb l)
           | S l0 => tb l - l0
           end) with 1.
  - reflexivity.
  - unfold tb.
    replace (4 * l + 3) with (S (4 * l + 2)) by lia. lia.  
Qed.

Lemma big_sum_2_bit_shift_matrix :
    forall m n (f : nat -> Matrix m n) z,
      z < 2 ->
      big_sum f 2 = big_sum (fun i => f (bit_xor i z)) 2.
Proof.
    intros m n f z Hz.
    assert (Hz01 : z = 0 \/ z = 1) by lia.
    destruct Hz01 as [-> | ->].
    - simpl.
      repeat rewrite bit_xor_0_r.
      reflexivity.
    - simpl.
      unfold bit_xor, bit.
      simpl.
      rewrite Mplus_comm. repeat rewrite Mplus_0_l.
      reflexivity.
Qed.

Lemma Cpow_neg1_mod2 : forall n,
    (((- C1) ^ n)%C = ((- C1) ^ (n mod 2))%C).
Proof.
  intro n.
  replace n with ((2 * (n / 2) + n mod 2)%nat) at 1.
  2:{ symmetry. apply Nat.div_mod. lia. }
  rewrite Cpow_add_r.
  rewrite Cpow_mult_r.
  replace (Coquelicot.Complex.Cpow
             (Coquelicot.Complex.Cpow (- C1) 2) (n / 2)) with C1.
  - lca.
  - change (C1 = (((- C1) ^ 2) ^ (n / 2))%C).
    replace (((- C1) ^ 2)%C) with C1 by (simpl; lca).
    symmetry. apply Cpow_1_l.
Qed.

Lemma Cpow_neg1_bit_eq : forall m n,
    bit m = bit n ->
    (((- C1) ^ m)%C = ((- C1) ^ n)%C).
Proof.
  intros m n H.
  unfold bit in H.
  rewrite Cpow_neg1_mod2.
  rewrite (Cpow_neg1_mod2 n).
  rewrite H.
  reflexivity.
Qed.

Lemma Purify_phase_bit_eq : forall b d x y,
    b < 2 ->
    d < 2 ->
    x < 2 ->
    y < 2 ->
    bit (b * x + d * bit_xor y x) =
    bit (bit d * y + bit (bit_xor b d) * x).
Proof.
  intros b d x y Hb Hd Hx Hy.
  assert (Hb01 : b = 0 \/ b = 1) by lia.
  assert (Hd01 : d = 0 \/ d = 1) by lia.
  assert (Hx01 : x = 0 \/ x = 1) by lia.
  assert (Hy01 : y = 0 \/ y = 1) by lia.
  destruct Hb01 as [-> | ->];
  destruct Hd01 as [-> | ->];
  destruct Hx01 as [-> | ->];
  destruct Hy01 as [-> | ->];
  unfold bit_xor, bit; simpl; reflexivity.
Qed.


Lemma Purify_after_cnot_ab_vec_bell_eq : forall i,
  Bell (idx_a i) (bit_xor (idx_b i) (idx_d i)) ⊗
  Bell (bit_xor (idx_a i) (idx_c i)) (idx_d i)
  = Purify_after_cnot_ab_vec i.
Proof. 
(* 变量代换 r = w xor z 后，将显式二重求和：1/2 · Σ_{z=0}^{1} Σ_{w=0}^{1}
      (-1)^{(idx_b i) z + (idx_d i) w}
      | z > ⊗ | z ⊕ idx_a i >
            ⊗ | w ⊕ z >
            ⊗ | w ⊕ z ⊕ idx_a i ⊕ idx_c i > 重写成
     |beta_{a,b xor d}>_s ⊗ |beta_{a xor c,d}>_t. *)
intros. unfold Bell. 
       unfold Purify_after_cnot_ab_vec.
       rewrite Mscale_kron_dist_r.
       rewrite Mscale_kron_dist_l. 
       rewrite Mscale_assoc.  f_equal.
        rewrite <- RtoC_inv by apply sqrt2_neq_0.
  rewrite <- RtoC_mult.
  f_equal.
  field_simplify; try apply sqrt2_neq_0. simpl.
  rewrite <-Rmult_assoc.
  rewrite sqrt_def; lra.  
       rewrite kron_Msum_distr_r.  
       apply big_sum_eq_bounded.  intros.   
    rewrite kron_Msum_distr_l. 
    symmetry. 
    remember ((fun w : nat => (- C1) ^ ((idx_b i) * x) *
          (- C1) ^ ((idx_d i) * (bit_xor w x)) .* (Base_vec 2 x
              ⊗ Base_vec 2 (bit_xor x (idx_a i))
              ⊗ Base_vec 2 w
              ⊗ Base_vec 2 (bit_xor w (bit_xor (idx_a i) (idx_c i)))))).
    rewrite (big_sum_eq_bounded _ (fun w => m (bit_xor w x)) _ ). 
  rewrite <-big_sum_2_bit_shift_matrix; try auto.  rewrite Heqm.
  apply big_sum_eq_bounded. intros. 
    rewrite Mscale_kron_dist_r. 
    rewrite Mscale_kron_dist_l. 
    rewrite Mscale_assoc. 
    f_equal.
   
   repeat rewrite <- Cpow_add.
   apply Cpow_neg1_bit_eq.
   apply Purify_phase_bit_eq; try assumption;
   unfold idx_b, idx_d, bit; apply Nat.mod_upper_bound; lia.
    
    rewrite kron_assoc; purify_wf_1.  reflexivity.  
    
    intros. rewrite Heqm.  replace (bit_xor (bit_xor x0 x) x) with (x0).
    reflexivity.
    
    rewrite bit_xor_assoc. rewrite (bit_xor_eq_0 x); try reflexivity; try rewrite bit_xor_0_r; unfold bit; try rewrite Nat.mod_small; try lia.
Qed.


Lemma Bell_Pure_State_Vector : forall a b,
  Pure_State_Vector (Bell a b).
Proof.
  intros a b.
  unfold Pure_State_Vector, Bell.
  split.
  - apply WF_scale. apply WF_Msum. intros. 
    + apply WF_scale. try apply WF_kron; try auto_wf; 
  try apply WF_base; unfold bit_xor, bit; try apply Nat.mod_upper_bound; try lia.
  assert (Ha : bit a = 0 \/ bit a = 1).
  { assert (bit a < 2) by (unfold bit; apply Nat.mod_upper_bound; lia).
    lia. }
  assert (Hb : bit b = 0 \/ bit b = 1).
  { assert (bit b < 2) by (unfold bit; apply Nat.mod_upper_bound; lia).
    lia. }
  destruct Ha as [Ha | Ha]; destruct Hb as [Hb | Hb].
  all: 
   simpl; rewrite Mplus_0_l;
    repeat rewrite bit_xor_0_l;
    repeat rewrite bit_xor_1_l;
    repeat rewrite Ha;
    repeat rewrite Hb;
    repeat change (bit 0) with 0;
    repeat change (bit 1) with 1;
    rewrite Mscale_adj;
    rewrite Mplus_adjoint;
    rewrite Mscale_mult_dist_r;
    rewrite Mscale_mult_dist_l;
    rewrite Mscale_assoc;
    rewrite Mmult_plus_distr_l;
    repeat rewrite Mmult_plus_distr_r;
    repeat rewrite Mscale_mult_dist_l;
    repeat rewrite Mscale_mult_dist_r;
    repeat rewrite Mscale_adj;
    repeat rewrite Mscale_mult_dist_l;
    repeat rewrite Mscale_mult_dist_r;
    repeat rewrite Mscale_assoc;
    Msimpl;
    repeat rewrite <- RtoC_inv by apply sqrt2_neq_0;
    rewrite Cconj_R;
    rewrite <- RtoC_mult;
    rewrite <- Rinv_mult_distr_depr; try apply sqrt2_neq_0; try lra;
    replace (√ 2 * √ 2)%R with 2%R by (rewrite sqrt_def; lra);
    Msimpl;
    solve_matrix.
Qed.


Lemma Purify_branch_cnot_b_correct : forall l i,
  {{ Purify_after_cnot_a l i }}
    <{ cnot_on_one [[(sb l) (S (sb l))]] [[(tb l) (S (tb l))]] }>
  {{ Purify_after_cnot_ab l i }}.
Proof.
  (* 论文中的第二步：对两个 Bell 对的第二个 qubit 做 bilateral CNOT。
     该步得到 retained source pair 的相位指标 b xor d。 *)
  intros l i.
  eapply rule_conseq
    with (P' := Purify_after_cnot_a l i)
         (Q' := Purify_after_cnot_ab_raw l i).
  - (* 使用 QUnit_Ctrl 规则处理第二个 CNOT。 *)
    unfold Purify_after_cnot_a.
    unfold Purify_after_cnot_ab_raw.
    apply rule_QUnit_Ctrl.
    unfold sa, sb, tb. lia.
  - apply implies_refl.
  - (* 将 raw 4-qubit 后置先改写成显式向量，再拆成两个 Bell 断言。 *)
    unfold Purify_after_cnot_ab_raw.
    unfold Purify_after_cnot_ab.
    rewrite Purify_after_cnot_ab_vec_raw_eq.
    rewrite <- Purify_after_cnot_ab_vec_bell_eq.
    replace (S (sb l)) with (ta l) by (unfold sb, ta; lia).
    replace (Bell (idx_a i) (bit_xor (idx_b i) (idx_d i)) ⊗
             Bell (bit_xor (idx_a i) (idx_c i)) (idx_d i))
      with (@kron (2 ^ (ta l - sa l)) 1 (2 ^ (S (tb l) - ta l)) 1
             (Bell (idx_a i) (bit_xor (idx_b i) (idx_d i)))
             (Bell (bit_xor (idx_a i) (idx_c i)) (idx_d i))).
    eapply implies_trans.
    + apply rule_Separ'.
      * unfold sa, sb, ta, tb. lia.
      * replace (S (tb l) - ta l) with 2 by (unfold ta, tb; lia).
        apply Bell_Pure_State_Vector.
      * replace (ta l - sa l) with 2 by (unfold sa, ta; lia).
        apply Bell_Pure_State_Vector.
    + destruct (rule_odotT
        (QExp_s (sa l) (ta l)
          (Bell (idx_a i) (bit_xor (idx_b i) (idx_d i))))
        (QExp_s (ta l) (S (tb l))
          (Bell (bit_xor (idx_a i) (idx_c i)) (idx_d i)))) as [Hodot _].
      apply Hodot.
    replace (ta l - sa l) with 2 by (unfold sa, ta; lia).
    replace (S (tb l) - ta l) with 2 by (unfold ta, tb; lia).
    reflexivity.
Qed.

(*-----------------------测量 target pair 的第一个 qubit: ta，记录到 x_l--------------------------*)
Definition Purify_meas_x_P (l : nat) (r : nat) : Pure_formula :=
    BEq (AId (cx l)) r.

Definition Purify_after_meas_x (l i: nat) : pro_formula :=
   [((/ 2)%R, Purify_meas_x_P l 0 /\s (| ∣0⟩ ⊗ Base_vec 2 (bit_xor 0 (bit_xor (idx_a i) (idx_c i))) >[ ta l, S (tb l)]));
   ((/ 2)%R, Purify_meas_x_P l 1 /\s (| (- C1) ^ (bit (idx_d i) * 1) .* (∣1⟩ ⊗ Base_vec 2 (bit_xor 1 (bit_xor (idx_a i) (idx_c i)))) >[ta l, S (tb l)]))].

Lemma norm_kron_base2 : forall a b,
    (a < 2)%nat -> (b < 2)%nat ->
    norm (Base_vec 2 a ⊗ Base_vec 2 b) = 1%R.
Proof.
    intros a b Ha Hb.
    rewrite norm_kron.
    rewrite norm_base_1 by assumption.
    rewrite norm_base_1 by assumption.
    lra.
Qed.


Lemma meas_norm0 : forall i,
    norm
      (/ √ 2 .*
        (Base_vec 2 0 ⊗
         Base_vec 2 (bit_xor 0 (bit_xor (idx_a i) (idx_c i))))) = (/ √ 2)%R.
Proof.
    intros i.
    rewrite norm_scale.
    rewrite norm_kron_base2 by (unfold bit_xor, bit; try apply Nat.mod_upper_bound; lia).
    rewrite Cmod_inv.
    try rewrite Cmod_R.
    try rewrite Rabs_right; try (apply sqrt_pos).
    autorewrite with R_db.
    - reflexivity.
    - pose proof (sqrt_pos 2); lra.
    - apply C0_fst_neq. simpl. apply sqrt2_neq_0.
Qed.

Lemma meas_norm1 : forall i,
    norm
      (/ √ 2 * (- C1) ^ idx_d i .*
        (Base_vec 2 1 ⊗
         Base_vec 2 (bit_xor 1 (bit_xor (idx_a i) (idx_c i))))) = (/ √ 2)%R.
Proof.
    intros i.
    rewrite norm_scale.
    rewrite Cmod_mult.
    rewrite Cmod_pow.
    rewrite Cmod_opp.
    rewrite Cmod_1.
    rewrite norm_kron_base2 by (unfold bit_xor, bit; try apply Nat.mod_upper_bound; lia).
    rewrite Cmod_inv.
    try rewrite Cmod_R.
    try rewrite Rabs_right; try (apply sqrt_pos).
    replace (R1 ^ idx_d i)%R with 1%R by (induction (idx_d i); simpl; lra).
    autorewrite with R_db.
    - reflexivity.
    - pose proof (sqrt_pos 2); lra.
    - apply C0_fst_neq. simpl. apply sqrt2_neq_0.
Qed.

  Lemma proj_test_general : forall (r a b : nat) (c : C),
    (r < 2)%nat ->
    (a < 2)%nat ->
    (b < 2)%nat ->
    (Base_vec 2 r × adjoint (Base_vec 2 r) ⊗ I 2) ×
      (Base_vec 2 0 ⊗ Base_vec 2 a .+
       c .* (Base_vec 2 1 ⊗ Base_vec 2 b))
    =
    if r =? 0 then
      Base_vec 2 0 ⊗ Base_vec 2 a
    else
      c .* (Base_vec 2 1 ⊗ Base_vec 2 b).
  Proof.
    intros r a b c Hr Ha Hb.
    destruct r as [|r].
    - destruct a as [|a]; destruct b as [|b];
        try lia;
        repeat rewrite base_qubit0;
        repeat rewrite base_qubit1;
        solve_matrix.
    - destruct r as [|r]; try lia.
      destruct a as [|a]; destruct b as [|b];
        try lia;
        repeat rewrite base_qubit0;
        repeat rewrite base_qubit1;
        solve_matrix.
  Qed.

  Lemma meas_x_proj_norm : forall i j,
  j<2 ->
    norm
      ((Base_vec 2 j × adjoint (Base_vec 2 j) ⊗ I 2)
         × Bell (bit_xor (idx_a i) (idx_c i)) (idx_d i))
    = (/ √ 2)%R.
  Proof.
    intros.
    unfold Bell. simpl.  rewrite Mplus_0_l. rewrite mul_0_r. simpl. rewrite Mscale_1_l. 
    rewrite Mscale_mult_dist_r.
    rewrite (proj_test_general j).
    destruct j. simpl.     
    apply meas_norm0. 
    assert (S j=1). lia. rewrite H0. simpl. 
    rewrite Mscale_assoc. rewrite mul_1_r. 
     rewrite idx_d_bit. 
    apply meas_norm1. lia.    
  all: unfold bit_xor, bit; try apply Nat.mod_upper_bound; lia.  
  Qed.

 Lemma Purify_branch_meas_x_correct : forall l i,
  {{ | Bell (bit_xor (idx_a i) (idx_c i)) (idx_d i) >[ ta l, S (tb l)] }}
    <{ (cx l) :=M [[(ta l) (S (ta l))]] }>
  {{ Purify_after_meas_x l i }}.
Proof.
  (* 论文中的第三步：测量 target pair 的第一个 qubit，记录到 x_l。 *)
   intros.
   eapply rule_conseq_l with  (P' :=
          | Bell (bit_xor (idx_a i) (idx_c i)) (idx_d i) >[ ta l, S (tb l)]
          /\s big_Sand
                (fun r : nat =>
                   PAssn (cx l) (ANum r) (Purify_meas_x_P l r))
                (2 ^ (S (ta l) - ta l))).
      * unfold Purify_meas_x_P.
        apply rule_ConjE.
        split.
        -- apply rule_PT.
        -- apply big_Sand_Assn_true.
           intros r. simpl. unfold not. apply In_empty.
      * eapply rule_conseq_r.
        2: {
          eapply (rule_QMeas
            (ta l) (S (ta l)) (ta l) (S (tb l))
            (Bell (bit_xor (idx_a i) (idx_c i)) (idx_d i))
            (cx l)
            (fun r : nat => Purify_meas_x_P l r)).
          - split; unfold ta, tb; lia.
          - replace (S (tb l) - ta l) with 2 by (unfold ta, tb; lia).
            apply Bell_Pure_State_Vector.
        } replace (S (ta l) - ta l) with 1 by (unfold ta; lia).
  replace (S (tb l) - ta l) with 2 by (unfold ta, tb; lia).
        simpl.  unfold U_v. 
       replace ((ta l - ta l)) with 0 by (unfold ta; lia). repeat  rewrite kron_1_l. 
        replace ((S (tb l) - S (ta l))) with 1 by (unfold ta; unfold tb; lia).  
        replace (S (tb l) - ta l) with 2 by (unfold ta, tb; lia). rewrite(meas_x_proj_norm ) by lia. rewrite meas_x_proj_norm by lia. simpl. 
unfold Bell. simpl. rewrite Mplus_0_l. rewrite mul_0_r. simpl. rewrite Mscale_1_l. 

repeat rewrite Mscale_mult_dist_r.
repeat rewrite Mscale_assoc. repeat rewrite <-RtoC_inv. rewrite <-RtoC_mult.  
autorewrite with R_db. 
repeat rewrite <-Rinv_mult_distr_depr; try (apply sqrt2_neq_0;   lra). autorewrite with R_db; try ( apply sqrt_neq_0_compat;  lra).      

repeat rewrite Mmult_plus_distr_l. repeat   rewrite Mscale_mult_dist_r.
 Msimpl. 
repeat rewrite Mmult_assoc. repeat rewrite <-base_qubit0. repeat rewrite <-base_qubit1. repeat  rewrite base_inner_1; try lia. repeat rewrite base_inner_0; try lia. unfold c_to_Vector1. Msimpl.  apply implies_refl. purify_wf_1. purify_wf_1.

apply Rinv_neq_0_compat. apply sqrt2_neq_0.
apply sqrt2_neq_0.
auto_wf. auto_wf.  
Qed.

(*-----------------------测量 target pair 的第二个 qubit: tb，记录到 y_l--------------------------*)

Definition Purify_after_meas_y (l i: nat) : pro_formula :=
[((/ 2)%R,
     (<{ (AId (cx l)) = (ANum 0) }> /\s
      <{
        (AId (cy l)) =
        (ANum (bit_xor 0 (bit_xor (idx_a i) (idx_c i))))
      }>)
     /\s
     (| ∣0⟩ ⊗
        ∣ bit_xor 0 (bit_xor (idx_a i) (idx_c i)) ⟩_ 2
      >[ ta l, S (tb l)]));

    ((/ 2)%R,
     (<{ (AId (cx l)) = (ANum 1) }> /\s
      <{
        (AId (cy l)) =
        (ANum (bit_xor 1 (bit_xor (idx_a i) (idx_c i))))
      }>)
     /\s
     (| (((- C1) ^ bit (idx_d i)) .*
          (∣1⟩ ⊗
           ∣ bit_xor 1 (bit_xor (idx_a i) (idx_c i)) ⟩_ 2))
      >[ ta l, S (tb l)]))
  ].

Definition Purify_meas_xy_P (l xval yval : nat) : Pure_formula :=
    PBexp <{ (AId (cx l)) = (ANum xval) }> /\p
    PBexp <{ (AId (cy l)) = (ANum yval) }>.



  Lemma proj_second_general : forall (r x y : nat) (c : C),
    (r < 2)%nat ->
    (x < 2)%nat ->
    (y < 2)%nat ->
    (I 2 ⊗ (Base_vec 2 r × adjoint (Base_vec 2 r))) ×
      (c .* (Base_vec 2 x ⊗ Base_vec 2 y))
    =
    if r =? y then
      c .* (Base_vec 2 x ⊗ Base_vec 2 y)
    else
      Zero.
  Proof.
    intros r x0 y0 c Hr Hx Hy.
    assert (Hr01 : r = 0 \/ r = 1) by lia.
    assert (Hx01 : x0 = 0 \/ x0 = 1) by lia.
    assert (Hy01 : y0 = 0 \/ y0 = 1) by lia.
    destruct Hr01 as [Hr01 | Hr01];
    destruct Hx01 as [Hx01 | Hx01];
    destruct Hy01 as [Hy01 | Hy01];
    subst;
    repeat rewrite base_qubit0;
    repeat rewrite base_qubit1;
    solve_matrix.
  Qed.

  Lemma norm_zero_vec4 : norm (@Zero 4 1) = 0%R.
  Proof.
    apply norm_zero_iff_zero.
    auto_wf.
    reflexivity.
  Qed.

  Lemma meas_y_norm_x0 : forall i r,
    (r < 2)%nat ->
    norm
      ((I 2 ⊗ (Base_vec 2 r × adjoint (Base_vec 2 r))) ×
        (∣0⟩ ⊗ Base_vec 2 (bit (bit_xor (idx_a i) (idx_c i)))))
    =
    if r =? bit (bit_xor (idx_a i) (idx_c i)) then 1%R else 0%R.
  Proof.
    intros i r Hr.
    rewrite <- base_qubit0.
    replace (Base_vec 2 0 ⊗ Base_vec 2 (bit (bit_xor (idx_a i) (idx_c i))))
      with (C1 .* (Base_vec 2 0 ⊗ Base_vec 2 (bit (bit_xor (idx_a i) (idx_c i)))))
      by (rewrite Mscale_1_l; reflexivity).
    rewrite proj_second_general by
      (try assumption; unfold bit_xor, bit; try apply Nat.mod_upper_bound; lia).
    destruct (r =? bit (bit_xor (idx_a i) (idx_c i))).
    - rewrite Mscale_1_l.
      rewrite norm_kron_base2 by
        (unfold bit_xor, bit; try apply Nat.mod_upper_bound; lia).
      reflexivity.
    - apply norm_zero_vec4.
  Qed.

  Lemma meas_y_norm_x1 : forall i r,
    (r < 2)%nat ->
    norm
      ((I 2 ⊗ (Base_vec 2 r × adjoint (Base_vec 2 r))) ×
        (((- C1) ^ bit (idx_d i)) .*
          (∣1⟩ ⊗ Base_vec 2 (bit (S (bit (bit_xor (idx_a i) (idx_c i))))))))
    =
    if r =? bit (S (bit (bit_xor (idx_a i) (idx_c i)))) then 1%R else 0%R.
  Proof.
    intros i r Hr.
    rewrite <- base_qubit1.
    rewrite proj_second_general by
      (try assumption; unfold bit_xor, bit; try apply Nat.mod_upper_bound; lia).
    destruct (r =? bit (S (bit (bit_xor (idx_a i) (idx_c i))))).
    - rewrite norm_scale.
      rewrite norm_kron_base2 by
        (unfold bit_xor, bit; try apply Nat.mod_upper_bound; lia).
      rewrite Cmod_pow.
      rewrite Cmod_opp.
      rewrite Cmod_1.
      replace (R1 ^ bit (idx_d i))%R with 1%R
        by (induction (bit (idx_d i)); simpl; lra).
      lra.
    - apply norm_zero_vec4.
  Qed.

Lemma rule_Oplus_l : forall F0 F1, APro [(1%R, F0); (0%R, F1)] ->> F0.
Proof.
    unfold assert_implies; intros.
    assert (Hswap :
      sat_Assert mu (APro [(0%R, F1); (1%R, F0)])).
    {
      change (APro [(0%R, F1); (1%R, F0)])
        with (APro (swap_list [(1%R, F0); (0%R, F1)] 0)).
      apply rule_POplusC.
      exact H.
    }
    apply sat_Pro_State' in Hswap.
    destruct Hswap as [HF0 _].
    exact HF0.
  Qed.

Lemma rule_Oplus_r : forall F0 F1,
    APro [(0%R, F0); (1%R, F1)] ->> F1.
Proof.
    unfold assert_implies; intros.
    apply sat_Pro_State' in H. apply H.
Qed.

Lemma Purify_branch_meas_y_correct : forall l i,
  {{ Purify_after_meas_x l i }}
    <{ (cy l) :=M [[(tb l) (S (tb l))]] }>
  {{ Purify_after_meas_y l i }}.
Proof.
  (* 论文中的第四步：测量 target pair 的第二个 qubit，记录到 y_l。 *)
intros. rewrite <-(pro_npro_swap (Purify_after_meas_x l i)). 
rewrite <-(pro_npro_swap (Purify_after_meas_y l i)).
unfold Purify_after_meas_x. 
unfold Purify_after_meas_y.
eapply rule_sum; simpl;  try lia. 
econstructor. lra. econstructor. lra. econstructor. 

{ econstructor. simpl. split. auto. split. purify_wf_1. 
        unfold ta, tb.
        replace (4 * l + 2) with (S (4 * l + 1)) by lia.
        simpl. 
        match goal with
        | |- 2 ^ ?n = 2 * 2 => replace n with 2 by lia; reflexivity
        | |- 2 ^ ?n = 4 => replace n with 2 by lia; reflexivity
        | |- 4 = 2 ^ ?n => replace n with 2 by lia; reflexivity
        end. 
        unfold ta. unfold tb. lia.
        econstructor. simpl. split. auto. 
        split. replace (2 ^ match ta l with
                             | 0 => S (tb l)
                             | S l0 => tb l - l0
                             end) with (4). apply WF_scale.
        purify_wf_1. 
        unfold ta, tb.
        replace (4 * l + 2) with (S (4 * l + 1)) by lia.
        simpl.
        match goal with
        | |- 2 ^ ?n = 4 => replace n with 2 by lia; reflexivity
        | |- 4 = 2 ^ ?n => replace n with 2 by lia; reflexivity
        end. unfold ta. unfold tb. lia.
        econstructor. } 
econstructor. 
    eapply rule_conseq_r'.
 { eapply rule_conseq_l with (P' :=
      | ∣0⟩ ⊗ Base_vec 2 (bit (bit_xor (idx_a i) (idx_c i)))
      >[ ta l, S (tb l)] /\s big_Sand (fun r : nat =>
                PAssn (cy l) (ANum r)
             (Purify_meas_xy_P l 0 r)) (2 ^ (S (tb l) - tb l))). 
eapply implies_trans.  apply rule_ConjC. apply rule_ConjCon. rewrite bit_xor_0_l. apply implies_refl. 
        replace ((S (tb l) - tb l)) with (1); unfold tb; try lia.  
        simpl. unfold Purify_meas_x_P. unfold Purify_meas_xy_P.
        rule_solve. rewrite c_update_find_not. auto. unfold cx; unfold cy. lia. 
        rewrite c_update_find_eq.  auto. rewrite c_update_find_not. auto. unfold cx; unfold cy. lia.  rewrite c_update_find_eq.  auto.  
eapply rule_QMeas. unfold ta. unfold tb. lia. 
replace (2 ^ (S (tb l) - ta l)) with (2*2).
apply pure_state_vector_kron. rewrite<- base_qubit0. apply Pure_State_Vector_base.
lia.  apply Pure_State_Vector_base. unfold bit. apply Nat.mod_upper_bound. lia. 
 replace (S (tb l) - ta l) with 2 by (unfold ta, tb; lia).
  reflexivity. }
    
2: econstructor. 2: eapply rule_conseq_r'.
2: { eapply rule_conseq_l with
    (P' :=
      | ((- C1) ^ bit (idx_d i)) .*
        (∣1⟩ ⊗ Base_vec 2 (bit (S (bit (bit_xor (idx_a i) (idx_c i))))))
      >[ ta l, S (tb l)]
      /\s big_Sand  (fun r : nat =>
           PAssn (cy l) (ANum r)
             (Purify_meas_xy_P l 1 r))
        (2 ^ (S (tb l) - tb l))). eapply implies_trans.  apply rule_ConjC. apply rule_ConjCon. rewrite bit_xor_1_l. rewrite (Nat.mul_1_r (bit (idx_d i))). apply implies_refl. 
        replace ((S (tb l) - tb l)) with (1); unfold tb; try lia.  
        simpl. unfold Purify_meas_x_P. unfold Purify_meas_xy_P.
        rule_solve. rewrite c_update_find_not. auto. unfold cx; unfold cy. lia. 
        rewrite c_update_find_eq.  auto. rewrite c_update_find_not. auto. unfold cx; unfold cy. lia.  rewrite c_update_find_eq.  auto. 
	   
	eapply rule_QMeas. unfold ta. unfold tb. lia.
	apply norm_1_pure_vec. 
	- replace (2 ^ (S (tb l) - ta l)) with (2*2). apply WF_scale. apply WF_kron; try lia.
	  + rewrite <-base_qubit1. apply WF_base. lia.
	  + apply WF_base. unfold bit. apply Nat.mod_upper_bound. lia. replace (S (tb l) - ta l) with 2 by (unfold ta, tb; lia).
  reflexivity. 
	- replace (2 ^ (S (tb l) - ta l)) with (2*2).  rewrite norm_scale.
	  rewrite Cmod_pow.
	  rewrite Cmod_opp.
	  rewrite Cmod_1.
	  replace (R1 ^ bit (idx_d i))%R with 1%R
	    by (induction (bit (idx_d i)); simpl; lra). rewrite Rmult_1_l.
      rewrite <-base_qubit1. 
	  rewrite norm_kron_base2 by
	    (unfold bit_xor, bit; try apply Nat.mod_upper_bound; lia).
	  lra. replace (S (tb l) - ta l) with 2 by (unfold ta, tb; lia).
  reflexivity.  }

  3: econstructor.

  all:  replace (S (tb l) - tb l) with 1 by (unfold tb; lia);
  replace (S (tb l) - ta l) with 2 by (unfold ta, tb; lia);
        simpl;  unfold U_v; 
       replace ((S (tb l) - S (tb l))) with 0 by (unfold tb; lia); simpl ((2 ^ 0)); repeat  rewrite kron_1_r;  
        replace ((tb l - ta l)) with 1 by (unfold ta; unfold tb; lia);   
        replace (S (tb l) - ta l) with 2 by (unfold ta, tb; lia); simpl;
       
        repeat rewrite meas_y_norm_x0 by lia;
        repeat rewrite meas_y_norm_x1 by lia. 

        bdestruct (0 =? bit (bit_xor (idx_a i) (idx_c i))).
         rewrite <-H. simpl. 
         repeat rewrite Rmult_0_l.   repeat rewrite Rmult_1_l.  rewrite Rinv_1. repeat rewrite Mscale_1_l. 
         rewrite bit_xor_0_l. rewrite <-H. 
         Msimpl. eapply implies_trans. apply rule_Oplus_l.   
          unfold Purify_meas_xy_P. rewrite <-base_qubit0. rewrite Mmult_assoc. rewrite base_inner_1; try lia. 
          unfold c_to_Vector1. Msimpl. 
         apply rule_ConjCon. apply SAnd_PAnd_eq. apply implies_refl.


           assert(1= bit (bit_xor (idx_a i) (idx_c i))). assert (Hb : bit (bit_xor (idx_a i) (idx_c i)) < 2). { unfold bit. apply Nat.mod_upper_bound. lia. }
  lia.  rewrite <-H0. 
  simpl.  repeat rewrite Rmult_0_l.  repeat rewrite Rmult_1_l.  rewrite Rinv_1. repeat rewrite Mscale_1_l.   rewrite bit_xor_0_l. rewrite <-H0.    Msimpl. eapply implies_trans. apply rule_Oplus_r.   
          unfold Purify_meas_xy_P. rewrite <-base_qubit1. rewrite Mmult_assoc. rewrite base_inner_1; try lia. 
          unfold c_to_Vector1. Msimpl. 
         apply rule_ConjCon. apply SAnd_PAnd_eq. apply implies_refl.
         
         
          bdestruct (0 =? bit (bit_xor (idx_a i) (idx_c i))).
          rewrite <-H. simpl.  
          repeat rewrite Rmult_0_l.   repeat rewrite Rmult_1_l.  rewrite Rinv_1. repeat rewrite Mscale_1_l.  
         rewrite bit_xor_1_l. rewrite <-H.  assert (bit 1=1). unfold bit. simpl. reflexivity. rewrite H0. 
        repeat  rewrite Mscale_mult_dist_r. 
         Msimpl.  eapply implies_trans. apply rule_Oplus_r.    
          unfold Purify_meas_xy_P. rewrite <-base_qubit1. rewrite Mmult_assoc. rewrite base_inner_1; try lia. 
          unfold c_to_Vector1. Msimpl. 
         apply rule_ConjCon. apply SAnd_PAnd_eq. apply implies_refl. 

           assert(1= bit (bit_xor (idx_a i) (idx_c i))). assert (Hb : bit (bit_xor (idx_a i) (idx_c i)) < 2). { unfold bit. apply Nat.mod_upper_bound. lia. }
  lia.  rewrite <-H0.  
  simpl. repeat rewrite Rmult_0_l.   repeat rewrite Rmult_1_l.  rewrite Rinv_1. repeat rewrite Mscale_1_l.  
         rewrite bit_xor_1_l. rewrite <-H0.  assert (bit 2=0). unfold bit. simpl. reflexivity. rewrite H1. 
        repeat  rewrite Mscale_mult_dist_r. 
         Msimpl.  eapply implies_trans. apply rule_Oplus_l.    
          unfold Purify_meas_xy_P. rewrite <-base_qubit0. rewrite Mmult_assoc. rewrite base_inner_1; try lia. 
          unfold c_to_Vector1. Msimpl. 
         apply rule_ConjCon. apply SAnd_PAnd_eq. apply implies_refl.      
Qed.


(*---------------------------------------------证明if语句的正确性--------------------------------------------*)

Definition  Purify_after_cond (l i:nat):= 
<{ (AId (cv l)) = (one_if_eq (idx_a i) (idx_c i)) }>.

Lemma Purify_branch_set_v_correct : forall l i,
  {{ Purify_after_meas_y l i }}
    <{ if (AId (cx l)) = (AId (cy l)) then
         (cv l) := 1
       else
         (cv l) := 0
       end }>
  {{ Purify_after_cond l i }}.
Proof.
  (* 论文中的第五步：由测量结果的等同性设置 v_l。
     这里对应证明 x_l = y_l 当且仅当 idx_a i = idx_c i。 *)
     intros.
      eapply rule_conseq_r'. 
        rewrite <-(pro_npro_swap (Purify_after_meas_y l i)). unfold Purify_after_meas_y.  
        eapply rule_sum with (nF2:= [ SPure <{ (AId (cv l)) = (one_if_eq (idx_a i) (idx_c i)) }>; ( SPure <{ (AId (cv l)) = (one_if_eq (idx_a i) (idx_c i)) }>)]); simpl; try reflexivity. econstructor. lra. econstructor. lra. econstructor.  econstructor; [| econstructor]; simpl; auto.
        econstructor.  eapply rule_cond_classic'. simpl. auto.
        split. 
        
        eapply rule_conseq. eapply rule_PAssgn  with (P:= <{ (AId (cv l)) = 1 }> /\p <{ 1 = (one_if_eq (idx_a i) (idx_c i)) }>).
        
         classic_slove_aux. unfold one_if_eq. bdestruct( (idx_a i) =? (idx_c i)).  rewrite H in *. rewrite Nat.eqb_refl in *. auto. 
         replace (bit (idx_a i) =? bit (idx_c i)) with false. apply bit_xor_neq_1 in H; unfold bit; try apply bit_id.   rewrite H in H3. rewrite bit_xor_neq_1 in H3; try unfold bit; try reflexivity; try lia. 

        destruct (c_find (cx l) x =? 0) eqn:Hx;
    simpl in H0; try contradiction.
  destruct (c_find (cy l) x =? 1) eqn:Hy;
    simpl in H3; try contradiction.
  destruct (c_find (cx l) x =? c_find (cy l) x) eqn:Hxy;
    simpl in H1; try contradiction.
  apply Nat.eqb_eq in Hx.
  apply Nat.eqb_eq in Hy.
  apply Nat.eqb_eq in Hxy.
  rewrite Hx in Hxy.
  rewrite Hy in Hxy.
  lia. symmetry.
        apply Nat.eqb_neq.
        intro Heq.
         apply H.  replace (idx_a i) with (bit (idx_a i));replace (idx_c i) with (bit (idx_c i)); auto; unfold bit; try apply bit_id.
         
          classic_slove_aux. rewrite <-H1. auto.   
         
       
        eapply rule_conseq. eapply rule_PAssgn  with (P:= <{ (AId (cv l)) = 0 }> /\p <{ 0 = (one_if_eq (idx_a i) (idx_c i)) }>). 
        
        
        classic_slove_aux. unfold one_if_eq. bdestruct( (idx_a i) =? (idx_c i)).  rewrite H in *. rewrite Nat.eqb_refl in *. rewrite (bit_xor_eq_0 ((idx_c i)) ) in H3; try unfold bit; try apply bit_xor_eq_0; try apply bit_id; try reflexivity. rewrite bit_xor_eq_0 in H3; unfold bit; simpl; try lia.    

  destruct (c_find (cx l) x =? 0) eqn:Hx;
    simpl in H0; try contradiction;
  destruct (c_find (cy l) x =? 0) eqn:Hy;
    simpl in H3; try contradiction;
  destruct (c_find (cx l) x =? c_find (cy l) x) eqn:Hxy;
    simpl in H1; try contradiction;
  apply Nat.eqb_eq in Hx.
  apply Nat.eqb_eq in Hy.
  apply Nat.eqb_neq in Hxy.
  apply Hxy.
  rewrite Hx, Hy.
  reflexivity. 

        replace (bit (idx_a i) =? bit (idx_c i)) with false. auto.  symmetry.
        apply Nat.eqb_neq.
        intro Heq.
         apply H.  replace (idx_a i) with (bit (idx_a i));replace (idx_c i) with (bit (idx_c i)); auto; unfold bit; try apply bit_id.  
  
         classic_slove_aux. rewrite <-H1. auto.

        econstructor.  eapply rule_cond_classic' with (F2:= <{ (AId (cv l)) = (one_if_eq (idx_a i) (idx_c i)) }>). simpl. auto.
        split. 
        
        eapply rule_conseq. eapply rule_PAssgn  with (P:= <{ (AId (cv l)) = 1 }> /\p <{ 1 = (one_if_eq (idx_a i) (idx_c i)) }>). 
        
        classic_slove_aux. unfold one_if_eq. bdestruct( (idx_a i) =? (idx_c i)).  rewrite H in *. rewrite Nat.eqb_refl in *. auto. 
         replace (bit (idx_a i) =? bit (idx_c i)) with false. apply bit_xor_neq_1 in H; unfold bit; try apply bit_id.   rewrite H in H3. rewrite bit_xor_eq_0 in H3; try unfold bit; try reflexivity.   
        destruct (c_find (cx l) x =? 1) eqn:Hx; simpl in H0; try contradiction;
        destruct (c_find (cy l) x =? 0) eqn:Hy; simpl in H3; try contradiction;
        destruct (c_find (cx l) x =? c_find (cy l) x) eqn:Hxy; simpl in H1; try contradiction; apply Nat.eqb_eq in Hx; apply Nat.eqb_eq in Hy;
        apply Nat.eqb_eq in Hxy;
        lia. symmetry.
        apply Nat.eqb_neq.
        intro Heq.
         apply H.  replace (idx_a i) with (bit (idx_a i));replace (idx_c i) with (bit (idx_c i)); auto; unfold bit; try apply bit_id. 
  
         classic_slove_aux. rewrite <-H1. auto.  
      
        eapply rule_conseq. eapply rule_PAssgn   with (P:= <{ (AId (cv l)) = 0 }> /\p <{ 0 = (one_if_eq (idx_a i) (idx_c i)) }>).

        classic_slove_aux. unfold one_if_eq. bdestruct( (idx_a i) =? (idx_c i)).  rewrite H in *. rewrite Nat.eqb_refl in *. rewrite (bit_xor_eq_0 ((idx_c i)) ) in H3; try unfold bit; try apply bit_xor_eq_0; try apply bit_id; try reflexivity. rewrite bit_xor_neq_1 in H3; unfold bit; simpl; try lia.   

  destruct (c_find (cx l) x =? 1) eqn:Hx;
    simpl in H0; try contradiction;
  destruct (c_find (cy l) x =? 1) eqn:Hy;
    simpl in H3; try contradiction;
  destruct (c_find (cx l) x =? c_find (cy l) x) eqn:Hxy;
    simpl in H1; try contradiction;
  apply Nat.eqb_eq in Hx.
  apply Nat.eqb_eq in Hy.
  apply Nat.eqb_neq in Hxy.
  apply Hxy.
  rewrite Hx, Hy.
  reflexivity. 

         replace (bit (idx_a i) =? bit (idx_c i)) with false. auto.  symmetry.
        apply Nat.eqb_neq.
        intro Heq.
         apply H.  replace (idx_a i) with (bit (idx_a i));replace (idx_c i) with (bit (idx_c i)); auto; unfold bit; try apply bit_id.  
  
         classic_slove_aux. rewrite <-H1. auto.
        
        econstructor. 

        simpl. eapply implies_trans. apply rule_OMerg.  lra.
        replace ((/ 2 + / 2)%R) with 1%R by lra. simpl. apply rule_Oplus.   
Qed.

  Lemma min_union_nonempty :
    forall x y,
      ~ NSet.Equal x NSet.empty ->
      ~ NSet.Equal y NSet.empty ->
      option_nat (NSet.min_elt (NSet.union x y)) =
      min (option_nat (NSet.min_elt x))
          (option_nat (NSet.min_elt y)).
  Proof.
    intros x y Hx Hy.
    pose proof (min_union x y) as H.
   apply H; auto.
  Qed.

Theorem Purify_branch_correct (l i: nat) : 
  {{ D_in_branch_i l i }}
    (Purify l) 
  {{ D_out_branch_i l i}}.
Proof.
  unfold Purify.
  (*证明第一个语句：source/target 的第一个 qubit 上做 CNOT。*)
  eapply rule_seq.
  - apply Purify_branch_cnot_a_correct.
  (*证明第二个语句：source/target 的第二个 qubit 上做 CNOT。*)
  - eapply rule_seq.
    + apply Purify_branch_cnot_b_correct. 
      unfold Purify_after_cnot_ab.
      unfold D_out_branch_i. 
      eapply rule_conseq_r.
      eapply implies_trans; [| apply rule_ConjC].  
      apply rule_OdotOP.
      eapply rule_conseq_r. apply rule_OdotC.
      (*使用Qframe规则进行局部推理*)
	      apply rule_qframe'. 
	      { simpl. intros a. split; intros Hin.
	        - apply NSet.inter_1 in Hin. apply In_empty in Hin. contradiction.
	        - apply In_empty in Hin. contradiction. }
	      simpl. unfold sa. unfold sb. lia.  
        repeat split.
        2: {intros Hin. apply NSet.inter_1 in Hin. simpl in Hin.  apply In_empty in Hin. contradiction. }
        2: { intros Hin. apply In_empty in Hin. contradiction. }
        2: {simpl. left.   
        assert (Hmin : NSet.min_elt
            (NSet.union (Qsys_to_Set (ta l) (S (ta l)))
               (NSet.union (Qsys_to_Set (tb l) (S (tb l)))
                  (NSet.union NSet.empty NSet.empty))) = Some (ta l)).
        { apply min_1.
          - intro Hempty. unfold NSet.Empty in Hempty.
            specialize (Hempty (ta l)). apply Hempty.
            apply NSet.union_2.
            apply (proj2 (In_Qsys (S (ta l)) (ta l) (ta l)
              ltac:(unfold ta; lia))). lia.
          - apply NSet.union_2.
            apply (proj2 (In_Qsys (S (ta l)) (ta l) (ta l)
              ltac:(unfold ta; lia))). lia.
          - intros q Hq. apply NSet.union_1 in Hq.
            destruct Hq as [Hq | Hq].
            + pose proof (proj1 (In_Qsys (S (ta l)) (ta l) q
                ltac:(unfold ta; lia)) Hq) as Hr.
              unfold ta in *. lia.
            + apply NSet.union_1 in Hq.
              destruct Hq as [Hq | Hq].
              * pose proof (proj1 (In_Qsys (S (tb l)) (tb l) q
                  ltac:(unfold tb; lia)) Hq) as Hr.
                unfold ta, tb in *. lia.
              * apply NSet.union_1 in Hq.
                destruct Hq as [Hq | Hq]; apply In_empty in Hq; contradiction. } 
        rewrite Hmin. simpl. unfold sb, ta. lia.  }
    (*证明第三个语句：测量 target 第一个 qubit 到 x_l。*)
    + eapply rule_seq. apply Purify_branch_meas_x_correct. 
    (*证明第4个语句：测量 target 第二个 qubit 到 y_l。*)
      eapply rule_seq. apply Purify_branch_meas_y_correct.
    (*最后证明条件分支的正确性*)
     apply Purify_branch_set_v_correct.
Qed.


Lemma bit_lt_2 : forall n, bit n < 2.
Proof.
    intros n. unfold bit.
    apply Nat.mod_upper_bound.
    lia.
Qed.

(*-----------------------------------假设只有一个block的情况---------------------------------------------*)

Lemma D_out_branch_i_WF : forall l i,
  WF_formula (D_out_branch_i l i).
Proof.
  intros l i.
  unfold D_out_branch_i.
  simpl.
  split.
  - split.  
    + eapply WF_Matrix_dim_change.
      * destruct (sa l) eqn:Hsa.
        -- unfold sa in Hsa.
           assert (l = 0) by nia.
           subst. simpl. lia.
        -- assert (sb l - n = 2) by (unfold sa, sb in *; lia).
           rewrite H. simpl. lia.
      * simpl. lia.
      * unfold Bell. 
        apply WF_scale. apply WF_Msum. 
        --intros. apply WF_scale.
           apply WF_kron; try lia.
           ++ apply WF_base. lia.
           ++ apply WF_base. apply bit_lt_2.
    + unfold sa, sb. lia.
  - exact Logic.I.
Qed.

Lemma D_out_branch_i_q_range : forall l i q,
  NSet.In q (snd (Free_state (D_out_branch_i l i))) ->
  4 * l <= q < 4 * l + 4.
Proof.
  intros l i q Hq.
  unfold D_out_branch_i in Hq; simpl in Hq.
  apply NSet.union_1 in Hq.
  destruct Hq as [Hq | Hq].
  - assert (sa l < S (sb l)) by (unfold sa, sb; lia).
    pose proof (proj1 (In_Qsys (S (sb l)) (sa l) q H) Hq) as Hrange.
    unfold sa, sb in Hrange. lia.
  - apply In_empty in Hq. contradiction.
Qed.

Lemma D_out_big_odot_q_range : forall eta k q,
  NSet.In q
    (snd (Free_state
      (big_odot (fun l => D_out_branch_i l (eta_l eta l)) k))) ->
  q < 4 * k.
Proof.
  intros eta k.
  induction k; intros q Hq.
  - simpl in Hq. apply In_empty in Hq. contradiction.
  - simpl in Hq.
    apply NSet.union_1 in Hq.
    destruct Hq as [Hq | Hq].
    + apply NSet.union_1 in Hq.
      destruct Hq as [Hq | Hq].
      * assert (sa k < S (sb k)) by (unfold sa, sb; lia).
        pose proof (proj1 (In_Qsys (S (sb k)) (sa k) q H) Hq) as Hrange.
        unfold sa, sb in Hrange. lia.
      * apply In_empty in Hq. contradiction.
    + apply IHk in Hq. lia.
Qed.

Lemma D_m_out_branch_WF : forall l i,
  WF_formula (D_m_out_branch l i).
Proof.
  intros m eta. unfold D_m_out_branch.
  induction m.
  - simpl. exact Logic.I.
  - simpl.
    split.
    + apply D_out_branch_i_WF.
    + split.
      * exact IHm.
      * rewrite empty_Empty.
        unfold NSet.Empty.
        intros q Hq.
        apply NSet.inter_1 in Hq as Hcur.
        apply NSet.inter_2 in Hq as Hprev.
        apply D_out_branch_i_q_range in Hcur.
        apply D_out_big_odot_q_range in Hprev.
        lia.
Unshelve.
all: try exact 0%nat.
Qed.

Theorem Purify_single_correct_aux:
  {{ D_m_in p 1 }}
    (Purify 0) 
  {{ D_m_out p 1}}.
Proof.
  unfold D_m_in. unfold D_m_out. eapply rule_sum_fun. 
  intros. unfold D_m_in_weight. unfold D_in_weight_i. simpl. pose (p_pos) as H0.
  rewrite Rmult_1_l. apply Rmult_gt_0_compat. apply H0. apply H0.
  intros. apply D_m_out_branch_WF.
  
  intros. unfold D_m_in_branch. simpl. unfold D_m_out_branch. simpl. 
  eapply rule_qframe. unfold NSet.Equal; intros a; split; intros Ha.
  - apply NSet.inter_2 in Ha. exact Ha.
  - eapply In_empty in Ha. contradiction. 
  
  simpl. intuition. repeat split.   eapply (Purify_branch_correct).
  - intro Hin. apply NSet.inter_1 in Hin. simpl in Hin. exact Hin.
  - intro Hin. eapply In_empty in Hin. contradiction.
  - simpl. left. lia.
Qed.

Lemma Purify_success_branch_to_post : forall a k,
  (((| Bell a k >[sa 0, S (sb 0)]) /\s <{ (AId (cv 0)) = 1 }>) ⊙ <{ true }>)
  ->> (SPure (BEq (AId (cv 0)) 1) /\s (| Bell a k >[0, 2])).
Proof.
  intros a k.
  eapply implies_trans.
  - apply (proj1 (rule_OdotE _)).
  - unfold sa, sb. simpl. apply rule_ConjC.
Qed.

Lemma Purify_fail_branch_to_post : forall a k,
  (((| Bell a k >[sa 0, S (sb 0)]) /\s <{ (AId (cv 0)) = 0 }>) ⊙ <{ true }>)
  ->> SPure (BEq (AId (cv 0)) 0).
Proof.
  intros a k.
  eapply implies_trans.
  - apply (proj1 (rule_OdotE _)).
  - apply rule_Conj_split_r.
Qed.

Definition Purify_post_success (a k : nat) : State_formula :=
  SPure (BEq (AId (cv 0)) 1) /\s (| Bell a k >[0, 2]).

Definition Purify_post_fail : State_formula :=
  SPure (BEq (AId (cv 0)) 0).

Definition D_m_out_1_standard (p : nat -> nat -> R) : pro_formula :=
  [((p 0%nat 0%nat * p 0%nat 0%nat)%R, Purify_post_success 0 0);
   ((p 0%nat 0%nat * p 0%nat 1%nat)%R, Purify_post_success 0 1);
   ((p 0%nat 0%nat * p 1%nat 0%nat)%R, Purify_post_fail);
   ((p 0%nat 0%nat * p 1%nat 1%nat)%R, Purify_post_fail);
   ((p 0%nat 1%nat * p 0%nat 0%nat)%R, Purify_post_success 0 1);
   ((p 0%nat 1%nat * p 0%nat 1%nat)%R, Purify_post_success 0 0);
   ((p 0%nat 1%nat * p 1%nat 0%nat)%R, Purify_post_fail);
   ((p 0%nat 1%nat * p 1%nat 1%nat)%R, Purify_post_fail);
   ((p 1%nat 0%nat * p 0%nat 0%nat)%R, Purify_post_fail);
   ((p 1%nat 0%nat * p 0%nat 1%nat)%R, Purify_post_fail);
   ((p 1%nat 0%nat * p 1%nat 0%nat)%R, Purify_post_success 1 0);
   ((p 1%nat 0%nat * p 1%nat 1%nat)%R, Purify_post_success 1 1);
   ((p 1%nat 1%nat * p 0%nat 0%nat)%R, Purify_post_fail);
   ((p 1%nat 1%nat * p 0%nat 1%nat)%R, Purify_post_fail);
   ((p 1%nat 1%nat * p 1%nat 0%nat)%R, Purify_post_success 1 1);
   ((p 1%nat 1%nat * p 1%nat 1%nat)%R, Purify_post_success 1 0)].

Lemma p_weight_pos : forall a b c d,
  (0 < p a b * p c d < 1)%R.
Proof.
  intros a b c d.
  pose proof (p_pos a b) as Hab.
  pose proof (p_pos c d) as Hcd.
  nra.
Qed.

Lemma rule_OMerg_cons : forall x (p0 p1 : R) F pF,
  (0 < p0 < 1)%R /\ (0 < p1 < 1)%R ->
  APro (x :: (p0, F) :: (p1, F) :: pF) ->>
  APro (x :: ((p0 + p1)%R, F) :: pF).
Proof.
  intros x p0 p1 F pF Hp.
  eapply implies_trans.
  - apply (rule_POplusC _ 0).
  - simpl.
    eapply implies_trans.
    + apply (rule_POplusC _ 1).
    + simpl.
      eapply implies_trans.
      * apply rule_OMerg. exact Hp.
      * change (APro (x :: ((p0 + p1)%R, F) :: pF))
          with (APro (swap_list (((p0 + p1)%R, F) :: x :: pF) 0)).
        apply (rule_POplusC _ 0).
Qed.

Ltac purify_prob :=
  pose proof (p_pos 0%nat 0%nat) as Hp00;
  pose proof (p_pos 0%nat 1%nat) as Hp01;
  pose proof (p_pos 1%nat 0%nat) as Hp10;
  pose proof (p_pos 1%nat 1%nat) as Hp11;
  pose proof p_sum1 as Hpsum;
  unfold D_post_q, p_fail, p_succ, bit in *;
  simpl in *;
  nra.

Ltac pswap n :=
  eapply implies_trans;
  [ apply (rule_POplusC _ n) | simpl ].

Ltac pmerge_weight :=
  eapply implies_trans;
  [ apply rule_OMerg; split; apply p_weight_pos | simpl ].

Ltac pmerge_prob :=
  eapply implies_trans;
  [ apply rule_OMerg; split; purify_prob | simpl ].

Ltac pmerge_cons_weight :=
  eapply implies_trans;
  [ apply rule_OMerg_cons; split; apply p_weight_pos | simpl ].

Ltac pull_to_second_5 :=
  pswap 4; pswap 3; pswap 2; pswap 1.

Ltac pull_to_second_4 :=
  pswap 3; pswap 2; pswap 1.

Ltac pull_failure_pair :=
  pswap 3; pswap 4; pswap 2; pswap 3;
  pswap 1; pswap 2; pswap 0; pswap 1.

Lemma D_m_out_1_to_D_post :
  D_m_out p 1 ->> D_post p.
Proof.
  unfold D_m_out, D_post.
  unfold D_m_in_weight, D_m_out_branch, D_out_branch_i.
  unfold D_post_weight, D_post_branch.
  unfold one_if_eq, eta_l, D_in_weight_i.
  unfold idx_a, idx_b, idx_c, idx_d, out_a, out_k.
  simpl.
  unfold bit, bit_xor.
  simpl.
  repeat rewrite Rmult_1_l.
  eapply implies_trans with (D1 := APro (D_m_out_1_standard p)).
  - apply rule_OCon''.
    + unfold D_m_out_1_standard, Purify_post_success, Purify_post_fail.
      simpl.
      repeat match goal with
      | |- Forall _ [] => constructor
      | |- Forall _ (_ :: _) =>
          constructor;
          [ simpl; repeat split; try exact I;
            try apply (proj1 (Bell_Pure_State_Vector _ _)); try lia
          | ]
      end.
    + simpl. reflexivity.
    + unfold D_m_out_1_standard, Purify_post_success, Purify_post_fail.
      simpl.
      repeat constructor;
        try apply Purify_success_branch_to_post;
        try apply Purify_fail_branch_to_post.
  - unfold D_m_out_1_standard.
    simpl.
    (* First merge the two successful branches for Bell 0 0. *)
    pull_to_second_5; pmerge_weight.
    (* Merge the two successful branches for Bell 0 1. *)
    pswap 3; pswap 2; pmerge_cons_weight.
    (* Merge the two successful branches for Bell 1 0. *)
    pswap 12; pswap 11; pswap 10; pswap 9;
    pswap 7; pswap 8; pswap 6; pswap 7;
    pswap 5; pswap 6; pswap 4; pswap 5;
    pswap 3; pswap 4; pswap 2; pswap 3;
    pswap 1; pswap 2; pswap 0; pswap 1;
    pmerge_weight.
    (* Merge the two successful branches for Bell 1 1. *)
    pswap 11; pswap 10; pswap 8; pswap 9;
    pswap 7; pswap 8; pswap 6; pswap 7;
    pswap 5; pswap 6; pswap 4; pswap 5;
    pswap 3; pswap 4; pswap 2; pswap 3;
    pswap 1; pswap 2; pswap 0; pswap 1;
    pmerge_weight.
    (* Merge all failure branches. *)
    pull_failure_pair; pmerge_weight.
    pull_to_second_5; pmerge_prob.
    pull_to_second_5; pmerge_prob.
    pull_to_second_5; pmerge_prob.
    pull_to_second_5; pmerge_prob.
    pull_to_second_5; pmerge_prob.
    pull_to_second_5; pmerge_prob.
    (* Reorder the five merged branches into D_post order. *)
    pswap 2; pswap 1; pswap 0;
    pswap 3; pswap 2; pswap 1;
    pswap 3; pswap 2; pswap 3.
    unfold Purify_post_success, Purify_post_fail.
    unfold D_post_q, p_fail, p_succ, bit.
    simpl.
    replace
      (1 -
       ((p 0%nat 0%nat + p 0%nat 1%nat) *
        (p 0%nat 0%nat + p 0%nat 1%nat) +
        (p 1%nat 0%nat + p 1%nat 1%nat) *
        (p 1%nat 0%nat + p 1%nat 1%nat)))%R
      with
      ((((((((p 0%nat 0%nat * p 1%nat 0%nat +
              p 0%nat 0%nat * p 1%nat 1%nat) +
             p 0%nat 1%nat * p 1%nat 0%nat) +
            p 0%nat 1%nat * p 1%nat 1%nat) +
           p 1%nat 0%nat * p 0%nat 0%nat) +
          p 1%nat 0%nat * p 0%nat 1%nat) +
         p 1%nat 1%nat * p 0%nat 0%nat) +
        p 1%nat 1%nat * p 0%nat 1%nat))%R
      by purify_prob.
    apply implies_refl.
Qed.

Theorem Purify_single_correct:
  {{ D_m_in p 1 }}
    (Purify 0) 
  {{ D_post p }}.
Proof.
  eapply rule_conseq_r'.
  - apply Purify_single_correct_aux.
  - apply D_m_out_1_to_D_post.
Qed.

 
(*-----------------------------------------------------------------------*)
(*----------------在有m个block块中，对第k个block纯化的正确性：
 -------------------{𝐹_𝜂 ^(𝑘−1)} 𝐏𝐮𝐫𝐢𝐟𝐲^(𝑘) {𝐹_𝜂 ^(𝑘)})， 由 主定理证明：Purify_F_eta_step给出----*)(*---------------------------------------------------------------------*)

(*先给出一些定义*)
Definition F_eta (eta r m : nat) : State_formula :=
  big_odot (fun l => D_out_branch_i l (eta_l eta l)) r ⊙
  big_odot (fun k => D_in_branch_i (r + k) (eta_l eta (r + k))) (m - r).

  Definition F_eta_step_pre (eta k m : nat) : State_formula :=
    big_odot (fun l => D_out_branch_i l (eta_l eta l)) k ⊙
    D_in_branch_i k (eta_l eta k) ⊙
    big_odot
      (fun j => D_in_branch_i (S k + j) (eta_l eta (S k + j)))
      (m - S k).

Definition F_eta_step_post (eta k m : nat) : State_formula :=
    big_odot (fun l => D_out_branch_i l (eta_l eta l)) k ⊙
    D_out_branch_i k (eta_l eta k) ⊙
    big_odot
      (fun j => D_in_branch_i (S k + j) (eta_l eta (S k + j)))
      (m - S k).

(*-------证明 引理 D_in_big_odot_shift_head， 
该引理用于odot的拆分，
表示 ⨀_{𝓁=1}^{k} 𝐻_{𝜂𝓁}^(𝓁) =  ⨀_{𝓁=1}^{k-1} 𝐻_{𝜂𝓁}^(𝓁) ⊙ 𝐻_{𝜂𝑘}(𝑘),-----------------------------*)

Lemma D_in_branch_i_q_range : forall l i q,
  NSet.In q (snd (Free_state (D_in_branch_i l i))) ->
  4 * l <= q < 4 * l + 4.
Proof.
  intros l i q Hq.
  unfold D_in_branch_i in Hq; simpl in Hq.
  apply NSet.union_1 in Hq.
  destruct Hq as [Hq | Hq].
  - assert (sa l < S (sb l)) by (unfold sa, sb; lia).
    pose proof (proj1 (In_Qsys (S (sb l)) (sa l) q H) Hq) as Hrange.
    unfold sa, sb in Hrange. lia.
  - assert (ta l < S (tb l)) by (unfold ta, tb; lia).
    pose proof (proj1 (In_Qsys (S (tb l)) (ta l) q H) Hq) as Hrange.
    unfold ta, tb in Hrange. lia.
Qed.

Lemma D_in_big_odot_q_range : forall eta k n q,
  NSet.In q
    (snd (Free_state
      (big_odot
        (fun j : nat => D_in_branch_i (S k + j) (eta_l eta (S k + j)))
        n))) ->
  4 * S k <= q < 4 * S k + 4 * n.
Proof.
  intros eta k n.
  induction n; intros q Hq.
  - simpl in Hq. apply In_empty in Hq. contradiction.
  - simpl in Hq.
    apply NSet.union_1 in Hq.
    destruct Hq as [Hq | Hq].
    + change
        (NSet.In q
          (snd (Free_state
            (D_in_branch_i (S k + n) (eta_l eta (S k + n))))))
        in Hq.
      apply D_in_branch_i_q_range in Hq. lia.
    + apply IHn in Hq. lia.
Qed.


Lemma D_in_shift_head_disjoint : forall eta k n,
  NSet.Equal
    (NSet.inter
      (snd (Free_state
        (D_in_branch_i (S (k + n)) (eta_l eta (S (k + n))))))
      (snd (Free_state
        (D_in_branch_i k (eta_l eta k) ⊙
         big_odot
           (fun j : nat => D_in_branch_i (S k + j) (eta_l eta (S k + j)))
           n))))
    NSet.empty.
Proof.
  intros eta k n.
  unfold NSet.Equal.
  intros q; split; intros Hq.
  - apply NSet.inter_1 in Hq as Hhigh.
    apply NSet.inter_2 in Hq as Hright.
    apply D_in_branch_i_q_range in Hhigh.
    simpl in Hright.
    apply NSet.union_1 in Hright.
    destruct Hright as [Hright | Hright].
    + change
        (NSet.In q
          (snd (Free_state (D_in_branch_i k (eta_l eta k)))))
        in Hright.
      apply D_in_branch_i_q_range in Hright. lia.
    + apply D_in_big_odot_q_range in Hright. lia.
  - apply In_empty in Hq. contradiction.
Qed.

Lemma D_in_big_odot_shift_head : forall eta k m,
  k < m ->
  big_odot
    (fun k0 : nat => D_in_branch_i (k + k0) (eta_l eta (k + k0)))
    (m - k)
  ->>
  D_in_branch_i k (eta_l eta k) ⊙
  big_odot
    (fun j : nat => D_in_branch_i (S k + j) (eta_l eta (S k + j)))
    (m - S k).
Proof.
  intros eta k m Hkm.
  replace (m - k) with (S (m - S k)) by lia.
  remember (m - S k) as n.
  clear Hkm m Heqn.
  induction n.
  - simpl. rewrite Nat.add_0_r. apply implies_refl.
  - simpl.
    replace (k + S n) with (S (k + n)) by lia.
    replace (S k + n) with (S (k + n)) by lia. 
    eapply implies_trans.
    + apply rule_OdotCon.
      * apply D_in_shift_head_disjoint.
      * apply implies_refl.
      * apply IHn.
    + apply rule_Odot_swap_left.
Qed.

(*------证明：Purify_F_eta_step（即 主定理{𝐹_𝜂 ^(𝑘−1)} 𝐏𝐮𝐫𝐢𝐟𝐲^(𝑘) {𝐹_𝜂 ^(𝑘)}）中使用Qframe规则需要的边界条件 ----*)

Lemma F_eta_step_pre_disjoint : forall eta k m,
  k < m ->
  NSet.Equal
    (NSet.inter
      (snd (Free_state
        (big_odot (fun l => D_out_branch_i l (eta_l eta l)) k)))
      (snd (Free_state
        (D_in_branch_i k (eta_l eta k) ⊙
         big_odot
           (fun j : nat => D_in_branch_i (S k + j) (eta_l eta (S k + j)))
           (m - S k)))))
    NSet.empty.
Proof.
  intros eta k m Hkm.
  unfold NSet.Equal.
  intros q; split; intros Hq.
  - apply NSet.inter_1 in Hq as Hleft.
    apply NSet.inter_2 in Hq as Hright.
    apply D_out_big_odot_q_range in Hleft.
    simpl in Hright.
    apply NSet.union_1 in Hright.
    destruct Hright as [Hright | Hright].
    + change
        (NSet.In q
          (snd (Free_state (D_in_branch_i k (eta_l eta k)))))
        in Hright.
      apply D_in_branch_i_q_range in Hright. lia.
    + apply D_in_big_odot_q_range in Hright. lia.
  - apply In_empty in Hq. contradiction.
Qed.

Lemma D_in_branch_i_considered : forall l i,
  Considered_Formula (D_in_branch_i l i).
Proof.
  intros l i. unfold D_in_branch_i. simpl.
  unfold sa, sb, ta, tb. lia.
Qed.

Lemma D_out_branch_i_considered : forall l i,
  Considered_Formula (D_out_branch_i l i).
Proof.
  intros l i. unfold D_out_branch_i. simpl.
  unfold sa, sb. lia.
Qed.

Lemma D_out_current_prev_disjoint : forall eta i k,
  i < k ->
  NSet.Equal
    (NSet.inter
      (snd (Free_state (D_out_branch_i k (eta_l eta k))))
      (snd (Free_state (D_out_branch_i i (eta_l eta i)))))
    NSet.empty.
Proof.
  intros eta i k Hik.
  unfold NSet.Equal.
  intros q; split; intros Hq.
  - apply NSet.inter_1 in Hq as Hcur.
    apply NSet.inter_2 in Hq as Hprev.
    apply D_out_branch_i_q_range in Hcur.
    apply D_out_branch_i_q_range in Hprev.
    lia.
  - apply In_empty in Hq. contradiction.
Qed.

Lemma D_out_pairwise_disjoint : forall eta i j k,
  i < k ->
  j < k ->
  i <> j ->
  NSet.Equal
    (NSet.inter
      (snd (Free_state (D_out_branch_i i (eta_l eta i))))
      (snd (Free_state (D_out_branch_i j (eta_l eta j)))))
    NSet.empty.
Proof.
  intros eta i j k Hi Hj Hij.
  unfold NSet.Equal.
  intros q; split; intros Hq.
  - apply NSet.inter_1 in Hq as Hiq.
    apply NSet.inter_2 in Hq as Hjq.
    apply D_out_branch_i_q_range in Hiq.
    apply D_out_branch_i_q_range in Hjq.
    lia.
  - apply In_empty in Hq. contradiction.
Qed.

Lemma Purify_mvar_q_min : forall k,
  option_nat (NSet.min_elt (snd (MVar (Purify k)))) = sa k.
Proof.
  intros k.
  assert (Hrange : forall q,
    NSet.In q (snd (MVar (Purify k))) -> sa k <= q <= tb k).
  { intros q Hq.
    simpl in Hq.
    apply NSet.union_1 in Hq.
    destruct Hq as [Hq | Hq].
    - apply NSet.union_1 in Hq.
      destruct Hq as [Hq | Hq].
      + pose proof (proj1 (In_Qsys (S (sa k)) (sa k) q ltac:(unfold sa; lia)) Hq) as Hr.
        unfold sa, tb in *. lia.
      + pose proof (proj1 (In_Qsys (S (ta k)) (ta k) q ltac:(unfold ta; lia)) Hq) as Hr.
        unfold sa, ta, tb in *. lia.
    - apply NSet.union_1 in Hq.
      destruct Hq as [Hq | Hq].
      + apply NSet.union_1 in Hq.
        destruct Hq as [Hq | Hq].
        * pose proof (proj1 (In_Qsys (S (sb k)) (sb k) q ltac:(unfold sb; lia)) Hq) as Hr.
          unfold sa, sb, tb in *. lia.
        * pose proof (proj1 (In_Qsys (S (tb k)) (tb k) q ltac:(unfold tb; lia)) Hq) as Hr.
          unfold sa, tb in *. lia.
      + apply NSet.union_1 in Hq.
        destruct Hq as [Hq | Hq].
        * pose proof (proj1 (In_Qsys (S (ta k)) (ta k) q ltac:(unfold ta; lia)) Hq) as Hr.
          unfold sa, ta, tb in *. lia.
        * apply NSet.union_1 in Hq.
          destruct Hq as [Hq | Hq].
          -- pose proof (proj1 (In_Qsys (S (tb k)) (tb k) q ltac:(unfold tb; lia)) Hq) as Hr.
             unfold sa, tb in *. lia.
          -- apply NSet.union_1 in Hq.
             destruct Hq as [Hq | Hq]; apply In_empty in Hq; contradiction. }
  assert (Hin : NSet.In (sa k) (snd (MVar (Purify k)))).
  { simpl. apply NSet.union_2. apply NSet.union_2.
    assert (sa k < S (sa k)) by lia.
    apply (proj2 (In_Qsys (S (sa k)) (sa k) (sa k) H)).
    lia. }
  assert (NSet.min_elt (snd (MVar (Purify k))) = Some (sa k)).
  { apply min_1.
    - intro Hempty. unfold NSet.Empty in Hempty.
      specialize (Hempty (sa k)). apply Hempty. exact Hin.
    - exact Hin.
    - intros a Ha. apply Hrange in Ha. lia. }
  rewrite H. reflexivity.
Qed.

Lemma Purify_mvar_q_max : forall k,
  option_nat (NSet.max_elt (snd (MVar (Purify k)))) = tb k.
Proof.
  intros k.
  assert (Hrange : forall q,
    NSet.In q (snd (MVar (Purify k))) -> sa k <= q <= tb k).
  { intros q Hq.
    simpl in Hq.
    apply NSet.union_1 in Hq.
    destruct Hq as [Hq | Hq].
    - apply NSet.union_1 in Hq.
      destruct Hq as [Hq | Hq].
      + pose proof (proj1 (In_Qsys (S (sa k)) (sa k) q ltac:(unfold sa; lia)) Hq) as Hr.
        unfold sa, tb in *. lia.
      + pose proof (proj1 (In_Qsys (S (ta k)) (ta k) q ltac:(unfold ta; lia)) Hq) as Hr.
        unfold sa, ta, tb in *. lia.
    - apply NSet.union_1 in Hq.
      destruct Hq as [Hq | Hq].
      + apply NSet.union_1 in Hq.
        destruct Hq as [Hq | Hq].
        * pose proof (proj1 (In_Qsys (S (sb k)) (sb k) q ltac:(unfold sb; lia)) Hq) as Hr.
          unfold sa, sb, tb in *. lia.
        * pose proof (proj1 (In_Qsys (S (tb k)) (tb k) q ltac:(unfold tb; lia)) Hq) as Hr.
          unfold sa, tb in *. lia.
      + apply NSet.union_1 in Hq.
        destruct Hq as [Hq | Hq].
        * pose proof (proj1 (In_Qsys (S (ta k)) (ta k) q ltac:(unfold ta; lia)) Hq) as Hr.
          unfold sa, ta, tb in *. lia.
        * apply NSet.union_1 in Hq.
          destruct Hq as [Hq | Hq].
          -- pose proof (proj1 (In_Qsys (S (tb k)) (tb k) q ltac:(unfold tb; lia)) Hq) as Hr.
             unfold sa, tb in *. lia.
          -- apply NSet.union_1 in Hq.
             destruct Hq as [Hq | Hq]; apply In_empty in Hq; contradiction. }
  assert (Hin : NSet.In (tb k) (snd (MVar (Purify k)))).
  { simpl. apply NSet.union_3. apply NSet.union_2. apply NSet.union_3.
    assert (tb k < S (tb k)) by lia.
    apply (proj2 (In_Qsys (S (tb k)) (tb k) (tb k) H)).
    lia. }
  assert (NSet.max_elt (snd (MVar (Purify k))) = Some (tb k)).
  { apply max_1.
    - intro Hempty. unfold NSet.Empty in Hempty.
      specialize (Hempty (tb k)). apply Hempty. exact Hin.
    - exact Hin.
    - intros a Ha. apply Hrange in Ha. lia. }
  rewrite H. reflexivity.
Qed.

Lemma D_out_frame_left_of_purify : forall eta i k,
  i < k ->
  snd (option_free (Free_State (D_out_branch_i i (eta_l eta i)))) <=
    option_nat (NSet.min_elt (snd (MVar (Purify k)))) \/
  option_nat (NSet.max_elt (snd (MVar (Purify k)))) <
    fst (option_free (Free_State (D_out_branch_i i (eta_l eta i)))).
Proof.
  intros eta i k Hik.
  left.
  rewrite Purify_mvar_q_min.
  unfold D_out_branch_i. simpl.
  unfold sa, sb. lia.
Qed.

Lemma D_out_branch_i_c_range : forall l i a,
  NSet.In a (fst (Free_state (D_out_branch_i l i))) ->
  a = cv l.
Proof.
  intros l i a H.
  unfold D_out_branch_i in H. simpl in H.
  apply NSet.union_1 in H.
  destruct H as [H | H].
  - apply In_empty in H. contradiction.
  - apply NSet.union_1 in H.
    destruct H as [H | H].
    + destruct (Nat.eq_dec a (cv l)) as [Heq | Hneq].
      * exact Heq.
      * apply NSet.add_3 in H.
        -- apply In_empty in H. contradiction.
        -- intro Heq. apply Hneq. symmetry. exact Heq.
    + apply In_empty in H. contradiction.
Qed.

Lemma Purify_mvar_c_range : forall k a,
  NSet.In a (fst (MVar (Purify k))) ->
  3 * k <= a < 3 * k + 3.
Proof.
  intros k a H.
  simpl in H.
  repeat
    (apply NSet.union_1 in H;
     destruct H as [H | H];
     try (apply In_empty in H; contradiction)).
  - destruct (Nat.eq_dec a (cx k)) as [Heq | Hneq].
    + subst. unfold cx. lia.
    + apply NSet.add_3 in H.
      * apply In_empty in H. contradiction.
      * intro Heq. apply Hneq. symmetry. exact Heq.
  - destruct (Nat.eq_dec a (cy k)) as [Heq | Hneq].
    + subst. unfold cy. lia.
    + apply NSet.add_3 in H.
      * apply In_empty in H. contradiction.
      * intro Heq. apply Hneq. symmetry. exact Heq.
  - destruct (Nat.eq_dec a (cv k)) as [Heq | Hneq].
    + subst. unfold cv. lia.
    + apply NSet.add_3 in H.
      * apply In_empty in H. contradiction.
      * intro Heq. apply Hneq. symmetry. exact Heq.
  - destruct (Nat.eq_dec a (cv k)) as [Heq | Hneq].
    + subst. unfold cv. lia.
    + apply NSet.add_3 in H.
      * apply In_empty in H. contradiction.
      * intro Heq. apply Hneq. symmetry. exact Heq.
Qed.

Lemma D_out_frame_classical_disjoint : forall eta i k,
  i < k ->
  NSet.Equal
    (NSet.inter
      (fst (Free_state (D_out_branch_i i (eta_l eta i))))
      (fst (MVar (Purify k))))
    NSet.empty.
Proof.
  intros eta i k Hik.
  unfold NSet.Equal.
  intros a; split; intros Ha.
  - apply NSet.inter_1 in Ha as Hout.
    apply NSet.inter_2 in Ha as Hmv.
    apply D_out_branch_i_c_range in Hout.
    apply Purify_mvar_c_range in Hmv.
    unfold cv in Hout. subst. lia.
  - apply In_empty in Ha. contradiction.
Qed.

Lemma D_in_tail_considered : forall eta k n,
  Considered_Formula
    (big_odot
      (fun j : nat => D_in_branch_i (S k + j) (eta_l eta (S k + j)))
      n).
Proof.
  assert (Hbranch : forall l i,
    Free_State (D_in_branch_i l i) = Some (sa l, S (tb l))).
  { intros l i. unfold D_in_branch_i. simpl.
    rewrite Nat.min_l by (unfold sa, ta; lia).
    rewrite Nat.max_r by (unfold sb, tb; lia).
    reflexivity. }
  assert (Htail : forall eta k n,
    Free_State
      (big_odot
        (fun j : nat => D_in_branch_i (S k + j) (eta_l eta (S k + j)))
        n) =
    match n with
    | 0 => None
    | S n' => Some (sa (S k), S (tb (S k + n')))
    end).
  { intros eta0 k0 n0. induction n0.
    - reflexivity.
    - cbn [big_odot]. cbn [Free_State].
      rewrite Hbranch. rewrite IHn0.
      destruct n0.
      + simpl. replace (S (k0 + 0)) with (S k0) by lia. reflexivity.
      + cbn [option_beq option_free]. simpl.
        rewrite Nat.min_r by (unfold sa; lia).
        rewrite Nat.max_l by (unfold tb; lia).
        reflexivity. }
  intros eta k n. induction n.
  - simpl. auto.
  - cbn [big_odot]. cbn [Considered_Formula Free_State].
    rewrite Hbranch. rewrite Htail.
    destruct n.
    + simpl. unfold sa, sb, ta, tb. lia.
    + cbn [option_beq option_free]. simpl.
      split.
      * unfold sa, sb, ta, tb. lia.
      * split.
        -- exact IHn.
        -- right. unfold sa, tb. lia.
Qed.

Lemma D_in_tail_classical_disjoint : forall eta k n,
  NSet.Equal
    (NSet.inter
      (fst (Free_state
        (big_odot
          (fun j : nat => D_in_branch_i (S k + j) (eta_l eta (S k + j)))
          n)))
      (fst (MVar (Purify k))))
    NSet.empty.
Proof.
  intros eta k n.
  unfold NSet.Equal.
  intros a; split; intros Ha.
  - apply NSet.inter_1 in Ha as Htail.
    clear Ha.
    induction n.
    + simpl in Htail. apply In_empty in Htail. contradiction.
    + simpl in Htail.
      apply NSet.union_1 in Htail.
      destruct Htail as [Htail | Htail].
      * unfold D_in_branch_i in Htail. simpl in Htail.
        apply NSet.union_1 in Htail.
        destruct Htail as [Htail | Htail];
          apply In_empty in Htail; contradiction.
      * apply IHn in Htail. exact Htail.
  - apply In_empty in Ha. contradiction.
Qed.

Lemma D_in_tail_right_of_purify : forall eta k n,
  snd
    (option_free
      (Free_State
        (big_odot
          (fun j : nat => D_in_branch_i (S k + j) (eta_l eta (S k + j)))
          n))) <= option_nat (NSet.min_elt (snd (MVar (Purify k)))) \/
  option_nat (NSet.max_elt (snd (MVar (Purify k)))) <
  fst
    (option_free
      (Free_State
        (big_odot
          (fun j : nat => D_in_branch_i (S k + j) (eta_l eta (S k + j)))
          n))).
Proof.
  assert (Hbranch : forall l i,
    Free_State (D_in_branch_i l i) = Some (sa l, S (tb l))).
  { intros l i. unfold D_in_branch_i. simpl.
    rewrite Nat.min_l by (unfold sa, ta; lia).
    rewrite Nat.max_r by (unfold sb, tb; lia).
    reflexivity. }
  assert (Htail : forall eta k n,
    Free_State
      (big_odot
        (fun j : nat => D_in_branch_i (S k + j) (eta_l eta (S k + j)))
        n) =
    match n with
    | 0 => None
    | S n' => Some (sa (S k), S (tb (S k + n')))
    end).
  { intros eta0 k0 n0. induction n0.
    - reflexivity.
    - cbn [big_odot]. cbn [Free_State].
      rewrite Hbranch. rewrite IHn0.
      destruct n0.
      + simpl. replace (S (k0 + 0)) with (S k0) by lia. reflexivity.
      + cbn [option_beq option_free]. simpl.
        rewrite Nat.min_r by (unfold sa; lia).
        rewrite Nat.max_l by (unfold tb; lia).
        reflexivity. }
  intros eta k n.
  destruct n.
  - simpl. left. pose proof (Purify_mvar_q_min k). lia.
  - rewrite Htail. right.
    rewrite Purify_mvar_q_max.
    simpl. unfold sa, tb in *. nia.
Qed.

Lemma D_out_with_tail_disjoint : forall eta k m,
  k < m ->
  NSet.Equal
    (NSet.inter
      (snd (Free_state
        (big_odot (fun l : nat => D_out_branch_i l (eta_l eta l)) k ⊙
         D_out_branch_i k (eta_l eta k))))
      (snd (Free_state
        (big_odot
          (fun j : nat => D_in_branch_i (S k + j) (eta_l eta (S k + j)))
          (m - S k)))))
    NSet.empty.
Proof.
  intros eta k m Hkm.
  rewrite empty_Empty.
  unfold NSet.Empty.
  intros q Hq.
  apply NSet.inter_1 in Hq as Hleft.
  apply NSet.inter_2 in Hq as Htail.
  simpl in Hleft.
  apply NSet.union_1 in Hleft.
  apply D_in_big_odot_q_range in Htail.
  destruct Hleft as [Hprev | Hcur].
  - apply D_out_big_odot_q_range in Hprev. lia.
  - apply NSet.union_1 in Hcur.
    destruct Hcur as [Hcur | Hcur].
    + pose proof (proj1 (In_Qsys (S (sb k)) (sa k) q
        ltac:(unfold sa, sb; lia)) Hcur) as Hrange.
      unfold sa, sb in Hrange. lia.
    + apply In_empty in Hcur. contradiction.
Qed.

(* 正式证明 主定理{𝐹_𝜂 ^(𝑘−1)} 𝐏𝐮𝐫𝐢𝐟𝐲^(𝑘) {𝐹_𝜂 ^(𝑘)} ----*)
Theorem Purify_F_eta_step (eta k m : nat) :
  k < m ->
  {{ F_eta eta k m }}
    (Purify k)
  {{ F_eta eta (S k) m }}.
Proof.
  intros Hkm.
  eapply rule_conseq
    with (P' := F_eta_step_pre eta k m)
      (Q' := F_eta_step_post eta k m).
  - unfold F_eta_step_pre. unfold F_eta_step_post.
    eapply rule_qframe.
    + apply D_out_with_tail_disjoint. exact Hkm.
    + apply D_in_tail_considered.
    + split.
      * eapply rule_qframe_big_odot'.
        -- intros i Hi.
           apply D_out_current_prev_disjoint. exact Hi.
        -- intros i j Hi Hj Hij.
           eapply D_out_pairwise_disjoint; eauto.
        -- intros i Hi.
           apply D_out_branch_i_considered.
        -- apply Purify_branch_correct.
        -- intros i Hi.
           apply D_out_frame_classical_disjoint. exact Hi.
        -- intros i Hi.
           apply D_out_frame_left_of_purify. exact Hi.
      * split.
        -- apply D_in_tail_classical_disjoint.
        -- apply D_in_tail_right_of_purify.
  - unfold F_eta. unfold F_eta_step_pre.
    eapply implies_trans.
    + apply rule_OdotCon.
      * apply F_eta_step_pre_disjoint. exact Hkm.
      * apply implies_refl.
      * apply D_in_big_odot_shift_head. exact Hkm.
    + apply rule_OdotA.
  - unfold F_eta_step_post. unfold F_eta.
    simpl. apply rule_Odot_swap_pair_frame.
Qed.

(*----------------------------最后证明m个block块纯化的正确性-------------------------*)

Fixpoint Purify_loop (m : nat) : com :=
  match m with
  | 0 => <{ skip }>
  | S m' => CSeq (Purify_loop m') (Purify m')
  end.

Theorem Purify_loop_prefix_correct : forall m eta r,
    r <= m ->
    {{ F_eta eta 0 m }}
      (Purify_loop r)
    {{ F_eta eta r m }}.
Proof.
    intros m eta r Hr.
    induction r.
    - simpl. apply rule_skip. 
    - simpl.
      eapply rule_seq.
      + apply IHr. lia.
      + apply Purify_F_eta_step. lia.
  Qed.

Lemma big_prod_R_gt_0 : forall (f : nat -> R) m,
  (forall i, i < m -> (0 < f i)%R) ->
  (0 < big_prod_R f m)%R.
Proof.
  intros f m Hpos.
  induction m.
  - simpl. lra.
  - simpl.
    apply Rmult_gt_0_compat.
    + apply IHm. intros i Hi. apply Hpos. lia.
    + apply Hpos. lia.
Qed.


Theorem Purify_loop_correct: forall m, 
  {{ D_m_in p m }}
    (Purify_loop m)
  {{ D_m_out p m }}.
Proof. intros. unfold D_m_in. unfold D_m_out. apply rule_sum_fun.
       pose (p_pos) as H0. intros.  unfold D_m_in_weight. apply big_prod_R_gt_0. intros. 
       unfold D_in_weight_i.  
        apply Rmult_gt_0_compat. apply H0. apply H0. 
       intros. apply D_m_out_branch_WF.
       intros.  eapply rule_conseq 
       with (P' := F_eta i 0 m)
            (Q' := F_eta i m m); try apply Purify_loop_prefix_correct; try lia; unfold D_m_in_branch; unfold D_m_out_branch; unfold F_eta. 
      simpl. eapply implies_trans. apply rule_OdotE. rewrite Nat.sub_0_r. apply rule_OdotC. 
      rewrite (Nat.sub_diag ). simpl. apply rule_OdotE.
Qed.

  
