Require Import Reals.
Require Import Coquelicot.Complex.
Require Import Strings.String.


Require Import Coq.Init.Datatypes.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import Lia.

From Quan Require Import QIMP_L.
From Quan Require Import Matrix.
From Quan Require Import Quantum.
Import Basic.
From Quan Require Import QState_L.
From Quan Require Import QAssert_L.
From Quan Require Import Reduced.
From Quan Require Import Mixed_State.
From Quan Require Import QSepar.
From Quan Require Import Ceval_Prop.

Local Open Scope nat_scope.

Definition assert_implies (P Q : Assertion) : Prop :=
    forall (s e:nat) (mu:dstate s e), sat_Assert  mu P -> sat_Assert  mu Q.
Notation "P ->> Q" := (assert_implies P Q)
    (at level 90) : assert_scope.
Local Open Scope assert_scope.
Notation "P <<->> Q" :=
    ((P ->> Q) /\ (Q ->> P)) (at level 80) : assert_scope.


Local Open Scope com_scope.
Local Open Scope assert_scope.
Local Open Scope nat_scope.
Local Open Scope matrix_scope.

Lemma implies_refl: forall (D:Assertion), D->> D.
Proof. unfold assert_implies. intros. assumption. Qed.

Lemma implies_trans: forall (D D1 D2:Assertion), 
(D->> D1)-> (D1->>D2) 
->(D->>D2).
Proof. unfold assert_implies. intros. auto. Qed.

Lemma implies_trans': forall (D D1 D2:Assertion), 
 (D1->>D2) -> (D->> D1) ->(D->>D2).
Proof.  unfold assert_implies. intros. auto. Qed.


Ltac rule_solve := 
  unfold "->>"; intros; try split; intros;
rewrite sat_Assert_to_State in *;
rewrite seman_find in *;
try match goal with 
H: WF_dstate ?mu /\  WF_formula ?F /\
    (forall x:cstate, d_find x ?mu <> Zero ->?Q)
|-_ => destruct H as [H1 H]; destruct H as [H2 H];
split; try assumption; split; [simpl; simpl in H2; try assumption; try apply H2; auto | intros]
end;
try match goal with 
H1:  forall x:cstate, d_find x ?mu <> Zero ->?Q,
H2: d_find ?x ?mu <> Zero
|- _ =>pose H2 as H2'; apply H1 in H2'; simpl in *
end;
repeat match goal with 
H : ?P/\ ?Q |-_ => destruct H  end;
repeat match goal with 
|- ?P /\?Q =>   split end ;
try auto; try assumption; try lia. 


Theorem rule_PT: forall F:State_formula,
F ->> BTrue.
Proof. rule_solve.  Qed.


Lemma rule_DT: forall D,
D->> <{ true }> .
Proof. unfold assert_implies. intros. rewrite sat_Assert_to_State in *.
apply BTrue_true.  apply WF_sat_Assert in H. assumption.
Qed.


(*Conj*)
Lemma rule_ConjT: forall (F:State_formula),
F ->> F /\s BTrue .
Proof. rule_solve.  Qed.

Lemma  rule_ConjE: forall (F1 F2: State_formula), 
(F2 ->> BTrue) /\ (BTrue ->> F2) ->
F1 ->> F1 /\s F2 .
Proof. unfold assert_implies. intros. apply sat_assert_conj. intuition.
       apply H2. apply rule_PT in H0. assumption.
Qed.

Lemma rule_Conj_split_l: forall (F1 F2:State_formula), F1 /\s F2 ->> F1 .
Proof.  rule_solve. Qed.
Lemma rule_Conj_split_r: forall (F1 F2:State_formula), F1 /\s F2 ->> F2 .
Proof.  rule_solve. Qed. 

Theorem rule_ConjC: forall F1 F2:State_formula,
((F1 /\s F2) <<->> (F2 /\s F1)).
Proof.  rule_solve. Qed.

Theorem rule_ConjCon:forall F1 F2 F3 F4:State_formula,
(F1 ->>F2) -> (F3 ->> F4) ->
(F1 /\s F3) ->> (F2 /\s F4).
Proof. 
 intros.  unfold assert_implies in *.
intros. rewrite sat_assert_conj in *. intuition.
Qed. 

Lemma rule_Conj_two: forall (F1 F2 F: State_formula),
 (F->> F1) ->
 (F ->> F2) ->
(F ->> (F1 /\s F2)).
Proof. unfold assert_implies. intros.   apply sat_assert_conj; split;
       auto.
Qed.


Notation "F1 /\p F2" := (PAnd F1  F2) (at level 80): assert_scope.
Notation "F1 \/p F2" := (POr F1  F2) (at level 80): assert_scope.
Lemma SAnd_PAnd_eq: forall (P1 P2:Pure_formula),
(P1 /\p P2) <<->> (P1 /\s P2).
Proof. rule_solve.
Qed.

#[export] Hint Resolve rule_Conj_split_l rule_Conj_split_r: rea_db.
  

(*Odot*)

  Lemma inter_comm:forall x y,
  NSet.Equal (NSet.inter x y)  (NSet.inter y x) .
  Proof.  unfold NSet.Equal. split; intros;
  apply NSet.inter_3.
   apply NSet.inter_2 with x. apply H. 
  apply NSet.inter_1 with y. apply H. 
  apply NSet.inter_2 with y. apply H.
  apply NSet.inter_1 with x. apply H. 
  Qed.
  
  Lemma inter_union_dist:forall x y z,
  NSet.Equal (NSet.inter x (NSet.union y z)) (NSet.union (NSet.inter x y) (NSet.inter x z)).
  Proof.  unfold NSet.Equal. split. intros.
  assert(NSet.In a x /\ NSet.In a (NSet.union y z)).
  split. apply NSet.inter_1 in H. assumption.
  apply NSet.inter_2 in H. assumption.
  destruct H0.  
  apply NSet.union_1 in H1. destruct H1.
  apply NSet.union_2. apply NSet.inter_3. assumption. assumption.
  apply NSet.union_3. apply NSet.inter_3. assumption. assumption.
  intros. apply NSet.union_1 in H. destruct H.
  apply NSet.inter_3. apply NSet.inter_1 in H. assumption.
  apply NSet.union_2. apply NSet.inter_2 in H. assumption.
  apply NSet.inter_3. apply NSet.inter_1 in H. assumption.
  apply NSet.union_3. apply NSet.inter_2 in H. assumption.
  Qed.
  
  
  Lemma  set_eq_trans: forall x y z,
  NSet.Equal x y ->
  NSet.Equal y z->
  NSet.Equal x z.
  Proof. unfold NSet.Equal; intros. split; intros. 
        apply H0. apply H. assumption.
       apply H. apply H0. assumption. 
  Qed.
  
  
  
  Theorem rule_OdotE: forall F:State_formula,
    (F ⊙ BTrue <<->> F ) .
  Proof. rule_solve;   
        apply inter_empty; right; reflexivity.
  Qed.
  
   Theorem rule_OdotC: forall F1 F2:State_formula,
  ((F1 ⊙ F2) <<->> (F2 ⊙ F1)).
  Proof.  
           rule_solve; try rewrite inter_comm; try assumption.
  Qed.
  

  
  Theorem rule_OdotA: forall F1 F2 F3:State_formula,
  ((F1 ⊙ (F2 ⊙ F3) )<<->>( (F1 ⊙ F2) ⊙ F3) ).
  Proof. rule_solve;
  [ | rewrite inter_comm | rewrite inter_comm | | rewrite inter_comm in H3;rewrite inter_comm   | rewrite inter_comm in H3  | rewrite inter_comm in H3 |rewrite inter_comm in H3; rewrite inter_comm  ]; 
  try rewrite inter_union_dist in *;
  try rewrite union_empty in *; try apply H3; try assumption.
  split; rewrite inter_comm; intuition. 
  split; rewrite inter_comm; intuition.
  split;[ | rewrite inter_comm]; intuition.
  split;[ | rewrite inter_comm]; intuition.  
Qed.




  Theorem rule_OdotO: forall (P1 P2:Pure_formula), 
   ((P1 ⊙ P2) <<->> (P1 /\p P2)) .
  Proof.  rule_solve;  apply inter_empty; intuition.
  Qed.

  Theorem rule_OdotO': forall (F1 F2:State_formula), 
 ((F1 ⊙ F2) ->> (F1 /\s F2)) .
Proof.  rule_solve. Qed.
  
  Theorem rule_OdotOP: forall (P:Pure_formula) (F:State_formula),
  ((P ⊙ F) <<->> (P /\s F)).
  Proof.   rule_solve; apply inter_empty;  intuition.
  Qed.
  
  Theorem rule_OdotOA: forall (P:Pure_formula) (F1 F2:State_formula),
  ((P /\s (F1 ⊙ F2)) <<->> ((P /\s F1) ⊙ (P /\s F2))).
  Proof.  rule_solve. Qed.
  
  
  
  Theorem rule_OdotOC: forall (F1 F2 F3:State_formula), 
  ((F1 ⊙(F2 /\s F3)) <<->> ((F1 ⊙ F2) /\s (F1 ⊙ F3))).
  Proof. rule_solve;
  try rewrite inter_union_dist in H3;
  try rewrite union_empty in H3 ; try apply H3;
  try rewrite inter_union_dist ;
  try rewrite union_empty; try split; try assumption. 
  Qed.
  
  Notation "| v >[ s , e ]" := (QExp_s s e v) (at level 80) :assert_scope.

  Local Open Scope assert_scope.
  Theorem  rule_ReArr:forall (s e  s' e':nat)  v u,
  ((| v >[ s , e ]) ⊗* (| u >[ s' , e' ]) ->>(| u >[ s' , e' ]) ⊗* (| v >[ s , e ])).
  Proof.  rule_solve;  rewrite inter_comm; assumption. 
  Qed.


Lemma WF_dstate_per_state{ s e:nat}: forall  (x:cstate ) (mu:dstate s e),
(d_find x mu) <>Zero -> (WF_dstate mu -> WF_state (x, (d_find x mu))) .
Proof. intros x (mu, IHmu0). induction mu. 
       simpl. intuition.
       destruct a.
       unfold WF_dstate.
       unfold d_find. unfold StateMap.find.
       simpl. intros. 
      inversion_clear H0. 
       destruct (Cstate_as_OT.compare x c).
       simpl. simpl in H. destruct H. 
       reflexivity.
       simpl. 
       assumption.
       unfold d_find in IHmu.
       unfold StateMap.find in IHmu.
       inversion_clear IHmu0.
       unfold WF_dstate in IHmu.
       unfold d_trace in IHmu.
       simpl in IHmu.
       apply IHmu in H0.
       assumption.
       assumption.
       assumption.
Qed.
  
Local Open Scope nat_scope.
  Theorem  rule_Separ:forall s x e u v, 
  ((| v >[ s , x ]) ⊗* (| u >[ x , e ])) ->>
  ( (| v ⊗ u >[ s , e ])).
  Proof.  rule_solve. auto_wf.  
   assert( (2 ^ (x - s)) * (2 ^ (e - x)) = 2^(e-s)).
  type_sovle'. destruct H18.  
   apply (@pure_state_vector_kron 
  (2 ^ (x - s)) (2 ^ (e - x)) ). intuition. intuition.
  assert(WF_qstate (d_find x0 mu)).
  apply WF_dstate_per_state; try assumption.  
  remember (((R1 / Cmod (trace (d_find x0 mu)))%R .* d_find x0 mu)).
  remember (Reduced m s e).
  assert( WF_qstate q). rewrite Heqq. apply WF_qstate_Reduced; try lia; 
  try assumption. rewrite Heqm. 
  rewrite Rdiv_unfold. rewrite Rmult_1_l.
  split; try lia. apply nz_Mixed_State_aux_to01.
  apply nz_Mixed_State_aux_to_nz_Mix_State.  apply H18. 
  pose (@qstate_Separ_pure' s e q x). 
  assert((Reduced q s x) = (Reduced m s x)).
  rewrite Heqq. rewrite Reduced_assoc; try lia; try assumption.
  reflexivity. 
  assert((Reduced q x e) = (Reduced m x e)).
  rewrite Heqq. rewrite Reduced_assoc; try lia; try assumption.
  reflexivity.
  assert(q= (@trace (2^(e-s)) q) .* @kron (2^(x-s)) (2^(x-s)) (2^(e-x)) (2^(e-x)) 
  (/(@trace (2^(x-s)) ((Reduced q s x))) .* (Reduced q s x))
  (/(@trace (2^(e-x)) ((Reduced q x e))) .* (Reduced q x e))).
  rewrite <-e1; try lia; try assumption.  
  rewrite Mscale_assoc. rewrite Cinv_r. rewrite Mscale_1_l. reflexivity.
  apply C0_fst_neq. apply Rgt_neq_0.
  apply nz_mixed_state_trace_gt0. apply H19.
  left. econstructor. exists (outer_product v v).
  assert( 0<R1<=1)%R. lra.  
  split. apply H22. split. econstructor. split.
  apply H4. unfold outer_product. reflexivity.
  rewrite Mscale_1_l.  
   rewrite H20. apply H13. 
  rewrite H22. rewrite H20. rewrite H21. 
  rewrite H13. rewrite H9.
  assert((@trace (2^(e-s)) q)= C1).
  rewrite Heqq. rewrite Heqm. 
  rewrite Reduced_trace; try lia.
  rewrite Rdiv_unfold. rewrite Rmult_1_l.
  rewrite trace_mult_dist.
  assert(@trace (2^(e0-s0)) (d_find x0 mu) = (fst (@trace (2^(e0-s0)) (d_find x0 mu)), snd (@trace (2^(e0-s0)) (d_find x0 mu)))).
  destruct (@trace (2^(e0-s0)) (d_find x0 mu)). simpl. reflexivity.
  rewrite H23. rewrite nz_mixed_state_trace_real; try apply H18.
  rewrite Cmod_snd_0; try simpl; try apply nz_mixed_state_trace_gt0;
  try apply nz_mixed_state_trace_real; try apply H18; try reflexivity.
  rewrite RtoC_inv;  try apply C0_fst_neq; try apply Rgt_neq_0;
  try apply nz_mixed_state_trace_gt0; try apply H18.
  rewrite Cinv_l; try apply C0_fst_neq; try apply Rgt_neq_0;
  try apply nz_mixed_state_trace_gt0; try apply H18. reflexivity.
  auto_wf. rewrite H23. Msimpl.
  unfold outer_product.    rewrite trace_mult.
  destruct H4. rewrite H24.
  rewrite trace_mult. 
  destruct H5. rewrite H25.
  repeat rewrite trace_I.
  rewrite <-RtoC_inv; try lra. rewrite Rinv_1. 
  Msimpl. rewrite <-kron_mixed_product.
  reflexivity. 
Qed.

Import Mixed_State.
Local Open Scope nat_scope.


Theorem  rule_Separ':forall s x e u v, 
 s<x/\x<e-> Pure_State_Vector u -> Pure_State_Vector v ->
(( (| v ⊗ u >[ s , e ])) ->>
((| v >[ s , x ]) ⊗* (| u >[ x , e ]))).
Proof. rule_solve.
simpl in *. split. split; try lia. apply H1. split. split; auto.
apply H0.
apply Qsys_inter_empty'; try lia.     
intros. pose H6. 
apply H4 in n. simpl in *.
split. unfold NSet.Equal.  intros. split. 
intros. pose H7. apply NSet.inter_1 in i. 
apply NSet.inter_2 in H7. apply In_Qsys in H7; try lia.  
apply In_Qsys in i; try lia.  intros. 
apply In_empty in H7. destruct H7. 
remember (((R1 / Cmod (trace (d_find x0 mu)))%R .* d_find x0 mu)).
remember (Reduced m s e).
assert( WF_qstate (d_find x0 mu)). apply WF_dstate_per_state; try assumption.
assert( WF_qstate q) as Wq. rewrite Heqq. apply WF_qstate_Reduced; try lia; 
try assumption. rewrite Heqm. 
rewrite Rdiv_unfold. rewrite Rmult_1_l.
split; try lia. apply nz_Mixed_State_aux_to01.
apply nz_Mixed_State_aux_to_nz_Mix_State. apply H7. 
destruct n. 
destruct H9. destruct H10. destruct H11.
split; split; try assumption; try split; try lia;
try split; try lia; try split; try lia.   
assert((Reduced q s x) = (Reduced m s x)).
rewrite Heqq. rewrite Reduced_assoc; try lia; try assumption.
reflexivity. rewrite<-H13. 
 unfold outer_product in *.
assert ((@adjoint (2^(e-s)) 1 (@kron (2^(x-s)) 1 (2^(e-x)) 1 v u))=(v ⊗ u) †).
f_equal. type_sovle'. rewrite H14 in H12.
rewrite kron_adjoint in H12.
assert((@Mmult (2^(e-s)) 1 (2^(e-s)) (v ⊗ u) ) ((v) † ⊗ (u) †)=
v ⊗ u × ((v) † ⊗ (u) †)). f_equal; type_sovle'.
rewrite H15 in H12.
rewrite kron_mixed_product in H12. destruct H0. destruct H1.  
rewrite Reduced_L; try lia; try assumption; auto_wf.
rewrite (Reduced_tensor_l _ (v × (v) †) ((u × (u) †))); try lia; try assumption;  auto_wf.
rewrite trace_mult.  rewrite H16. rewrite trace_I.
Msimpl. reflexivity. 

assert((Reduced q x e) = (Reduced m x e)).
rewrite Heqq. rewrite Reduced_assoc; try lia; try assumption.
reflexivity. rewrite<-H13. 
 unfold outer_product in *.
assert ((@adjoint (2^(e-s)) 1 (@kron (2^(x-s)) 1 (2^(e-x)) 1 v u))=(v ⊗ u) †).
f_equal. type_sovle'. rewrite H14 in H12.
rewrite kron_adjoint in H12.
assert((@Mmult (2^(e-s)) 1 (2^(e-s)) (v ⊗ u) ) ((v) † ⊗ (u) †)=
v ⊗ u × ((v) † ⊗ (u) †)). f_equal; type_sovle'.
rewrite H15 in H12.
rewrite kron_mixed_product in H12. destruct H0. destruct H1.  
rewrite Reduced_R; try lia; try assumption; auto_wf.
rewrite (Reduced_tensor_r _ (v × (v) †) ((u × (u) †))); try lia; try assumption;  auto_wf.
rewrite trace_mult.  rewrite H17. rewrite trace_I.
Msimpl. reflexivity.
Qed. 
  
Theorem  rule_odotT: forall qs1 qs2, 
(((qs1) ⊗* (qs2)) <<->> ((qs1)  ⊙ (qs2))) .
Proof. rule_solve.   Qed.
 

Local Open Scope assert_scope.
Local Open Scope R_scope.
Theorem rule_Oplus: forall (pF:pro_formula),
  pF ->> (pro_to_npro_formula pF).
Proof.
   intros.  unfold assert_implies. simpl. intros.
  econstructor.
  inversion_clear H. 
  assert(length (get_pro_formula pF )= length (pro_to_npro_formula pF)).
  inversion_clear H2. rewrite get_pro_formula_length.
  rewrite pro_to_npro_formula_length. reflexivity.
   apply H.  
  rewrite pro_npro_swap. intuition.
Qed.



Fixpoint swap_list {A:Type} (l:list A) (i:nat):=
  match l ,i with 
  |[], _ =>[]
  |h::[], _ => h::[]
  |h:: h'::t, 0=> h':: h :: t 
  |h:: h'::t, S i' => h:: (swap_list (h'::t) i')
  end .

Import Ceval_Prop.

Lemma  big_dapp_nil'{s e:nat}: forall g (f:list (dstate s e)),
g=[]\/f=[]-> dstate_eq (big_dapp g f ) (d_empty s e) .
Proof. intros. destruct H. simpl. destruct g; destruct f.
    simpl. unfold dstate_eq ;try reflexivity.
    simpl. unfold dstate_eq ;try reflexivity. 
    discriminate H. discriminate H. 
    simpl. destruct g; destruct f.
    simpl. unfold dstate_eq ;try reflexivity.
    discriminate H.
    simpl. unfold dstate_eq ;try reflexivity. 
    discriminate H. 
Qed.

Lemma swap_app{s e:nat} :forall (g:list R)  (f:(list (dstate s e))) ( i:nat),
length g =length f->
dstate_eq (big_dapp g f) (big_dapp (swap_list g i) (swap_list f i)).
Proof. induction g. intros.  
        apply dstate_eq_trans with (d_empty s e). 
        apply big_dapp_nil'. left. reflexivity.
        apply dstate_eq_trans with ( (d_empty s e)).
        unfold dstate_eq. reflexivity.
        apply dstate_eq_sym. apply big_dapp_nil'.
        left. destruct i. reflexivity. simpl. reflexivity.
        induction f. intros.  
        apply dstate_eq_trans with (d_empty s e).
        apply big_dapp_nil'. right. reflexivity.
        apply dstate_eq_trans with ( (d_empty s e)).
        unfold dstate_eq. reflexivity.
        apply dstate_eq_sym. apply big_dapp_nil'.
        right. destruct i. reflexivity. simpl. reflexivity. 
        intros.
        induction i. destruct g. destruct f.   simpl swap_list.
        unfold dstate_eq.
        reflexivity. intros. discriminate H.
        intros.
        simpl swap_list. destruct f. discriminate H.
        simpl. 
        apply dstate_eq_trans with 
        ((d_app (d_app (d_scale_not_0 a a0)  (d_scale_not_0 r d)) (big_dapp g f ))).
        apply dstate_eq_sym.
        apply d_app_assoc'.  
        apply dstate_eq_trans with 
        ((d_app (d_app  (d_scale_not_0 r d) (d_scale_not_0 a a0)) (big_dapp g f ))).
        apply d_app_eq. apply d_app_comm.
        unfold dstate_eq. reflexivity.
        apply d_app_assoc'.
        intros. 
        simpl. destruct g; destruct f. 
        simpl. reflexivity.
        discriminate H.   discriminate H. 
        apply dstate_eq_trans with (
        (d_app (d_scale_not_0 a a0)(big_dapp (swap_list (r :: g) i) (swap_list (d::f) i)))
        ). 
        apply d_app_eq. reflexivity. 
        apply IHg.  injection H. intuition.
      simpl. reflexivity.  
Qed.

Lemma swap_app'{s e:nat} :forall (g:list R)  (f:(list (dstate s e))) i (mu mu':dstate s e),
big_dapp' g f mu->
big_dapp' (swap_list g i) (swap_list f i) mu'->
dstate_eq mu mu'.
Proof. induction g; intros; inversion H;subst. 
        -destruct i; simpl in *; inversion_clear H0; reflexivity.
        -induction i. destruct g; destruct td. simpl in H0.
        inversion H0; subst. inversion_clear H9. inversion_clear H6.
        apply d_app_eq.   apply d_scale_eq with hd hd a.
        apply dstate_eq_refl. assumption. assumption. apply dstate_eq_refl.
        inversion_clear H6. inversion_clear H6.
        simpl in H0. inversion H0; subst. 
        inversion H6; subst. inversion H9 ; subst.
        apply dstate_eq_trans with ((d_app (d_app r r2) d2)).
        apply dstate_eq_sym.
        apply d_app_assoc'. 
        apply dstate_eq_trans with ((d_app (d_app r1 r3) d)).
        apply d_app_eq. 
       apply dstate_eq_trans with ((d_app r2 r)).
       apply d_app_comm. 
       apply d_app_eq. 
       apply d_scale_eq with d0 d0 r0. 
       apply dstate_eq_refl. assumption. assumption.
       apply d_scale_eq with hd hd a. 
       apply dstate_eq_refl. assumption. assumption.
       apply big_dapp_eq with g td. assumption. assumption.
       apply d_app_assoc'. 
       destruct g; destruct td. simpl in *.
       apply big_dapp_eq with ([a]) ([hd]). 
       assumption. assumption.
       inversion_clear H6. inversion_clear H6.
       simpl in H0. 
       inversion H0; subst. 
       apply d_app_eq. apply d_scale_eq with hd hd a.
       apply dstate_eq_refl. assumption. assumption.
       apply IHg with ((d0 :: td)) i.
       assumption. assumption.
Qed.

Lemma swap_app_exist{s e:nat} :forall (g:list R)  (f:(list (dstate s e))) i (mu:dstate s e),
big_dapp' g f mu->
exists (mu':dstate s e), (and (dstate_eq mu mu')
(big_dapp' (swap_list g i) (swap_list f i) mu')).
Proof. induction g; intros; inversion H;subst. 
        -exists (d_empty s e). split. apply dstate_eq_refl.
         destruct i; simpl in *; try apply big_dapp_nil'; try econstructor.
        -assert(exists d' : dstate s e,
         and (dstate_eq d d')
         (big_dapp' (swap_list g i)
          (swap_list td i) d')). 
          apply IHg. assumption.
          destruct H0. destruct H0.
          destruct i.  simpl in *.
          destruct g; destruct td. inversion_clear H5.
          inversion H1; subst.
          exists ((d_app r )d). 
          split. apply d_app_eq. apply dstate_eq_refl.
          apply dstate_eq_sym. assumption. assumption.
          inversion_clear H5. inversion_clear H5.
          inversion H5; subst. 
          exists (d_app r1 (d_app r d1)).
          split. 
          apply dstate_eq_trans with ((d_app (d_app r r1) d1)).
          apply dstate_eq_sym.
          apply d_app_assoc'. 
          apply dstate_eq_trans with ((d_app (d_app r1 r) d1)).
          apply d_app_eq. 
         apply dstate_eq_trans with ((d_app r1 r)).
         apply d_app_comm. apply dstate_eq_refl. 
         apply dstate_eq_refl. apply d_app_assoc'.
         apply big_dapp_cons. assumption. apply big_dapp_cons.
          assumption. assumption.
          destruct g; destruct td.
           inversion H5; subst. 
        simpl. exists ((d_app r (d_empty s e))).
        split. apply dstate_eq_refl. assumption.
        inversion_clear H5. inversion_clear H5.
        simpl .  inversion H5; subst.
        assert(exists mu' : dstate s e,
        and (dstate_eq (d_app r1 d1) mu')
        (big_dapp' (swap_list (r0 :: g) i)
          (swap_list (d0 :: td) i) mu')).
          apply IHg. assumption.
          destruct H3. 
        exists (d_app r (x0)).
        split. apply d_app_eq. apply dstate_eq_refl.
        intuition. apply big_dapp_cons. 
        intuition. intuition.
Qed.  


Lemma swap_and{s e:nat} :forall  (g:list (R* State_formula))  (P: (dstate s e) -> (R*State_formula) -> Prop)
(f:(list (dstate s e))) i,
(Forall_two P f g)->
(Forall_two P (swap_list f i) (swap_list g i)).
Proof. induction g; intros; induction f; intros. 
destruct i; simpl; intuition. inversion_clear H.
inversion_clear H.
induction i. simpl in *; destruct f; destruct g.
simpl. intuition. inversion_clear H. inversion_clear H1.
inversion_clear H. inversion_clear H1.
inversion_clear H. inversion_clear H1.
econstructor. assumption. econstructor. assumption.
assumption.
simpl. destruct f; destruct g. 
assumption. inversion_clear H. inversion_clear H1.
inversion_clear H. inversion_clear H1.
inversion_clear H. inversion_clear H1.
econstructor. assumption.
apply IHg. econstructor. assumption.
assumption.
Qed.


Lemma swap_length: forall {A:Type} (pF:list A) i,
length (swap_list pF i)= length pF .
Proof. induction pF; induction i; simpl; try reflexivity.
       destruct pF. simpl. reflexivity.
       simpl. reflexivity. destruct pF. simpl. reflexivity.
       simpl. f_equal. rewrite IHpF. simpl. reflexivity. 
Qed.


Lemma  swap_get_pro:  forall pF1 i,
(get_pro_formula (swap_list pF1 i))=
swap_list (get_pro_formula pF1) i.
Proof. induction pF1. intros. destruct i. simpl. reflexivity.
     simpl. reflexivity.
     destruct i.
     intros. destruct a. destruct pF1. simpl.
     reflexivity. destruct p. simpl. reflexivity.
     destruct pF1. destruct a. simpl. reflexivity.
     destruct a.  destruct p.
     simpl. f_equal. apply IHpF1.   
  
Qed.



Lemma  swap_pro_to_npro:  forall pF1 i,
(pro_to_npro_formula (swap_list pF1 i))=
swap_list (pro_to_npro_formula pF1) i.
Proof. induction pF1. intros. destruct i. simpl. reflexivity.
     simpl. reflexivity.
     destruct i.
     intros. destruct a. destruct pF1. simpl.
     reflexivity. destruct p. simpl. reflexivity.
     destruct pF1. destruct a. simpl. reflexivity.
     destruct a.  destruct p.
     simpl. f_equal. apply IHpF1.   
  
Qed.

Lemma sum_over_list_swap: forall pF i,
sum_over_list  (get_pro_formula pF)=
sum_over_list  (get_pro_formula (swap_list pF i)).
Proof.   
        induction pF; intros.  destruct i. simpl in *. reflexivity.
        simpl. reflexivity.
        
        destruct i. destruct pF. simpl. reflexivity.
         destruct a. destruct p.  
         simpl.  repeat rewrite sum_over_list_cons in *.
        repeat rewrite <-Rplus_assoc.  rewrite (Rplus_comm r r0).
        reflexivity. 

         destruct pF.  destruct a. simpl.  reflexivity.
         destruct a. destruct p. simpl. 
         repeat rewrite sum_over_list_cons in *.  
         f_equal. rewrite<-IHpF. simpl. 
         rewrite sum_over_list_cons. f_equal. 
Qed.

Lemma Forall_swap{G:Type}: forall (pF:list G) (f:G->Prop) i,
Forall f pF  ->
Forall f (swap_list pF i).
Proof.  induction pF; intros.  destruct i. simpl in *.  assumption.
simpl. assumption.
destruct i. destruct pF. simpl. assumption. 
 simpl.  inversion_clear H. inversion_clear H1.
 econstructor. assumption. econstructor. assumption.
 assumption. 
 destruct pF. simpl.  assumption. simpl. 
 inversion_clear H.  econstructor. assumption.
 apply IHpF. assumption.
Qed.

Lemma distribution_formula_swap: forall pF i,
distribution_formula  pF ->
distribution_formula  (swap_list pF i) .
Proof. intros. inversion_clear H. econstructor.
       rewrite swap_pro_to_npro. apply Forall_swap.
       assumption. destruct H1. split.
       rewrite swap_get_pro.
       apply Forall_swap.  assumption. 
       rewrite <-sum_over_list_swap. assumption.
Qed.


Theorem rule_POplusC: forall pF1 i,
APro ( pF1 ) ->>
APro (swap_list pF1 i).
Proof.  intros.  unfold assert_implies. 
intros.
inversion_clear H. inversion_clear H2. 
econstructor. intuition. apply distribution_formula_swap. 
assumption. assert(exists d, and (dstate_eq mu' d) ( big_dapp'
( (swap_list  (get_pro_formula pF1) i))
(swap_list mu_n i) d )). 
apply swap_app_exist. assumption.
destruct H2. destruct H2.
econstructor.
rewrite swap_get_pro. apply H5. 
apply dstate_eq_trans with mu'. assumption. assumption.
apply swap_and. assumption.
Qed.


Theorem rule_OplusC: forall F1 F2 ,
ANpro [F1; F2]->>
ANpro [F2; F1].
Proof.  intros.  unfold assert_implies. 
intros.
inversion_clear H. destruct p_n. discriminate H0. destruct p_n. 
discriminate H0. destruct p_n.  simpl in *. 
apply (rule_POplusC _ 0) in H1. simpl in *. 
econstructor. 
assert(length [r0;r] = length [F2; F1]). simpl. reflexivity.
apply H. simpl. apply H1. 
discriminate H0.
Qed.


Lemma big_and_impiles{s' e':nat}: forall (p_n:list R)  (nF1 nF2: npro_formula) (mu_n:list (dstate s' e')) a,
(Forall_two (fun f_i g_i=>(0<fst(g_i)) -> sat_State f_i (snd g_i) /\ d_trace f_i = a ) mu_n (npro_to_pro_formula nF1 p_n))->
(Forall_two (fun (f_i g_i: (State_formula)) =>   (f_i) ->>  (g_i)) nF1 nF2)->
(Forall_two (fun f_i g_i=>(0<fst(g_i)) -> sat_State f_i (snd g_i)/\ d_trace f_i = a) mu_n (npro_to_pro_formula nF2 p_n)).
Proof. induction p_n; destruct nF1; destruct nF2; intros; simpl ; inversion_clear H;
       try econstructor; try  assumption; inversion_clear H0. 
       unfold assert_implies in H.  
       intros. simpl in *. 
       assert( sat_Assert l1h s0). apply H. 
       rewrite sat_Assert_to_State. apply H1. assumption.  
       rewrite sat_Assert_to_State in H4.
       split; try assumption. apply H1. assumption. 
       eapply IHp_n. apply H2. apply H3. 
Qed.


Theorem  rule_OCon: forall (nF1 nF2:npro_formula) (p_n: list R),
(Forall (fun x=> WF_formula x) nF2)->
length nF1 =length p_n ->
(Forall_two (fun (f_i g_i: State_formula) => f_i ->> g_i) nF1 nF2)->
((npro_to_pro_formula nF1 p_n) ->> (npro_to_pro_formula nF2 p_n)).
Proof. intros.    unfold assert_implies. intros. 
inversion_clear H2. inversion_clear H5.
econstructor. intuition.
econstructor; try rewrite (get_pro_formula_eq nF1);
try rewrite <-(Forall_two_length_eq _ _ _ H1);
inversion_clear H4; try assumption.
rewrite pro_npro_inv. assumption.
rewrite <-(Forall_two_length_eq _ _ _ H1); assumption.
econstructor. rewrite (get_pro_formula_eq  nF1 _  _).
apply H2. assumption.
rewrite <-(Forall_two_length_eq _ _ _ H1); assumption. 
assumption.
eapply big_and_impiles. apply H7. apply H1.
Qed.

Theorem  rule_OCon': forall (nF1 nF2:npro_formula) ,
(Forall (fun x=> WF_formula x) nF2)->
(Forall_two (fun (x y: State_formula)=> x ->> y) nF1 nF2)
->(nF1->> nF2).
Proof. intros.    unfold assert_implies. intros. 
inversion_clear H1. 
econstructor.  
rewrite<- (Forall_two_length_eq _ _ _ H0). apply H2.
assert((npro_to_pro_formula nF1 p_n) ->> (npro_to_pro_formula nF2 p_n)).
apply rule_OCon. intuition. intuition. apply H0.
apply H1. assumption.
Qed.


Lemma rule_OCon''_aux:forall (s e:nat) (pF1 pF2:pro_formula) (mu_n:list (dstate s e)) 
(P:(dstate s e)-> (R* State_formula)->Prop) (Q:State_formula->State_formula->Prop), 
(forall (i :dstate s e) (j k:R*State_formula), ((fst j)=(fst k))->
(P i j) -> Q (snd j) (snd k)->(P i k))->
(get_pro_formula pF1 = get_pro_formula pF2)->
(Forall_two Q (pro_to_npro_formula pF1) (pro_to_npro_formula pF2) )->
(Forall_two P mu_n pF1 )->
Forall_two P  mu_n pF2.
Proof. induction pF1; intros; destruct pF2; simpl in *.
inversion_clear H2. econstructor. inversion_clear H1.
inversion_clear H1. inversion_clear H2. inversion_clear H1. 
econstructor. apply H with  a; try assumption. injection H0. auto. 
eapply IHpF1. apply H. injection H0. auto. auto. auto.
Qed.





Theorem  rule_OCon'': forall (pF1 pF2:pro_formula),
(Forall (fun x=> WF_formula x) (pro_to_npro_formula pF2))->
(get_pro_formula pF1 = get_pro_formula pF2)->
(Forall_two (fun (f_i g_i: State_formula) => f_i ->> g_i) 
(pro_to_npro_formula pF1) (pro_to_npro_formula pF2))->
(pF1 ->> pF2).
Proof. intros. unfold assert_implies. intros. 
inversion_clear H2. inversion_clear H5.
econstructor. intuition. inversion_clear H4.
econstructor. assumption.  rewrite <-H0; assumption.  
econstructor. rewrite<-H0. apply H2. assumption. 
eapply rule_OCon''_aux with (P:=(fun (mu_i : dstate s e)
(pF_i : R * State_formula) => (0 < fst pF_i)%R -> sat_State mu_i (snd pF_i) /\ d_trace mu_i = d_trace mu)) 
(Q:=(fun f_i g_i : State_formula => f_i ->> g_i)). 
intros. destruct H8.  rewrite H5. assumption.
split.  rewrite <-sat_Assert_to_State. apply H9.   
rewrite sat_Assert_to_State. assumption. assumption.
apply H0.  assumption. assumption.  
Qed.


Theorem rule_OMerg:forall (p0 p1:R) (F:State_formula) (pF:pro_formula),
0< p0<1/\ 0< p1 <1->
APro ((p0 , F) :: ( p1, F) :: pF) ->> APro (((p0+p1), F):: pF).
Proof. intros. unfold assert_implies. intros.

inversion_clear H. inversion_clear H0.
inversion_clear H4. 
econstructor. intuition. unfold distribution_formula in *. 
destruct H3 as [H3' H3]. destruct H3. inversion_clear H3.  inversion_clear H8.
split. simpl in *.  inversion_clear H3'. assumption.
split. econstructor. simpl in *. apply Rplus_le_le_0_compat.
assumption. assumption. assumption.
simpl in *.  repeat rewrite sum_over_list_cons in *.
simpl in *. rewrite Rplus_assoc. assumption.
destruct mu_n. inversion_clear H0.
destruct mu_n. inversion_clear H0. inversion_clear H7.
simpl in *. inversion H0; subst. inversion H12; subst.
assert( exists (d': dstate s e), d_scale (p0+p1) 
((d_app ((d_scale_not_0 (p0 / (p0 + p1)) d))
(d_scale_not_0 (p1 / (p0 + p1)) d0))) d').
apply d_scale_exsits. destruct H4.
inversion H11; subst. lra. 
inversion H13; subst. lra.
inversion H4; subst. lra.
econstructor.   simpl.  
assert( big_dapp' (p0 + p1 :: get_pro_formula pF) 
(((d_app ((d_scale_not_0 (p0 / (p0 + p1)) d))
(d_scale_not_0 (p1 / (p0 + p1)) d0)))::mu_n)
 (d_app ((d_scale_not_0 (p0 + p1)
 (d_app (d_scale_not_0 (p0 / (p0 + p1)) d)
    (d_scale_not_0 (p1 / (p0 + p1)) d0)))) d2)). 
apply big_dapp_cons. assumption. assumption.
apply H10. 
simpl. apply (dstate_eq_trans _ _ _ _ _ H5).
apply dstate_eq_trans with ((d_app (d_app ((d_scale_not_0 p0 d))
(d_scale_not_0 p1 d0)) d2)).
apply dstate_eq_sym. apply d_app_assoc'. 
apply d_app_eq.    
apply dstate_eq_trans with (d_app (d_scale_not_0 (p0 + p1) (d_scale_not_0 (p0 / (p0 + p1)) d))
((d_scale_not_0 (p0 + p1) (d_scale_not_0 (p1 / (p0 + p1)) d0)))).
apply d_app_eq; 
[apply dstate_eq_trans with ((d_scale_not_0  ((p0 + p1) *(p0 / (p0 + p1))) d))|
apply dstate_eq_trans with ((d_scale_not_0  ((p0 + p1) *(p1 / (p0 + p1))) d0))];
[rewrite Rmult_div_assoc| | rewrite Rmult_div_assoc| ];
[rewrite Rmult_comm| | rewrite Rmult_comm| ];
[rewrite Rdiv_unfold| | rewrite Rdiv_unfold| ];
[rewrite Rmult_assoc| | rewrite Rmult_assoc| ];
[rewrite Rinv_r| | rewrite Rinv_r| ]; 
try  rewrite Rmult_1_r.  unfold dstate_eq ;  reflexivity. lra.
  apply dstate_eq_sym.  apply d_scale_not_0_assoc.
 unfold dstate_eq ;  reflexivity.
lra.  apply dstate_eq_sym.  apply d_scale_not_0_assoc.
apply  d_scale_not_0_app_distr.
apply dstate_eq_refl.
econstructor. intros. split.   apply d_seman_app. 
split. rewrite Rdiv_unfold.
apply Rmult_gt_0_compat. intuition. 
apply Rinv_0_lt_compat. lra.
apply (Rcomplements.Rdiv_le_1 p0 (p0+p1)). lra.
lra.    split. rewrite Rdiv_unfold.
apply Rmult_gt_0_compat. intuition. 
apply Rinv_0_lt_compat. lra.
apply (Rcomplements.Rdiv_le_1 p1 (p0+p1)). lra.
lra. repeat rewrite Rdiv_unfold. 
rewrite <-Rmult_plus_distr_r.
rewrite Rinv_r. lra. lra. 
inversion_clear H6.  simpl in *. apply H15. lra. 
inversion_clear H6.  inversion_clear H16. simpl in *. apply H6. lra.
inversion_clear H6. inversion_clear H16. destruct H15. simpl in *. lra.
destruct H6; simpl in *. lra. 
rewrite d_trace_app. 
repeat rewrite d_trace_scale_not_0. 


  rewrite H16. rewrite H18.  rewrite <-Rmult_plus_distr_r.
  repeat rewrite Rdiv_unfold. rewrite <-Rmult_plus_distr_r.
  rewrite Rinv_r. rewrite Rmult_1_l. reflexivity.
  apply tech_Rplus. intuition. intuition.
  rewrite Rplus_comm. apply Rdiv_in01. intuition. intuition.
  apply Rdiv_in01. intuition. intuition. 
  apply WWF_dstate_aux_to_WF_dstate_aux.
  apply WF_d_scale_not_0.    apply Rdiv_in01. intuition.
  intuition. 
  apply WF_sat_State with F. assumption. 
  apply WWF_dstate_aux_to_WF_dstate_aux.
  apply WF_d_scale_not_0. rewrite Rplus_comm.
  apply Rdiv_in01. intuition. intuition.
  apply WF_sat_State with F. assumption.
  inversion_clear H6. inversion_clear H15.
  assumption. 
Qed.


(*Some properties about Assgnment*)

Lemma Assn_impl:forall i a D1 D2,
D1 ->> D2 ->
Assn_sub i a D1 ->> Assn_sub i a D2 .
Proof. intros. unfold assert_implies in *. intros.
inversion_clear H0.
econstructor. assumption. 
apply H. assumption.   
Qed.



Notation "v ' " := (AId v) (at level 0, no associativity): com_scope.

Lemma c_update_aeval_eq{s e:nat}: forall i a b c (q:qstate s e),  
~NSet.In i (Free_aexp a) -> 
aeval (c, q) a = aeval (c_update i b c, q) a.
Proof. induction a; intros; simpl in *; [ | | | | | | | | | f_equal];
       try (f_equal;  [rewrite (IHa1 b) | rewrite (IHa2 b)]; try reflexivity;
         intro; destruct H; [apply NSet.union_2| apply NSet.union_3]; 
         assumption); try reflexivity.
      rewrite c_update_find_not. reflexivity.  
      intro. destruct H. apply NSet.add_1. lia. 
       rewrite (IHa1  b). reflexivity. 
       intro. destruct H. apply NSet.union_2. apply NSet.union_2.
       assumption. 
       rewrite (IHa2  b). reflexivity. 
       intro. destruct H. apply NSet.union_2. apply NSet.union_3.
       assumption.
       rewrite (IHa3  b). reflexivity.
       intro. destruct H. apply NSet.union_3.
       assumption.
Qed.

Lemma c_update_beval_eq{s e:nat}: forall i b a c (q:qstate s e),  ~NSet.In i (Free_bexp b) -> 
beval (c, q) b = beval (c_update i a c, q) b.
Proof. induction b; intros; simpl in *; [ | | | f_equal| | f_equal | f_equal|  ];
       try (f_equal; erewrite c_update_aeval_eq; f_equal; 
       intro; destruct H; [apply NSet.union_2| apply NSet.union_3]; 
         assumption); try apply IHb; try assumption;
         try (f_equal; [apply IHb1 | apply IHb2]; 
         intro; destruct H; [apply NSet.union_2| apply NSet.union_3]; 
         assumption ); try reflexivity. 
Qed.

Lemma Assn_true_P: forall i a, ~NSet.In i (Free_aexp a) ->
(BTrue ->> PAssn i a (BEq (AId i) a) ).
Proof. rule_solve.  repeat rewrite c_update_find_eq. 
       apply (c_update_aeval_eq _ _ (aeval (x, (d_find x mu)) a) x (d_find x mu) ) in H.
       apply Nat.eqb_eq in H. rewrite H. assumption. 
Qed.

Lemma big_Sand_Assn_true: forall a D n, 
(forall i:nat, ~NSet.In a (Free_aexp i)) ->
D ->> big_Sand (fun i : nat => PAssn a i (BEq (a ') i)) n.
Proof. unfold assert_implies. intros.  
apply Big_Sand_forall.
intros. apply Assn_true_P.
apply H. 
eapply rule_DT. apply H0.
Qed.

Lemma Assn_true_F: forall i a, ~NSet.In i (Free_aexp a) ->
(BTrue ->> SAssn i a (BEq (i ') a) ).
Proof. rule_solve.  repeat rewrite c_update_find_eq. 
       apply (c_update_aeval_eq _ _ (aeval (x, (d_find x mu)) a) x (d_find x mu) ) in H.
       apply Nat.eqb_eq in H. rewrite H. assumption. 
Qed.

Lemma Assn_true: forall i a D, ~NSet.In i (Free_aexp a) ->
(D ->> Assn_sub i a (BEq (i ') a)).
Proof. unfold assert_implies. intros.
apply WF_sat_Assert in H0. 
econstructor. assumption.
rewrite sat_Assert_to_State.  
econstructor. apply WF_d_update_cstate. assumption.
destruct mu as (mu, IHmu). simpl in *.
induction mu. econstructor.

destruct a0. 
assert(State_eval <{ (i) ' = a }> (c_update i (aeval (c, q) a) c, q)).
simpl.  rewrite c_update_find_eq. 
rewrite <-(c_update_aeval_eq i _  ((aeval (c, q) a))).
assert(aeval (c, q) a = aeval (c, q) a).
reflexivity. apply Nat.eqb_eq in H1. rewrite H1.
auto. assumption. 


simpl.  rewrite app_fix_2. apply d_seman_app_aux. 
apply WF_state_dstate_aux. 
apply WF_state_eq with (c,q). reflexivity.
inversion_clear H0. assumption.
apply WF_d_update_cstate. inversion_clear H0.
assumption.  econstructor. assumption. econstructor.

subst.
inversion_clear IHmu. apply (IHmu0  H2).
 inversion_clear H0. assumption.
Qed.


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
Proof. induction a; intros; simpl in *; try  apply cstate_eq_union in H;
  try rewrite IHa1; try rewrite IHa2;try rewrite IHa3; try reflexivity; try apply H.
 unfold cstate_eq in H. 
 apply NSet.add_1.
 reflexivity. 
 destruct H. apply cstate_eq_union in H. apply H.
 destruct H. apply cstate_eq_union in H. apply H.
Qed.


Lemma cstate_eq_b{ s e:nat}: forall c1 c2 (b:bexp) (q: qstate s e),
cstate_eq c1 c2 (Free_bexp b)->
beval (c1, q) b=beval (c2,q) b.
Proof. induction b; intros; simpl in *; try apply cstate_eq_union in H;
  try rewrite (cstate_eq_a c1 c2 a1);
 try rewrite (cstate_eq_a c1 c2 a2); 
 try  rewrite IHb; try  rewrite IHb1; try  rewrite IHb2; try apply H; try reflexivity.
Qed.


Lemma cstate_eq_P{ s e:nat}: forall P c1 c2  (q: qstate s e),
cstate_eq c1 c2 (Free_pure P)->
State_eval P (c1, q) <->
State_eval P (c2, q).
Proof. induction P; intros; split; intros;
 simpl in *.
 try rewrite<- (cstate_eq_b c1). 
 assumption. assumption.
 try rewrite (cstate_eq_b _ c2). assumption. assumption. 
 rewrite <-(cstate_eq_a c1 c2). apply H0. assumption.
 rewrite (cstate_eq_a c1 c2). apply H0. assumption.
 try apply cstate_eq_union in H; split;
 try  apply (IHP1 c1 c2); try  eapply (IHP2 c1 c2); try apply H0; try apply H.
 try apply cstate_eq_union in H; split;
 try  rewrite (IHP1 c1 c2); try  rewrite (IHP2 c1 c2); try apply H0; try apply H.

 intro. destruct H0. eapply IHP. apply H. assumption.
 intro. destruct H0. rewrite <-(IHP c1 c2). apply H1. assumption.

 apply cstate_eq_union in H.
 destruct H0. left. rewrite <-(IHP1 c1 c2); try assumption; try apply H.
 right.  rewrite <-(IHP2 c1 c2); try assumption; try apply H.
 
 apply cstate_eq_union in H.
 destruct H0. left. rewrite (IHP1 c1 c2); try assumption; try apply H.
 right.  rewrite (IHP2 c1 c2); try assumption; try apply H.

 intros. apply IHP with (c_update i a c1).
 unfold cstate_eq in *. 
 intros. destruct (eq_dec j i).
 subst.  repeat rewrite c_update_find_eq. reflexivity.
 apply (@NSet.remove_2 _ i j) in H1; try lia. 
 apply H in H1. repeat rewrite c_update_find_not; try lia.
 apply H0. 

 intros. apply IHP with (c_update i a c2).
 unfold cstate_eq in *. 
 intros. destruct (eq_dec j i).
 subst.  repeat rewrite c_update_find_eq. reflexivity.
 apply (@NSet.remove_2 _ i j) in H1; try lia. 
 apply H in H1. repeat rewrite c_update_find_not; try lia.
 apply H0.

 simpl in *.   
 rewrite (cstate_eq_a _  c1).
 apply IHP with ((c_update i (aeval (c1, q) a) c1)).
 unfold cstate_eq in *.
 intros. destruct (eq_dec j i).
  rewrite e0. 
 repeat rewrite c_update_find_eq.
 reflexivity. 
 pose (@NSet.union_2 (Free_pure P) (Free_aexp a) j H1). 
 apply H in i0.  
 repeat rewrite c_update_find_not; try lia.
assumption. 
unfold cstate_eq in *. intros.
pose (@NSet.union_3 (Free_pure P) (Free_aexp a) j H1). 
 apply H in i0. rewrite i0. reflexivity.

 simpl in *.   
 rewrite (cstate_eq_a _  c2).
 apply IHP with ((c_update i (aeval (c2, q) a) c2)).
 unfold cstate_eq in *.
 intros. destruct (eq_dec j i).
  rewrite e0. 
 repeat rewrite c_update_find_eq. 
 reflexivity. 
 pose (@NSet.union_2 (Free_pure P) (Free_aexp a) j H1). 
 apply H in i0.  
 repeat rewrite c_update_find_not; try lia.
assumption. 
unfold cstate_eq in *. intros.
pose (@NSet.union_3 (Free_pure P) (Free_aexp a) j H1). 
 apply H in i0. rewrite i0. reflexivity.

Qed.


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
auto.
simpl in *. destruct H. 
econstructor.
destruct mu2. 
destruct a. destruct a0.
econstructor.
simpl in H.
rewrite <-(cstate_eq_P _ c c0) .
intuition.
simpl.
rewrite (state_eq_Pure _  _ (c,q)).
inversion_clear H0.
assumption. reflexivity. apply H.
econstructor.
destruct a.
destruct a0. 
econstructor.
simpl in H.
rewrite <-(cstate_eq_P _ c c0) .
intuition.
simpl.
rewrite (state_eq_Pure _  _ (c,q)).
inversion_clear H0.
assumption.
reflexivity. apply H.
rewrite <-State_eval_dstate_Forall.
apply IHmu1.
simpl in H. 
intuition. destruct mu1. simpl in *.
destruct H. destruct H1.
inversion_clear H0.
rewrite State_eval_dstate_Forall.
assumption. discriminate. discriminate. 
Qed. 

Lemma cstate_eq_F{ s e:nat}: forall F c1 c2 (q: qstate s e),
cstate_eq c1 c2 (fst (Free_state F))->
State_eval F (c1, q)->
State_eval F (c2, q).
Proof. induction F; intros.
rewrite <-(cstate_eq_P P c1 c2).
assumption. assumption.
apply qstate_eq_Qexp with (c1,q).
reflexivity. assumption.
simpl in *. 
split. intuition.
split. apply IHF1 with c1. 
apply cstate_eq_union in H.
intuition. intuition.
apply IHF2 with c1.
apply cstate_eq_union in H.
intuition. intuition.
simpl in *. 
split. apply IHF1 with c1. 
apply cstate_eq_union in H.
intuition. intuition.
apply IHF2 with c1.
apply cstate_eq_union in H.
intuition. intuition.
simpl in *.  
apply cstate_eq_union in H.
rewrite <-(cstate_eq_a c1  c2).
apply IHF with (c_update i (aeval (c1, q) a) c1).
 unfold cstate_eq in *.
 intros. destruct (eq_dec j i).
  rewrite e0. 
 repeat rewrite c_update_find_eq. 
 reflexivity.
 apply H in H1.  
 repeat rewrite c_update_find_not; try lia.
assumption. 
unfold cstate_eq in *. intros.
 apply H in H1. rewrite H1. reflexivity.
Qed.

Lemma Assn_conj_P: forall (P1 P2 : Pure_formula) i a,
~NSet.In i ( (Free_pure P1)) ->
P1 /\p PAssn i a P2 ->>
(PAssn i a (P1 /\p P2)). 
Proof. rule_solve.  apply (cstate_eq_P P1 x ); try assumption.
       unfold cstate_eq. intros. destruct (eq_dec j i).
       rewrite e0 in *. destruct H. assumption.
       rewrite c_update_find_not. reflexivity. lia.
Qed.


Lemma Assn_conj_F: forall (F1 F2 : State_formula) i a,
~NSet.In i (fst (Free_state F1)) ->
F1 /\s SAssn i a F2 ->>
(SAssn i a (F1 /\s F2)) . 
Proof. rule_solve.  apply (cstate_eq_F F1 x ); try assumption.
       unfold cstate_eq. intros. destruct (eq_dec j i).
       rewrite e0 in *. destruct H. assumption.
       rewrite c_update_find_not. reflexivity. lia.
Qed.

Lemma Assn_comm:forall i a (F1 F2:State_formula), 
SAssn i a (F1 /\s F2) ->> SAssn i a (F2 /\s F1).
Proof. rule_solve.
Qed.



Lemma State_eval_Assn{s e:nat}: forall (mu:list (state s e)) i a F,
WF_dstate_aux mu->
State_eval_dstate  (SAssn i a F)  mu->
State_eval_dstate F (d_update_cstate_aux i a mu) .
Proof. induction mu; intros. simpl in *. assumption.  
inversion_clear H0. simpl in H1. destruct a.
destruct mu. simpl in *. econstructor. assumption. econstructor.
inversion_clear H. remember (s0 :: mu).    
simpl. rewrite app_fix_2.  apply d_seman_app_aux.
apply WF_state_dstate_aux. apply WF_state_eq with (c,q).
reflexivity.  assumption.  apply WF_d_update_cstate.  assumption. 
econstructor. simpl in H1. assumption. econstructor.
apply IHmu.  assumption.   
subst. apply State_eval_dstate_Forall. discriminate.
assumption.
Qed.


Lemma sat_Assn{s e:nat}: forall (mu:dstate s e) i a F,
sat_State mu (SAssn i a F) ->
sat_State (d_update_cstate i a mu) F.
Proof. intros (mu,IHmu) i a F. intros. inversion_clear H. 
econstructor. apply WF_d_update_cstate. assumption.
simpl in *. apply State_eval_Assn. assumption. assumption.
Qed.  



Lemma Assn_sub_Plus_aux:forall (s e:nat) (pF1 pF2:pro_formula) (mu_n:list (dstate s e)) v a 
(P:(dstate s e)-> (R*State_formula)->Prop) (Q:State_formula->State_formula->Prop), 
(forall (i :dstate s e) (j k:R*State_formula), ((fst j)=(fst k))-> 
(P i j) -> Q (snd j) (snd k)->(P (d_update_cstate v a i) k))->
(get_pro_formula pF1 = get_pro_formula pF2)->
(Forall_two Q (pro_to_npro_formula pF1) (pro_to_npro_formula pF2) )->
(Forall_two P mu_n pF1 )->
Forall_two P (d_update_cstate_list v a mu_n) pF2.
Proof. induction pF1; intros; destruct pF2; simpl in *.
inversion_clear H2. econstructor. inversion_clear H1.
inversion_clear H1. inversion_clear H2. inversion_clear H1. 
econstructor. apply H with a; try assumption. injection H0. auto. 
eapply IHpF1. apply H. injection H0. auto. auto. auto.
Qed.



Lemma Assn_sub_Plus: forall (nF1 nF2: npro_formula) i a,
(Forall (fun x=> WF_formula x) nF2)->
Forall_two (fun (F1 F2: State_formula) => F1 ->> SAssn i a F2) nF1 nF2->
((ANpro nF1)->> Assn_sub i a (ANpro nF2)). 
Proof. intros nF1 nF2 i a H' H . unfold assert_implies. intros. inversion_clear H0. 
inversion_clear H2. inversion_clear H4. rewrite get_pro_formula_p_n in H2; 
try symmetry; try assumption. 
econstructor. assumption. econstructor. erewrite <-(Forall_two_length_eq _ _ nF2); try apply H. apply H1. 
simpl in *. econstructor. apply WF_d_update_cstate. assumption.
symmetry in H1.
inversion_clear H3. econstructor; rewrite get_pro_formula_p_n in * ;try assumption.
rewrite pro_npro_inv. assumption.
erewrite <-(Forall_two_length_eq _ _ nF2); try apply H. apply H1.
erewrite <-(Forall_two_length_eq _ _ nF2); try apply H. apply H1.  
pose(big_dapp_exsist p_n (d_update_cstate_list i a mu_n)) .
symmetry in H1.
destruct e0. rewrite d_update_cstate_length. eapply big_dapp'_length. apply H2. 
econstructor. simpl in *. rewrite get_pro_formula_p_n in *. apply H4. 
erewrite <-(Forall_two_length_eq _ _ nF2); try apply H.  apply H1.  
apply dstate_eq_trans with (d_update_cstate i a mu'). 
apply d_update_cstate_eq. assumption.  
apply dstate_eq_sym. eapply  big_dapp'_update. 
apply H2. assumption.
apply Assn_sub_Plus_aux with (pF1:=(npro_to_pro_formula nF1 p_n)) (Q:=(fun F1 F2 : State_formula => F1 ->> SAssn i a F2)).
intros. destruct H8. rewrite H7. assumption. split.
 unfold assert_implies in H9. 
pose (H9 s e i0). repeat rewrite sat_Assert_to_State in s0.
apply sat_Assn. apply s0. assumption. 
rewrite d_trace_update'. assumption. 
apply WWF_dstate_aux_to_WF_dstate_aux. eapply WF_sat_State. apply H8. 
apply get_pro_formula_eq; try assumption.
erewrite <-(Forall_two_length_eq _ _ nF2); try apply H. assumption.
rewrite pro_npro_inv; try assumption. rewrite pro_npro_inv. assumption.
erewrite <-(Forall_two_length_eq _ _ nF2); try apply H. assumption.
rewrite d_trace_update'. assumption. 
apply WWF_dstate_aux_to_WF_dstate_aux.
assumption.
Qed.


Lemma sat_Pro_State{s e:nat}: forall (mu:dstate s e) F0 F1,
sat_Pro mu [(0, F0); (1, F1)] <-> 
sat_State mu F1.
Proof. intros; split; intros.  inversion_clear H. 
simpl in *.  inversion H0; subst. 
inversion H4; subst.
inversion H7; subst. inversion H9; subst. simpl in *.
apply sat_State_dstate_eq with r. 
apply dstate_eq_trans with ((d_app (d_empty s e) (d_app r (d_empty s e)))).
apply dstate_eq_sym. apply dstate_eq_trans with ((d_app r (d_empty s e))).
apply d_app_empty_l. apply dstate_eq_trans with ((d_app (d_empty s e) r)).
apply d_app_comm. apply d_app_empty_l.
apply dstate_eq_sym. 
assumption. apply sat_State_dstate_eq with hd0.
apply dstate_eq_sym.
apply d_scale_1_l . assumption. inversion_clear H2. 
inversion_clear H3. apply H2. simpl. lra. 
lra.

assert(exists d, d_scale 1 mu d).
apply d_scale_exsits. destruct H0. 
econstructor.  
simpl in *.  
 assert(big_dapp' [0; 1] [x; mu] (d_app (d_empty s e) (d_app x (d_empty s e)))).
 apply big_dapp_cons. apply d_scalar_0. 
 apply big_dapp_cons. assumption.  
 apply big_dapp_nil. apply H1.
 apply dstate_eq_trans with ((d_app x (d_empty s e) )).
 apply dstate_eq_trans with x.
 apply dstate_eq_sym.
 apply d_scale_1_l. assumption. 
 apply dstate_eq_trans with ((d_app  (d_empty s e) x)).
 apply dstate_eq_sym.  apply d_app_empty_l.
 apply  d_app_comm. apply dstate_eq_sym.  
 apply d_app_empty_l.  
 econstructor. simpl . intros. lra. 
 econstructor. intuition. econstructor.
Qed.


Lemma sat_Pro_State'{s e:nat}: forall (mu:dstate s e) F0 F1,
sat_Assert mu (APro [(0, F0); (1, F1)] )<-> 
sat_Assert mu F1 /\ WF_formula F0.
Proof. intros. split; intros. inversion_clear H. rewrite sat_Assert_to_State.
       split. 
        eapply sat_Pro_State. apply H2. inversion_clear H1.
        simpl in *. inversion_clear H. apply H1.
       econstructor. eapply WF_sat_Assert. apply H. econstructor. simpl. 
       econstructor. apply H. econstructor. 
       destruct H. rewrite sat_Assert_to_State in H. 
       eapply sat_State_WF_formula. apply H. econstructor.
       split. simpl. econstructor.
       lra. econstructor. lra. econstructor.
       simpl. repeat rewrite sum_over_list_cons. repeat rewrite sum_over_list_nil.
       rewrite Rplus_0_l. rewrite Rplus_0_r. reflexivity.
       apply sat_Pro_State. apply sat_Assert_to_State. apply H. 
Qed.

Lemma sat_NPro_State{s e:nat}: forall (mu:dstate s e) (F0 F1:State_formula),
sat_Assert mu F0 /\ WF_formula F1->
sat_Assert mu (ANpro [F0; F1]).
Proof. intros. assert([F0; F1]= pro_to_npro_formula ([(1, F0); (0, F1)])).
       reflexivity. rewrite H0. eapply rule_Oplus.
       assert([(1, F0); (0, F1)]= swap_list  ([(0, F1); (1, F0)]) 0).
       reflexivity. rewrite H1.
       apply rule_POplusC. 
       apply sat_Pro_State'. apply H. 
Qed. 


Lemma Rmult_plus_gt_0:forall r1 r2 r3 r4,
0<r3/\ 0<r4 /\ 0<=r1 /\ 0<=r2->
~(r1 =0 /\ r2 =0) ->
0<r1*r3+r2*r4.
Proof. intros. apply Classical_Prop.not_and_or in H0. destruct H0. 
       apply Rplus_lt_le_0_compat. apply Rmult_lt_0_compat; try lra. 
       apply Rmult_le_pos; try lra. 
       apply Rplus_le_lt_0_compat. apply Rmult_le_pos; try lra. 
       apply Rmult_lt_0_compat; try lra.  
Qed.

Local Open Scope R_scope.
Lemma d_seman_scale': forall s e (p:R) (mu:dstate s e) (F:State_formula),
0<p->
(d_trace (d_scale_not_0 p mu))<=1->
sat_State mu F -> 
sat_State (d_scale_not_0 p mu) F.
Proof. 
       intros. destruct mu as [mu IHmu]. 
       inversion H1; subst. 
       simpl in H3.
       apply sat_F.
       apply WWF_dstate_aux_to_WF_dstate_aux.
       split. 
       apply WWF_d_scale_not_0. intuition.
       apply WWF_dstate_aux_to_WF_dstate_aux.
       assumption.
       assumption. 
        apply d_seman_scale_aux.
       intuition. unfold WF_dstate in H1. 
       simpl in H1. intuition. 
Qed.


Lemma d_scale_to_not_0{s e:nat}: forall (p: R) (mu: (dstate s e)) ,  
p<>0->
d_scale p mu (d_scale_not_0 p mu).
Proof. intros. apply d_scalar_r. assumption.  
Qed.

Lemma d_scale_to_not_0'{s e:nat}: forall (p: R) (mu mu1: (dstate s e)) ,  
p<>0->
d_scale p mu mu1->
mu1=(d_scale_not_0 p mu).
Proof. intros. induction H0. lra. 
 reflexivity.
Qed.

Lemma big_dapp'_to_app'{s e:nat}: forall (p_n:list R) (mu_n :list (dstate s e)) (mu:dstate s e),  
length p_n= length mu_n->
(Forall (fun x =>0< x%R) p_n)->
big_dapp' p_n mu_n mu->
mu=(big_dapp p_n mu_n).
Proof. intros. induction H1. simpl. reflexivity.
simpl. apply d_scale_to_not_0' in H1. 
rewrite H1. f_equal. apply IHbig_dapp'. 
injection H. intuition. inversion_clear H0. assumption.
inversion_clear H0. lra.   
Qed.



Lemma d_seman_scale'': forall s e (p:R) (mu:dstate s e) (F:State_formula),
sat_State mu F -> StateMap.this mu<>[]->
sat_State (d_scale_not_0 (/d_trace mu) mu) F.
Proof. 
intros. destruct mu as [mu IHmu]. 
inversion H; subst. 
simpl in H2.
apply sat_F.
apply WWF_dstate_aux_to_WF_dstate_aux in H1. 
apply WWF_dstate_aux_to_WF_dstate_aux.
split. 
apply WWF_d_scale_not_0. 
apply Rinv_0_lt_compat. apply (WF_dstate_gt0_le1).
apply H0. 
apply WWF_dstate_aux_to_WF_dstate_aux.
split. intuition. intuition. 
intuition.  simpl.   simpl.
 rewrite d_trace_map.
unfold d_trace. simpl. rewrite Rinv_l.
lra. apply WWF_dstate_not_0.
apply WF_sat_State in H. intuition.
intuition. 
apply Rinv_0_lt_compat. 
apply WF_dstate_gt0_le1.
apply WF_sat_State in H. intuition.
apply WWF_dstate_aux_to_WF_dstate_aux.
split. intuition. intuition.
 apply d_seman_scale_aux.
 apply Rinv_0_lt_compat. 
 apply WF_dstate_gt0_le1.
 apply WF_sat_State in H. intuition.
intuition. simpl. assumption.
Qed.

From Quan Require Import Basic.
Local Open Scope  R_scope.
Lemma sat_dapp_npro{s e:nat}: forall (mu1 mu2: (dstate s e)) (F1 F2:State_formula),
sat_Assert (mu1) (ANpro [F1;F2]) ->
sat_Assert (mu2)  (ANpro [F1;F2]) ->
WF_dstate (d_app mu1 mu2)->
sat_Assert (d_app mu1 mu2)  (ANpro [F1;F2]).
Proof. intros.
       assert(StateMap.this mu1=[] \/ ~(StateMap.this mu1=[])) as Hmu1.
       apply Classical_Prop.classic. destruct Hmu1  as [Hmu1 | Hmu1].
       apply sat_Assert_dstate_eq with ((d_app (d_empty s e) mu2)).
       apply d_app_eq. unfold dstate_eq. rewrite Hmu1. simpl. reflexivity.
       reflexivity.
       apply sat_Assert_dstate_eq with mu2.
       apply dstate_eq_sym.  
       apply d_app_empty_l. assumption. 
       
       assert(StateMap.this mu2=[] \/ ~(StateMap.this mu2=[])) as Hmu2.
       apply Classical_Prop.classic. destruct Hmu2 as [Hmu2 | Hmu2].
       apply sat_Assert_dstate_eq with ((d_app mu1 (d_empty s e) )).
       apply d_app_eq. reflexivity.
       unfold dstate_eq. rewrite Hmu2. simpl. reflexivity.
       apply sat_Assert_dstate_eq with mu1.
       apply dstate_eq_sym.  
       apply d_app_empty_r. assumption.

       inversion_clear H. inversion_clear H0. 
       destruct p_n; destruct p_n0; try discriminate H2; try discriminate H.
       destruct p_n; destruct p_n0; try discriminate H2; try discriminate H.
       destruct p_n; destruct p_n0; try discriminate H2; try discriminate H.
       assert( (r=0/\r0=0) \/ ~(r=0/\r0=0))%R.
       apply Classical_Prop.classic. destruct H0. 
       destruct H0. rewrite H0 in *. rewrite H5 in *.
       simpl in *. inversion_clear H3. inversion_clear H4. 
       inversion_clear H7 as [H' H11]. destruct H11 as [H11 H12].
       inversion_clear H9 as [H'' H13]. destruct H13 as [H13 H14].  simpl in *.
       repeat rewrite sum_over_list_cons in *. 
       rewrite sum_over_list_nil in *.  rewrite Rplus_0_l in *. 
       rewrite Rplus_0_r in *. subst. 
       rewrite sat_Pro_State in *. 
       apply rule_OplusC. apply sat_NPro_State. 
       rewrite sat_Assert_to_State. split.
       apply d_seman_app'; try assumption.  inversion_clear H'.
       assumption. 

       assert( (r1=0/\r2=0) \/ ~(r1=0/\r2=0))%R.
       apply Classical_Prop.classic. destruct H5. 
       destruct H5. rewrite H5 in *. rewrite H6 in *.
       assert(r=1 /\ r0 =1).
       simpl in *. inversion_clear H3. inversion_clear H4. 
       inversion_clear H8. inversion_clear H10.  simpl in *.
       repeat rewrite sum_over_list_cons in *. 
       rewrite sum_over_list_nil in *.  rewrite Rplus_0_l in *. 
       rewrite Rplus_0_r in *. destruct H12. subst. destruct H13. subst. auto.
        destruct H7. subst. 
       simpl in *. 
       apply (rule_POplusC _ 0) in H3.   apply (rule_POplusC _ 0) in H4.
       simpl in *. 
       rewrite sat_Pro_State' in *. 
        apply sat_NPro_State. 
       rewrite sat_Assert_to_State in *.
       split.
       apply d_seman_app'; try intuition. apply H3.
       

       assert(0 < d_trace mu1<=1). 
       apply WF_dstate_gt0_le1. assumption. eapply WF_sat_Pro; apply H3.
       assert(0 < d_trace mu2<=1). 
       apply WF_dstate_gt0_le1. assumption. eapply WF_sat_Pro; apply H4.

       inversion_clear H3. inversion_clear H4.
       inversion_clear H9. inversion_clear H11.
       destruct H13. destruct H14. simpl in *. 
       inversion_clear H11. inversion_clear H17. clear H18.
       inversion_clear H14. inversion_clear H18. clear H19. simpl in *.
       repeat rewrite sum_over_list_cons in *. rewrite sum_over_list_nil in *.
       rewrite Rplus_0_r in *.
       assert(length [((r * (d_trace mu1) + r0 * (d_trace mu2)) 
       / ((d_trace mu1)+(d_trace mu2)))%R; ((r1 * (d_trace mu1) + r2 * (d_trace mu2)) 
       / ((d_trace mu1)+(d_trace mu2)))%R] = length [F1; F2])%nat. reflexivity.    
       econstructor. apply H18.

       
       econstructor. assumption.
       simpl. econstructor. simpl. assumption.
       split. 
       econstructor; [|econstructor; [|econstructor] ]; try apply Rcomplements.Rdiv_le_0_compat; try
       apply Rplus_le_le_0_compat; try apply Rmult_le_pos;
       try apply Rplus_lt_0_compat; try assumption; try lra.
       simpl. repeat rewrite sum_over_list_cons in *. rewrite sum_over_list_nil in *.
       rewrite Rplus_0_r in *.  repeat rewrite Rdiv_unfold.
       rewrite <-Rmult_plus_distr_r.   rewrite <-Rplus_assoc. 
       rewrite (Rplus_assoc _ (r0 * d_trace mu2) _). rewrite (Rplus_comm  (r0 * d_trace mu2) _).
        rewrite <-Rplus_assoc.  rewrite <-Rmult_plus_distr_r.
        rewrite Rplus_assoc. rewrite <-Rmult_plus_distr_r.
       
       
      rewrite H13. rewrite H15. repeat rewrite Rmult_1_l.

       apply Rinv_r. apply Rgt_neq_0. apply Rplus_lt_0_compat; lra. 
      simpl. 
       inversion_clear H10. inversion_clear H12. simpl in *.
       destruct mu_n. inversion_clear H21. destruct mu_n. inversion_clear H21.
       inversion_clear H24. inversion_clear H21. inversion_clear H24. clear H25.
       destruct mu_n0. inversion_clear H23. destruct mu_n0. inversion_clear H23.
       inversion_clear H25. inversion_clear H23. inversion_clear H25. clear H26.
       inversion H19; subst. inversion H31; subst. inversion H33; subst.
       clear H33.  clear H19. clear H31.
       inversion H10; subst. inversion H31; subst. inversion H34; subst.
       clear H34.  clear H10. clear H31.
       
       pose(big_dapp'_to_app ([((r * (d_trace mu1) + r0 * (d_trace mu2)) 
       / ((d_trace mu1)+(d_trace mu2)))%R; ((r1 * (d_trace mu1) + r2 * (d_trace mu2)) 
       / ((d_trace mu1)+(d_trace mu2)))%R])
       [((d_scale_not_0 (((d_trace mu1)+(d_trace mu2)) /(r * (d_trace mu1) + r0 * (d_trace mu2))) 
       (d_app r3 r5 ))); ((d_scale_not_0 (((d_trace mu1)+(d_trace mu2)) /(r1 * (d_trace mu1) + r2 * (d_trace mu2))) 
       (d_app r4  r6 )))]  ).
       econstructor. apply b. reflexivity. clear b.
       econstructor. apply Rdiv_lt_0_compat.  
       apply Rmult_plus_gt_0; try lra.
        apply Rplus_lt_0_compat; try lra.
       econstructor. apply Rdiv_lt_0_compat. 
       apply Rmult_plus_gt_0; try lra.
       apply Rplus_lt_0_compat; try lra.
       econstructor. 
   
       simpl. clear b. 
       apply dstate_eq_trans with 
       (d_app
     (( (d_app r3 r5)))
     (( ( (d_app r4 r6)))
        )). 
        apply dstate_eq_trans with (d_app r3 (d_app r5 (d_app r4 r6))).
        apply dstate_eq_trans with (d_app r3 (d_app (d_app r5 r4) r6)).
        apply dstate_eq_trans with (d_app r3 (d_app (d_app r4 r5) r6)).
        apply dstate_eq_trans with (d_app r3 (d_app r4 (d_app r5 r6))).
        apply dstate_eq_trans with (d_app  (d_app r3 r4) (d_app r5 r6)).
        apply d_app_eq. 
        apply dstate_eq_trans with (d_app r3 (d_app r4 (d_empty s e))). assumption.
        apply d_app_eq. apply dstate_eq_refl. apply d_app_empty_r.
        apply dstate_eq_trans with  (d_app r5 (d_app r6 (d_empty s e))). assumption.
        apply d_app_eq. apply dstate_eq_refl. apply d_app_empty_r.
        apply d_app_assoc'. 
        apply d_app_eq. apply dstate_eq_refl. 
        apply dstate_eq_sym.
        apply d_app_assoc'. 
        apply d_app_eq. apply dstate_eq_refl. 
        apply d_app_eq. apply d_app_comm. apply dstate_eq_refl.
        apply d_app_eq. apply dstate_eq_refl.
        apply d_app_assoc'.
        apply dstate_eq_sym. apply d_app_assoc'.
       apply d_app_eq.  
       apply dstate_eq_trans with 
       ((d_scale_not_0 (((r * d_trace mu1 + r0 * d_trace mu2) / (d_trace mu1 + d_trace mu2)) * ((d_trace mu1 + d_trace mu2) / (r * d_trace mu1 + r0 * d_trace mu2))))
       (d_app r3 r5)).
       assert(((r * d_trace mu1 + r0 * d_trace mu2) / (d_trace mu1 + d_trace mu2) *
       ((d_trace mu1 + d_trace mu2) / (r * d_trace mu1 + r0 * d_trace mu2)))=1).
       repeat rewrite Rdiv_unfold.  
       rewrite Rmult_assoc. rewrite <-(Rmult_assoc  (/ (d_trace mu1 + d_trace mu2))).
       rewrite Rinv_l. rewrite Rmult_1_l.
       rewrite Rinv_r. reflexivity. apply Rgt_neq_0.
       apply Rmult_plus_gt_0; try lra. 
       apply Rgt_neq_0. apply Rplus_lt_0_compat; try lra. 
        rewrite H10. apply dstate_eq_sym.
       apply d_scale_not_0_1_l. 
       apply dstate_eq_sym. 
       apply d_scale_not_0_assoc.
       apply dstate_eq_trans with 
       ((d_scale_not_0 (((r1 * d_trace mu1 + r2 * d_trace mu2) / (d_trace mu1 + d_trace mu2)) * ((d_trace mu1 + d_trace mu2) / (r1 * d_trace mu1 + r2 * d_trace mu2))))
       (d_app r4 r6)).
       assert(((r1 * d_trace mu1 + r2 * d_trace mu2) / (d_trace mu1 + d_trace mu2) *
       ((d_trace mu1 + d_trace mu2) / (r1 * d_trace mu1 + r2 * d_trace mu2)))=1).
       repeat rewrite Rdiv_unfold. 
       rewrite Rmult_assoc. rewrite <-(Rmult_assoc  (/ (d_trace mu1 + d_trace mu2))).
       rewrite Rinv_l. rewrite Rmult_1_l.
       rewrite Rinv_r. reflexivity. apply Rgt_neq_0.
       apply Rmult_plus_gt_0; try lra. 
       apply Rgt_neq_0. apply Rplus_lt_0_compat; try lra.  
        rewrite H10. apply dstate_eq_sym.
       apply d_scale_not_0_1_l.
       apply dstate_eq_trans with ((d_scale_not_0
       ((r1 * d_trace mu1 + r2 * d_trace mu2) / (d_trace mu1 + d_trace mu2))
       (d_scale_not_0
          ((d_trace mu1 + d_trace mu2) /
           (r1 * d_trace mu1 + r2 * d_trace mu2)) 
          (d_app r4 r6)))).
          apply dstate_eq_sym. apply d_scale_not_0_assoc.
          apply dstate_eq_sym. apply d_app_empty_r.
        clear b.
       
       
       econstructor; simpl in *. split.
       apply sat_State_dstate_eq with (d_scale_not_0
       (d_trace mu1 + d_trace mu2)
       (d_scale_not_0 (/ (r * d_trace mu1 + r0 * d_trace mu2)) (d_app r3 r5))).
       rewrite Rdiv_unfold. apply d_scale_not_0_assoc.
       apply d_seman_scale'. lra. 
       rewrite d_trace_scale_not_0; try lra. 
       rewrite d_trace_scale_not_0.
       destruct (Req_dec r 0). subst. repeat rewrite Rmult_0_l.
       repeat rewrite Rplus_0_l.
       inversion_clear H30. 
       rewrite (d_trace_eq  (d_app (d_empty s e) r5) r5).
       inversion H29; subst. destruct H0. auto.
       rewrite d_trace_scale_not_0; try lra. 
       destruct H24. lra. rewrite H25.
       rewrite Rinv_l. rewrite Rmult_1_r. rewrite <-d_trace_app.
       apply WF_dstate_in01. assumption. 
       apply WWF_dstate_to_WF_dstate. assumption. 
       apply WWF_dstate_to_WF_dstate. assumption.
       apply Rmult_integral_contrapositive_currified.
       lra. lra. apply d_app_empty_l. lra. 
       destruct (Req_dec r0 0). subst. repeat rewrite Rmult_0_l.
       repeat rewrite Rplus_0_r.
       inversion_clear H29. 
       rewrite (d_trace_eq  (d_app  r3 (d_empty s e) ) r3).
       inversion H30; subst. lra. 
       rewrite d_trace_scale_not_0; try lra. 
       destruct H12. lra. rewrite H26.
       rewrite Rinv_l. rewrite Rmult_1_r. rewrite <-d_trace_app.
       apply WF_dstate_in01. assumption. 
       apply WWF_dstate_to_WF_dstate. assumption. 
       apply WWF_dstate_to_WF_dstate. assumption.
       apply Rmult_integral_contrapositive_currified.
       lra. lra. apply d_app_empty_r. lra.
       inversion H30; subst. lra. inversion H29; subst. lra. 
       rewrite d_trace_app. repeat rewrite d_trace_scale_not_0; try lra. 
       destruct H12. lra. destruct H24. lra. 
       rewrite H28. rewrite H31. rewrite Rinv_l.
       rewrite Rmult_1_r.  
       rewrite <-d_trace_app.
       apply WF_dstate_in01. assumption. 
       apply WWF_dstate_to_WF_dstate. assumption. 
       apply WWF_dstate_to_WF_dstate. assumption.
       apply Rgt_neq_0.
       apply Rmult_plus_gt_0; try lra.
       apply WWF_d_scale_not_0; try lra.
       apply WWF_dstate_to_WF_dstate.
       eapply WF_sat_State. apply H12. lra.
       apply WWF_d_scale_not_0; try lra.
       apply WWF_dstate_to_WF_dstate.
       eapply WF_sat_State. apply H24. lra.
       apply Rinv_0_lt_compat.
       apply Rmult_plus_gt_0; try lra.
       inversion H30; subst; inversion H29; subst.
       destruct H0. auto.
       rewrite Rmult_0_l. rewrite Rplus_0_l.
       apply sat_State_dstate_eq with ((d_scale_not_0 (/ (r0 * d_trace mu2))
       ( (d_scale_not_0 r0 d1)))).
       apply d_scale_not_0_eq. apply dstate_eq_sym.
       apply d_app_empty_l.  
       destruct H24. lra. rewrite<-H25. 
       rewrite<-d_trace_scale_not_0; try lra.
       apply d_seman_scale''. intuition.
       apply d_seman_scale_not_0. lra. apply H24.
       intro. apply d_scale_not_0_nil in H26.
       apply WF_dstate_gt0_le1 in H3; try assumption.
       unfold d_trace in H25. rewrite H26 in H25.
       simpl in H25. lra.
       rewrite Rmult_0_l. rewrite Rplus_0_r.
       apply sat_State_dstate_eq with ((d_scale_not_0 (/ (r * d_trace mu1))
       ( (d_scale_not_0 r d)))).
       apply d_scale_not_0_eq. apply dstate_eq_sym.
       apply d_app_empty_r.  
       destruct H12. lra. rewrite<-H25. 
       rewrite<-d_trace_scale_not_0; try lra.
       apply d_seman_scale''. intuition.
       apply d_seman_scale_not_0. lra. apply H12.
       intro. apply d_scale_not_0_nil in H26.
       apply WF_dstate_gt0_le1 in H8; try assumption.
       unfold d_trace in H25. rewrite H26 in H25.
       simpl in H25. lra.
       apply sat_State_dstate_eq with 
       (d_app (d_scale_not_0 (/ (r * d_trace mu1 + r0 * d_trace mu2))
       ((d_scale_not_0 r d))) (d_scale_not_0 (/ (r * d_trace mu1 + r0 * d_trace mu2))
       ((d_scale_not_0 r0 d1)))).
       apply d_scale_not_0_app_distr.
       apply d_seman_app'.
       apply d_seman_scale'. apply Rinv_0_lt_compat.
       apply Rplus_lt_0_compat; apply Rmult_gt_0_compat; try lra.
       rewrite d_trace_scale_not_0; try lra.
       rewrite d_trace_scale_not_0; try lra.
       destruct H12. lra. rewrite H26.  rewrite Rmult_comm. 
       rewrite <-Rdiv_unfold. 
       apply (Rcomplements.Rdiv_le_1 (r * d_trace mu1)). 
       apply Rmult_plus_gt_0; try lra. 
       rewrite <-Rplus_0_r at 1. 
       apply Rplus_le_compat_l. 
       apply Rmult_le_pos; try lra.
       apply Rinv_0_lt_compat.
       apply Rplus_lt_0_compat; apply Rmult_gt_0_compat; try lra.
       apply d_seman_scale_not_0; try lra. apply H12. lra.
       apply d_seman_scale'. apply Rinv_0_lt_compat.
       apply Rplus_lt_0_compat; apply Rmult_gt_0_compat; try lra.
       rewrite d_trace_scale_not_0; try lra.
       rewrite d_trace_scale_not_0; try lra.
       destruct H24. lra. rewrite H26. 
       rewrite Rmult_comm. 
       rewrite <-Rdiv_unfold. 
       apply (Rcomplements.Rdiv_le_1 (r0 * d_trace mu2)). 
       apply Rmult_plus_gt_0; try lra. 
       rewrite <-Rplus_0_l at 1. 
       apply Rplus_le_compat_r. 
       apply Rmult_le_pos; try lra.
       apply Rinv_0_lt_compat.
       apply Rplus_lt_0_compat; apply Rmult_gt_0_compat; try lra.
       apply d_seman_scale_not_0; try lra. apply H24. lra.
       apply WWF_dstate_to_WF_dstate.
       split. apply WWF_d_app. 
       apply WWF_d_scale_not_0. 
       apply Rinv_0_lt_compat.
       apply Rplus_lt_0_compat; apply Rmult_gt_0_compat; try lra.
       apply WWF_d_scale_not_0. lra.
       apply WWF_dstate_to_WF_dstate.
       eapply WF_sat_State. apply H12. lra.
       apply WWF_d_scale_not_0.  
       apply Rinv_0_lt_compat.
       apply Rplus_lt_0_compat; apply Rmult_gt_0_compat; try lra.
       apply WWF_d_scale_not_0. lra.
       apply WWF_dstate_to_WF_dstate.
       eapply WF_sat_State. apply H24. lra.
       rewrite d_trace_app; try repeat rewrite d_trace_scale_not_0.
       rewrite <-Rmult_plus_distr_l. 
       destruct H12. lra. destruct H24. lra. 
       rewrite H26. rewrite H27. 
       rewrite Rinv_l. lra. apply Rgt_neq_0.
       apply Rmult_plus_gt_0; try lra.
       lra. 
       apply Rinv_0_lt_compat.
       apply Rplus_lt_0_compat; apply Rmult_gt_0_compat; try lra.
       lra.
       apply Rinv_0_lt_compat.
       apply Rplus_lt_0_compat; apply Rmult_gt_0_compat; try lra.
       apply WWF_d_scale_not_0. 
       apply Rinv_0_lt_compat.
       apply Rplus_lt_0_compat; apply Rmult_gt_0_compat; try lra.
       apply WWF_d_scale_not_0. lra.
       apply WWF_dstate_to_WF_dstate.
       eapply WF_sat_State. apply H12. lra.
       apply WWF_d_scale_not_0.  
       apply Rinv_0_lt_compat.
       apply Rplus_lt_0_compat; apply Rmult_gt_0_compat; try lra.
       apply WWF_d_scale_not_0. lra.
       apply WWF_dstate_to_WF_dstate.
       eapply WF_sat_State. apply H24. lra.
       rewrite d_trace_scale_not_0. 
       inversion H30; subst; inversion H29; subst.
       destruct H0; try lra. 
       rewrite Rmult_0_l. rewrite Rplus_0_l.
       rewrite (d_trace_eq (d_app (d_empty s e) (d_scale_not_0 r0 d1)) ((d_scale_not_0 r0 d1))).
       rewrite d_trace_scale_not_0; try lra.
       rewrite Rdiv_unfold.
       rewrite Rmult_assoc. 
       destruct H24. lra. rewrite H25. rewrite Rinv_l.
       rewrite Rmult_1_r. rewrite d_trace_app. reflexivity.
       apply WWF_dstate_to_WF_dstate. assumption.
       apply WWF_dstate_to_WF_dstate. assumption.
       apply Rmult_integral_contrapositive_currified.
       lra. lra. 
       apply d_app_empty_l.
       rewrite Rmult_0_l. rewrite Rplus_0_r.
       rewrite (d_trace_eq (d_app  (d_scale_not_0 r d) (d_empty s e) ) ((d_scale_not_0 r d))).
       rewrite d_trace_scale_not_0; try lra.
       rewrite Rdiv_unfold.
       rewrite Rmult_assoc. 
       destruct H12. lra. rewrite H25. rewrite Rinv_l.
       rewrite Rmult_1_r. rewrite d_trace_app. reflexivity.
       apply WWF_dstate_to_WF_dstate. assumption.
       apply WWF_dstate_to_WF_dstate. assumption.
       apply Rmult_integral_contrapositive_currified.
       lra. lra. 
       apply d_app_empty_r.
       rewrite d_trace_app. repeat rewrite d_trace_scale_not_0; try lra.
       rewrite Rdiv_unfold.
       rewrite Rmult_assoc.
       destruct H12. lra. destruct H24. lra. 
       rewrite H26. rewrite H27.
       rewrite Rinv_l. rewrite Rmult_1_r.
       rewrite d_trace_app. reflexivity.
       apply WWF_dstate_to_WF_dstate. assumption.
       apply WWF_dstate_to_WF_dstate. assumption.
       apply Rgt_neq_0. apply Rmult_plus_gt_0; try lra.
       apply WWF_d_scale_not_0. lra.
       apply WWF_dstate_to_WF_dstate.
       eapply WF_sat_State. apply H12. lra.
       apply WWF_d_scale_not_0. lra.
       apply WWF_dstate_to_WF_dstate.
       eapply WF_sat_State. apply H24. lra.
       apply Rdiv_lt_0_compat.  apply Rplus_lt_0_compat; try lra.
       apply Rmult_plus_gt_0; try lra.
   
       

       econstructor; simpl in *. split.
       apply sat_State_dstate_eq with (d_scale_not_0
       (d_trace mu1 + d_trace mu2)
       (d_scale_not_0 (/ (r1 * d_trace mu1 + r2 * d_trace mu2)) (d_app r4 r6))).
       rewrite Rdiv_unfold. apply d_scale_not_0_assoc.
       apply d_seman_scale'. lra. 
       rewrite d_trace_scale_not_0; try lra. 
       rewrite d_trace_scale_not_0.
       destruct (Req_dec r1 0). subst. repeat rewrite Rmult_0_l.
       repeat rewrite Rplus_0_l.
       inversion_clear H32. 
       rewrite (d_trace_eq  (d_app (d_empty s e) r6) r6).
       inversion H33; subst. destruct H5. auto.
       rewrite d_trace_scale_not_0; try lra. 
       destruct H23. lra. rewrite H25.
       rewrite Rinv_l. rewrite Rmult_1_r. rewrite <-d_trace_app.
       apply WF_dstate_in01. assumption. 
       apply WWF_dstate_to_WF_dstate. assumption. 
       apply WWF_dstate_to_WF_dstate. assumption.
       apply Rmult_integral_contrapositive_currified.
       lra. lra. apply d_app_empty_l. lra. 
       destruct (Req_dec r2 0). subst. repeat rewrite Rmult_0_l.
       repeat rewrite Rplus_0_r.
       inversion_clear H33. 
       rewrite (d_trace_eq  (d_app  r4 (d_empty s e) ) r4).
       inversion H32; subst. lra. 
       rewrite d_trace_scale_not_0; try lra. 
       destruct H21. lra. rewrite H26.
       rewrite Rinv_l. rewrite Rmult_1_r. rewrite <-d_trace_app.
       apply WF_dstate_in01. assumption. 
       apply WWF_dstate_to_WF_dstate. assumption. 
       apply WWF_dstate_to_WF_dstate. assumption.
       apply Rmult_integral_contrapositive_currified.
       lra. lra. apply d_app_empty_r. lra.
       inversion H32; subst. lra. inversion H33; subst. lra. 
       rewrite d_trace_app. repeat rewrite d_trace_scale_not_0; try lra. 
       destruct H21. lra. destruct H23. lra. 
       rewrite H28. rewrite H31. rewrite Rinv_l.
       rewrite Rmult_1_r.  
       rewrite <-d_trace_app.
       apply WF_dstate_in01. assumption. 
       apply WWF_dstate_to_WF_dstate. assumption. 
       apply WWF_dstate_to_WF_dstate. assumption.
       apply Rgt_neq_0. apply Rmult_plus_gt_0; try lra.
       apply WWF_d_scale_not_0; try lra.
       apply WWF_dstate_to_WF_dstate.
       eapply WF_sat_State. apply H21. lra.
       apply WWF_d_scale_not_0; try lra.
       apply WWF_dstate_to_WF_dstate.
       eapply WF_sat_State. apply H23. lra.
       apply Rinv_0_lt_compat.
       apply Rmult_plus_gt_0; try lra.
       inversion H32; subst; inversion H33; subst.
       destruct H5. auto.
       rewrite Rmult_0_l. rewrite Rplus_0_l.
       apply sat_State_dstate_eq with ((d_scale_not_0 (/ (r2 * d_trace mu2))
       ( (d_scale_not_0 r2 d2)))).
       apply d_scale_not_0_eq. apply dstate_eq_sym.
       apply d_app_empty_l.  
       destruct H23. lra. rewrite<-H25. 
       rewrite<-d_trace_scale_not_0; try lra.
       apply d_seman_scale''. intuition.
       apply d_seman_scale_not_0. lra. apply H23.
       intro. apply d_scale_not_0_nil in H26.
       apply WF_dstate_gt0_le1 in H3; try assumption.
       unfold d_trace in H25. rewrite H26 in H25.
       simpl in H25. lra.
       rewrite Rmult_0_l. rewrite Rplus_0_r.
       apply sat_State_dstate_eq with ((d_scale_not_0 (/ (r1 * d_trace mu1))
       ( (d_scale_not_0 r1 d0)))).
       apply d_scale_not_0_eq. apply dstate_eq_sym.
       apply d_app_empty_r.  
       destruct H21. lra. rewrite<-H25. 
       rewrite<-d_trace_scale_not_0; try lra.
       apply d_seman_scale''. intuition.
       apply d_seman_scale_not_0. lra. apply H21.
       intro. apply d_scale_not_0_nil in H26.
       apply WF_dstate_gt0_le1 in H8; try assumption.
       unfold d_trace in H25. rewrite H26 in H25.
       simpl in H25. lra.
       apply sat_State_dstate_eq with 
       (d_app (d_scale_not_0 (/ (r1 * d_trace mu1 + r2 * d_trace mu2))
       ((d_scale_not_0 r1 d0))) (d_scale_not_0 (/ (r1 * d_trace mu1 + r2 * d_trace mu2))
       ((d_scale_not_0 r2 d2)))).
       apply d_scale_not_0_app_distr.
       apply d_seman_app'.
       apply d_seman_scale'. apply Rinv_0_lt_compat.
       apply Rplus_lt_0_compat; apply Rmult_gt_0_compat; try lra.
       rewrite d_trace_scale_not_0; try lra.
       rewrite d_trace_scale_not_0; try lra.
       destruct H21. lra. rewrite H26.
       rewrite Rmult_comm. 
       rewrite <-Rdiv_unfold. 
       apply (Rcomplements.Rdiv_le_1 (r1 * d_trace mu1)). 
       apply Rmult_plus_gt_0; try lra. 
       rewrite <-Rplus_0_r at 1. 
       apply Rplus_le_compat_l. 
       apply Rmult_le_pos; try lra.
       apply Rinv_0_lt_compat.
       apply Rplus_lt_0_compat; apply Rmult_gt_0_compat; try lra.
       apply d_seman_scale_not_0; try lra. apply H21. lra.
       apply d_seman_scale'. apply Rinv_0_lt_compat.
       apply Rplus_lt_0_compat; apply Rmult_gt_0_compat; try lra.
       rewrite d_trace_scale_not_0; try lra.
       rewrite d_trace_scale_not_0; try lra.
       destruct H23. lra. rewrite H26. 
       rewrite Rmult_comm. 
       rewrite <-Rdiv_unfold. 
       apply (Rcomplements.Rdiv_le_1 (r2 * d_trace mu2)). 
       apply Rmult_plus_gt_0; try lra. 
       rewrite <-Rplus_0_l at 1. 
       apply Rplus_le_compat_r. 
       apply Rmult_le_pos; try lra.
       apply Rinv_0_lt_compat.
       apply Rplus_lt_0_compat; apply Rmult_gt_0_compat; try lra.
       apply d_seman_scale_not_0; try lra. apply H23. lra.
       apply WWF_dstate_to_WF_dstate.
       split. apply WWF_d_app. 
       apply WWF_d_scale_not_0. 
       apply Rinv_0_lt_compat.
       apply Rplus_lt_0_compat; apply Rmult_gt_0_compat; try lra.
       apply WWF_d_scale_not_0. lra.
       apply WWF_dstate_to_WF_dstate.
       eapply WF_sat_State. apply H21. lra.
       apply WWF_d_scale_not_0.  
       apply Rinv_0_lt_compat.
       apply Rplus_lt_0_compat; apply Rmult_gt_0_compat; try lra.
       apply WWF_d_scale_not_0. lra.
       apply WWF_dstate_to_WF_dstate.
       eapply WF_sat_State. apply H23. lra.
       rewrite d_trace_app; try repeat rewrite d_trace_scale_not_0.
       rewrite <-Rmult_plus_distr_l. 
       destruct H21. lra. destruct H23. lra. 
       rewrite H26. rewrite H27. 
       rewrite Rinv_l. lra. 
       apply Rgt_neq_0. apply Rmult_plus_gt_0; try lra.  
       lra. 
       apply Rinv_0_lt_compat.
       apply Rplus_lt_0_compat; apply Rmult_gt_0_compat; try lra.
       lra.
       apply Rinv_0_lt_compat.
       apply Rplus_lt_0_compat; apply Rmult_gt_0_compat; try lra.
       apply WWF_d_scale_not_0. 
       apply Rinv_0_lt_compat.
       apply Rplus_lt_0_compat; apply Rmult_gt_0_compat; try lra.
       apply WWF_d_scale_not_0. lra.
       apply WWF_dstate_to_WF_dstate.
       eapply WF_sat_State. apply H21. lra.
       apply WWF_d_scale_not_0.  
       apply Rinv_0_lt_compat.
       apply Rplus_lt_0_compat; apply Rmult_gt_0_compat; try lra.
       apply WWF_d_scale_not_0. lra.
       apply WWF_dstate_to_WF_dstate.
       eapply WF_sat_State. apply H23. lra.
       rewrite d_trace_scale_not_0. 
       inversion H32; subst; inversion H33; subst.
       destruct H5; try lra. 
       rewrite Rmult_0_l. rewrite Rplus_0_l.
       rewrite (d_trace_eq (d_app (d_empty s e) (d_scale_not_0 r2 d2)) ((d_scale_not_0 r2 d2))).
       rewrite d_trace_scale_not_0; try lra.
       rewrite Rdiv_unfold.
       rewrite Rmult_assoc. 
       destruct H23. lra. rewrite H25. rewrite Rinv_l.
       rewrite Rmult_1_r. rewrite d_trace_app. reflexivity.
       apply WWF_dstate_to_WF_dstate. assumption.
       apply WWF_dstate_to_WF_dstate. assumption.
       apply Rmult_integral_contrapositive_currified.
       lra. lra. 
       apply d_app_empty_l.
       rewrite Rmult_0_l. rewrite Rplus_0_r.
       rewrite (d_trace_eq (d_app  (d_scale_not_0 r1 d0) (d_empty s e) ) ((d_scale_not_0 r1 d0))).
       rewrite d_trace_scale_not_0; try lra.
       rewrite Rdiv_unfold.
       rewrite Rmult_assoc. 
       destruct H21. lra. rewrite H25. rewrite Rinv_l.
       rewrite Rmult_1_r. rewrite d_trace_app. reflexivity.
       apply WWF_dstate_to_WF_dstate. assumption.
       apply WWF_dstate_to_WF_dstate. assumption.
       apply Rmult_integral_contrapositive_currified.
       lra. lra. 
       apply d_app_empty_r.
       rewrite d_trace_app. repeat rewrite d_trace_scale_not_0; try lra.
       rewrite Rdiv_unfold.
       rewrite Rmult_assoc.
       destruct H21. lra. destruct H23. lra. 
       rewrite H26. rewrite H27.
       rewrite Rinv_l. rewrite Rmult_1_r.
       rewrite d_trace_app. reflexivity.
       apply WWF_dstate_to_WF_dstate. assumption.
       apply WWF_dstate_to_WF_dstate. assumption.
       apply Rgt_neq_0. apply Rmult_plus_gt_0; try lra.
       apply WWF_d_scale_not_0. lra.
       apply WWF_dstate_to_WF_dstate.
       eapply WF_sat_State. apply H21. lra.
       apply WWF_d_scale_not_0. lra.
       apply WWF_dstate_to_WF_dstate.
       eapply WF_sat_State. apply H23. lra.
       apply Rdiv_lt_0_compat.  apply Rplus_lt_0_compat; try lra.
        apply Rmult_plus_gt_0; try lra.
       econstructor.
Qed.

Fixpoint WF_assert (D:Assertion) :=
  match D with 
  |APro pF => distribution_formula pF
  |ANpro nF => (Forall (fun x=> WF_formula x) nF) /\ nF <> []
  |Assn_sub i a D => WF_assert D
  end .

Fixpoint empty_list (n:nat) s e :=
  match n with 
  |0=> []
  |S n=> (d_empty s e):: (empty_list n s e)
  end.

Lemma  sat_Pro_dstate_eq': forall s e (D:pro_formula) (mu mu': dstate s e),
(D<>[]) ->
dstate_eq mu mu'->
sat_Pro mu D-> sat_Pro mu' D.
Proof.  induction D; intros. destruct H. reflexivity. 
        inversion_clear H1.
        destruct mu_n. destruct a.
         simpl in H2. inversion H2; subst. 
        econstructor. 
        apply H2. 
        apply dstate_eq_trans with mu. apply dstate_eq_sym.
        assumption. assumption.
        rewrite <-(d_trace_eq  mu _ H0). assumption.
Qed.





Lemma big_dapp'_out_empty {s e : nat}: forall
(p_n : list R) , 
exists mu, big_dapp' p_n (empty_list (length p_n) s e) mu /\ dstate_eq (d_empty s e) mu.
Proof. induction p_n; intros; simpl in *. 
        econstructor. split; econstructor.
        destruct IHp_n. destruct H.
        pose (d_scale_exsits a (d_empty s e)). 
        destruct e0. 
        exists (d_app x0  x).
        split. econstructor.
        assumption. assumption.
        apply dstate_eq_trans with 
        ((d_app (d_empty s e) (d_empty s e))).
        apply dstate_eq_sym.
        apply d_app_empty_l.
        apply d_app_eq.
        apply dstate_eq_sym. 
        eapply d_scale_empty. apply H1.
        assumption.
Qed.

Lemma sat_Pro_empty_aux{s e:nat}: forall (pF:pro_formula),
(Forall (fun x=> WF_formula x) (pro_to_npro_formula pF))->
Forall_two
(fun (mu_i : dstate s e) (pF_i : R * State_formula) =>
   0 < fst pF_i ->
   sat_State mu_i (snd pF_i) /\
   d_trace mu_i = d_trace (d_empty s e))
  (empty_list (length (get_pro_formula pF)) s e) pF .
Proof. 
induction pF. simpl. econstructor.
simpl. econstructor.  intros. 
split. econstructor. apply WF_dstate_empty.
simpl. inversion_clear H. assumption. reflexivity.
apply IHpF. inversion_clear H. assumption.
Qed.

Lemma sat_Pro_empty{s e:nat}: forall (pF:pro_formula) (mu:dstate s e) ,
(Forall (fun x=> WF_formula x) (pro_to_npro_formula pF))->
(pF<>[]) ->
StateMap.this mu = [] ->
sat_Pro mu pF.
Proof. intros. 

     apply sat_Pro_dstate_eq' with (d_empty s e). assumption.
     unfold dstate_eq. rewrite H1. reflexivity.
   
     pose (@big_dapp'_out_empty s e (get_pro_formula pF)).
     destruct e0. destruct H2.
     
     econstructor. apply H2. assumption.
     apply sat_Pro_empty_aux. assumption.
Qed.

Lemma sum_fun_to_list: forall (f:nat-> R) n, 
sum_over_list (fun_to_list f n) = big_sum f n .
Proof. induction n;intros. simpl. apply sum_over_list_nil.
       simpl. rewrite sum_over_list_app. f_equal.
       assumption. rewrite sum_over_list_cons.
       rewrite sum_over_list_nil. rewrite Rplus_0_r.
       reflexivity. 
  
Qed.

Local Open Scope nat_scope.
Lemma  Forall_fun_to_list{G:Type}: forall (f: G-> Prop) (g:nat->G) n0,
(forall i, i< n0 -> f (g i))<->
Forall f (fun_to_list g n0) .
Proof. induction n0; intros.  simpl. split; intros. try apply Forall_nil. lia.
split; intros. 
 simpl. rewrite Forall_app. split. apply IHn0. intros.
 apply H. lia. econstructor. apply H. lia. apply Forall_nil.
 simpl in *.  apply Forall_app in H. destruct H.
  assert( i= n0\/ i<> n0). 
  apply Classical_Prop.classic. destruct H2. inversion_clear H1.
  subst. assumption. apply IHn0. assumption. lia. 
Qed.

Local Open Scope R_scope.
Lemma sat_Assert_empty{s e:nat}: forall D (mu:dstate s e) ,
WF_assert D-> 
StateMap.this mu = [] ->
sat_Assert mu D.
Proof. induction D; intros.  
     econstructor. unfold WF_dstate. rewrite H0. econstructor.
     apply H. apply sat_Pro_empty. apply H.
     inversion_clear H. intro. subst. simpl in *.
     rewrite sum_over_list_nil in *. lra.  assumption.


     assert(length (fun_to_list (fun i=> if i =? 0 then 1 else 0) (length nF))= length nF).
     rewrite fun_to_list_length. reflexivity.
     econstructor. apply H1. 
     econstructor. unfold WF_dstate. rewrite H0. econstructor.
     econstructor. rewrite pro_npro_inv. apply H. 
     rewrite fun_to_list_length. reflexivity.
    
     repeat rewrite get_pro_formula_p_n. split.
     apply Forall_fun_to_list. intros. destruct i. simpl. lra.
     simpl. lra.
     rewrite sum_fun_to_list.
     apply big_sum_unique. exists 0%nat. simpl.
     split. destruct H. 
     assert(length nF <>0)%nat. destruct nF. destruct H2. reflexivity.
     discriminate. lia. split. lra. intros.
     assert(x'<>0)%nat. lia. apply Nat.eqb_neq in H4.
     rewrite H4. reflexivity. 
     rewrite fun_to_list_length. reflexivity.
     apply sat_Pro_empty. rewrite pro_npro_inv. apply H.
     rewrite fun_to_list_length. reflexivity.
     destruct H. induction nF. destruct H2. reflexivity.
     destruct ((fun_to_list
     (fun i : nat =>
      if i =? 0 then 1 else 0)
     (length (a :: nF)))). simpl. discriminate. simpl. discriminate.
     assumption.

     econstructor.  unfold WF_dstate. rewrite H0. econstructor.
     apply IHD. simpl in H. assumption.
     simpl. rewrite H0. reflexivity.
Qed. 


Import Sorted.
Lemma sat_State_Npro{s e:nat}:forall (mu:dstate s e) F1 F2,
WF_dstate mu-> 
WF_formula F1 /\ WF_formula F2->
(forall x,  (d_find x mu) <> Zero -> State_eval F1 (x, d_find x mu)
 \/ State_eval F2 (x, d_find x mu))->
sat_Assert mu (ANpro [F1;F2]).
Proof. intros (mu, IHmu); simpl in *; intros F1 F2 H  HF. intros. 
       induction mu. 
       apply sat_Assert_empty. simpl. 
       split. econstructor. apply HF. 
       econstructor. apply HF. econstructor.
       discriminate. reflexivity.
       destruct mu.
       destruct a.  
       pose(H0 c).  unfold d_find in *. unfold StateMap.find in *.
       destruct o.  simpl in *. MC.elim_comp.
       simpl. apply WF_qstate_not_Zero. 
       inversion_clear H. apply H2.
      simpl in *. 
      destruct (Cstate_as_OT.compare c c).
      apply Cstate_as_OT.lt_not_eq in l. intuition.
      apply sat_NPro_State. split.
      rewrite sat_Assert_to_State. 
      econstructor. inversion_clear H.
      unfold WF_dstate. apply WF_state_dstate_aux. assumption. 
      econstructor. apply H1. econstructor.
      apply  HF.
      apply Cstate_as_OT.lt_not_eq in l. intuition.
      simpl in H1.  
      destruct (Cstate_as_OT.compare c c).
      apply Cstate_as_OT.lt_not_eq in l. intuition.
      apply rule_OplusC. 
      apply sat_NPro_State. split.
      rewrite sat_Assert_to_State. 
      econstructor. inversion_clear H.
      unfold WF_dstate. apply WF_state_dstate_aux. assumption. 
      econstructor. apply H1. econstructor.
      apply HF.
      apply Cstate_as_OT.lt_not_eq in l. intuition.  
      assert(Sorted.Sorted (StateMap.Raw.PX.ltk (elt:=qstate s e)) [a]).
      apply Sorted_cons. apply Sorted.Sorted_nil. 
      apply Sorted.HdRel_nil.  inversion_clear IHmu.
      assert( dstate_eq {| StateMap.this := a :: p :: mu; StateMap.sorted := IHmu |}
      (d_app (StateMap.Build_slist H1) (StateMap.Build_slist H2))).
       destruct a. 
       destruct p. unfold d_app. unfold StateMap.map2. unfold dstate_eq.
       simpl. destruct (Cstate_as_OT.compare c c0).
       rewrite map2_r_refl. reflexivity.
       unfold Cstate_as_OT.eq in *. rewrite e0 in H3.
       inversion_clear H3. apply Cstate_as_OT.lt_not_eq in H4.
       simpl in H4.  intuition. 
       inversion_clear H3. unfold StateMap.Raw.PX.ltk in H4.
       simpl in H4.  rewrite <-H4 in l.  apply Cstate_as_OT.lt_not_eq in l.
        intuition. 
        apply sat_Assert_dstate_eq with 
       (d_app (StateMap.Build_slist H1) (StateMap.Build_slist H2)).
       apply dstate_eq_sym.
       apply H4. 
       apply sat_dapp_npro. destruct a.  
       pose(H0 c).  unfold d_find in *. unfold StateMap.find in *.
       destruct o.  simpl in *. MC.elim_comp.
       simpl. 
       apply WF_qstate_not_Zero. 
       inversion_clear H. apply H6.
      simpl in *. 
      destruct (Cstate_as_OT.compare c c).
      apply Cstate_as_OT.lt_not_eq in l. intuition.
      apply sat_NPro_State. split.
      rewrite sat_Assert_to_State. 
      econstructor. inversion_clear H.
      unfold WF_dstate. apply WF_state_dstate_aux. assumption. 
      econstructor. apply H5. econstructor.
      apply HF.
      apply Cstate_as_OT.lt_not_eq in l. intuition.
      simpl in H5.  
      destruct (Cstate_as_OT.compare c c).
      apply Cstate_as_OT.lt_not_eq in l. intuition.
      apply rule_OplusC. 
      apply sat_NPro_State. split.
      rewrite sat_Assert_to_State. 
      econstructor. inversion_clear H.
      unfold WF_dstate. apply WF_state_dstate_aux. assumption. 
      econstructor.  apply H5. econstructor.
      apply HF.
      apply Cstate_as_OT.lt_not_eq in l. intuition.
      apply IHmu0. inversion_clear H. assumption.
      
      intros. destruct p.  pose(H0 x). destruct a.
      pose H5. 
      apply dstate_1 with (t:=c0) (q:=q0) in n.
      assert(d_find x {| StateMap.this := (c0, q0) :: (c, q) :: mu; StateMap.sorted := IHmu |}=
      d_find x {| StateMap.this := (c, q) :: mu; StateMap.sorted := H2 |}).
       unfold d_find . 
      unfold StateMap.find. simpl in *. 
      MC.elim_comp. reflexivity. 
      rewrite H6 in *. apply o. assumption. 
      econstructor. assumption. assumption.    
      eapply WF_dstate_eq. apply H4.  assumption.  
Qed.

Lemma sat_Npro_Pro{s e:nat}:forall (mu:dstate s e) F1 F2, 
sat_Assert mu (ANpro [F1;F2])-> (exists p, 0<=p<=1 /\ sat_Assert mu (APro [(p, F1);(1-p, F2)])).
Proof. intros. inversion_clear H. destruct p_n. discriminate H0. destruct p_n.
      discriminate H0. destruct p_n. inversion_clear H1. 
      assert(r0=1-r). inversion_clear H2. simpl in *. repeat rewrite sum_over_list_cons in *.
      rewrite sum_over_list_nil in *. rewrite Rplus_0_r in *. lra. subst. 
      exists r. split. inversion_clear H2. simpl in *. destruct H4. inversion_clear H2.
      inversion_clear H6.  rewrite Rcomplements.Rle_minus_r in H2. rewrite Rplus_0_l in *.
      lra.  econstructor; try assumption. discriminate H0.
Qed.

Lemma sat_NPro_State'{s e:nat}:forall (mu:dstate s e) F, 
(ANpro [F;F])->> F.
Proof. unfold assert_implies. intros. rewrite sat_Assert_to_State.
      inversion_clear H. destruct p_n. discriminate H0. destruct p_n.
      discriminate H0. destruct p_n. inversion_clear H1.
      destruct (Req_dec r 0). subst. assert(r0=1).
      inversion_clear H2 as [H' H1]. destruct H1 as [H1 H4]. simpl in H4.
      repeat rewrite sum_over_list_cons in *. rewrite sum_over_list_nil in *. rewrite Rplus_0_l in *.
      rewrite Rplus_0_r in *. assumption. subst.  
      apply sat_Pro_State in H3. assumption.
      
      destruct (Req_dec r0 0). subst. assert(r=1).
      inversion_clear H2 as [H' H4]. destruct H4 as [H4 H5]. simpl in H5.
      repeat rewrite sum_over_list_cons in *. rewrite sum_over_list_nil in *. rewrite Rplus_0_l in *.
      rewrite Rplus_0_r in *. assumption. subst.  
      assert( sat_Assert mu0 (APro [(1, F); (0, F)])). econstructor; try assumption.
      apply (rule_POplusC _ 0) in H4. simpl in H4.
      apply sat_Pro_State' in H4. rewrite sat_Assert_to_State in *. apply H4. 
      
      inversion_clear H3. simpl in H5. 
      destruct mu_n. inversion_clear H5. destruct mu_n. inversion_clear H5. inversion_clear H8.
      destruct mu_n. inversion H5; subst. inversion H13; subst. inversion H15; subst. clear H15. 
    
      inversion_clear H7. inversion_clear H8. clear H9. simpl in *.
      inversion H12; subst. lra.  inversion H14; subst. lra.
      apply sat_State_dstate_eq with ((d_app (d_scale_not_0 r d) (d_scale_not_0 r0 d0))).
      apply dstate_eq_sym. eapply dstate_eq_trans. apply H6. apply d_app_eq; try apply dstate_eq_refl.
      apply d_app_empty_r.  
       inversion_clear H2. simpl in *. destruct H11. inversion_clear H2. 
      inversion_clear H16. repeat rewrite sum_over_list_cons in *. rewrite sum_over_list_nil in *.
      rewrite Rplus_0_r in *. 
      apply d_seman_app; try lra. apply H3; lra. apply H7; lra. 
      inversion_clear H5. inversion_clear H8. inversion_clear H9. discriminate H0.
Qed.

(*big_oplus*)
Local Open Scope nat_scope.

Lemma Forall_two_forall{A B:Type}:forall n (P: A-> B-> Prop) (f:nat-> A) (g:nat-> B),
(forall j,  (j< n)-> P (f j) (g j)) ->
(Forall_two (fun i j=> P i j) (fun_to_list f n) (fun_to_list g n)).
Proof.
induction n. intros. simpl. econstructor. 
intros. simpl. apply Forall_two_app.
 apply IHn. intros. apply H. lia.
 simpl.
 econstructor. apply H. lia. econstructor.
Qed.

Lemma big_pOplus_p_eq_bound: forall p_n q_n F_n n,
(forall i, i< n -> p_n i= q_n i)->
(big_pOplus p_n  F_n n->> big_pOplus q_n F_n n).
Proof. intros. unfold assert_implies. intros. inversion_clear H0.
        inversion_clear H3. econstructor. assumption.
        inversion_clear H2. econstructor.
        rewrite big_pOplus_get_npro in *.
        assumption. split.
        rewrite big_pOplus_get_pro in *.
        rewrite  <-Forall_fun_to_list in *. intros. rewrite<- H; try assumption.
        apply H6. assumption. 
        rewrite sum_over_list_big_pOplus in *. 
        rewrite (big_sum_eq_bounded _ p_n); try assumption.
        apply H6. 
        intros. symmetry. apply H. assumption.   
        econstructor. rewrite big_pOplus_get_pro in *.
        apply (big_dapp_eq_bound  _ (fun_to_list q_n n)) in H0.
        apply H0. apply Forall_two_forall. assumption.
        assumption.  
        rewrite (Forall_two_nth  _ _ _ (d_empty s e) (1%R, SPure (PBexp <{BTrue}>))).
        rewrite (Forall_two_nth  _ _ _ (d_empty s e) (1%R, SPure (PBexp <{BTrue}>))) in H5.
        destruct H5. split. rewrite big_pOplus_length in *. assumption.
        rewrite big_pOplus_length in *.
        intros.  pose( H5 i H6). split; 
        try rewrite snd_nth_big_pOplus in *;
        try rewrite fst_nth_big_pOplus in *; try lia; 
        try apply a; try rewrite H; try lia; try assumption. 
Qed.




Lemma big_Oplus_to_formua_aux{ s e:nat}: forall (pF:pro_formula) 
(mu_n:list (dstate s e)) 
(P: (dstate s e) -> (R* State_formula) -> Prop) (Q: (dstate s e) -> R -> Prop)
(T: (dstate s e) -> (State_formula) -> Prop),
(forall i j, 
P i j-> T i (snd j) -> Q i (fst j) )->
(Forall_two T mu_n (pro_to_npro_formula pF))->
Forall_two P mu_n pF ->
Forall_two Q mu_n (get_pro_formula pF).
Proof. induction pF; intros; simpl in *; destruct mu_n. econstructor. 
       inversion_clear H1.  inversion_clear H0. 
       inversion_clear H1. inversion_clear H0.  
      econstructor. apply H; try assumption. 
      eapply IHpF; try apply H3; try apply H4; try assumption.

Qed.


Lemma list_app{A:Type}:forall (a:list A),
a<>[]->
exists b c, b ++ [c]= a .
Proof. induction a; intros. destruct H; reflexivity.
       assert(a0=[]\/ a0<>[]).
       apply Classical_Prop.classic. destruct H0. 
       subst. exists []. exists a. simpl. reflexivity.   
       destruct IHa. assumption. destruct H1.  
       exists (a::x). exists x0. simpl. f_equal. assumption. 
  
Qed.

Lemma npro_to_pro_formula_app:forall (nF1 nF2 : npro_formula) (p_n1 p_n2:list R),
length nF1= length p_n1->
length nF2= length p_n2 ->
npro_to_pro_formula (nF1 ++ nF2) (p_n1++ p_n2)=
npro_to_pro_formula nF1 p_n1 ++ (npro_to_pro_formula nF2 p_n2) .
Proof. induction nF1; destruct nF2; simpl in *; intros; destruct p_n1; destruct p_n2; try lia; simpl in *; try reflexivity; try lia.
rewrite app_nil_r. rewrite app_nil_r. rewrite app_nil_r. reflexivity.
f_equal. rewrite IHnF1. f_equal.  lia. simpl. lia.   
Qed.

Lemma forall_impli_Forall{s e:nat}: forall n (mu_n:list (dstate s e)) (F_n:nat-> State_formula) (F: State_formula),
(forall i, i < n -> F_n i ->> F) ->
length mu_n = n->
Forall_two (fun (i : dstate s e) (j : State_formula) => sat_State i j -> sat_State i F)
mu_n (big_Oplus F_n n) .
Proof. induction n; intros; destruct mu_n; simpl in *; try lia.  econstructor.
       pose (list_app (d::mu_n)). destruct e0. discriminate.
       destruct H1. rewrite <-H1. 
       apply Forall_two_app. apply IHn.
       intros. apply H. lia. injection H0.
       intros. rewrite <-H2. 
       assert(length (x ++ [x0]) = length (d :: mu_n)).
       rewrite H1. reflexivity. simpl in H3. rewrite app_length in H3.
       simpl in *. 
       lia.  
       econstructor. intros.
       apply sat_Assert_to_State. apply (H n). lia.
       rewrite sat_Assert_to_State.
       assumption. econstructor. 

Qed.



Lemma big_Oplus_to_formula: forall n (F_n:nat-> State_formula) (F:State_formula),
0<n-> (forall i, i < n -> F_n i ->> F) ->
 big_Oplus F_n n ->> F. 
Proof. unfold assert_implies; intros.  inversion_clear H1.
       inversion_clear H3. 
       inversion_clear H5. 
       rewrite get_pro_formula_p_n in *.
       apply sat_Assert_dstate_eq with mu'.
       apply dstate_eq_sym. assumption.
       rewrite sat_Assert_to_State.
       eapply big_dapp'_seman; try apply H3.
       inversion_clear H4. rewrite get_pro_formula_p_n in *. 
       
       split; try lra. apply Forall_impl with ((fun x : R => (0 <= x)%R)).
       intros. lra. apply H8.  
       symmetry. assumption. 
       assert(p_n= get_pro_formula (npro_to_pro_formula (big_Oplus F_n n) p_n) ).
       rewrite get_pro_formula_p_n. reflexivity. 
       symmetry. assumption. rewrite H5.
       eapply (big_Oplus_to_formua_aux ) with (T:=
       (fun i j=> sat_State i j -> sat_State i F)); try apply H7.
       simpl.  
       intros. apply H9. apply H8. lra.  
       rewrite pro_npro_inv. 
       apply forall_impli_Forall. assumption. 
       erewrite <-big_dapp'_length; try apply H3.
       rewrite <-fun_to_list_big_Oplus_eq in H2. 
       rewrite fun_to_list_length in H2. assumption.
       symmetry. assumption.
       
       symmetry. assumption.
Qed.