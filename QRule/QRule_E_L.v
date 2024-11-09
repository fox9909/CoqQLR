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
From Quan Require Import QState.
From Quan Require Import QAssert.
From Quan Require Import Par_trace.
From Quan Require Import ParDensityO.
From Quan Require Import QSepar.
Import Basic.

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
    H: WF_dstate ?mu /\ StateMap.this ?mu <> [] /\ 
         (forall x:cstate, d_find x ?mu <> Zero ->?Q)
    |-_ => destruct H as [H1 H]; destruct H as [H2 H];
    split; try assumption; split; try assumption; intros
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
Proof. rule_solve. Qed.

Lemma rule_Conj_split_l: forall (F1 F2:State_formula), F1 /\s F2 ->> F1 .
Proof.  rule_solve. Qed.
Lemma rule_Conj_split_r: forall (F1 F2:State_formula), F1 /\s F2 ->> F2 .
Proof.  rule_solve. Qed. 

Theorem rule_ConjC: forall F1 F2:State_formula,
((F1 /\s F2) <<->> (F2 /\s F1)).
Proof.      rule_solve. Qed.



From Quan Require Import QRule_Q_L.
       
Lemma sat_assert_conj: forall s e (mu:dstate s e) (F1 F2:State_formula),
sat_Assert mu (F1 /\s F2)<->
sat_Assert mu F1/\ sat_Assert mu F2 .
Proof.  split; destruct mu as [mu IHmu]; intros;
      repeat rewrite sat_Assert_to_State in *.
      inversion_clear H.  apply State_eval_conj in H1.
      simpl in *. split; econstructor; intuition.

      destruct H. inversion_clear H. inversion_clear H0.
      econstructor. intuition.
      apply State_eval_conj. split; intuition.  
Qed.

Theorem rule_CconjCon:forall F1 F2 F3 F4:State_formula,
(F1 ->>F2) -> (F3 ->> F4) ->
(F1 /\s F3) ->> (F2 /\s F4).
Proof. 
 intros.  unfold assert_implies in *.
intros. rewrite sat_assert_conj in *. intuition.
Qed. 



#[export] Hint Resolve rule_Conj_split_l rule_Conj_split_r: rea_db.
  
  
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
  
  Lemma union_empty:forall x y ,
  NSet.Equal ( (NSet.union x y)) NSet.empty <->
  NSet.Equal x NSet.empty /\ NSet.Equal y NSet.empty.
  Proof.  unfold NSet.Equal. split; intros.  
   split; split; intros.
    apply H. apply NSet.union_2. assumption. 
    inversion_clear H0. 
    apply H. apply NSet.union_3. assumption.
    inversion_clear H0.
    destruct H. 
    split. intros. apply NSet.union_1 in H1. destruct H1.
    apply H. assumption.
    apply H0. assumption.
    intros. inversion_clear H1. 
  Qed. 
  

  
  Lemma inter_empty:forall x y ,
  NSet.Equal x NSet.empty \/ NSet.Equal y NSet.empty->
  NSet.Equal (NSet.inter x y) NSet.empty.
  Proof. unfold NSet.Equal. intros. 
        destruct H. 
        split. intros. apply H. 
        apply NSet.inter_1 in H0. assumption.
        intros. inversion_clear H0.
        split. intros. apply H. 
        apply NSet.inter_2 in H0. assumption.
        intros. inversion_clear H0.
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
  Proof. rule_solve.   
        apply inter_empty. right. reflexivity.
  Qed.
  
   Theorem rule_OdotC: forall F1 F2:State_formula,
  ((F1 ⊙ F2) <<->> (F2 ⊙ F1)).
  Proof.  
           rule_solve; try rewrite inter_comm; try assumption.
  Qed.
  
  
  Theorem rule_OdotA: forall F1 F2 F3:State_formula,
  ((F1 ⊙ (F2 ⊙ F3) )<<->>( (F1 ⊙ F2) ⊙ F3) ).
  Proof.     rule_solve; [rewrite inter_comm | | rewrite inter_comm in H3| rewrite inter_comm in H3 ]; 
             try rewrite inter_union_dist in *;
              try rewrite union_empty in *.
              split;  rewrite inter_comm;
              intuition. apply H3.   
              split;[ | rewrite inter_comm];
              intuition. rewrite inter_comm; apply H3. 
  Qed.

  Notation "F1 /\p F2" := (PAnd F1  F2) (at level 80): assert_scope.
  Notation "F1 \/p F2" := (POr F1  F2) (at level 80): assert_scope.
  
  Theorem rule_OdotO: forall (P1 P2:Pure_formula), 
   ((P1 ⊙ P2) <<->> (P1 /\p P2)) .
  Proof.  rule_solve.  apply inter_empty. intuition.
  Qed.
  
  Theorem rule_OdotOP: forall (P:Pure_formula) (F:State_formula),
  ((P ⊙ F) <<->> (P /\s F)).
  Proof.   rule_solve. apply inter_empty.  intuition.
  Qed.
  
  Theorem rule_OdotOA: forall (P:Pure_formula) (F1 F2:State_formula),
  ((P /\s (F1 ⊙ F2)) <<->> ((P /\s F1) ⊙ (P /\s F2))).
  Proof.  rule_solve. Qed.
  
  
  
  Theorem rule_OdotOC: forall (F1 F2 F3:State_formula), 
  ((F1 ⊙(F2 /\s F3)) <<->> ((F1 ⊙ F2) /\s (F1 ⊙ F3))).
  Proof. rule_solve;[rewrite inter_union_dist in H3;
  rewrite union_empty in H3 | rewrite inter_union_dist in H3;
  rewrite union_empty in H3 | rewrite inter_union_dist ;
  rewrite union_empty
  ]; try apply H3; try split; try assumption. 
  Qed.
  
  Notation "| v >[ s , e ]" := (QExp_s s e v) (at level 80) :assert_scope.

  Local Open Scope assert_scope.
  Theorem  rule_ReArr:forall (s e  s' e':nat)  v u,
  ((| v >[ s , e ]) ⊗* (| u >[ s' , e' ]) ->>(| u >[ s' , e' ]) ⊗* (| v >[ s , e ])).
  Proof.  rule_solve.  rewrite inter_comm. assumption. 
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
  
Import ParDensityO.
Local Open Scope nat_scope.
  Theorem  rule_Separ:forall s x e u v, 
  ((| v >[ s , x ]) ⊗* (| u >[ x , e ])) ->>
  ( (| v ⊗ u >[ s , e ])).
  Proof.  rule_solve.  
   assert( (2 ^ (x - s)) * (2 ^ (e - x)) = 2^(e-s)).
  type_sovle'. destruct H14.
   apply (@ParDensityO.pure_state_vector_kron 
  (2 ^ (x - s)) (2 ^ (e - x)) ). intuition. intuition.  
  assert(WF_qstate (d_find x0 mu)).
  apply WF_dstate_per_state; try assumption.  
  remember (((R1 / Cmod (trace (d_find x0 mu)))%R .* d_find x0 mu)).
  remember (PMpar_trace m s e).
  assert( WF_qstate q). rewrite Heqq. apply Mix_par_trace; try lia; 
  try assumption. rewrite Heqm. 
  rewrite Rdiv_unfold. rewrite Rmult_1_l.
  split; try lia. apply Mixed_State_aux_to01.
  apply Mixed_State_aux_to_Mix_State.  apply H14. 
  pose (@Par_Pure_State_kron s e q x). 
  assert((PMpar_trace q s x) = (PMpar_trace m s x)).
  rewrite Heqq. rewrite PMpar_trace_assoc; try lia; try assumption.
  reflexivity. 
  assert((PMpar_trace q x e) = (PMpar_trace m x e)).
  rewrite Heqq. rewrite PMpar_trace_assoc; try lia; try assumption.
  reflexivity.
  assert(q= (@trace (2^(e-s)) q) .* @kron (2^(x-s)) (2^(x-s)) (2^(e-x)) (2^(e-x)) 
  (/(@trace (2^(x-s)) ((PMpar_trace q s x))) .* (PMpar_trace q s x))
  (/(@trace (2^(e-x)) ((PMpar_trace q x e))) .* (PMpar_trace q x e))).
  rewrite <-e1; try lia; try assumption.  
  rewrite Mscale_assoc. rewrite Cinv_r. rewrite Mscale_1_l. reflexivity.
  apply C0_fst_neq. apply Rgt_neq_0.
  apply mixed_state_trace_gt0. apply H15.
  left. econstructor. exists (outer_product v v).
  assert( 0<R1<=1)%R. lra.  
  split. apply H18. split. econstructor. split.
  apply H4. unfold outer_product. reflexivity.
  rewrite Mscale_1_l. 
   rewrite H16. apply H13. 
  rewrite H18. rewrite H16. rewrite H17. 
  rewrite H13. rewrite H9.
  assert((@trace (2^(e-s)) q)= C1).
  rewrite Heqq. rewrite Heqm. 
  rewrite Ptrace_trace; try lia.
  rewrite Rdiv_unfold. rewrite Rmult_1_l.
  rewrite trace_mult_dist.
  assert(@trace (2^(e0-s0)) (d_find x0 mu) = (fst (@trace (2^(e0-s0)) (d_find x0 mu)), snd (@trace (2^(e0-s0)) (d_find x0 mu)))).
  destruct (@trace (2^(e0-s0)) (d_find x0 mu)). simpl. reflexivity.
  rewrite H19. rewrite mixed_state_trace_real; try apply H14.
  rewrite Cmod_snd_0; try simpl; try apply mixed_state_trace_gt0;
  try apply mixed_state_trace_real; try apply H14; try reflexivity.
  rewrite RtoC_inv;  try apply C0_fst_neq; try apply Rgt_neq_0;
  try apply mixed_state_trace_gt0; try apply H14.
  rewrite Cinv_l; try apply C0_fst_neq; try apply Rgt_neq_0;
  try apply mixed_state_trace_gt0; try apply H14. reflexivity.
  auto_wf. rewrite H19. Msimpl.
  unfold outer_product.    rewrite trace_mult'.
  destruct H4. rewrite H20.
  rewrite trace_mult'. 
  destruct H5. rewrite H21.
  repeat rewrite trace_I.
  rewrite <-RtoC_inv; try lra. rewrite Rinv_1. 
  Msimpl. rewrite <-kron_mixed_product.
  reflexivity. 
Qed.


Theorem  rule_Separ':forall s x e u v, 
 s<x/\x<e-> Pure_State_Vector u -> Pure_State_Vector v ->
(( (| v ⊗ u >[ s , e ])) ->>
((| v >[ s , x ]) ⊗* (| u >[ x , e ]))).
Proof.   
intros.  unfold assert_implies. simpl. 
intros. rewrite sat_Assert_to_State in *. 
rewrite seman_find in *. split. intuition.
split. intuition. intros. pose H3. 
apply H2 in n. simpl in *.
split. unfold NSet.Equal.  intros. split. 
intros. pose H4. apply NSet.inter_1 in i. 
apply NSet.inter_2 in H4. apply In_Qsys in H4; try lia.  
apply In_Qsys in i; try lia.  intros. 
apply In_empty in H4. destruct H4. 
remember (((R1 / Cmod (trace (d_find x0 mu)))%R .* d_find x0 mu)).
remember (PMpar_trace m s e).
assert( WF_qstate (d_find x0 mu)). apply WF_dstate_per_state; try assumption.
apply H2.
assert( WF_qstate q). rewrite Heqq. apply Mix_par_trace; try lia; 
try assumption. rewrite Heqm. 
rewrite Rdiv_unfold. rewrite Rmult_1_l.
split; try lia. apply Mixed_State_aux_to01.
apply Mixed_State_aux_to_Mix_State. apply H4.
destruct n. 
destruct H7. destruct H8. destruct H9.
split; split; try assumption; try split; try lia;
try split; try lia; try split; try lia.   
assert((PMpar_trace q s x) = (PMpar_trace m s x)).
rewrite Heqq. rewrite PMpar_trace_assoc; try lia; try assumption.
reflexivity. rewrite<-H11. 
 unfold outer_product in *.
assert ((@adjoint (2^(e-s)) 1 (@kron (2^(x-s)) 1 (2^(e-x)) 1 v u))=(v ⊗ u) †).
f_equal. type_sovle'. rewrite H12 in H10.
rewrite kron_adjoint in H10.
assert((@Mmult (2^(e-s)) 1 (2^(e-s)) (v ⊗ u) ) ((v) † ⊗ (u) †)=
v ⊗ u × ((v) † ⊗ (u) †)). f_equal; type_sovle'.
rewrite H13 in H10.
rewrite kron_mixed_product in H10. destruct H0. destruct H1.  
rewrite PMpar_trace_L; try lia; try assumption; auto_wf.
rewrite (PMpar_trace_l _ (v × (v) †) ((u × (u) †))); try lia; try assumption;  auto_wf.
rewrite trace_mult'.  rewrite H14. rewrite trace_I.
Msimpl. reflexivity.

assert((PMpar_trace q x e) = (PMpar_trace m x e)).
rewrite Heqq. rewrite PMpar_trace_assoc; try lia; try assumption.
reflexivity. rewrite<-H11. 
 unfold outer_product in *.
assert ((@adjoint (2^(e-s)) 1 (@kron (2^(x-s)) 1 (2^(e-x)) 1 v u))=(v ⊗ u) †).
f_equal. type_sovle'. rewrite H12 in H10.
rewrite kron_adjoint in H10.
assert((@Mmult (2^(e-s)) 1 (2^(e-s)) (v ⊗ u) ) ((v) † ⊗ (u) †)=
v ⊗ u × ((v) † ⊗ (u) †)). f_equal; type_sovle'.
rewrite H13 in H10.
rewrite kron_mixed_product in H10. destruct H0. destruct H1.  
rewrite PMpar_trace_R; try lia; try assumption; auto_wf.
rewrite (PMpar_trace_r _ (v × (v) †) ((u × (u) †))); try lia; try assumption;  auto_wf.
rewrite trace_mult'.  rewrite H15. rewrite trace_I.
Msimpl. reflexivity.
Qed. 
  
Theorem  rule_odotT: forall qs1 qs2, 
(((qs1) ⊗* (qs2)) <<->> ((qs1)  ⊙ (qs2))) .
Proof. rule_solve.   Qed.
 


Local Open Scope assert_scope.
Import ParDensityO.
Lemma dstate_eq_not_nil: forall s e (mu mu':dstate s e),
dstate_eq mu mu' -> StateMap.this mu <> []
->StateMap.this mu' <> [].
Proof. intros s e(mu,IHmu) (mu', IHmu').
       unfold dstate_eq.
       induction mu; induction mu'.
       - simpl. intuition  .
       -simpl. intuition.
       -simpl. destruct a. intuition. 
       -simpl. destruct a. destruct a0.
        intros. discriminate.
Qed.

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

Import Ceval_Linear.

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

Require Import Forall_two.
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
       rewrite swap_get_pro.
       apply Forall_swap. assumption. 
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
length nF1 =length p_n ->
(Forall_two (fun (f_i g_i: State_formula) => f_i ->> g_i) nF1 nF2)->
((npro_to_pro_formula nF1 p_n) ->> (npro_to_pro_formula nF2 p_n)).
Proof. intros.    unfold assert_implies. intros. 
inversion_clear H1. inversion_clear H4.
econstructor. intuition.
econstructor; rewrite (get_pro_formula_eq nF1);
try rewrite <-(Forall_two_length_eq _ _ _ H0);
inversion_clear H3; try assumption.
econstructor. rewrite (get_pro_formula_eq  nF1 _  _).
apply H1. assumption.
rewrite <-(Forall_two_length_eq _ _ _ H0); assumption. 
assumption.
eapply big_and_impiles. apply H6. apply H0.
Qed.

Theorem  rule_OCon': forall (nF1 nF2:npro_formula) ,
(Forall_two (fun (x y: State_formula)=> x ->> y) nF1 nF2)
->(nF1->> nF2).
Proof. intros.    unfold assert_implies. intros. 
inversion_clear H0. 
econstructor.  
rewrite<- (Forall_two_length_eq _ _ _ H). apply H1.
assert((npro_to_pro_formula nF1 p_n) ->> (npro_to_pro_formula nF2 p_n)).
apply rule_OCon. intuition. intuition. apply H0. assumption.
Qed.

Theorem rule_OdotO': forall (F1 F2:State_formula), 
 ((F1 ⊙ F2) ->> (F1 /\s F2)) .
Proof.  rule_solve. Qed.


Theorem rule_OMerg:forall (p0 p1:R) (F:State_formula) (pF:pro_formula),
0< p0<1/\ 0< p1 <1->
APro ((p0 , F) :: ( p1, F) :: pF) ->> APro (((p0+p1), F):: pF).
Proof. intros. unfold assert_implies. intros.

  inversion_clear H. inversion_clear H0.
  inversion_clear H4. 
  econstructor. intuition. unfold distribution_formula in *. 
  destruct H3. inversion_clear H3.  inversion_clear H8.
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
sat_Assert mu F1.
Proof. intros. split; intros. inversion_clear H. rewrite sat_Assert_to_State. eapply sat_Pro_State. apply H2.
       econstructor. eapply WF_sat_Assert. apply H. econstructor. simpl. 
       econstructor. lra. econstructor. lra. econstructor.
       simpl. repeat rewrite sum_over_list_cons. repeat rewrite sum_over_list_nil.
       rewrite Rplus_0_l. rewrite Rplus_0_r. reflexivity.
       apply sat_Pro_State. apply sat_Assert_to_State. assumption.
Qed.

Lemma sat_NPro_State{s e:nat}: forall (mu:dstate s e) (F0 F1:State_formula),
sat_Assert mu F0 ->
sat_Assert mu (ANpro [F0; F1]).
Proof. intros. assert([F0; F1]= pro_to_npro_formula ([(1, F0); (0, F1)])).
       reflexivity. rewrite H0. eapply rule_Oplus.
       assert([(1, F0); (0, F1)]= swap_list  ([(0, F1); (1, F0)]) 0).
       reflexivity. rewrite H1.
       apply rule_POplusC. 
       apply sat_Pro_State'. assumption.
Qed. 



Require Import ParDensityO.

Lemma  ruleState: forall s e (mu:list (state s e)) (sigma:cstate) (rho:qstate s e) H1 H2 F,
sat_State {| StateMap.this := (sigma, rho) :: mu;StateMap.sorted := H1 |} F-> mu<>nil ->
sat_State {| StateMap.this := mu; StateMap.sorted := H2 |} F.
Proof. intros.  
simpl in *. econstructor. inversion_clear H. inversion_clear H3. 
assumption.  apply State_eval_dstate_Forall.
assumption. inversion_clear H. inversion_clear H4. assumption.
Qed.


Lemma Rdiv_in01': forall p1 p2,
0 < p1 ->
0 < p2 ->
0 < p1 / (p1 + p2) <=1.
Proof. split.  rewrite Rdiv_unfold. apply Rmult_gt_0_compat.
intuition. apply Rinv_0_lt_compat. apply Rplus_lt_0_compat.
intuition. intuition. apply (Rcomplements.Rdiv_le_1 p1 _).
apply Rplus_lt_0_compat.
intuition. intuition.  assert(p1=p1+0)%R. rewrite Rplus_0_r.
reflexivity. rewrite H1 at 1. apply Rplus_le_compat_l.
intuition. 
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


Lemma app_fix{s e:nat} : forall c0 (q0:qstate s e) (d d':list (cstate * qstate s e)),
(fix map2_aux (m' : StateMap.Raw.t (qstate s e)) :
                 StateMap.Raw.t (qstate s e) :=
               match m' with
               | [] =>
                   (c0,  q0)
                   :: StateMap.Raw.map2_l option_app d
               | p :: l' =>
                   let (k', e') := p in
                   match Cstate_as_OT.compare c0 k' with
                   | OrderedType.LT _ =>
                       (c0,  q0)
                       :: StateMap.Raw.map2 option_app d  m'
                   | OrderedType.EQ _ =>
                       (c0, q0 .+ e')
                       :: StateMap.Raw.map2 option_app d  l'
                   | OrderedType.GT _ => (k', e') :: map2_aux l'
                   end
               end) d'= StateMap.Raw.map2 option_app ((c0, q0)::d)  d'
               .
Proof. destruct d'. simpl. reflexivity.
   destruct p. 
   destruct (Cstate_as_OT.compare c0 c);
   simpl; MC.elim_comp;  reflexivity.
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

Lemma d_seman_scale'': forall s e (p:R) (mu:dstate s e) (F:State_formula),
sat_State mu F -> 
sat_State (d_scale_not_0 (/d_trace mu) mu) F.
Proof. 
       intros. destruct mu as [mu IHmu]. 
       inversion H; subst. 
       simpl in H1.
       apply sat_F.
       apply WWF_dstate_aux_to_WF_dstate_aux in H0. 
       apply WWF_dstate_aux_to_WF_dstate_aux.
       split. 
       apply WWF_d_scale_not_0. 
       apply Rinv_0_lt_compat. apply (WF_dstate_gt0_le1).
       apply WF_sat_State in H. intuition.
       intuition. 
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



Local Open Scope R_scope.
Lemma  rule2: forall s e (mu:list (state s e)) (sigma:cstate) (rho:qstate s e) H1 H2
F0 F1 ,
sat_Assert {| StateMap.this := (sigma, rho) :: mu; StateMap.sorted := H1 |} (ANpro ([F0; F1]))
-> mu<>nil ->
sat_Assert {| StateMap.this := mu; StateMap.sorted := H2 |} (ANpro ([F0; F1])).
Proof. 
intros. inversion_clear H. destruct p_n.
simpl in *. discriminate H3. destruct p_n. 
discriminate H3. destruct p_n. clear H3.
inversion_clear H4.

assert(r=0\/ r<>0). 
apply Classical_Prop.classic.
destruct H4.  subst. 
(*r=0*)
econstructor. assert(length [0; r0] = length [F0; F1]).
reflexivity.  apply H4. simpl. 

inversion_clear H3. simpl in *. repeat rewrite sum_over_list_cons in * .
simpl in *. rewrite sum_over_list_nil in *.
rewrite Rplus_0_l in *. rewrite Rplus_0_r in *. subst.
apply sat_Pro_State in H5. apply sat_Pro_State'.
apply (ruleState _ _ _ _ _ _ H2) in H5. rewrite sat_Assert_to_State. 
assumption. assumption.

assert(r0=0\/ r0<>0). 
apply Classical_Prop.classic.
destruct H6.  subst.

(*r0=0*)
econstructor. assert(length [r; 0] = length [F0; F1]).
reflexivity.  apply H6. simpl. 
econstructor.   inversion_clear H. assumption. assumption. 

assert(sat_Assert{| StateMap.this := (sigma, rho) :: mu;
  StateMap.sorted := H1 |} (APro ([(0, F1); (r, F0)]))).
assert([(0, F1); (r, F0)] = swap_list [(r, F0); (0, F1)] 0).
simpl. reflexivity. rewrite H6. clear H6. apply rule_POplusC.
econstructor. assumption. assumption. assumption. clear H5. 

inversion_clear H3. simpl in *. repeat rewrite sum_over_list_cons in * .
simpl in *. rewrite sum_over_list_nil in *.
rewrite Rplus_0_l in *. rewrite Rplus_0_r in *. subst. 
apply sat_Pro_State' in H6.   rewrite sat_Assert_to_State in H6.
apply (ruleState _ _ _ _ _ _ H2) in H6. 
assert(sat_Assert {| StateMap.this := mu; StateMap.sorted := H2 |} (APro [(1, F0); (0, F1)])).
assert([(1, F0); (0, F1)] = swap_list [(0, F1); (1, F0)] 0).
reflexivity. rewrite H3. apply rule_POplusC.
apply sat_Pro_State'. rewrite sat_Assert_to_State. assumption.
inversion_clear H3. assumption. assumption. 

 (*r<>0/\r0<>0*)
inversion_clear H5.  
destruct mu_n. simpl in *. inversion_clear H7. 
destruct mu_n. simpl in *. inversion_clear H7.
inversion_clear H10. 
destruct mu_n. simpl in *. 

inversion H7; subst. inversion H15; subst.
inversion H17; subst. clear H17.
apply d_scale_to_not_0' in H14.
apply d_scale_to_not_0' in H16.
apply big_dapp'_to_app' in H7. 
simpl in H7. 
unfold dstate_eq in H8.
unfold d_app in H8. 
unfold StateMap.map2 in H8. 
simpl in H8. unfold StateMap.Raw.empty in H8.
rewrite map2_nil_r in H8. rewrite H14 in H8.
rewrite H16 in H8. clear H14. clear H16. 
clear H7. 
destruct d0 as [d0 IHd0]. destruct d as [d IHd].
destruct d0;  destruct d.
simpl in *. discriminate H8. inversion_clear H9. destruct H5. 
inversion_clear H3. inversion_clear H5. simpl. lra.  simpl in H5.  
inversion_clear H7. destruct H10. 
inversion_clear H3. inversion_clear H7. inversion_clear H12. simpl. lra.
apply WF_sat_State in H7. simpl in *. 
intuition. inversion_clear H9. 
destruct H5. 
inversion_clear H3. inversion_clear H5. simpl. lra. 
apply WF_sat_State in H5. simpl in *. intuition.
destruct p. destruct p0.
simpl in H8. 

inversion_clear H3.  inversion_clear H5. inversion_clear H10.
simpl in *. clear H11. simpl in *. 
repeat rewrite sum_over_list_cons in *. rewrite sum_over_list_nil in *.
rewrite Rplus_0_r in *.  simpl in *.
inversion_clear H9. inversion_clear H11. simpl in *.
destruct H10. lra. destruct H9. lra. clear H12. 
assert( WF_dstate_aux d). inversion_clear H10. inversion_clear H12. assumption.
assert(WF_state (c, q)). inversion_clear H9. inversion_clear H14. assumption.
assert( WF_dstate_aux d0). inversion_clear H9. inversion_clear H16. assumption.
assert(WF_state (c0, q0)). inversion_clear H10. inversion_clear H17. assumption.
destruct (Cstate_as_OT.compare c0 c). 
injection H8. intros. 

  
econstructor.  assert(length ([((r/ d_trace_aux mu) * d_trace_aux d); ((r0/ d_trace_aux mu) * d_trace_aux ((c,q)::d0))]) = length [F0; F1]).
reflexivity. apply H21.  simpl.  
 assert(distribution_formula
[(r / d_trace_aux mu * d_trace_aux d, F0);
 (r0 / d_trace_aux mu *
  (s_trace (c, q) + d_trace_aux d0), F1)]). 
econstructor. econstructor. simpl.
apply Rmult_le_pos. 
apply Rcomplements.Rdiv_le_0_compat. lra.
apply WF_dstate_gt0_le1. assumption.  inversion H. assumption.
apply WF_dstate_in01_aux. assumption.
 econstructor. simpl.
apply Rmult_le_pos. 
apply Rcomplements.Rdiv_le_0_compat. lra.
apply WF_dstate_gt0_le1. assumption.  inversion_clear H. assumption.
 assert(s_trace (c, q) + d_trace_aux d0=d_trace_aux ((c,q)::d0)).
 reflexivity. rewrite H21. 
 apply WF_dstate_in01_aux.  apply WF_sat_State in H9. 
 intuition. apply Forall_nil. simpl in *.
 repeat rewrite sum_over_list_cons. rewrite sum_over_list_nil.
 rewrite Rplus_0_r.  simpl. repeat rewrite Rdiv_unfold. 
 rewrite (Rmult_comm r).   rewrite (Rmult_comm r0).
 repeat rewrite Rmult_assoc. rewrite <-Rmult_plus_distr_l.
  assert(r * d_trace_aux d + r0 * (s_trace (c, q) + d_trace_aux d0)= d_trace_aux mu).
  rewrite H18. rewrite d_trace_app_aux. simpl. 
   repeat rewrite d_trace_map.
  unfold s_trace. simpl. 
  rewrite q_trace_scale. unfold q_trace. rewrite Rmult_plus_distr_l. reflexivity.
  lra. lra. lra. apply WWF_dstate_map. lra. 
 apply WWF_dstate_aux_to_WF_dstate_aux. assumption.
 econstructor.  apply WWF_qstate_scale. 
 split. lra.  apply WWF_qstate_to_WF_qstate. assumption.   
 apply WWF_dstate_map. lra.   apply WWF_dstate_aux_to_WF_dstate_aux.
 assumption. 
 rewrite <-H21. apply Rinv_l.  rewrite H21. 
 apply WWF_dstate_not_0. assumption.
 inversion_clear H. apply WWF_dstate_aux_to_WF_dstate_aux. 
 assumption. simpl. 
 econstructor. inversion_clear H. assumption. 
simpl. apply H21.

destruct d.  simpl in *. rewrite Rmult_0_r in *. 
inversion_clear H21. simpl in *.
 repeat rewrite sum_over_list_cons in H23.
rewrite sum_over_list_nil in *. rewrite Rplus_0_r in *.
simpl in *. rewrite Rplus_0_l in *. rewrite H23.


apply sat_Pro_State.  
econstructor. inversion_clear H. assumption.
simpl. rewrite H18. simpl. inversion_clear H9.
inversion_clear H24. econstructor. 
assert((@pair StateMap.Raw.key (qstate s e) c
(q_scale r0 q))= s_scale r0 (c,q)). reflexivity.
rewrite H24. apply s_seman_scale. lra. 
 assumption.
rewrite map2_r_refl. destruct d0. simpl. apply Forall_nil.
 apply State_eval_dstate_Forall. destruct p. simpl. discriminate.
apply d_seman_scale_aux. lra.  apply State_eval_dstate_Forall. discriminate.
apply H25. 


inversion_clear H1.  inversion_clear IHd.

econstructor. 
assert(big_dapp'
([r / d_trace_aux mu * d_trace_aux (((p::d)));
 r0 / d_trace_aux mu * (s_trace (c, q) + d_trace_aux d0)])

 ([d_scale_not_0 (d_trace_aux mu ) (d_scale_not_0 (R1/d_trace_aux (p::d)) (StateMap.Build_slist H24));
 d_scale_not_0 (d_trace_aux mu ) (d_scale_not_0 (R1/d_trace_aux (((c,q)::d0))) (StateMap.Build_slist IHd0))
 ])
 
 (d_app (d_scale_not_0 (r / d_trace_aux mu * d_trace_aux (((p::d)))) 
       (d_scale_not_0 (d_trace_aux mu ) (d_scale_not_0 (R1/d_trace_aux ((p::d))) (StateMap.Build_slist H24)))
 ) (d_app (d_scale_not_0 (r0 / d_trace_aux mu * (s_trace (c, q) + d_trace_aux d0)) (d_scale_not_0 (d_trace_aux mu ) (d_scale_not_0 (R1/d_trace_aux (((c,q)::d0))) (StateMap.Build_slist IHd0))) ) (d_empty s e)))).

 econstructor. 
 apply d_scalar_r.
 assert(
r / d_trace_aux mu * d_trace_aux (p :: d) > 0).
apply Rmult_gt_0_compat.
apply Rdiv_lt_0_compat.
lra. apply WF_dstate_gt0_le1.
assumption. inversion_clear H. assumption.
apply WF_dstate_gt0_le1. discriminate.
apply WF_sat_State in H10. assumption.
 lra.
 econstructor. 
 apply d_scalar_r.
 assert(r0 / d_trace_aux mu * (s_trace (c, q) + d_trace_aux d0) > 0).
 apply Rmult_gt_0_compat.
apply Rdiv_lt_0_compat.
lra. apply WF_dstate_gt0_le1.
assumption. inversion_clear H. assumption.
assert(s_trace (c, q) + d_trace_aux d0= d_trace_aux ((c,q)::d0)).
simpl. reflexivity. rewrite H26.
apply WF_dstate_gt0_le1. discriminate.
apply WF_sat_State in H9. intuition.
 lra.
 apply big_dapp_nil. simpl.
apply H26. 
apply dstate_eq_trans with (d_app (d_scale_not_0 r (StateMap.Build_slist H24))
(d_scale_not_0 r0 (StateMap.Build_slist (IHd0)))).
unfold dstate_eq. unfold d_app.
unfold StateMap.map2. unfold d_scale_not_0.
unfold StateMap.map. simpl. assumption.
apply d_app_eq. 
apply dstate_eq_sym. 
eapply dstate_eq_trans. 
apply d_scale_not_0_assoc. 
eapply dstate_eq_trans. 
apply d_scale_not_0_assoc.
unfold dstate_eq.
f_equal. f_equal. 
repeat rewrite Rdiv_unfold. rewrite Rmult_1_l.
 rewrite Rmult_assoc. rewrite Rmult_assoc.
 rewrite <-(Rmult_assoc (d_trace_aux ((p :: d)))) . 
 rewrite (Rmult_comm (d_trace_aux ((p :: d)) )).
repeat   rewrite Rmult_assoc . 
 rewrite Rinv_r. rewrite Rmult_1_r. 
 rewrite Rinv_l. rewrite Rmult_1_r. reflexivity.
 apply WWF_dstate_not_0. assumption.
 inversion_clear H. apply WWF_dstate_aux_to_WF_dstate_aux. 
 assumption. 
 apply WWF_dstate_not_0. discriminate.
apply WF_sat_State in H10. 
 apply WWF_dstate_aux_to_WF_dstate_aux. 
 assumption. 
 eapply dstate_eq_trans.
 apply dstate_eq_sym. 
 apply d_app_empty_l.
 eapply dstate_eq_trans.
 apply d_app_comm.
 apply d_app_eq.
 apply dstate_eq_sym. 
eapply dstate_eq_trans. 
apply d_scale_not_0_assoc. 
eapply dstate_eq_trans. 
apply d_scale_not_0_assoc.
unfold dstate_eq.
f_equal. f_equal.  
repeat rewrite Rdiv_unfold. rewrite Rmult_1_l.
 rewrite Rmult_assoc. rewrite Rmult_assoc.
 rewrite <-(Rmult_assoc (s_trace (c, q) + d_trace_aux d0)) . 
 rewrite (Rmult_comm (s_trace (c, q) + d_trace_aux d0)).
repeat   rewrite Rmult_assoc . 
 rewrite Rinv_r. rewrite Rmult_1_r. 
 rewrite Rinv_l. rewrite Rmult_1_r. reflexivity.
 apply WWF_dstate_not_0. assumption.
 inversion_clear H. apply WWF_dstate_aux_to_WF_dstate_aux. 
 assumption. 
 apply WWF_dstate_not_0. discriminate.
 apply WWF_dstate_aux_to_WF_dstate_aux.
 apply WF_sat_State in H9.  apply H9.  
  reflexivity.
 
simpl. econstructor. intros. split. apply d_seman_scale.
apply WF_dstate_gt0_le1. assumption.
inversion_clear H. 
assumption.
assert((R1 / (s_trace p + d_trace_aux d))=
/d_trace ({|
  StateMap.this := p :: d;
  StateMap.sorted := H24
|})).  rewrite Rdiv_unfold.
unfold d_trace. rewrite Rmult_1_l. simpl. reflexivity.
rewrite H27.
 apply d_seman_scale''. intuition.
 apply (ruleState _ _ _ c0 q0 IHd).
 assumption. discriminate. 
 rewrite d_trace_scale_not_0.
rewrite d_trace_scale_not_0.
unfold d_trace.  simpl. 
rewrite Rdiv_unfold. rewrite Rmult_1_l.
rewrite Rinv_l. rewrite Rmult_1_r. reflexivity.
assert((s_trace p + d_trace_aux d = d_trace_aux (p::d))).
reflexivity. rewrite H27.
apply WWF_dstate_not_0.
discriminate. apply WWF_dstate_aux_to_WF_dstate_aux. 
apply WF_sat_State in H10.  assumption.
rewrite Rdiv_unfold.
rewrite Rmult_1_l.
apply Rinv_0_lt_compat.
assert((s_trace p + d_trace_aux d = d_trace_aux (p::d))).
reflexivity. rewrite H27.
apply WF_dstate_gt0_le1.
discriminate.  
apply WF_sat_State in H10.  assumption.
apply WF_dstate_gt0_le1. assumption.
inversion_clear H. assumption.
 econstructor. intros. split.
apply d_seman_scale.
apply WF_dstate_gt0_le1. assumption.
inversion_clear H.  assumption.
assert((R1 / (s_trace (c,q) + d_trace_aux d0))=
/d_trace ({|
  StateMap.this :=  (c, q) :: d0;
  StateMap.sorted := IHd0
|})).  rewrite Rdiv_unfold.
unfold d_trace. rewrite Rmult_1_l. simpl. reflexivity.
rewrite H27.
 apply d_seman_scale''. intuition.
 assumption. 
 rewrite d_trace_scale_not_0.
rewrite d_trace_scale_not_0. 
unfold d_trace. simpl.
rewrite Rdiv_unfold. rewrite Rmult_1_l.
rewrite Rinv_l. rewrite Rmult_1_r. reflexivity.
assert((s_trace (c,q) + d_trace_aux d0 = d_trace_aux ((c,q)::d0))).
reflexivity. rewrite H27.
apply WWF_dstate_not_0.
discriminate. apply WWF_dstate_aux_to_WF_dstate_aux. 
apply WF_sat_State in H9. intuition.
assert((R1 / (s_trace (c,q) + d_trace_aux d0))=
/d_trace ({|
  StateMap.this :=  (c, q) :: d0;
  StateMap.sorted := IHd0
|})). rewrite Rdiv_unfold.
unfold d_trace.  rewrite Rmult_1_l. simpl. reflexivity.
rewrite H27.
apply Rinv_0_lt_compat.
apply WF_dstate_gt0_le1.
discriminate. 
apply WF_sat_State in H9. intuition. 
apply WF_dstate_gt0_le1. assumption.
 inversion_clear H. assumption. 
 econstructor.


- injection H8. intros.
econstructor. 
assert(length ([((r/ d_trace_aux mu) * d_trace_aux d); (r0/ d_trace_aux mu) * d_trace_aux (d0)]) = length [F0; F1]).
reflexivity. apply H21. simpl. 
 assert(distribution_formula
 [(r / d_trace_aux mu * d_trace_aux d, F0);
   (r0 / d_trace_aux mu * d_trace_aux d0, F1)]). 
simpl. econstructor.
econstructor.  simpl. apply Rmult_le_pos. 
apply Rcomplements.Rdiv_le_0_compat. lra.
apply WF_dstate_gt0_le1. assumption.  inversion H. assumption.
apply WF_dstate_in01_aux. assumption. 
econstructor. simpl. apply Rmult_le_pos. 
apply Rcomplements.Rdiv_le_0_compat. lra.
apply WF_dstate_gt0_le1. assumption.  inversion_clear H. assumption.
 apply WF_dstate_in01_aux. assumption. 
 apply Forall_nil. simpl in *. 
repeat rewrite sum_over_list_cons.
rewrite sum_over_list_nil. 
rewrite Rplus_0_r.  simpl. 
repeat rewrite Rdiv_unfold. 
 rewrite Rmult_comm. rewrite <-Rmult_assoc.
 rewrite (Rmult_comm _ (d_trace_aux d0)). 
 rewrite <-Rmult_assoc.  rewrite <-Rmult_plus_distr_r.
 assert(r * d_trace_aux d + r0 * ( d_trace_aux d0)= d_trace_aux mu).
  rewrite H18. rewrite d_trace_app_aux. simpl.
   repeat rewrite d_trace_map.
 reflexivity.
  lra. lra. apply WWF_dstate_map. lra. 
 apply WWF_dstate_aux_to_WF_dstate_aux. assumption.
 apply WWF_dstate_map. lra.  apply WWF_dstate_aux_to_WF_dstate_aux.
 assumption. 
 rewrite <-H21. rewrite (Rmult_comm _ r).
 rewrite (Rmult_comm _ r0). apply Rinv_r.  rewrite H21. 
 apply WWF_dstate_not_0. assumption.
 inversion_clear H. apply WWF_dstate_aux_to_WF_dstate_aux. 
 assumption. 
econstructor. inversion_clear H. assumption.
apply H21. 


destruct d. destruct d0.
simpl in *. intuition.
simpl in *. rewrite Rmult_0_r in *.
inversion_clear H21. simpl in *.
repeat rewrite sum_over_list_cons in H23.
rewrite sum_over_list_nil in *. rewrite Rplus_0_r in *.
simpl in *. rewrite Rplus_0_l in *. rewrite H23.

apply sat_Pro_State. 
econstructor. inversion_clear H. assumption. destruct p. 
simpl. rewrite H18. simpl. inversion_clear H9.
inversion_clear H24. inversion_clear H25. econstructor. 
assert((@pair StateMap.Raw.key (qstate s e) c1
((q_scale r0 q1)))= s_scale r0 (c1,q1)). reflexivity.
rewrite H25. apply s_seman_scale. lra. 
 assumption. 
rewrite map2_r_refl. destruct d0. simpl. apply Forall_nil.
 apply State_eval_dstate_Forall. destruct p. simpl. discriminate.
apply d_seman_scale_aux. lra.  apply State_eval_dstate_Forall. discriminate.
apply H26.


destruct d0.
 simpl in *. rewrite Rmult_0_r in *.
inversion_clear H21. simpl in *.  
repeat rewrite sum_over_list_cons in H23.
rewrite sum_over_list_nil in *. rewrite Rplus_0_r in *.
simpl in *. rewrite Rplus_0_r in *. rewrite H23.

assert(sat_Assert {| StateMap.this := mu; StateMap.sorted := H2 |} (APro [(1, F0); (0, F1)])).
assert(( [(1, F0); (0, F1)])= swap_list ( [(0, F1); (1, F0)]) 0).
reflexivity. rewrite H21. apply rule_POplusC. 
apply sat_Pro_State'. rewrite sat_Assert_to_State. 
econstructor. inversion_clear H. assumption.  
rewrite H18. destruct p.  simpl.  inversion_clear H10.
inversion_clear H25. inversion_clear H26. econstructor. 
assert((@pair StateMap.Raw.key (qstate s e) c1
(q_scale r q1))= s_scale r (c1,q1)). reflexivity.
rewrite H26. apply s_seman_scale. lra.
inversion_clear H26.  assumption.
rewrite map2_l_refl. destruct d. apply Forall_nil.
apply State_eval_dstate_Forall. simpl. destruct p. discriminate.
apply d_seman_scale_aux. lra. 
 apply State_eval_dstate_Forall. discriminate. 
apply H27. inversion_clear H21. assumption. 


inversion_clear IHd.
inversion_clear IHd0. 

econstructor. 
assert(big_dapp'
([r / d_trace_aux mu * d_trace_aux ((p :: d));
 r0 / d_trace_aux mu * ( d_trace_aux ((p0 :: d0)))])

 ([d_scale_not_0 (d_trace_aux mu ) (d_scale_not_0 (R1/d_trace_aux ((p :: d))) (StateMap.Build_slist H22));
 d_scale_not_0 (d_trace_aux mu ) (d_scale_not_0 (R1/d_trace_aux ((p0 :: d0))) (StateMap.Build_slist H24))
 ])
 
 (d_app (d_scale_not_0 (r / d_trace_aux mu * d_trace_aux ((p :: d))) 
       (d_scale_not_0 (d_trace_aux mu ) (d_scale_not_0 (R1/d_trace_aux ((p :: d))) (StateMap.Build_slist H22)))
 ) (d_app (d_scale_not_0 (r0 / d_trace_aux mu * (d_trace_aux (p0 :: d0))) (d_scale_not_0 (d_trace_aux mu ) (d_scale_not_0 (R1/d_trace_aux (p0 :: d0)) (StateMap.Build_slist H24))) ) (d_empty s e)))).

 econstructor. apply d_scalar_r.
 assert(
  r / d_trace_aux mu * d_trace_aux (p :: d) > 0).
  apply Rmult_gt_0_compat.
  apply Rdiv_lt_0_compat.
  lra. apply WF_dstate_gt0_le1.
  assumption. inversion_clear H. assumption.
  apply WF_dstate_gt0_le1. discriminate. 
  apply WF_sat_State in H10. assumption.
   lra.
   econstructor. 
 
 apply d_scalar_r. 
 assert(
r0 / d_trace_aux mu * d_trace_aux (p0 :: d0) > 0).
apply Rmult_gt_0_compat.
apply Rdiv_lt_0_compat.
lra. apply WF_dstate_gt0_le1.
assumption. inversion_clear H. assumption.
apply WF_dstate_gt0_le1. discriminate. assumption.
 lra.
 apply big_dapp_nil.
apply H26. 
apply dstate_eq_trans with (d_app (d_scale_not_0 r (StateMap.Build_slist H22))
(d_scale_not_0 r0 (StateMap.Build_slist (H24)))).
unfold dstate_eq. unfold d_app.
unfold StateMap.map2. unfold d_scale_not_0.
unfold StateMap.map. simpl. assumption.
apply d_app_eq. 
apply dstate_eq_sym. 
eapply dstate_eq_trans. 
apply d_scale_not_0_assoc. 
eapply dstate_eq_trans. 
apply d_scale_not_0_assoc.
unfold dstate_eq.
f_equal. f_equal. 
repeat rewrite Rdiv_unfold. rewrite Rmult_1_l.
 rewrite Rmult_assoc. rewrite Rmult_assoc.
 rewrite <-(Rmult_assoc (d_trace_aux (p :: d))) . 
 rewrite (Rmult_comm (d_trace_aux (p :: d))).
repeat   rewrite Rmult_assoc . 
 rewrite Rinv_r. rewrite Rmult_1_r. 
 rewrite Rinv_l. rewrite Rmult_1_r. reflexivity.
 apply WWF_dstate_not_0. assumption.
 inversion_clear H. apply WWF_dstate_aux_to_WF_dstate_aux. assumption.
 apply WWF_dstate_not_0. discriminate.
 apply WWF_dstate_aux_to_WF_dstate_aux.
 inversion_clear H14. inversion_clear H21.
 assumption.
 
 eapply dstate_eq_trans.
 apply dstate_eq_sym. 
 apply d_app_empty_l.
 eapply dstate_eq_trans.
 apply d_app_comm.
 apply d_app_eq.
 apply dstate_eq_sym. 
eapply dstate_eq_trans. 
apply d_scale_not_0_assoc. 
eapply dstate_eq_trans. 
apply d_scale_not_0_assoc.
unfold dstate_eq.
f_equal. f_equal.  
repeat rewrite Rdiv_unfold. rewrite Rmult_1_l.
 rewrite Rmult_assoc. rewrite Rmult_assoc.
 rewrite <-(Rmult_assoc ( d_trace_aux ((p0 :: d0)))) . 
 rewrite (Rmult_comm ( d_trace_aux ((p0 :: d0)))).
repeat   rewrite Rmult_assoc . 
 rewrite Rinv_r. rewrite Rmult_1_r. 
 rewrite Rinv_l. rewrite Rmult_1_r. reflexivity.

 apply WWF_dstate_not_0. assumption.
 inversion_clear H. apply WWF_dstate_aux_to_WF_dstate_aux. assumption.
 apply WWF_dstate_not_0. discriminate.
 apply WWF_dstate_aux_to_WF_dstate_aux. assumption.
  reflexivity.
 
simpl. econstructor. intros. split.   apply d_seman_scale.
apply WF_dstate_gt0_le1. assumption.
inversion_clear H. 
assumption. 

assert((R1 / (s_trace p + d_trace_aux d))=
/d_trace ({|
  StateMap.this :=  p :: d;
  StateMap.sorted := H22
|})).  rewrite Rdiv_unfold.
unfold d_trace. rewrite Rmult_1_l. simpl. reflexivity.
rewrite H27.
 apply d_seman_scale''. intuition.
 apply (ruleState _ _ _ c0 q0 IHd).
 assumption. discriminate. 
 rewrite d_trace_scale_not_0.
 rewrite d_trace_scale_not_0. 
 unfold d_trace. simpl.
 rewrite Rdiv_unfold. rewrite Rmult_1_l.
 rewrite Rinv_l. rewrite Rmult_1_r. reflexivity.
 assert((s_trace p + d_trace_aux d= d_trace_aux (p::d))).
 reflexivity. rewrite H27.
 apply WWF_dstate_not_0.
 discriminate. apply WWF_dstate_aux_to_WF_dstate_aux. assumption.
 assert((R1 / (s_trace p + d_trace_aux d))=
 /d_trace ({|
   StateMap.this :=  p :: d;
   StateMap.sorted := H22
 |})).  rewrite Rdiv_unfold.
 unfold d_trace. rewrite Rmult_1_l. simpl. reflexivity.
 rewrite H27. 
 apply Rinv_0_lt_compat.  
 apply WF_dstate_gt0_le1. discriminate. assumption.
   apply WF_dstate_gt0_le1. assumption.
  inversion_clear H. assumption.
 econstructor. intros. split.
apply d_seman_scale.
apply WF_dstate_gt0_le1. assumption.
inversion_clear H.  assumption.
assert((R1 / (s_trace p0 + d_trace_aux d0))=
/d_trace ({|
  StateMap.this :=  p0 :: d0;
  StateMap.sorted := H24
|})).  rewrite Rdiv_unfold.
unfold d_trace. rewrite Rmult_1_l. simpl. reflexivity.
rewrite H27.
 apply d_seman_scale''. intuition.
 apply (ruleState _ _ _ c q IHd0).
 assumption. discriminate.
 rewrite d_trace_scale_not_0.
rewrite d_trace_scale_not_0. 
unfold d_trace. simpl.
rewrite Rdiv_unfold. rewrite Rmult_1_l.
rewrite Rinv_l. rewrite Rmult_1_r. reflexivity.
assert((s_trace p0 + d_trace_aux d0= d_trace_aux (p0::d0))).
reflexivity. rewrite H27.
apply WWF_dstate_not_0.
discriminate. apply WWF_dstate_aux_to_WF_dstate_aux. 
apply WF_sat_State in H9. destruct H9. inversion_clear H22.
 intuition.
 assert((R1 / (s_trace p0 + d_trace_aux d0))=
/d_trace ({|
  StateMap.this :=  p0 :: d0;
  StateMap.sorted := H24
|})).  rewrite Rdiv_unfold.
unfold d_trace. rewrite Rmult_1_l. simpl. reflexivity.
rewrite H27.  
apply Rinv_0_lt_compat. 
apply WF_dstate_gt0_le1. discriminate.
assumption.
apply WF_dstate_gt0_le1. assumption.
 inversion_clear H. assumption.
econstructor.


-injection H8. intros. 
econstructor.
assert(length ([((r/ d_trace_aux mu) * d_trace_aux ((c0,q0)::d)); (r0/ d_trace_aux mu) * d_trace_aux (d0)]) = length [F0; F1]).
reflexivity. apply H21. simpl.
assert(distribution_formula[(r / d_trace_aux mu *
(s_trace (c0, q0) + d_trace_aux d), F0);
(r0 / d_trace_aux mu * d_trace_aux d0, F1)]). 
simpl. econstructor.  simpl. econstructor.
  simpl. apply Rmult_le_pos. 
apply Rcomplements.Rdiv_le_0_compat. lra.
apply WF_dstate_gt0_le1. assumption.  inversion H. assumption.
assert(s_trace (c0, q0) + d_trace_aux d=d_trace_aux ((c0,q0)::d)).
 reflexivity. rewrite H21.
 apply WF_dstate_in01_aux. apply WF_sat_State in H10.
 intuition. 
 econstructor. simpl.
 apply Rmult_le_pos. 
apply Rcomplements.Rdiv_le_0_compat. lra.
apply WF_dstate_gt0_le1. assumption.  inversion H. assumption.
 apply WF_dstate_in01_aux. assumption.  
 
 apply Forall_nil. simpl in *.
repeat rewrite sum_over_list_cons.
rewrite sum_over_list_nil. 
rewrite Rplus_0_r.  simpl. 
repeat rewrite Rdiv_unfold. 
 rewrite (Rmult_comm r).   rewrite (Rmult_comm r0).
 repeat rewrite Rmult_assoc. rewrite <-Rmult_plus_distr_l.
  assert(r * ((s_trace (c0, q0) + d_trace_aux d)) + r0 * ( d_trace_aux d0)= d_trace_aux mu).
  rewrite H18. rewrite app_fix. rewrite d_trace_app_aux. simpl.
   repeat rewrite d_trace_map. unfold s_trace. simpl.
  rewrite q_trace_scale. rewrite Rmult_plus_distr_l. reflexivity.
  lra. lra. lra.  
 econstructor.  apply WWF_qstate_scale. 
 split. lra. apply WWF_qstate_to_WF_qstate. assumption.     
 apply WWF_dstate_map. lra.  apply WWF_dstate_aux_to_WF_dstate_aux.
 assumption. 
 apply WWF_dstate_map. lra. 
 apply WWF_dstate_aux_to_WF_dstate_aux. assumption. 
 rewrite <-H21. apply Rinv_l.  rewrite H21. 
 apply WWF_dstate_not_0. assumption.
 inversion_clear H. apply WWF_dstate_aux_to_WF_dstate_aux. 
 assumption. simpl. 
 econstructor. inversion_clear H. assumption. 
simpl. apply H21.


destruct d0.
 simpl in *. rewrite Rmult_0_r in *.
inversion_clear H21.  simpl in *.
 repeat rewrite sum_over_list_cons in H23.
rewrite sum_over_list_nil in *. rewrite Rplus_0_r in *.
simpl in *. rewrite Rplus_0_r in *. rewrite H23.

assert(sat_Assert {| StateMap.this := mu; StateMap.sorted := H2 |} (APro [(1, F0); (0, F1)])).
assert(( [(1, F0); (0, F1)])= swap_list ( [(0, F1); (1, F0)]) 0).
reflexivity. rewrite H21. apply rule_POplusC. 
apply sat_Pro_State'. rewrite sat_Assert_to_State. 
econstructor. inversion_clear H. assumption.
simpl.  
rewrite H18. simpl.  inversion_clear H10.
inversion_clear H25. econstructor. 
assert((@pair StateMap.Raw.key (qstate s e) c0
(q_scale r q0))= s_scale r (c0,q0)). reflexivity.
rewrite H25. apply s_seman_scale. lra.
 assumption.
rewrite map2_l_refl. destruct d. apply Forall_nil.
apply State_eval_dstate_Forall. destruct p. simpl.  discriminate.
apply d_seman_scale_aux. lra.  apply State_eval_dstate_Forall. discriminate.
apply H26.  inversion_clear H21. assumption. 

inversion_clear IHd0.

econstructor. 
assert(big_dapp'
([r / d_trace_aux mu * d_trace_aux (((c0,q0)::d));
 r0 / d_trace_aux mu * ( d_trace_aux ((p :: d0)))])

 ([d_scale_not_0 (d_trace_aux mu ) (d_scale_not_0 (R1/d_trace_aux ((c0,q0)::d)) (StateMap.Build_slist IHd));
 d_scale_not_0 (d_trace_aux mu ) (d_scale_not_0 (R1/d_trace_aux ((p :: d0))) (StateMap.Build_slist H22))
 ])
 
 (d_app (d_scale_not_0 (r / d_trace_aux mu * d_trace_aux (((c0,q0)::d))) 
       (d_scale_not_0 (d_trace_aux mu ) (d_scale_not_0 (R1/d_trace_aux ((c0,q0)::d)) (StateMap.Build_slist IHd)))
 ) (d_app (d_scale_not_0 (r0 / d_trace_aux mu * (d_trace_aux ((p :: d0)))) (d_scale_not_0 (d_trace_aux mu ) (d_scale_not_0 (R1/d_trace_aux ((p :: d0))) (StateMap.Build_slist H22))) ) (d_empty s e)))).

 econstructor. apply d_scalar_r.
 assert(
r / d_trace_aux mu * d_trace_aux ((c0,q0) :: d) > 0).
apply Rmult_gt_0_compat.
apply Rdiv_lt_0_compat.
lra. apply WF_dstate_gt0_le1.
assumption. inversion_clear H. assumption.
apply WF_dstate_gt0_le1. discriminate.
apply WF_sat_State in H10. intuition.
 lra.
 econstructor.  
 apply d_scalar_r. 
 assert(
r0 / d_trace_aux mu * d_trace_aux (p :: d0) > 0).
apply Rmult_gt_0_compat.
apply Rdiv_lt_0_compat.
lra. apply WF_dstate_gt0_le1.
assumption. inversion_clear H. assumption.
apply WF_dstate_gt0_le1. discriminate. assumption.
 lra.
 apply big_dapp_nil.
apply H24. 
apply dstate_eq_trans with (d_app (d_scale_not_0 r (StateMap.Build_slist IHd))
(d_scale_not_0 r0 (StateMap.Build_slist (H22)))).
unfold dstate_eq. unfold d_app.
unfold StateMap.map2. unfold d_scale_not_0.
unfold StateMap.map. simpl. assumption.
apply d_app_eq. 
apply dstate_eq_sym. 
eapply dstate_eq_trans. 
apply d_scale_not_0_assoc. 
eapply dstate_eq_trans. 
apply d_scale_not_0_assoc.
unfold dstate_eq.
f_equal. f_equal. 
repeat rewrite Rdiv_unfold. rewrite Rmult_1_l.
 rewrite Rmult_assoc. rewrite Rmult_assoc.
 rewrite <-(Rmult_assoc (d_trace_aux (((c0, q0) :: d)))) . 
 rewrite (Rmult_comm (d_trace_aux ((c0, q0) :: d) )).
repeat   rewrite Rmult_assoc . 
 rewrite Rinv_r. rewrite Rmult_1_r. 
 rewrite Rinv_l. rewrite Rmult_1_r. reflexivity.
 apply WWF_dstate_not_0. assumption.
 inversion_clear H. apply WWF_dstate_aux_to_WF_dstate_aux. assumption.
 apply WWF_dstate_not_0. discriminate.
 apply WWF_dstate_aux_to_WF_dstate_aux. 
 inversion_clear H10. assumption.
 
 eapply dstate_eq_trans.
 apply dstate_eq_sym. 
 apply d_app_empty_l.
 eapply dstate_eq_trans.
 apply d_app_comm.
 apply d_app_eq.
 apply dstate_eq_sym. 
eapply dstate_eq_trans. 
apply d_scale_not_0_assoc. 
eapply dstate_eq_trans. 
apply d_scale_not_0_assoc.
unfold dstate_eq.
f_equal. f_equal.  
repeat rewrite Rdiv_unfold. rewrite Rmult_1_l.
 rewrite Rmult_assoc. rewrite Rmult_assoc.
 rewrite <-(Rmult_assoc ( d_trace_aux ((p :: d0)))) . 
 rewrite (Rmult_comm ( d_trace_aux ((p :: d0)))).
repeat   rewrite Rmult_assoc . 
 rewrite Rinv_r. rewrite Rmult_1_r. 
 rewrite Rinv_l. rewrite Rmult_1_r. reflexivity.
 apply WWF_dstate_not_0. assumption.
 inversion_clear H. apply WWF_dstate_aux_to_WF_dstate_aux. assumption.
 apply WWF_dstate_not_0. discriminate.
 apply WWF_dstate_aux_to_WF_dstate_aux. assumption.
 reflexivity.
 
 simpl. econstructor. intros; split. apply d_seman_scale.
 apply WF_dstate_gt0_le1. assumption.
 inversion_clear H. 
 assumption.


 assert((R1 / (s_trace (c0,q0) + d_trace_aux d))=
/d_trace ({|
  StateMap.this :=  (c0, q0) :: d;
  StateMap.sorted := IHd
|})).  rewrite Rdiv_unfold.
unfold d_trace. rewrite Rmult_1_l. simpl. reflexivity.
rewrite H25.
 apply d_seman_scale''. intuition. 
 assumption.  
 rewrite d_trace_scale_not_0. 
 rewrite d_trace_scale_not_0. 
 unfold d_trace. simpl.
 rewrite Rdiv_unfold. rewrite Rmult_1_l.
 rewrite Rinv_l. rewrite Rmult_1_r. reflexivity.
 assert((s_trace (c0,q0) + d_trace_aux d= d_trace_aux ((c0,q0)::d))).
 reflexivity. rewrite H25.
 apply WWF_dstate_not_0.
 discriminate. apply WWF_dstate_aux_to_WF_dstate_aux. 
 apply WF_sat_State in H10.   
  intuition.  
 assert((R1 / (s_trace (c0,q0) + d_trace_aux d))=
 /d_trace ({|
   StateMap.this :=  (c0, q0) :: d;
   StateMap.sorted := IHd
 |})).  rewrite Rdiv_unfold.
 unfold d_trace. rewrite Rmult_1_l. simpl. reflexivity.
 rewrite H25.  apply Rinv_0_lt_compat.
 apply WF_dstate_gt0_le1. discriminate.
 apply WF_sat_State in H10. intuition. 
  apply WF_dstate_gt0_le1. assumption.
  inversion_clear H. assumption.

 econstructor. intros; split. 
 apply d_seman_scale.
 apply WF_dstate_gt0_le1. assumption.
 inversion_clear H.  assumption.


 assert((R1 / (s_trace p + d_trace_aux d0))=
/d_trace ({|
  StateMap.this :=  p :: d0;
  StateMap.sorted := H22
|})).  rewrite Rdiv_unfold.
unfold d_trace. rewrite Rmult_1_l. simpl. reflexivity.
rewrite H25.
 apply d_seman_scale''. intuition. 
 apply (ruleState _ _ _ c q IHd0).
 assumption. discriminate. 
 rewrite d_trace_scale_not_0.
 rewrite d_trace_scale_not_0. 
 unfold d_trace. simpl.
 rewrite Rdiv_unfold. rewrite Rmult_1_l.
 rewrite Rinv_l. rewrite Rmult_1_r. reflexivity.
 assert((s_trace p + d_trace_aux d0= d_trace_aux (p::d0))).
 reflexivity. rewrite H25.
 apply WWF_dstate_not_0.
 discriminate. apply WWF_dstate_aux_to_WF_dstate_aux.
 assumption. 
 assert((R1 / (s_trace p + d_trace_aux d0))=
/d_trace ({|
  StateMap.this :=  p :: d0;
  StateMap.sorted := H22
|})).  rewrite Rdiv_unfold.
unfold d_trace. rewrite Rmult_1_l. simpl. reflexivity.
rewrite H25.
 apply Rinv_0_lt_compat. 
 apply WF_dstate_gt0_le1.
 discriminate. assumption. 
 apply WF_dstate_gt0_le1. assumption.
  inversion_clear H. assumption.
  econstructor.

reflexivity.
 inversion_clear H3.
simpl in H5. inversion_clear H5.
inversion_clear H11.
econstructor. lra. econstructor.    lra.
econstructor.
assumption. assumption.
inversion_clear H7.
inversion_clear H10.
inversion_clear H11.
discriminate H3.
Qed.
