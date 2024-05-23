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

From Quan Require Import QIMP.
Require Import Basic_Supplement.
From Quan Require Import Matrix.
From Quan Require Import Quantum.
From Quan Require Import QState.
From Quan Require Import QAssert.

Local Open Scope nat_scope.



Lemma dstate_eq_trans: forall n (mu mu1 mu2: dstate n),
  dstate_eq mu mu1 -> dstate_eq mu1 mu2
  -> dstate_eq mu mu2.
  Proof. intros n (mu, IHmu) (mu1,IHmu1) (mu2,IHmu2).
    unfold dstate_eq. simpl.
    intros. rewrite H. assumption.
    Qed.

  


Ltac rule_solve := 
    rewrite sat_Assert_to_State in *;
    rewrite seman_find in *;
    match goal with 
    H: WF_dstate ?mu /\ StateMap.this ?mu <> [] /\ 
         (forall x:cstate, d_find x ?mu <> Zero ->?Q)
    |-_ => destruct H as [H1 H]; destruct H as [H2 H];
    split; try assumption; split; try assumption; intros
    end;
    match goal with 
    H1:  forall x:cstate, d_find x ?mu <> Zero ->?Q,
    H2: d_find ?x ?mu <> Zero
    |- _ => apply H1 in H2
    end;
    match goal with 
    H0: State_eval ?F ?st |- _=> simpl in H0
    end.


Theorem rule_PT: forall F:State_formula,
  F ->> BTrue.
  Proof.
    intros. unfold "->>". intros. rule_solve.
     simpl. intuition.
  Qed.


Local Hint Unfold s_scalar : auto.
Local Hint Resolve s_seman_scalar : auto.




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

Lemma union_empty_refl:forall x ,
NSet.Equal (NSet.union (NSet.empty) x) x.
Proof. unfold NSet.Equal. intros.
      split. intros. 
      apply NSet.union_1 in H. destruct H. inversion_clear H.
      assumption. intros.
      apply NSet.union_3. assumption.
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
  (F ⊙ BTrue ->> F ) /\ (F ->>F ⊙ BTrue).
Proof. intros. unfold assert_implies; apply conj;
      intros; rule_solve; simpl;  intuition.
      apply inter_empty. right. reflexivity.      
Qed.

 Theorem rule_OdotC: forall F1 F2:State_formula,
((F1 ⊙ F2) ->> (F2 ⊙ F1))/\
((F2 ⊙ F1) ->> (F1 ⊙ F2)).
Proof. intros. unfold assert_implies; apply conj;
        intros; rule_solve; simpl; 
         destruct H0; destruct H3. 
        split. rewrite inter_comm. assumption.
           split. assumption. assumption.
        split. rewrite inter_comm. assumption.
         split.  assumption. assumption.
Qed.


Theorem rule_OdotA: forall F1 F2 F3:State_formula,
((F1 ⊙ (F2 ⊙ F3) )->>( (F1 ⊙ F2) ⊙ F3) )/\
(( (F1 ⊙ F2) ⊙ F3) ->> (F1 ⊙ (F2 ⊙ F3) )).
Proof. intros. unfold assert_implies. apply conj;

            intros; rule_solve; simpl; destruct H0; destruct H3.
             destruct H4.
            destruct H5. 
            split. rewrite inter_comm.
            rewrite inter_union_dist in *.
            rewrite union_empty in *.
            split;  rewrite inter_comm;
            intuition.
            split. split.  
            rewrite inter_union_dist in H0.
            apply union_empty in H0. intuition.
            split. 
            assumption. assumption. assumption.
            destruct H3. destruct H5. 
            split. rewrite inter_comm in H0.
             rewrite inter_union_dist in *.
             rewrite union_empty in *.
             split. intuition.   rewrite inter_comm;
             intuition. 
             split.  assumption.
            split. rewrite inter_comm in H0.
            rewrite inter_union_dist in H0.
            rewrite union_empty in H0.
            rewrite inter_comm. intuition.
            split. assumption. assumption.
Qed.

Theorem rule_OdotO: forall (P1 P2:Pure_formula), 
 ((P1 ⊙ P2) ->> (P1 /\ P2)) /\
 ((P1 /\ P2) ->> (P1 ⊙ P2)).
Proof. intros.  unfold assert_implies.  
       split;
       intros; rule_solve; simpl; intuition.
       apply inter_empty. intuition.
Qed.

Theorem rule_OdotOP: forall (P:Pure_formula) (F:State_formula),
(P ⊙ F ->> P /\ F)/\
(P /\ F ->> P ⊙ F).
Proof.  intros.  unfold assert_implies. split;

       intros; rule_solve; simpl; intuition.
       apply inter_empty.  intuition.
Qed.

Theorem rule_OdotOA: forall (P:Pure_formula) (F1 F2:State_formula),

((P /\ (F1 ⊙ F2)) ->> ((P /\ F1) ⊙ (P /\ F2)))
/\
(((P /\ F1) ⊙ (P /\ F2))->>(P /\ (F1 ⊙ F2))).
Proof. intros.  unfold assert_implies; split;
    intros; rule_solve; simpl; destruct H0; 
    destruct H3; destruct H4. 

    split. repeat rewrite union_empty_refl. assumption.
     split; intuition.
    split. intuition. split. repeat rewrite union_empty_refl in H0.
    assumption.
    intuition.
Qed.



Theorem rule_OdotOC: forall (F1 F2 F3:State_formula), 
((F1 ⊙(F2 /\ F3)) ->> ((F1 ⊙ F2) /\ (F1 ⊙ F3)))
/\
(((F1 ⊙ F2) /\ (F1 ⊙ F3))->>(F1 ⊙(F2 /\ F3))).
Proof. intros.  unfold assert_implies;  split;

intros;  rule_solve; simpl; destruct H0; 
destruct H3.

rewrite inter_union_dist in H0.
rewrite union_empty in H0.  
split. split. intuition. 
intuition.
split. intuition.  intuition.
split.  rewrite inter_union_dist. 
rewrite union_empty. intuition. 
intuition.
Qed.

Notation "| v >[ s , e ]" := (QExp_s s e v) (at level 80) :assert_scope.



Local Open Scope assert_scope.
Theorem  rule_ReArr:forall (s e  s' e':nat)  v u,
((| v >[ s , e ]) ⊗* (| u >[ s' , e' ]) ->>(| u >[ s' , e' ]) ⊗* (| v >[ s , e ])).
Proof. intros.  unfold assert_implies. simpl. 
       intros; intros.  rule_solve; simpl; destruct H0.
       destruct H3; destruct H3. 

       split. rewrite inter_comm. assumption. 
       split; intuition.
Qed.

Theorem  rule_Separ:forall s x e u v, 
((| v >[ s , x ]) ⊗* (| u >[ x , e ])) ->>
( (| v ⊗ u >[ s , e ])).
Proof.   intros.  unfold assert_implies. simpl. 
intros;   rule_solve. simpl.  destruct H0. destruct H3.
admit.
Admitted. 

Theorem  rule_odotT: forall s e s' e' u v, 
((| v >[ s , e ]) ⊗* (| u >[ s' , e' ])) ->>
((| v >[ s , e ])  ⊙ (| u >[ s' , e' ])).
Proof. intros. unfold assert_implies. intros.
rule_solve.   
Qed.


Lemma dstate_eq_not_nil: forall n (mu mu':dstate n),
dstate_eq mu mu' -> StateMap.this mu <> []
->StateMap.this mu' <> [].
Proof. intros n (mu,IHmu) (mu', IHmu').
       unfold dstate_eq.
       induction mu; induction mu'.
       - simpl. intuition  .
       -simpl. intuition.
       -simpl. destruct a. intuition. 
       -simpl. destruct a. destruct a0.
        intros. discriminate.
Qed.






(* Fixpoint omit_pro (pF:probabilistic_formula): unprobabilistic_formula:=
  match pF with 
  |PState p F => F
  |POplus pF1 pF2 => NOplus (omit_pro pF1) (omit_pro pF2)
  end . *)

  (* Lemma scale_omit: forall pF p,
  omit_pro (scale_pro p pF)= omit_pro pF.
  Proof. intros. induction pF. 
       simpl. reflexivity.
       simpl. rewrite <-IHpF.
       reflexivity.

    
  Qed. *)

(* Local Open Scope R_scope.
  Lemma sat_scale: forall p pF  n (x:dstate (2^n))  ,
  0<p<=1->
  sat_Pro x (scale_pro (1/p) pF) ->
  sat_Pro (d_scalar p x) (pF) .
  Proof. induction pF; intros.
     -inversion_clear H0. destruct H2.
      destruct H0.
      econstructor. admit.
      exists ((d_scalar (p0) x0)).
      split. 
    
  Qed. *)

Fixpoint pro_to_npro_formula (pF:pro_formula ): npro_formula:=
    match pF with 
    |[] => []
    |(p, F) :: pF'=> F:: (pro_to_npro_formula pF')
    end.

Lemma pro_npro_swap: forall pF,
(npro_to_pro_formula (pro_to_npro_formula pF) (get_pro_formula pF))=
pF.
Proof. intros. induction pF.
    simpl. reflexivity. 
    destruct a.
    simpl.  f_equal. intuition. 
  
Qed.






Local Open Scope assert_scope.
Local Open Scope R_scope.
Theorem rule_Oplus: forall (pF:pro_formula),
  pF ->> (pro_to_npro_formula pF).
Proof.
  intros.  unfold assert_implies. simpl. intros.
  econstructor.
  inversion_clear H. admit.
  rewrite pro_npro_swap. intuition.
Admitted.


Lemma npro_to_pro_formula_eq: forall nF1 nF2 p_n i,
length nF1 = length nF2->
(fst (nth i (npro_to_pro_formula nF2 p_n) (0, SPure (PBexp BFalse))))=
(fst (nth i (npro_to_pro_formula nF1 p_n) (0,SPure (PBexp BFalse)))) .
Proof.  induction nF1; destruct nF2; destruct p_n; intros;
      try reflexivity;
      try discriminate H.
      induction i.
      simpl. reflexivity.
      simpl. apply IHnF1. injection H. intuition.
Qed.


(* Lemma big_dapp_eq_bounded : forall n (f g:(nat -> dstate n)) i, 
    (forall x, (x < i)%nat -> f x = g x) -> big_dapp f i = big_dapp g i.
Proof. 
  intros. 
  induction i.
  + simpl; reflexivity.
  + simpl. 
    rewrite H by lia.
    rewrite IHi by (intros; apply H; lia).
    reflexivity.
Qed.

Lemma big_and_impiles_bounded : forall (f g:nat -> Prop) i, 
    (forall x, (x < i)%nat -> (f x -> g x)) -> (big_and f i -> big_and g i).
Proof. 
  intros. 
  induction i.
  + simpl; reflexivity.
  + simpl. split.
     apply IHi. intros. apply H. lia. assumption.
     apply H0. 
  apply H. lia. apply H0.
Qed.

Lemma length_eq:forall nF1 nF2 p_n,
length nF1 = length nF2->
(length (npro_to_pro_formula nF2 p_n))=
(length (npro_to_pro_formula nF1 p_n)) .
Proof. induction nF1; destruct nF2; destruct p_n;
        intros; try reflexivity; try discriminate H.
        simpl. f_equal. apply IHnF1. injection H.
        intuition.   
   
  
Qed.

Lemma snd_npro_to_pro_formula: forall nF2 p_n x,
length p_n=length nF2->
(snd (nth x (npro_to_pro_formula nF2 p_n) (0, SPure (PBexp BFalse))))=
(nth x nF2 (SPure (PBexp BFalse))).
Proof. induction nF2; induction p_n; intros; destruct x; try reflexivity;
    try discriminate H. 
     simpl. apply IHnF2. injection H. intuition.
Qed.




(* 
         simpl. intros.
        intros; inversion_clear H1. inversion_clear H2. 
        destruct H3. destruct H2. destruct H2. destruct H3. 
        destruct H4. destruct H5.
  econstructor. econstructor. intuition. 
 exists x. exists x0. split. assumption.
 split. assumption. split. intuition.
  inversion_clear H5. inversion_clear H6.
  destruct H8. inversion_clear H9.
 destruct H6.  destruct H8.
 destruct H10. destruct H9.
 split.
 econstructor. intuition. 
 exists x1. split. assumption. split. assumption.
 assert(sat_Assert x1 F0'). 
   apply H. econstructor. econstructor. assumption.
   inversion_clear H13. inversion_clear H14. intuition.

 econstructor.  intuition. 
 exists x2. split. assumption. split. assumption.
 assert(sat_Assert x2 F1').
 apply H0. econstructor. econstructor. assumption.
 inversion_clear H13. inversion_clear H14. intuition. *)




Lemma d_app_assoc': 
forall {n : nat} (mu1 mu2 mu3 : dstate n),
dstate_eq (d_app (d_app mu1 mu2) mu3) (d_app mu1 (d_app mu2 mu3)).
Proof. Admitted.

Lemma big_dapp_extend_l: forall  l (n : nat) (f : nat ->(dstate n) ),
dstate_eq 
(d_app (f 0%nat)  (big_dapp (fun x : nat => f (S x)) l))  (big_dapp f (S l)).
Proof.
intros. 
induction l; simpl.   
+ unfold dstate_eq. unfold d_app. simpl. unfold StateMap.Raw.empty. 
  rewrite map2_nil. rewrite map2_r_refl. rewrite map2_l_refl. reflexivity.
+ apply dstate_eq_trans with (d_app (d_app (f 0%nat)
 (big_dapp (fun x : nat => f (S x)) l)) (f (S l))).
 apply dstate_eq_sym.
 apply d_app_assoc'.
 apply dstate_eq_trans with ((d_app (big_dapp f (S l))
 (f (S l)))).  apply d_app_eq. apply IHl. unfold dstate_eq. reflexivity.
 apply d_app_eq. simpl. reflexivity. 
simpl; reflexivity.

Qed.


Lemma big_dapp_sum : forall  l1 l2 n (f:nat->(dstate n)), 
 dstate_eq (big_dapp f (l1 + l2)%nat) (d_app ( big_dapp f l1)  (big_dapp (fun x => f (l1 + x)%nat) l2)). 
Proof. 
intros.
induction l1.
+ simpl. apply dstate_eq_sym. apply d_app_nil_mu. 
+ simpl. apply dstate_eq_trans with ((d_app  (d_app (big_dapp f l1)
(big_dapp (fun x : nat => f (l1 + x)%nat) l2))  (f (l1 + l2)%nat))).
 apply d_app_eq. assumption. unfold dstate_eq. reflexivity. 
 apply  dstate_eq_trans with (d_app
  (big_dapp f l1) (d_app (big_dapp (fun x : nat => f (l1 + x)%nat) l2)
 (f (l1 + l2)%nat))). apply  d_app_assoc'.
 apply  dstate_eq_trans with (d_app (big_dapp f l1)
 (d_app  (f l1)
 (big_dapp (fun x : nat => f (S (l1 + x))) l2))).
 apply  d_app_eq. unfold dstate_eq. reflexivity.
  remember (fun x : nat => f (l1 + x)%nat) as g.
  replace (f l1) with (g O) by (subst; rewrite Nat.add_0_r; reflexivity).
  replace (f (l1 + l2)%nat) with (g l2) by (subst; reflexivity). 
  replace (big_dapp (fun x : nat => f (S (l1 + x))%nat) l2) with
          (big_dapp (fun x : nat => g (S x)) l2).
  2:{ apply big_dapp_eq_bounded. subst. 
  intros; rewrite <- plus_n_Sm. reflexivity. }
  apply dstate_eq_trans with ((big_dapp g (S l2))).
  simpl. unfold dstate_eq.  reflexivity.
  apply dstate_eq_sym.
  apply big_dapp_extend_l.
  apply dstate_eq_sym.
  apply  d_app_assoc'.
Qed. *)
