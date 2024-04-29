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
Lemma seman_find_aux{n}:forall  (mu:list (cstate * qstate n)) (F: State_formula),
(mu<> nil /\ WF_dstate_aux mu) -> (State_eval_dstate F mu <->
(forall x:cstate, (option_qstate (StateMap.Raw.find x mu) <> Zero) -> (State_eval F 
(x, (option_qstate (StateMap.Raw.find x mu)))))).
Proof. induction mu; intros; simpl.
      -destruct H. destruct H. reflexivity.
      -split; destruct a; destruct mu;
       intros; simpl. simpl in H1. 
       destruct (Cstate_as_OT.compare x c).
       simpl in H1.  destruct H1. reflexivity.
       simpl. unfold Cstate_as_OT.eq in e. rewrite e.
       intuition. simpl in H1.  destruct H1. reflexivity.
       intros.  destruct (Cstate_as_OT.compare x c).
       simpl in H1.  destruct H1. reflexivity.
       simpl. unfold Cstate_as_OT.eq in e. rewrite e.
       intuition. apply IHmu. split. discriminate. 
       destruct H. inversion_clear H2. intuition. 
       apply H0. apply H1. 
       simpl in H0.  
       assert (option_qstate (StateMap.Raw.find c [(c,q)]) <> Zero).
       simpl. destruct (Cstate_as_OT.compare c c).
       apply Cstate_as_OT.lt_not_eq in l. intuition.
       simpl. destruct H. inversion_clear H1.
       apply WF_state_not_Zero in H2.  simpl in H2.
       intuition.  apply Cstate_as_OT.lt_not_eq in l. intuition.
       apply H0 in H1. simpl in H1.
       destruct (Cstate_as_OT.compare c c).
       apply Cstate_as_OT.lt_not_eq in l. intuition.
       simpl in H1. intuition.  
        apply Cstate_as_OT.lt_not_eq in l. intuition.
       split.  
       assert (option_qstate (StateMap.Raw.find c ((c, q) :: p :: mu )) <> Zero).
       simpl. destruct (Cstate_as_OT.compare c c).
       apply Cstate_as_OT.lt_not_eq in l. intuition.
       simpl. destruct H. inversion_clear H1.
       apply WF_state_not_Zero in H2.  simpl in H2.
       intuition.  apply Cstate_as_OT.lt_not_eq in l. intuition.
       apply H0 in H1. 
       destruct (Cstate_as_OT.compare c c).
       apply Cstate_as_OT.lt_not_eq in l. intuition.
       simpl in H1. intuition.  
        apply Cstate_as_OT.lt_not_eq in l. intuition.
        assert((forall x : cstate,
        option_qstate (StateMap.Raw.find (elt:=qstate n) x (p :: mu)) <>
        Zero ->
        State_eval F
          (x,
           option_qstate (StateMap.Raw.find (elt:=qstate n) x (p :: mu))))).
    intros.  assert(Cstate_as_OT.lt c x). destruct p.
    apply dstate_1 with (mu:=( (c0,q0) :: mu)) (q:=q) (t:=c).
    admit. intuition. 
    assert(option_qstate
    match Cstate_as_OT.compare x c with
    | OrderedType.LT _ => None
    | OrderedType.EQ _ => Some q
    | OrderedType.GT _ =>
        StateMap.Raw.find (elt:=qstate n) x (p :: mu)
    end <> Zero ->
  State_eval F
    (x,
     option_qstate
       match Cstate_as_OT.compare x c with
       | OrderedType.LT _ => None
       | OrderedType.EQ _ => Some q
       | OrderedType.GT _ =>
           StateMap.Raw.find (elt:=qstate n) x (p :: mu)
       end)). apply H0.
       destruct (Cstate_as_OT.compare x c). 
    rewrite l in H2.
   
Admitted.


Lemma seman_find{n}:forall  (mu:dstate (2^n)) (F: State_formula),
sat_State mu F <->
(forall x:cstate, d_find x mu <>Zero -> (State_eval F 
(x, (d_find x mu)))).
Proof. intros. destruct mu as [mu IHmu].
split. induction mu;intros.
unfold not in H0.
unfold d_find in H0. simpl in H0. 
intuition.
inversion_clear H. destruct a.
simpl in H2. 
-admit.
Admitted.

Lemma dstate_eq_trans: forall n (mu mu1 mu2: dstate (2^n)),
  dstate_eq mu mu1 -> dstate_eq mu1 mu2
  -> dstate_eq mu mu2.
  Proof. intros n (mu, IHmu) (mu1,IHmu1) (mu2,IHmu2).
    unfold dstate_eq. simpl.
    intros. rewrite H. assumption.
    Qed.

    Lemma seman_eq: forall n (mu mu':dstate (2^n)) (F:State_formula),
dstate_eq mu mu'->
sat_State  mu F-> sat_State  mu' F.
Proof. Admitted.
Lemma sat_Assert_to_State: forall n (mu:dstate (2^n)) (F:State_formula),
sat_Assert mu F <-> sat_State mu F.
Proof. split. intros. inversion_clear H. 
      inversion_clear H1. destruct p_n. simpl in H3.
      inversion_clear H2. rewrite sum_over_list_nil_formula in H4.
      lra. simpl in *. destruct H3.
      inversion_clear H2. 
      rewrite sum_over_list_cons_formula in H5.
      simpl in H5. rewrite sum_over_list_nil_formula in H5.
      rewrite Rplus_0_r in H5. rewrite H5 in H1.
      assert(dstate_eq (d_scalar 1 (nth 0 mu_n (d_empty (2 ^ n)))) (nth 0 mu_n (d_empty (2 ^ n)))).
      apply d_scalar_1_l. 
      assert(dstate_eq (d_app (d_empty (2 ^ n)) (d_scalar 1 (nth 0 mu_n (d_empty (2 ^ n))))) 
      ((d_scalar 1 (nth 0 mu_n (d_empty (2 ^ n)))))).
      apply d_app_nil_mu. 
      assert(dstate_eq mu (nth 0 mu_n (d_empty (2 ^ n))) 
      ).
      apply dstate_eq_trans with ((d_app (d_empty (2 ^ n))
      (d_scalar 1 (nth 0 mu_n (d_empty (2 ^ n)))))).
      intuition.
      apply dstate_eq_trans with ((d_scalar 1
      (nth 0 mu_n (d_empty (2 ^ n))))).
      intuition. intuition. apply seman_eq with ((nth 0 mu_n (d_empty (2 ^ n)))).
      intuition. intuition.
      intros.
      econstructor.
      discriminate.
      econstructor. inversion_clear H. intuition.
      assert(distribution_formula (npro_to_pro_formula F [1%R])).
      simpl. unfold distribution_formula. 
      split. intuition.
     rewrite sum_over_list_cons_formula.
      simpl. rewrite sum_over_list_nil_formula. rewrite Rplus_0_r.
      reflexivity. apply H0.
      simpl. 
      split. assert(dstate_eq mu
      (d_app (d_empty (2 ^ n))
         (d_scalar 1 (nth 0 [mu] (d_empty (2 ^ n)))))).
         simpl. 
        apply dstate_eq_trans with ((d_scalar 1 mu)).
        apply dstate_eq_sym.
        apply d_scalar_1_l. 
        apply dstate_eq_sym. apply d_app_nil_mu.
        apply H0. simpl. intuition.   

       
Qed.


Ltac rule_solve := 
    rewrite sat_Assert_to_State in *;
    rewrite seman_find in *; intros;
    match goal with 
    H1: forall x:cstate, d_find x ?mu <> Zero ->?Q,
    H2: d_find ?x ?mu <> Zero
    |- _ => apply H1 in H2
    end;
    match goal with 
    H0: State_eval ?F ?st |- _=> simpl in H0
    end.


Theorem rule_PT: forall F:State_formula,
  F ->> BTrue.
  Proof.
    intros. unfold "->>". intros.
    rule_solve.
     simpl. intuition.
  Qed.


Local Hint Unfold s_scalar : auto.
Local Hint Resolve s_seman_scalar : auto.


Theorem rule_OdotE: forall F:State_formula,
  (F ⊙ BTrue ->> F ) /\ (F ->>F ⊙ BTrue).
Proof. intros. unfold assert_implies; apply conj;
      intros; rule_solve; simpl;  intuition.      
Admitted.

 Theorem rule_OdotC: forall F1 F2:State_formula,
((F1 ⊙ F2) ->> (F2 ⊙ F1))/\
((F2 ⊙ F1) ->> (F1 ⊙ F2)).
Proof. intros. unfold assert_implies; apply conj;
        intros; rule_solve; simpl; 
         destruct H0; destruct H1. 
        
        split.  admit. split. assumption. assumption.
        split. admit. split.  assumption. assumption.

Admitted.


Theorem rule_OdotA: forall F1 F2 F3:State_formula,
((F1 ⊙ (F2 ⊙ F3) )->>( (F1 ⊙ F2) ⊙ F3) )/\
(( (F1 ⊙ F2) ⊙ F3) ->> (F1 ⊙ (F2 ⊙ F3) )).
Proof. intros. unfold assert_implies. apply conj;

            intros; rule_solve; simpl; destruct H0; destruct H1. destruct H2.
            destruct H3. 
            split.  admit. split. split. admit. split. 
            assumption. assumption. assumption.
            destruct H1. destruct H3. 
            split. admit. split.  assumption.
            split. admit. split. assumption. assumption.
      Admitted.

Theorem rule_OdotO: forall (P1 P2:Pure_formula), 
 ((P1 ⊙ P2) ->> (P1 /\ P2)) /\
 ((P1 /\ P2) ->> (P1 ⊙ P2)).
Proof. intros.  unfold assert_implies.  
       split;
       intros; rule_solve; simpl; intuition.
        admit.
 Admitted.

Theorem rule_OdotOP: forall (P:Pure_formula) (F:State_formula),
(P ⊙ F ->> P /\ F)/\
(P /\ F ->> P ⊙ F).
Proof.  intros.  unfold assert_implies. split;

       intros; rule_solve; simpl; intuition.
       admit.
Admitted.

Theorem rule_OdotOA: forall (P:Pure_formula) (F1 F2:State_formula),

((P /\ (F1 ⊙ F2)) ->> ((P /\ F1) ⊙ (P /\ F2)))
/\
(((P /\ F1) ⊙ (P /\ F2))->>(P /\ (F1 ⊙ F2))).
Proof. intros.  unfold assert_implies; split;
    intros; rule_solve; simpl; destruct H0; 
    destruct H1; destruct H2. 

    split. admit. split; intuition.
    split. intuition. split. admit. 
    intuition.
Admitted.



Theorem rule_OdotOC: forall (F1 F2 F3:State_formula), 
((F1 ⊙(F2 /\ F3)) ->> ((F1 ⊙ F2) /\ (F1 ⊙ F3)))
/\
(((F1 ⊙ F2) /\ (F1 ⊙ F3))->>(F1 ⊙(F2 /\ F3))).
Proof. intros.  unfold assert_implies;  split;

intros;  rule_solve; simpl; destruct H0; 
destruct H1.

split. split. admit. intuition.
split. admit. intuition.
split. admit. intuition.
Admitted.

Notation "| v >[ s , e ]" := (QExp_s s e v) (at level 80) :assert_scope.



Local Open Scope assert_scope.
Theorem  rule_ReArr:forall (s e  s' e':nat)  v u,
((| v >[ s , e ]) ⊗* (| u >[ s' , e' ]) ->>(| u >[ s' , e' ]) ⊗* (| v >[ s , e ])).
Proof. intros.  unfold assert_implies. simpl. 
       intros; intros.  rule_solve; simpl; destruct H0;
       destruct H0; destruct H1. 

       split. admit. 
       split; intuition.
Admitted.

Theorem  rule_Separ:forall s x e u v, 
((| v >[ s , x ]) ⊗* (| u >[ x , e ])) ->>
( (| v ⊗ u >[ s , e ])).
Proof.   intros.  unfold assert_implies. simpl. 
intros;   rule_solve. simpl.  destruct H0. destruct H1.
admit.
Admitted. 

Theorem  rule_odotT: forall s e s' e' u v, 
((| v >[ s , e ]) ⊗* (| u >[ s' , e' ])) ->>
((| v >[ s , e ])  ⊙ (| u >[ s' , e' ])).
Proof. intros. unfold assert_implies. intros.
rule_solve.   simpl. intuition.
Qed.

Lemma dstate_eq_not_nil: forall n (mu mu':dstate (2^n)),
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

Theorem  rule_OCon: forall (nF1 nF2:npro_formula) (p_n: list R),
length nF1 =length nF2
->big_and (fun i:nat => (nth i nF1 BFalse) ->> (nth i nF2 BFalse)) (length nF1) 
->((npro_to_pro_formula nF1 p_n) ->> (npro_to_pro_formula nF2 p_n)).
Proof.    unfold assert_implies. intros. 
inversion_clear H1.
          econstructor. intuition. admit.  
       admit.
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
Admitted.



Theorem  rule_OCon': forall  (F0 F0' F1 F1':probabilistic_formula),
(0 < mode F0' + mode F1' <= 1)->
(F0 ->> F0') -> (F1 ->> F1') -> (((F0) ⊕p (F1))->> ((F0') ⊕p (F1'))).
Proof.  intros.  unfold assert_implies in *. simpl. intros.
intros; inversion_clear H2. inversion_clear H3. 
destruct H4. destruct H3. destruct H3. destruct H4. destruct H5. 
econstructor. econstructor. intuition. 
exists x. exists x0.  split. assumption.
split. assumption. split. assumption.
split. assert(sat_Assert x F0').    
apply H0. econstructor. intuition. inversion_clear H7. intuition.
assert(sat_Assert x0 F1'). 
apply H1. econstructor. intuition. inversion_clear H7. assumption.
Qed.

Lemma d_scalar_assoc': forall n (p1 p2:R) (mu:dstate (2^n)), 
  dstate_eq (d_scalar p1 (d_scalar p2 mu))
 (d_scalar (Rmult p1  p2) mu).
 Proof.
  intros n p1 p2 (mu, IHmu). 
  induction mu. simpl. reflexivity.
          destruct a.  
          unfold d_scalar. unfold map. simpl.
          unfold d_scalar in IHmu0. unfold map in IHmu0. 
          simpl in IHmu0.
          inversion_clear IHmu.
          unfold dstate_eq. simpl.
          unfold dstate_eq in IHmu0.
          simpl in IHmu0.
          apply IHmu0 in H.
          rewrite Mscale_assoc.
          assert(((Cmult (RtoC p1) (RtoC p2)))=
          ((RtoC (Rmult p1 p2)))).
          unfold RtoC.
          unfold Cmult. simpl.
          repeat rewrite Rmult_0_l.
          repeat rewrite Rmult_0_r.
          rewrite Rplus_0_r.
          rewrite Rminus_0_r.
          intuition.
          rewrite H1. f_equal.
          intuition.
  Qed.

  

    
Lemma d_scalar_1_l': forall n (mu:dstate (2^n)), 
dstate_eq (d_scalar 1 mu)  mu.
Proof. intros n (mu, IHmu). 
        unfold d_scalar; unfold map;
        simpl; induction mu. reflexivity.
        destruct a. inversion_clear IHmu.
        unfold dstate_eq in IHmu0.
        simpl in IHmu0.
        apply IHmu0 in H.
        unfold dstate_eq. simpl.
        f_equal.
         rewrite Mscale_1_l. reflexivity.
        assumption.
Qed.




Theorem rule_OMerg:forall (p0 p1 p2:R) (F F':State_formula),
 ((p0 · F) ⊕p ( p1 · F)) ⊕p ( p2 · F') 
 ->>  (((p0+p1) · F) ⊕p (p2 · F')).
Proof. intros. unfold assert_implies.
  
  intros.  inversion_clear H. inversion_clear H0.
  destruct H1. destruct H0. destruct H0. destruct H1.
  destruct H2. destruct H3.
  econstructor. econstructor. simpl. simpl in H. assumption. 
  exists x. exists x0. 
 split. assumption. split. assumption.
  split. assumption.  
  inversion_clear H3. destruct H6. destruct H3.
  destruct H3.
  destruct H6. destruct H7. destruct H8.
  inversion H8;subst. inversion_clear H9.
  assert(0+0< p0 + p1).
  apply Rplus_lt_compat. intuition. intuition. 
  rewrite Rplus_0_l in H9.
  split. 
  econstructor. intuition. destruct H14. destruct H11.

  remember (d_scalar (1/(p0+p1)) (d_app x1 x2)) as mu'.
  exists mu'. rewrite Heqmu'.
   split.    
    apply dstate_eq_trans' with 
   ((d_scalar ((p0 + p1) *(1 / (p0 + p1))) (d_app x1 x2))) .
   rewrite Rmult_div_assoc.  rewrite Rmult_1_r.
   rewrite Rdiv_unfold.
   rewrite Rinv_r.  apply dstate_eq_trans' with ((d_app x1 x2)).
   assumption. apply dstate_eq_sym'.
   apply d_scalar_1_l'.  lra. 
   apply dstate_eq_sym'.
   apply d_scalar_assoc'. 
   apply seman_eq with (mu:= (
    (d_app ((d_scalar (p0 / (p0 + p1)) x3))
     (d_scalar (p1 / (p0 + p1)) x4)))).
     repeat rewrite Rdiv_unfold. rewrite Rmult_comm.
     rewrite Rmult_comm with (r1:=p1).
    apply dstate_eq_trans' with (d_app (d_scalar (/ (p0 + p1)) (d_scalar p0 x3))
    ((d_scalar (/ (p0 + p1)) (d_scalar p1 x4)))).
    apply d_app_eq. apply dstate_eq_sym'.
     apply d_scalar_assoc'.  apply dstate_eq_sym'.
     apply d_scalar_assoc'. 
     apply dstate_eq_trans' with (d_scalar  (/ (p0 + p1)) (d_app
     ( (d_scalar p0 x3))
     ( (d_scalar p1 x4)))).
     (* apply d_scalar_eq_trans' with 
     ()  *)
     apply d_scalar_app_distr. 
     apply Nnil_d_app. apply Nnil_d_scalar.
     intuition. apply Nnil_d_scalar. intuition.
     apply WF_to_Nil_aux. destruct H9. apply (WF_seman _ _ _ H10).
     apply Nnil_d_scalar.
     intuition. apply Nnil_d_scalar. intuition.
     destruct H7. apply WF_to_Nil_aux. apply (WF_seman _ _ _ H10).
     apply Nnil_d_scalar. intuition.
     apply Nnil_d_app. apply Nnil_d_scalar.
     intuition. apply WF_to_Nil_aux. destruct H9. apply (WF_seman _ _ _ H10).
     apply Nnil_d_scalar. intuition.
     destruct H7. apply WF_to_Nil_aux. apply (WF_seman _ _ _ H10).
     rewrite Rmult_1_l.
     apply d_scalar_eq_aux. 
     apply d_app_eq.  apply dstate_eq_sym'.
     intuition. apply dstate_eq_sym'.
     intuition. 
     apply d_seman_app.
      split. rewrite Rdiv_unfold.
     apply Rmult_gt_0_compat. intuition. 
     apply Rinv_0_lt_compat. intuition.
     apply (Rcomplements.Rdiv_le_1 p0 (p0+p1)). lra.
     lra.    split. rewrite Rdiv_unfold.
     apply Rmult_gt_0_compat. intuition. 
     apply Rinv_0_lt_compat. intuition.
     apply (Rcomplements.Rdiv_le_1 p1 (p0+p1)). lra.
     lra. repeat rewrite Rdiv_unfold. 
     rewrite <-Rmult_plus_distr_r.
     rewrite Rinv_r. lra. lra. apply H9.
     apply H7. assumption.
Qed.



Lemma WF_seman_lt_0:forall n (mu:dstate (2^n)) (F:probabilistic_formula),
WF_seman_Assert F mu -> (0< pro(F)).
Proof. intros. inversion_clear H.  
        simpl. apply H0.  simpl. apply H0.
Qed.


Theorem rule_POplusA: forall F1 F2 F3:probabilistic_formula,
((F1 oplusp (F2 oplusp F3) )->>( (F1 oplusp F2) oplusp F3) )/\
(( (F1 oplusp F2) oplusp F3) ->> (F1 oplusp (F2 oplusp F3) )).
Proof. intros.  unfold assert_implies. split;
       intros;
       inversion_clear H; 
       destruct H1; destruct H; destruct H;
       destruct H1;
       [inversion_clear H2 | inversion_clear H1];
       destruct H4;
       [ destruct H2| destruct H1];
       [ destruct H2| destruct H1];
       destruct H4;
       apply seman_APoplus;
       simpl; simpl in H0;
       [rewrite Rplus_assoc| |rewrite <-Rplus_assoc|];
       try assumption;
       [exists (d_app x x1) | exists x1];
       [exists x2| exists (d_app x2 x0)];
       split. apply dstate_eq_trans' with 
       ((d_app x x0)). intuition.
       apply dstate_eq_trans' with ((d_app x (d_app x1 x2))).
       apply d_app_eq. apply dstate_eq_refl. intuition.
       apply dstate_eq_sym'.
       apply d_app_assoc.  

       apply Nnil_d_app. apply Nnil_d_app.
       apply WF_to_Nil_aux. apply (WF_seman _ _ _ H1).
       apply WF_to_Nil_aux. apply (WF_seman _ _ _ H4).
       apply WF_to_Nil_aux. apply (WF_seman _ _ _ H5).
       apply Nnil_d_app.
       apply WF_to_Nil_aux. apply (WF_seman _ _ _ H1).
        apply Nnil_d_app.
       apply WF_to_Nil_aux. apply (WF_seman _ _ _ H4).
       apply WF_to_Nil_aux. apply (WF_seman _ _ _ H5).
       split. apply seman_APoplus. 
       simpl in H0. split. destruct H0.
       rewrite <-Rplus_assoc in H0.
       split. assert(0+0 < pro F1 + pro F2).
       apply Rplus_lt_compat. apply (WF_seman_lt_0  _ _ _ H1).
       apply (WF_seman_lt_0  _ _ _ H4). rewrite Rplus_0_l in H7.
       assumption. 
       apply Rplus_le_reg_pos_r with (r2:=pro F3).
       assert(0<pro F3).
       apply (WF_seman_lt_0  _ _ _ H5).
       intuition. intuition. 
       apply map2_app_not_nil. 
       apply (WF_seman _ _ _ H1). 
       apply (WF_seman _ _ _ H4).
       exists x. exists x1. 
       split. apply dstate_eq_refl.
       split. intuition. intuition. intuition.
-- apply dstate_eq_trans' with 
((d_app x x0)). intuition.
apply dstate_eq_trans' with ((d_app (d_app x1 x2) x0 )).
apply d_app_eq. intuition. apply dstate_eq_refl.
apply d_app_assoc.   
apply Nnil_d_app. apply Nnil_d_app.
apply WF_to_Nil_aux. apply (WF_seman _ _ _ H4).
apply WF_to_Nil_aux. apply (WF_seman _ _ _ H5).
apply WF_to_Nil_aux. apply (WF_seman _ _ _ H2).
apply Nnil_d_app.
apply WF_to_Nil_aux. apply (WF_seman _ _ _ H4).
 apply Nnil_d_app.
apply WF_to_Nil_aux. apply (WF_seman _ _ _ H5).
apply WF_to_Nil_aux. apply (WF_seman _ _ _ H2).
split. intuition. apply seman_APoplus. 
simpl in H0. split. destruct H0.
rewrite Rplus_assoc in H0.
split. assert(0+0 < pro F2 + pro F3).
apply Rplus_lt_compat. apply (WF_seman_lt_0  _ _ _ H5).
apply (WF_seman_lt_0  _ _ _ H2). rewrite Rplus_0_l in H7.
assumption. 
apply Rplus_le_reg_pos_r with (r2:=pro F1).
assert(0<pro F1).
apply (WF_seman_lt_0  _ _ _ H4).
intuition. rewrite <-Rplus_comm in H0. intuition. 
apply map2_app_not_nil. 
apply (WF_seman _ _ _ H5). 
apply (WF_seman _ _ _ H2).
exists x2. exists x0. 
split. apply dstate_eq_refl.
split. intuition. intuition. 
Qed.

Theorem rule_POplusC: forall F1 F2 :probabilistic_formula,
((F1 oplusp F2  )->>( F2 oplusp F1 ))/\
(( (F2 oplusp F1) ) ->> (F1 oplusp F2  )).

Proof.  intros.  unfold assert_implies. split; 

intros;
inversion_clear H; destruct H1; destruct H; destruct H; 
destruct H1; apply seman_APoplus;
try rewrite Rplus_comm; try assumption;
exists x0; exists x; split;
try apply dstate_eq_trans' with ((d_app x x0));
try intuition;
apply d_app_comm.
Qed.
