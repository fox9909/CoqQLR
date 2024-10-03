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
From Quan Require Import QState_L.
From Quan Require Import QAssert_L.
From Quan Require Import Par_trace.

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
 (D1->>D2) -> (D->> D1)
->(D->>D2).
Proof.  unfold assert_implies. intros. auto. Qed.


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
  
  Theorem  rule_odotT: forall qs1 qs2, 
  (((qs1) ⊗* (qs2)) ->>
  ((qs1)  ⊙ (qs2))) /\
  (((qs1) ⊙ (qs2)) ->>
  ((qs1)  ⊗* (qs2))).
  Proof. split; intros; unfold assert_implies; intros;
  rule_solve.   
  Qed.
 

(* Theorem rule_OdotOC: forall (F1 F2 F3:State_formula), 
((F1 ⊙(F2 /\ F3)) ->> ((F1 ⊙ F2) /\ (F1 ⊙ F3))).
Proof. 
intros; unfold assert_implies.
intros; rule_solve. 
destruct H0. destruct H3.
destruct H3. destruct H3.
destruct H4. destruct H5.
split. 
exists x0; exists x1; exists x2;
exists x3; exists x4; exists x5;
intuition.
Qed. *)



Theorem rule_AndC: forall F1 F2:State_formula,
((F1 /\ F2) ->> (F2 /\ F1))/\
((F2 /\ F1) ->> (F1 /\ F2)).
Proof. intros. unfold assert_implies; apply conj;
        intros; rule_solve; simpl;
         destruct H0;
        split; intuition.
Qed.


Lemma State_eval_conj: forall s e (mu:list (cstate * qstate s e)) (F1 F2:State_formula),
State_eval_dstate  (F1 /\ F2) mu <->
State_eval_dstate   F1 mu/\ State_eval_dstate F2 mu .
Proof. intros. split; intros; 
       induction mu; 
       simpl in H. destruct H.
       -destruct mu; destruct a; inversion_clear H; simpl;
        intuition. 
      -destruct H. destruct H. 
      -destruct a. destruct mu. simpl. econstructor. 
       destruct H. inversion_clear H. inversion_clear H0.
      split; intuition. apply Forall_nil.
      simpl.  destruct H. inversion_clear H.
      inversion_clear H0. intuition. 
Qed.
       
      
Lemma sat_assert_conj: forall s e (mu:dstate s e) (F1 F2:State_formula),
sat_Assert mu (F1 /\ F2)<->
sat_Assert mu F1/\ sat_Assert mu F2 .
Proof.  split; destruct mu as [mu IHmu]; intros;
      repeat rewrite sat_Assert_to_State in *.
      inversion_clear H.  apply State_eval_conj in H1.
      simpl in *. split; econstructor; intuition.

      destruct H. inversion_clear H. inversion_clear H0.
      econstructor. intuition.
      apply State_eval_conj. split; intuition.
      
Qed.

Theorem rule_AndCon:forall F1 F2 F3 F4:State_formula,
(F1->>F2) -> (F3->>F4) ->
(F1 /\ F3) ->> (F2 /\ F4).
Proof. intros.  unfold assert_implies in *.
intros. rewrite sat_assert_conj in *. intuition.
Qed. 


(* Inductive d_combin {s0 e0 s1 e1 s2 e2:nat}: (list (cstate * qstate s0 e0))-> (list (cstate * qstate s1 e1))-> (list (cstate * qstate s2 e2))-> Prop:=
|combin_nil: d_combin nil nil nil 
|combin_cons: forall sigma rho0  rho1  rho' mu0 mu1 mu',
              q_combin rho0 rho1 rho'->
              d_combin mu0 mu1 mu'->
               d_combin ((sigma, rho0)::mu0) ((sigma, rho1)::mu1) ((sigma, rho')::mu').

Local Close Scope assert_scope.
Definition q_subseq{s e:nat} (rho0 rho1: qstate s e):Prop:=
  rho0=rho1 \/exists (rho': qstate s e), @Mplus (2^(e-s)) (2^(e-s)) rho0 rho'=rho1.               


Fixpoint d_subseq{s e: nat} (mu0 mu1: list (cstate *qstate s e)): Prop:=
match mu0, mu1 with 
|nil , nil=> True
|(c0,q0)::mu0', (c1,q1)::(mu1')=>c0=c1 /\ q_subseq q0 q1 /\ d_subseq mu0' mu1'
|_, _=> False
end. *)


Lemma WF_dstate_per_state: forall s e (x:cstate ) (mu:dstate s e),
(d_find x mu) <>Zero -> (WF_dstate mu -> WF_qstate (d_find x mu)) .
Proof. intros s e x (mu, IHmu0). induction mu. 
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
       assumption. assumption.
Qed. 



(* Lemma State_eval_combin: forall s e (mu:list(cstate * qstate s e)) (F1 F2:State_formula),
State_eval_dstate (F1 ⊙ F2) mu <->
(exists s0 e0 s1 e1 (mu0:list(cstate * qstate s0 e0)) (mu1:list(cstate * qstate s1 e1)), 
and (d_combin mu0 mu1 mu ) 
((State_eval_dstate F1 mu0 /\ State_eval_dstate F2 mu1)))
.
Proof. 
Proof. split. induction mu;intros. simpl in H.
--destruct H.
-destruct a. destruct mu.
  inversion_clear H. clear H1.
  destruct H0. destruct H. destruct H.
  destruct H. destruct H. destruct H.
  destruct H. simpl in *. 
  exists x. exists x0.
  exists x1. exists x2.
  exists [(c, x3)].
  exists [((c, x4))]. 
 split.  apply combin_cons. intuition. apply combin_nil.
 split;  econstructor; intuition.
 inversion_clear H.
  assert(exists
  (s0 e0 s1 e1 : nat) (mu0 : list (cstate * qstate s0 e0)) 
(mu1 : list (cstate * qstate s1 e1)),
  d_combin mu0 mu1 (p :: mu) /\
  State_eval_dstate F1 mu0 /\ State_eval_dstate F2 mu1).
  apply IHmu. 
  apply State_eval_dstate_Forall.
 discriminate. assumption. 
 destruct H. destruct H. 
 destruct H. destruct H.
 destruct H. destruct H.
 simpl in H0. destruct H0.
 destruct H0. destruct H0.
 destruct H0. destruct H0.
 destruct H0. 
 exists x. exists x0.
 exists x1. exists x2. 
 exists ((c, x9)::x3).
 exists ((c, x10)::x4). 
 split. 
admit.
admit.
 induction mu;intros. 
  destruct H. destruct H. destruct H.
  destruct H. destruct H. destruct H.
  destruct H. inversion H; subst. destruct H0.
  destruct H0.

  destruct a. destruct mu.
  destruct H. destruct H. destruct H.
  destruct H. destruct H.  destruct H.
  destruct H.
  inversion H; subst. inversion H7; subst.
  simpl. econstructor. simpl in *. 
  exists x. exists x0. exists x1. exists x2.
  exists rho0. exists rho1. split. intuition.
  destruct H0. inversion_clear H0. inversion_clear H1. 
  split; intuition. econstructor.
  
  
  destruct p. 
  destruct H. destruct H. destruct H.
  destruct H. destruct H.  destruct H.
  destruct H. inversion H; subst. clear H. 
  inversion H7; subst. clear H7. 
  destruct H0. inversion_clear H. 
  inversion_clear H0.
  assert(State_eval_dstate (F1 ⊙ F2) ((c0, q0) :: mu)).
  apply IHmu. exists x. exists x0. 
  exists x1. exists x2. exists ((c0, rho2) :: mu2).
  exists ((c0, rho3) :: mu3). 
  split.  econstructor; intuition. 
  intuition.

  simpl. econstructor. simpl.
  exists x. exists x0. 
  exists x1. exists x2. exists rho0.
  exists rho1. intuition. 
   apply H0.
 
Admitted.


Inductive d_combin' {s0 e0 s1 e1 s2 e2:nat}: (dstate s0 e0)-> (dstate s1 e1)-> (dstate s2 e2)-> Prop:=
|d_combin'_0: forall mu1 mu2 mu', 
d_combin (StateMap.this mu1) (StateMap.this mu2)
                 (StateMap.this mu')->d_combin' mu1 mu2 mu'.


Lemma sat_assert_combin: forall s e (mu:dstate s e) (F1 F2:State_formula),
sat_Assert mu (F1 ⊙ F2)<-> 
(exists s0 e0 s1 e1 (mu0:dstate s0 e0) (mu1:dstate s1 e1), 
and (d_combin' mu0 mu1 mu) 
((sat_Assert mu0 F1 /\ sat_Assert mu1 F2))).
Proof.  split; destruct mu as [mu IHmu]; intros;
      repeat rewrite sat_Assert_to_State in *.
      inversion_clear H.  apply State_eval_combin in H1.
      simpl in *. destruct H1. destruct H.
      destruct H. destruct H. destruct H.
      destruct H.
      exists x. exists x0. exists x1.
      exists x2.
Admitted. *)

Local Open Scope assert_scope.
(* Theorem rule_OdotCon:forall F1 F2 F3 F4:State_formula,
(F1->>F2) -> (F3->>F4) ->
(F1 ⊙ F3) ->> (F2 ⊙ F4).
Proof. intros.  unfold assert_implies in *.
intros. rewrite sat_assert_combin in *.
destruct H1. destruct H1. destruct H1.
destruct H1. destruct H1. destruct H1.
exists x. exists x0. exists x1. exists x2.
exists x3. exists x4. 
split. intuition. intuition.
Qed. *)
(* Theorem rule_OdotAnd: forall F1 F2:State_formula,
  (F1 ⊙ F2 ->> F1 ).
Proof. induction F1; unfold assert_implies in *.
      intros; rule_solve; simpl.
      destruct H0.  destruct H0.
      destruct H0. destruct H0.
      destruct H0. destruct H0.
      rewrite (state_eq_Pure P (x, d_find x mu) (x, x4)).
      intuition. reflexivity.
      induction qs; unfold assert_implies in *.
      intros; rule_solve; simpl.
      destruct H0. destruct H0. 
      destruct H0. destruct H0.
      destruct H0. destruct H0.
      destruct H0.
      inversion H0; subst.
      split. intuition.
      split. intuition.
      split. admit.
      admit. admit.
      intros.  apply rule_odotT.
      apply (rule_OdotCon _ ((qs1 ⊙ qs2)) _ (F2)) in H.
      apply rule_OdotA in H.
      rewrite sat_assert_combin in *.
      destruct H. destruct H. destruct H.
      destruct H. destruct H. destruct H.
      exists x. exists x0. exists x1. exists x2.
      exists x3. exists x4.
      split. intuition. 
      split. intuition.
      apply IHqs2 with F2. intuition.
      apply rule_odotT. apply implies_refl.
      intros. 
      apply rule_OdotA in H.
      rewrite sat_assert_combin in *.
      destruct H. destruct H. destruct H.
      destruct H. destruct H. destruct H.
      exists x. exists x0. exists x1. exists x2.
      exists x3. exists x4.
      split. intuition. 
      split. intuition.
      apply IHF1_2 with F2. intuition.
     intros. apply rule_OdotC in H.
     apply rule_OdotOC in H.
     rewrite sat_assert_conj in *.
     split. apply IHF1_1 with F2.
     apply rule_OdotC.
     intuition.  
     apply IHF1_2 with F2.
     apply rule_OdotC.
     intuition.  
Admitted. *)
    



 
Import ParDensityO.


(* Theorem  rule_Separ':forall s x e u v, 
((| v >[ s , x ]) ⊗* (| u >[ x , e ])) ->>
( (| v ⊗ u >[ s , e ])).
Proof.  
    intros;  unfold assert_implies; 
       intros;  rule_solve; simpl.
       destruct H0. destruct H0.
       destruct H0. destruct H0.
       destruct H0. destruct H0.
       destruct H0. inversion H0; subst.
       clear H0. destruct H3.
       split. intuition. split. intuition.
       split. intuition.
       rewrite <-PMtrace_scale.
       unfold outer_product in *.
       assert((@adjoint (2^(e-s)) 1 (v ⊗ u))=
       (v ⊗ u) †). f_equal.
       type_sovle'. rewrite H5.
       rewrite kron_adjoint.
       assert(@Mmult (2^(e-s)) 1 (2^(e-s))
       (v ⊗ u) ((v) † ⊗ (u) †)=
       v ⊗ u × ((v) † ⊗ (u) †) ).
       f_equal; type_sovle'.
       rewrite H6. 
       rewrite kron_mixed_product.
       destruct H0. destruct H7.
       destruct H8. destruct H3.
       destruct H10. destruct H11.
       assert(x3=x). lia. subst.
       rewrite Nat.sub_diag in *.
       rewrite <-H12. rewrite<- H9.
       admit. 
       assert(x1=s/\s=x/\x=e). lia.
       destruct H5. destruct H6.
       subst.

Admitted.  *)


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

  Lemma swap_app{s e:nat} :forall (g:list R)  (f:(list (dstate s e))) ( i:nat),
  length g =length f->
   dstate_eq (big_dapp g f) (big_dapp (swap_list g i) (swap_list f i)).
  Proof. induction g. intros.  
         apply dstate_eq_trans with (d_empty s e).
         apply big_dapp_nil. left. reflexivity.
         apply dstate_eq_trans with ( (d_empty s e)).
         unfold dstate_eq. reflexivity.
         apply dstate_eq_sym. apply big_dapp_nil.
         left. destruct i. reflexivity. simpl. reflexivity.
         induction f. intros.  
         apply dstate_eq_trans with (d_empty s e).
         apply big_dapp_nil. right. reflexivity.
         apply dstate_eq_trans with ( (d_empty s e)).
         unfold dstate_eq. reflexivity.
         apply dstate_eq_sym. apply big_dapp_nil.
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
         destruct i; simpl in *; apply big_app_nil.
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
         apply big_app_cons. assumption. apply big_app_cons.
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
        intuition. apply big_app_cons. 
        intuition. intuition.
Qed.  

Lemma swap_and{s e:nat} :forall  (g:list (State_formula)) 
(f:(list (dstate s e))) i,
  (big_and  f  g ) ->(big_and  (swap_list f i) (swap_list g i)).
Proof. induction g; intros; induction f; intros. 
destruct i; simpl; intuition.
simpl in H. destruct H. simpl in H. destruct H.
induction i. simpl in *; destruct f; destruct g.
simpl. intuition.
destruct H. destruct H0. destruct H. destruct H0.
simpl in *.  intuition.
simpl. destruct f; destruct g. 
assumption. destruct H. destruct H0. destruct H. destruct H0.
simpl in *. split. intuition. apply IHg.
simpl.  
intuition.   
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
sum_over_list_formula  pF=
sum_over_list_formula  (swap_list pF i) .
Proof.   
        induction pF; intros.  destruct i. simpl in *. reflexivity.
        simpl. reflexivity.
        
        destruct i. destruct pF. simpl. reflexivity. 
         simpl.  repeat rewrite sum_over_list_cons_formula in *.
        repeat rewrite <-Rplus_assoc.  rewrite (Rplus_comm  (fst p) (fst a)).
        reflexivity. 

         destruct pF. simpl.  reflexivity. simpl. 
         repeat rewrite sum_over_list_cons_formula in *. 
         f_equal. apply IHpF.
Qed.

Lemma Forall_swap{G:Type}: forall (pF:list G) (f:G->Prop) i,
Forall f pF  ->
Forall f
  (swap_list pF i).
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
  rewrite swap_get_pro. apply H6. 
apply dstate_eq_trans with mu'. assumption. assumption.
rewrite swap_pro_to_npro.
 apply swap_and.  intuition.
 apply Forall_swap. assumption.
Qed.


Fixpoint big_impiles (g: npro_formula ) (f:npro_formula) : Prop := 
           match g ,f with 
           |[] ,[] => True
           |[], _ => False
           | _ ,[]=> False
           | hg::tg, hf:: tf =>  and (hg ->> hf)  (big_impiles tg tf) 
            end.

Lemma big_impiles_length:forall nF1 nF2,
big_impiles nF1 nF2 -> length nF1 =length nF2 .
Proof. induction nF1; induction nF2.
     simpl. intuition.
     simpl. intuition.
     simpl. intuition.
     simpl. intros. f_equal.
     destruct H. apply IHnF1 in H0. intuition.
Qed.


Lemma big_and_impiles{s' e':nat}: forall nF1 nF2  (mu_n:list (dstate s' e')),
big_and mu_n nF1  ->
big_impiles nF1 nF2 ->
big_and mu_n nF2 .
Proof. induction nF1; destruct nF2;intros .
       simpl. simpl in H. assumption.
       simpl in *. destruct H0.
       simpl in *. destruct H0.
       simpl in *. destruct H0. 
       destruct mu_n. simpl in *.
       destruct H.   
       simpl in H.  destruct H.
       unfold assert_implies in H0.
       simpl. split. 
       assert( sat_Assert  d s).
       apply H0. rewrite sat_Assert_to_State. 
       assumption. rewrite sat_Assert_to_State in H3.
       assumption. 
       apply IHnF1. assumption.
       assumption. 
Qed.


Theorem  rule_OCon: forall (nF1 nF2:npro_formula) (p_n: list R),
length nF1 =length p_n ->
big_impiles nF1 nF2 
->((npro_to_pro_formula nF1 p_n) ->> (npro_to_pro_formula nF2 p_n)).
Proof. intros.    unfold assert_implies. intros. 

inversion_clear H1. inversion_clear H4.
econstructor. intuition. 
apply distribution_formula_npro_to_pro with nF1.
assumption.
rewrite<- (big_impiles_length _ _ H0).
assumption. assumption. 
econstructor. rewrite (get_pro_formula_eq  nF1 _  _).
apply H1. assumption.
rewrite<- (big_impiles_length _ _ H0). assumption. 
assumption. rewrite pro_npro_inv in *.
apply big_and_impiles with nF1.
assumption. assumption.
assumption.
 rewrite<- (big_impiles_length _ _ H0).
assumption.   apply H7.
Qed.

Theorem rule_OMerg:forall (p0 p1:R) (F:State_formula) (pF:pro_formula),
0< p0<1/\ 0< p1 <1->
 APro ((p0 , F) :: ( p1, F) :: pF)
 ->> APro (((p0+p1), F):: pF).
Proof. intros. unfold assert_implies. intros.

  inversion_clear H. inversion_clear H0.
  inversion_clear H4. 
  econstructor. intuition. unfold distribution_formula in *. 
  destruct H3. inversion_clear H3.  inversion_clear H9.
  split. econstructor. simpl in *. apply Rplus_le_le_0_compat.
  assumption. assumption. assumption. repeat rewrite sum_over_list_cons_formula in *.
  simpl in *. rewrite Rplus_assoc. assumption.
  destruct mu_n. inversion_clear H0.
  destruct mu_n. inversion_clear H0. inversion_clear H8.
  simpl in *. inversion H0; subst. inversion H13; subst.
  assert( exists (d': dstate s e), d_scale (p0+p1) ((d_app ((d_scale_not_0 (p0 / (p0 + p1)) d))
  (d_scale_not_0 (p1 / (p0 + p1)) d0))) d').
  apply d_scale_exsits. destruct H4.
  inversion H12; subst. lra. 
  inversion H14; subst. lra.
  inversion H4; subst. lra.
  econstructor.   simpl.  
  assert( big_dapp' (p0 + p1 :: get_pro_formula pF) 
 (((d_app ((d_scale_not_0 (p0 / (p0 + p1)) d))
  (d_scale_not_0 (p1 / (p0 + p1)) d0)))::mu_n)
   (d_app ((d_scale_not_0 (p0 + p1)
   (d_app (d_scale_not_0 (p0 / (p0 + p1)) d)
      (d_scale_not_0 (p1 / (p0 + p1)) d0)))) d2)). 
  apply big_app_cons. assumption. assumption.
  apply H11. 
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
    apply dstate_eq_sym.  apply d_scale_assoc'.
   unfold dstate_eq ;  reflexivity.
  lra.  apply dstate_eq_sym.  apply d_scale_assoc'.
  apply  d_scalar_app_distr'.
  apply dstate_eq_refl. 
  simpl.  split.  apply d_seman_app. 
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
  rewrite Rinv_r. lra. lra. apply H6.
  apply H6. apply H6.  
  inversion_clear H7. inversion_clear H16.
  econstructor.  rewrite d_trace_app.
  repeat rewrite d_trace_scale_not_0.
  rewrite H11. rewrite H7.  rewrite <-Rmult_plus_distr_r.
  repeat rewrite Rdiv_unfold. rewrite <-Rmult_plus_distr_r.
  rewrite Rinv_r. rewrite Rmult_1_l. reflexivity.
  apply tech_Rplus. intuition. intuition.
  rewrite Rplus_comm. apply Rdiv_in01. intuition. intuition.
  apply Rdiv_in01. intuition. intuition. 
  apply WWF_dstate_aux_to_WF_dstate_aux.
   apply WF_d_scale_aux.    apply Rdiv_in01. intuition. intuition.
  destruct H6.  apply WF_sat_State with F. assumption.
  apply WWF_dstate_aux_to_WF_dstate_aux.
  apply WF_d_scale_aux. rewrite Rplus_comm.
     apply Rdiv_in01. intuition. intuition.
     destruct H6. destruct H16. 
     apply WF_sat_State with F. assumption.
assumption. 
Qed.



Lemma sat_Pro_State{s e:nat}: forall (mu:dstate s e) F0 F1,
sat_Pro mu [(0, F0); (1, F1)] -> 
sat_State mu F1  /\ ((exists (x:dstate s e), and (d_trace x = d_trace mu) (sat_State x F0))) .
Proof. intros.  inversion_clear H. 
 simpl in *.  inversion H0; subst. 
 inversion H5; subst.
 inversion H8; subst. inversion H10; subst. simpl in *.
 split.
 apply sat_State_dstate_eq with r. 
 apply dstate_eq_trans with ((d_app (d_empty s e) (d_app r (d_empty s e)))).
 apply dstate_eq_sym. apply dstate_eq_trans with ((d_app r (d_empty s e))).
 apply d_app_empty_l. apply dstate_eq_trans with ((d_app (d_empty s e) r)).
 apply d_app_comm. apply d_app_empty_l.
 apply dstate_eq_sym. 
 assumption. apply sat_State_dstate_eq with hd0.
 apply dstate_eq_sym.
 apply d_scale_1_l . assumption. intuition.
 exists hd. split. inversion_clear H3. assumption.
 intuition. 
 lra. 

Qed.


Lemma npro_formula_cons{s e:nat}: forall (F1 F2: State_formula) (mu : dstate s e),
sat_State mu F1->
(exists (x:dstate s e), and (d_trace x = d_trace mu) (sat_State x F2))
->sat_Pro mu [(1, F1); (0, F2)].
 Proof. intros. 
     destruct H0.  assert(exists d, d_scale 1 mu d).
     apply d_scale_exsits. destruct H1. 
     econstructor.  
     simpl in *.  
      assert(big_dapp' [1; 0] [mu; x] (d_app x0 (d_app (d_empty s e) (d_empty s e)))).
      apply big_app_cons.  assumption. 
      apply big_app_cons.  apply d_scalar_0.
      apply big_app_nil. apply H2.
      apply dstate_eq_trans with ((d_app (d_empty s e) x0)).
      apply dstate_eq_trans with x0.
      apply dstate_eq_sym.
      apply d_scale_1_l. assumption.
      apply dstate_eq_sym.  apply d_app_empty_l.
      apply dstate_eq_trans with ((d_app x0 (d_empty s e))).
      apply  d_app_comm. apply d_app_eq.
      apply dstate_eq_refl. apply dstate_eq_sym.  
      apply d_app_empty_l.  
       simpl in *.  intuition.
       simpl. econstructor. reflexivity. 
      econstructor. intuition.
       apply Forall_nil.
 Qed.

 Require Import ParDensityO.
 Lemma WWF_state_scale{s e}: forall c (q: qstate s e) (p:R), 
 (0<p) /\ WWF_state (c,q)-> @WWF_state s e ((c, p .* q)).
 Proof.
         unfold WF_state. unfold WF_qstate. simpl. 
         intros. destruct H. unfold WWF_state in *.
         split. apply Mixed_State_scale_aux. intuition.
         intuition. intuition. 
 Qed. 

Lemma  ruleState: forall s e (mu:list (state s e)) (sigma:cstate) (rho:qstate s e) H1 H2
F,
sat_State {| StateMap.this := (sigma, rho) :: mu;
              StateMap.sorted := H1 |} F
              -> mu<>nil ->
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


Lemma big_dapp'_to_app{s e:nat}: forall (p_n:list R) (mu_n:list (dstate s e)) ,  
length p_n= length mu_n->
(Forall (fun x => x<>0%R) p_n)->
big_dapp' p_n mu_n (big_dapp p_n mu_n).
Proof.  induction p_n; intros. inversion H0; subst. destruct mu_n.
 simpl. apply big_app_nil. discriminate H.
 destruct mu_n. discriminate H. 
  simpl.  apply big_app_cons. 
  apply d_scalar_r. inversion H0.
  assumption. apply IHp_n. injection H. intuition.
  inversion_clear H0.
assumption.
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
(Forall (fun x => x<>0%R) p_n)->
big_dapp' p_n mu_n mu->
mu=(big_dapp p_n mu_n).
Proof. intros. induction H1. simpl. reflexivity.
simpl. apply d_scale_to_not_0' in H1. 
rewrite H1. f_equal. apply IHbig_dapp'. 
injection H. intuition. inversion_clear H0. assumption.
inversion_clear H0. assumption.  
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
Lemma d_seman_scale: forall s e (p:R) (mu:dstate s e) (F:State_formula),
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
       apply Rinv_0_lt_compat. apply WF_dstate_in01'.
       apply WF_sat_State in H. intuition.
       intuition. 
       apply WWF_dstate_aux_to_WF_dstate_aux.
       split. intuition. intuition.
       intuition. simpl. rewrite d_trace_scale_aux.
      unfold d_trace. simpl. rewrite Rinv_l.
      lra. apply WWF_dstate_not_0.
      apply WF_sat_State in H. intuition.
      intuition. 
      apply Rinv_0_lt_compat. 
      apply WF_dstate_in01'.
      apply WF_sat_State in H. intuition.
      apply WWF_dstate_aux_to_WF_dstate_aux.
       split. intuition. intuition.
        apply d_seman_scale_aux.
        apply Rinv_0_lt_compat. 
        apply WF_dstate_in01'.
        apply WF_sat_State in H. intuition.
       intuition. simpl. assumption.
Qed.



Local Open Scope R_scope.
Lemma  rule2: forall s e (mu:list (state s e)) (sigma:cstate) (rho:qstate s e) H1 H2
F0 F1 ,
sat_Assert {| StateMap.this := (sigma, rho) :: mu;
              StateMap.sorted := H1 |} (ANpro ([F0; F1]))
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
assert([(0, F0); (r0, F1)] = swap_list [(r0, F1); (0, F0)] 0).
simpl. reflexivity.  rewrite H4. clear H4. apply rule_POplusC.
econstructor.   inversion_clear H. assumption. 
assert([(r0, F1); (0, F0)] = swap_list [(0, F0); (r0, F1)] 0).
reflexivity. rewrite H4. apply distribution_formula_swap.  assumption. 

inversion_clear H3. repeat rewrite sum_over_list_cons_formula in * .
simpl in *. rewrite sum_over_list_nil_formula in *.
rewrite Rplus_0_l in *. rewrite Rplus_0_r in *. subst.
apply sat_Pro_State in H5.  destruct H5. 

apply npro_formula_cons. 
apply ruleState with sigma rho H1. assumption. 
assumption. 
destruct H5. destruct H5. 
exists (d_scale_not_0 (d_trace_aux mu / (d_trace_aux ((sigma, rho)::mu))) x).
 split. rewrite d_trace_scale_not_0.
rewrite H5. unfold d_trace. simpl StateMap.this. rewrite Rdiv_unfold.
rewrite Rmult_assoc. rewrite Rinv_l.
rewrite Rmult_1_r. reflexivity.
apply WWF_dstate_not_0. discriminate.
apply WWF_dstate_aux_to_WF_dstate_aux. intuition.
simpl. rewrite Rplus_comm. apply Rdiv_in01'.
apply WF_dstate_in01'. assumption.  inversion_clear H. assumption. 
apply WF_state_in01. inversion_clear H. assumption.
 apply d_seman_scalar .
 simpl. rewrite Rplus_comm.
 apply Rdiv_in01'. apply WF_dstate_in01'. assumption.  inversion_clear H. assumption. 
 apply WF_state_in01. inversion_clear H. assumption.
 intuition. 

assert(r0=0\/ r0<>0). 
apply Classical_Prop.classic.
destruct H6.  subst.

(*r0=0*)
econstructor. assert(length [r; 0] = length [F0; F1]).
reflexivity.  apply H6. simpl. 
econstructor.   inversion_clear H. assumption. assumption. 

assert(sat_Assert{|
  StateMap.this := (sigma, rho) :: mu;
  StateMap.sorted := H1 |} (APro ([(0, F1); (r, F0)]))).
assert([(0, F1); (r, F0)] = swap_list [(r, F0); (0, F1)] 0).
simpl. reflexivity. rewrite H6. clear H6. apply rule_POplusC.
econstructor. assumption. assumption. assumption. 
clear H5. inversion_clear H6. clear H5. clear H7.

inversion_clear H3. repeat rewrite sum_over_list_cons_formula in * .
simpl in *. rewrite sum_over_list_nil_formula in *.
rewrite Rplus_0_l in *. rewrite Rplus_0_r in *. subst.
apply sat_Pro_State in H8.  destruct H8. clear H4. 

apply npro_formula_cons. 
apply ruleState with sigma rho H1. assumption. 
assumption. 
destruct H6. destruct H4. 
exists (d_scale_not_0 (d_trace_aux mu / (d_trace_aux ((sigma, rho)::mu))) x).
 split. rewrite d_trace_scale_not_0.
rewrite H4. unfold d_trace. simpl StateMap.this. rewrite Rdiv_unfold.
rewrite Rmult_assoc. rewrite Rinv_l.
rewrite Rmult_1_r. reflexivity.
apply WWF_dstate_not_0. discriminate.
apply WWF_dstate_aux_to_WF_dstate_aux. intuition.
simpl. rewrite Rplus_comm. apply Rdiv_in01'.
apply WF_dstate_in01'. assumption.  inversion_clear H. assumption. 
apply WF_state_in01. inversion_clear H. assumption.
 apply d_seman_scalar .
 simpl. rewrite Rplus_comm.
 apply Rdiv_in01'. apply WF_dstate_in01'. assumption.  inversion_clear H. assumption. 
 apply WF_state_in01. inversion_clear H. assumption.
 intuition. 

 (*r<>0/\r0<>0*)
inversion_clear H5. 
destruct mu_n. simpl in *. destruct H9.
destruct mu_n. simpl in *. intuition. 
destruct mu_n. simpl in *. 

inversion H7; subst. inversion H16; subst.
inversion H18; subst. clear H18.
apply d_scale_to_not_0' in H15.
apply d_scale_to_not_0' in H17.
apply big_dapp'_to_app' in H7. 
simpl in H7. 
unfold dstate_eq in H8.
unfold d_app in H8. 
unfold StateMap.map2 in H8. 
simpl in H8. unfold StateMap.Raw.empty in H8.
rewrite map2_nil_r in H8. rewrite H15 in H8.
rewrite H17 in H8. clear H15. clear H17. 
clear H7. 
destruct d0 as [d0 IHd0]. destruct d as [d IHd].
destruct d0;  destruct d.
simpl in *. discriminate H8. destruct H9.
destruct H7. apply WF_sat_State in H7. simpl in *.
intuition.  destruct H9. 
apply WF_sat_State in H5. simpl in *. intuition.
destruct p. destruct p0.
simpl in H8. 


destruct (Cstate_as_OT.compare c0 c). 
injection H8. intros. 

inversion_clear H3.  inversion_clear H12. inversion_clear H14.
simpl in *. clear H15. 
repeat rewrite sum_over_list_cons_formula in *. rewrite sum_over_list_nil_formula in *.
rewrite Rplus_0_r in *.  simpl in *. destruct H9. destruct H14.
econstructor.  assert(length ([((r/ d_trace_aux mu) * d_trace_aux d); ((r0/ d_trace_aux mu) * d_trace_aux ((c,q)::d0))]) = length [F0; F1]).
reflexivity. apply H17.  simpl.  
 assert(distribution_formula
[(r / d_trace_aux mu * d_trace_aux d, F0);
 (r0 / d_trace_aux mu *
  (s_trace (c, q) + d_trace_aux d0), F1)]). 
econstructor. econstructor. simpl.
apply Rmult_le_pos. 
apply Rcomplements.Rdiv_le_0_compat. lra.
apply WF_dstate_in01'. assumption.  inversion H. assumption.
apply WF_dstate_in01_aux.  apply WF_sat_State in H9. 
destruct H9.  inversion_clear H17. assumption. 
 econstructor. simpl.
apply Rmult_le_pos. 
apply Rcomplements.Rdiv_le_0_compat. lra.
apply WF_dstate_in01'. assumption.  inversion_clear H. assumption.
 assert(s_trace (c, q) + d_trace_aux d0=d_trace_aux ((c,q)::d0)).
 reflexivity. rewrite H17.
 apply WF_dstate_in01_aux.  apply WF_sat_State in H14.
 intuition. apply Forall_nil.
 repeat rewrite sum_over_list_cons_formula. rewrite sum_over_list_nil_formula.
 rewrite Rplus_0_r.  simpl. repeat rewrite Rdiv_unfold. 
 rewrite (Rmult_comm r).   rewrite (Rmult_comm r0).
 repeat rewrite Rmult_assoc. rewrite <-Rmult_plus_distr_l.
  assert(r * d_trace_aux d + r0 * (s_trace (c, q) + d_trace_aux d0)= d_trace_aux mu).
  rewrite H5. rewrite d_trace_app_aux. simpl. repeat rewrite d_trace_scale_aux.
  rewrite s_trace_scale. rewrite Rmult_plus_distr_l. reflexivity.
  lra. lra. lra. apply WWF_d_scale_aux. lra. 
 apply WWF_dstate_aux_to_WF_dstate_aux. apply WF_sat_State in H9.
 destruct H9.  inversion_clear H17. assumption. 
 econstructor.  apply WWF_state_scale. 
 split. lra.     apply WF_sat_State in H14.
 destruct H14. inversion_clear H17.
 unfold WWF_state. split.
 apply Mixed_State_aux_to_Mix_State. simpl. apply H18.
 apply H18.
 apply WWF_d_scale_aux. lra.  apply WWF_dstate_aux_to_WF_dstate_aux. 
  apply WF_sat_State in H14.
 destruct H14. inversion_clear H17. assumption.
 rewrite <-H17. apply Rinv_l.  rewrite H17. 
 apply WWF_dstate_not_0. assumption.
 inversion_clear H. apply WWF_dstate_aux_to_WF_dstate_aux. 
 assumption. simpl. 
 econstructor. inversion_clear H. assumption. 
simpl. apply H17.

destruct d.  simpl in *. rewrite Rmult_0_r in *.
inversion_clear H17. repeat rewrite sum_over_list_cons_formula in H19.
rewrite sum_over_list_nil_formula in *. rewrite Rplus_0_r in *.
simpl in *. rewrite Rplus_0_l in *. rewrite H19.

assert(sat_Assert {| StateMap.this := mu; StateMap.sorted := H2 |}
(APro([(0, F0); (1, F1)]))).
assert([(0, F0); (1, F1)] = swap_list [(1, F1); (0, F0)] 0).
reflexivity. rewrite H17. apply rule_POplusC.
econstructor.  inversion_clear H. assumption.
econstructor. intuition. repeat rewrite sum_over_list_cons_formula.
repeat rewrite sum_over_list_nil_formula. rewrite Rplus_0_r. intuition.
apply npro_formula_cons.
econstructor. inversion_clear H. assumption.
simpl. rewrite H5. simpl. inversion_clear H14.
inversion_clear H21. econstructor. 
assert((@pair StateMap.Raw.key (qstate s e) c
(@scale (Nat.pow (S (S O)) (e-s)) (Nat.pow (S (S O)) (e-s))
   (RtoC r0) q))= s_scale r0 (c,q)). reflexivity.
rewrite H21. apply s_seman_scale. lra.
 assumption.
rewrite map2_r_refl. destruct d0. simpl. apply Forall_nil.
 apply State_eval_dstate_Forall. destruct p. simpl. discriminate.
apply d_seman_scale_aux. lra.  apply State_eval_dstate_Forall. discriminate.
apply H22. 

exists (d_scale_not_0 (d_trace_aux mu) (d_scale_not_0 ( / (d_trace_aux ([(c0,q0)]) )) 
(StateMap.Build_slist IHd))).
simpl. split.  rewrite d_trace_scale_not_0.
rewrite d_trace_scale_not_0.
rewrite Rplus_0_r. unfold d_trace. simpl. 
rewrite Rplus_0_r. rewrite Rinv_l.
rewrite Rmult_1_r. reflexivity.
apply WF_state_not_0. inversion_clear H9.
apply WF_state_dstate. apply H20.
rewrite Rplus_0_r. apply Rinv_0_lt_compat.
apply WF_state_in01. apply WF_state_dstate.
inversion_clear H9. apply H20.
apply WF_dstate_in01'. assumption. inversion_clear H. assumption. 
apply d_seman_scalar. 
apply WF_dstate_in01'. assumption. inversion_clear H. assumption.
rewrite Rplus_0_r.
apply d_seman_scale.
unfold s_trace. simpl.
apply Rinv_0_lt_compat.
apply mixed_state_Cmod_1.
apply WF_sat_State in H9. 
destruct H9. inversion_clear H20.
apply H21. 
unfold d_trace. simpl.
unfold s_trace. simpl. 
rewrite trace_mult_dist.
rewrite Cmod_mult. rewrite Cmod_R.
rewrite Rabs_right. 
rewrite Rinv_l. rewrite Rplus_0_r.  lra. 
assert(Cmod (@trace (2^(e-s)) q0) > 0).
apply mixed_state_Cmod_1.
apply WF_sat_State in H9. 
destruct H9. inversion_clear H20.
apply H21. lra.
assert(/ Cmod (@trace (2^(e-s)) q0) > 0).
apply Rinv_0_lt_compat. 
apply mixed_state_Cmod_1.
apply WF_sat_State in H9. 
destruct H9. inversion_clear H20.
apply H21. lra. 
assumption.
 simpl. 
inversion_clear H17. assumption.

inversion_clear H1.  inversion_clear IHd.

econstructor. 
assert(big_dapp'
([r / d_trace_aux mu * d_trace_aux (((p::d)));
 r0 / d_trace_aux mu * (s_trace (c, q) + d_trace_aux d0)])

 ([d_scale_not_0 (d_trace_aux mu ) (d_scale_not_0 (R1/d_trace_aux (p::d)) (StateMap.Build_slist H20));
 d_scale_not_0 (d_trace_aux mu ) (d_scale_not_0 (R1/d_trace_aux (((c,q)::d0))) (StateMap.Build_slist IHd0))
 ])
 
 (d_app (d_scale_not_0 (r / d_trace_aux mu * d_trace_aux (((p::d)))) 
       (d_scale_not_0 (d_trace_aux mu ) (d_scale_not_0 (R1/d_trace_aux ((p::d))) (StateMap.Build_slist H20)))
 ) (d_app (d_scale_not_0 (r0 / d_trace_aux mu * (s_trace (c, q) + d_trace_aux d0)) (d_scale_not_0 (d_trace_aux mu ) (d_scale_not_0 (R1/d_trace_aux (((c,q)::d0))) (StateMap.Build_slist IHd0))) ) (d_empty s e)))).

 econstructor. 
 apply d_scalar_r.
 assert(
r / d_trace_aux mu * d_trace_aux (p :: d) > 0).
apply Rmult_gt_0_compat.
apply Rdiv_lt_0_compat.
lra. apply WF_dstate_in01'.
assumption. inversion_clear H. assumption.
apply WF_dstate_in01'. discriminate.
apply WF_sat_State in H9.
destruct H9. inversion_clear H22.
assumption. lra.
 econstructor. 
 apply d_scalar_r.
 assert(r0 / d_trace_aux mu * (s_trace (c, q) + d_trace_aux d0) > 0).
 apply Rmult_gt_0_compat.
apply Rdiv_lt_0_compat.
lra. apply WF_dstate_in01'.
assumption. inversion_clear H. assumption.
assert(s_trace (c, q) + d_trace_aux d0= d_trace_aux ((c,q)::d0)).
simpl. reflexivity. rewrite H22.
apply WF_dstate_in01'. discriminate.
apply WF_sat_State in H14. intuition.
 lra.
 apply big_app_nil. simpl.
apply H22. 
apply dstate_eq_trans with (d_app (d_scale_not_0 r (StateMap.Build_slist H20))
(d_scale_not_0 r0 (StateMap.Build_slist (IHd0)))).
unfold dstate_eq. unfold d_app.
unfold StateMap.map2. unfold d_scale_not_0.
unfold StateMap.map. simpl. assumption.
apply d_app_eq. 
apply dstate_eq_sym. 
eapply dstate_eq_trans. 
apply d_scale_assoc'. 
eapply dstate_eq_trans. 
apply d_scale_assoc'.
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
apply WF_sat_State in H9. destruct H9. inversion_clear H22.
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
apply d_scale_assoc'. 
eapply dstate_eq_trans. 
apply d_scale_assoc'.
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
 apply WF_sat_State in H14. apply H14.  
  reflexivity.
 
simpl.  split.  apply d_seman_scalar.
apply WF_dstate_in01'. assumption.
inversion_clear H. 
assumption.
assert((R1 / (s_trace p + d_trace_aux d))=
/d_trace ({|
  StateMap.this := p :: d;
  StateMap.sorted := H20
|})).  rewrite Rdiv_unfold.
unfold d_trace. rewrite Rmult_1_l. simpl. reflexivity.
rewrite H22.
 apply d_seman_scale''. intuition.
 apply (ruleState _ _ _ c0 q0 IHd).
 assumption. discriminate.
 split. 
apply d_seman_scalar.
apply WF_dstate_in01'. assumption.
inversion_clear H.  assumption.
assert((R1 / (s_trace (c,q) + d_trace_aux d0))=
/d_trace ({|
  StateMap.this :=  (c, q) :: d0;
  StateMap.sorted := IHd0
|})).  rewrite Rdiv_unfold.
unfold d_trace. rewrite Rmult_1_l. simpl. reflexivity.
rewrite H22.
 apply d_seman_scale''. intuition.
 assumption. intuition. 
econstructor.
 rewrite d_trace_scale_not_0.
rewrite d_trace_scale_not_0.
unfold d_trace.  simpl. 
rewrite Rdiv_unfold. rewrite Rmult_1_l.
rewrite Rinv_l. rewrite Rmult_1_r. reflexivity.
assert((s_trace p + d_trace_aux d = d_trace_aux (p::d))).
reflexivity. rewrite H22.
apply WWF_dstate_not_0.
discriminate. apply WWF_dstate_aux_to_WF_dstate_aux. 
apply WF_sat_State in H9. destruct H9.
inversion_clear H23. assumption.
rewrite Rdiv_unfold.
rewrite Rmult_1_l.
apply Rinv_0_lt_compat.
apply WF_dstate_in01'.
discriminate. 
apply WF_sat_State in H9. destruct H9.
inversion_clear H22. assumption.
apply WF_dstate_in01'. assumption.
inversion_clear H. assumption.
econstructor. rewrite d_trace_scale_not_0.
rewrite d_trace_scale_not_0. 
unfold d_trace. simpl.
rewrite Rdiv_unfold. rewrite Rmult_1_l.
rewrite Rinv_l. rewrite Rmult_1_r. reflexivity.
assert((s_trace (c,q) + d_trace_aux d0 = d_trace_aux ((c,q)::d0))).
reflexivity. rewrite H22.
apply WWF_dstate_not_0.
discriminate. apply WWF_dstate_aux_to_WF_dstate_aux. 
apply WF_sat_State in H14. intuition. 
rewrite Rdiv_unfold.
rewrite Rmult_1_l.
apply Rinv_0_lt_compat.
apply WF_dstate_in01'.
discriminate. 
apply WF_sat_State in H14. intuition. 
apply WF_dstate_in01'. assumption.
 inversion_clear H. assumption.
apply Forall_nil.


- injection H8. intros.
inversion_clear H3.  inversion_clear H12. inversion_clear H14.
simpl in *. clear H15. 
repeat rewrite sum_over_list_cons_formula in *. rewrite sum_over_list_nil_formula in *.
rewrite Rplus_0_r in *.  simpl in *. destruct H9. destruct H14.
econstructor. 
assert(length ([((r/ d_trace_aux mu) * d_trace_aux d); (r0/ d_trace_aux mu) * d_trace_aux (d0)]) = length [F0; F1]).
reflexivity. apply H17. simpl. 
 assert(distribution_formula
 [(r / d_trace_aux mu * d_trace_aux d, F0);
   (r0 / d_trace_aux mu * d_trace_aux d0, F1)]). 
simpl. econstructor.
econstructor.  simpl. apply Rmult_le_pos. 
apply Rcomplements.Rdiv_le_0_compat. lra.
apply WF_dstate_in01'. assumption.  inversion H. assumption.
apply WF_dstate_in01_aux.  apply WF_sat_State in H9. 
destruct H9.  inversion_clear H17. assumption.
econstructor. simpl. apply Rmult_le_pos. 
apply Rcomplements.Rdiv_le_0_compat. lra.
apply WF_dstate_in01'. assumption.  inversion_clear H. assumption.
 apply WF_dstate_in01_aux.  apply WF_sat_State in H14.
 destruct H14. inversion_clear H17. assumption.
 apply Forall_nil. 
repeat rewrite sum_over_list_cons_formula.
rewrite sum_over_list_nil_formula. 
rewrite Rplus_0_r.  simpl. 
repeat rewrite Rdiv_unfold. 
 rewrite Rmult_comm. rewrite <-Rmult_assoc.
 rewrite (Rmult_comm _ (d_trace_aux d0)). 
 rewrite <-Rmult_assoc.  rewrite <-Rmult_plus_distr_r.
 assert(r * d_trace_aux d + r0 * ( d_trace_aux d0)= d_trace_aux mu).
  rewrite H5. rewrite d_trace_app_aux. simpl. repeat rewrite d_trace_scale_aux.
 reflexivity.
  lra. lra. apply WWF_d_scale_aux. lra. 
 apply WWF_dstate_aux_to_WF_dstate_aux. apply WF_sat_State in H9.
 destruct H9.  inversion_clear H17. assumption. 
 apply WWF_d_scale_aux. lra.  apply WWF_dstate_aux_to_WF_dstate_aux. 
  apply WF_sat_State in H14.
 destruct H14. inversion_clear H17. assumption.
 rewrite <-H17. rewrite (Rmult_comm _ r).
 rewrite (Rmult_comm _ r0). apply Rinv_r.  rewrite H17. 
 apply WWF_dstate_not_0. assumption.
 inversion_clear H. apply WWF_dstate_aux_to_WF_dstate_aux. 
 assumption. 
econstructor. inversion_clear H. assumption.
apply H17. 


destruct d. destruct d0.
simpl in *. intuition.
simpl in *. rewrite Rmult_0_r in *.
inversion_clear H17. repeat rewrite sum_over_list_cons_formula in H19.
rewrite sum_over_list_nil_formula in *. rewrite Rplus_0_r in *.
simpl in *. rewrite Rplus_0_l in *. rewrite H19.

assert(sat_Assert {| StateMap.this := mu; StateMap.sorted := H2 |}
(APro([(0, F0); (1, F1)]))).
assert([(0, F0); (1, F1)] = swap_list [(1, F1); (0, F0)] 0).
reflexivity. rewrite H17. apply rule_POplusC.
econstructor.  inversion_clear H. assumption.
econstructor. intuition. repeat rewrite sum_over_list_cons_formula.
repeat rewrite sum_over_list_nil_formula. rewrite Rplus_0_r. intuition.
apply npro_formula_cons.
econstructor. inversion_clear H. assumption.
simpl.  
rewrite H5. destruct p.  simpl. inversion_clear H14.
inversion_clear H21. inversion_clear H22. econstructor. 
assert((@pair StateMap.Raw.key (qstate s e) c1
(@scale (Nat.pow (S (S O)) (e-s)) (Nat.pow (S (S O)) (e-s))
   (RtoC r0) q1))= s_scale r0 (c1,q1)). reflexivity.
rewrite H22. apply s_seman_scale. lra.
 assumption.
rewrite map2_r_refl. destruct d0. apply Forall_nil.
apply State_eval_dstate_Forall. simpl. destruct p. discriminate.
apply d_seman_scale_aux. lra. inversion_clear H20.
 apply State_eval_dstate_Forall. discriminate.
apply H23. 

exists (d_scale_not_0 (d_trace_aux mu) (d_scale_not_0 ( / (d_trace_aux ([(c0,q0)]) )) 
(StateMap.Build_slist IHd))).
simpl. split.  rewrite d_trace_scale_not_0.
rewrite d_trace_scale_not_0.
rewrite Rplus_0_r. unfold d_trace. simpl. 
rewrite Rplus_0_r. rewrite Rinv_l.
rewrite Rmult_1_r. reflexivity.
apply WF_state_not_0. inversion_clear H9.
apply WF_state_dstate. apply H20.
rewrite Rplus_0_r. apply Rinv_0_lt_compat.
apply WF_state_in01. apply WF_state_dstate.
inversion_clear H9. apply H20.
apply WF_dstate_in01'. assumption. inversion_clear H. assumption. 
apply d_seman_scalar. 
apply WF_dstate_in01'. assumption. inversion_clear H. assumption.
rewrite Rplus_0_r.
assert( s_trace (c0, q0)=d_trace ({|
  StateMap.this := [(c0, q0)];
  StateMap.sorted := IHd
|})). unfold d_trace. simpl. rewrite Rplus_0_r.
reflexivity. rewrite H20.
apply d_seman_scale''. intuition.
assumption. 
inversion_clear H17. assumption.

destruct d0.
 simpl in *. rewrite Rmult_0_r in *.
inversion_clear H17. repeat rewrite sum_over_list_cons_formula in H19.
rewrite sum_over_list_nil_formula in *. rewrite Rplus_0_r in *.
simpl in *. rewrite Rplus_0_r in *. rewrite H19.

apply npro_formula_cons.
econstructor. inversion_clear H. assumption.
simpl.  
rewrite H5. destruct p.  simpl. inversion_clear H9.
inversion_clear H20. inversion_clear H21. econstructor. 
assert((@pair StateMap.Raw.key (qstate s e) c1
(@scale (Nat.pow (S (S O)) (e-s)) (Nat.pow (S (S O)) (e-s))
   (RtoC r) q1))= s_scale r (c1,q1)). reflexivity.
rewrite H21. apply s_seman_scale. lra.
inversion_clear H17.  assumption.
rewrite map2_l_refl. destruct d. apply Forall_nil.
apply State_eval_dstate_Forall. simpl. destruct p. discriminate.
apply d_seman_scale_aux. lra. inversion_clear H17.
 apply State_eval_dstate_Forall. discriminate.
apply H22. 

exists (d_scale_not_0 (d_trace_aux mu) (d_scale_not_0 ( / (d_trace_aux ([(c,q)]) )) 
(StateMap.Build_slist IHd0))).
simpl. split.  rewrite d_trace_scale_not_0.
rewrite d_trace_scale_not_0.
rewrite Rplus_0_r. unfold d_trace. simpl. 
rewrite Rplus_0_r. rewrite Rinv_l.
rewrite Rmult_1_r. reflexivity.
apply WF_state_not_0. inversion_clear H14.
apply WF_state_dstate. apply H17.
rewrite Rplus_0_r. apply Rinv_0_lt_compat.
apply WF_state_in01. apply WF_state_dstate.
inversion_clear H14. apply H17.
apply WF_dstate_in01'. assumption. inversion_clear H. assumption. 
apply d_seman_scalar. 
apply WF_dstate_in01'. assumption. inversion_clear H. assumption.
rewrite Rplus_0_r. 
assert( s_trace (c, q)=d_trace ({|
  StateMap.this := [(c, q)];
  StateMap.sorted := IHd0
|})). unfold d_trace. simpl. rewrite Rplus_0_r.
reflexivity. rewrite H17.
apply d_seman_scale''. intuition.
assumption.  

clear H17.
inversion_clear IHd.
inversion_clear IHd0. 

econstructor. 
assert(big_dapp'
([r / d_trace_aux mu * d_trace_aux ((p :: d));
 r0 / d_trace_aux mu * ( d_trace_aux ((p0 :: d0)))])

 ([d_scale_not_0 (d_trace_aux mu ) (d_scale_not_0 (R1/d_trace_aux ((p :: d))) (StateMap.Build_slist H17));
 d_scale_not_0 (d_trace_aux mu ) (d_scale_not_0 (R1/d_trace_aux ((p0 :: d0))) (StateMap.Build_slist H19))
 ])
 
 (d_app (d_scale_not_0 (r / d_trace_aux mu * d_trace_aux ((p :: d))) 
       (d_scale_not_0 (d_trace_aux mu ) (d_scale_not_0 (R1/d_trace_aux ((p :: d))) (StateMap.Build_slist H17)))
 ) (d_app (d_scale_not_0 (r0 / d_trace_aux mu * (d_trace_aux (p0 :: d0))) (d_scale_not_0 (d_trace_aux mu ) (d_scale_not_0 (R1/d_trace_aux (p0 :: d0)) (StateMap.Build_slist H19))) ) (d_empty s e)))).

 econstructor. apply d_scalar_r.
 assert(
  r / d_trace_aux mu * d_trace_aux (p :: d) > 0).
  apply Rmult_gt_0_compat.
  apply Rdiv_lt_0_compat.
  lra. apply WF_dstate_in01'.
  assumption. inversion_clear H. assumption.
  apply WF_dstate_in01'. discriminate.
  apply WF_sat_State in H9.
  destruct H9. inversion_clear H21.
  assumption. lra.
   econstructor. 
 
 apply d_scalar_r. 
 assert(
r0 / d_trace_aux mu * d_trace_aux (p0 :: d0) > 0).
apply Rmult_gt_0_compat.
apply Rdiv_lt_0_compat.
lra. apply WF_dstate_in01'.
assumption. inversion_clear H. assumption.
apply WF_dstate_in01'. discriminate.
apply WF_sat_State in H14. destruct H14.
inversion_clear H21. assumption. 
 lra.
 apply big_app_nil.
apply H21. 
apply dstate_eq_trans with (d_app (d_scale_not_0 r (StateMap.Build_slist H17))
(d_scale_not_0 r0 (StateMap.Build_slist (H19)))).
unfold dstate_eq. unfold d_app.
unfold StateMap.map2. unfold d_scale_not_0.
unfold StateMap.map. simpl. assumption.
apply d_app_eq. 
apply dstate_eq_sym. 
eapply dstate_eq_trans. 
apply d_scale_assoc'. 
eapply dstate_eq_trans. 
apply d_scale_assoc'.
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
 inversion_clear H9. inversion_clear H21.
 assumption.
 
 eapply dstate_eq_trans.
 apply dstate_eq_sym. 
 apply d_app_empty_l.
 eapply dstate_eq_trans.
 apply d_app_comm.
 apply d_app_eq.
 apply dstate_eq_sym. 
eapply dstate_eq_trans. 
apply d_scale_assoc'. 
eapply dstate_eq_trans. 
apply d_scale_assoc'.
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
 apply WWF_dstate_aux_to_WF_dstate_aux.
 inversion_clear H14. inversion_clear H21.
 assumption. reflexivity.
 
simpl.  split.  apply d_seman_scalar.
apply WF_dstate_in01'. assumption.
inversion_clear H. 
assumption. 

assert((R1 / (s_trace p + d_trace_aux d))=
/d_trace ({|
  StateMap.this :=  p :: d;
  StateMap.sorted := H17
|})).  rewrite Rdiv_unfold.
unfold d_trace. rewrite Rmult_1_l. simpl. reflexivity.
rewrite H21.
 apply d_seman_scale''. intuition.
 apply (ruleState _ _ _ c0 q0 IHd).
 assumption. discriminate.
 split. 
apply d_seman_scalar.
apply WF_dstate_in01'. assumption.
inversion_clear H.  assumption.
assert((R1 / (s_trace p0 + d_trace_aux d0))=
/d_trace ({|
  StateMap.this :=  p0 :: d0;
  StateMap.sorted := H19
|})).  rewrite Rdiv_unfold.
unfold d_trace. rewrite Rmult_1_l. simpl. reflexivity.
rewrite H21.
 apply d_seman_scale''. intuition.
 apply (ruleState _ _ _ c q IHd0).
 assumption. discriminate.
 intuition. 
econstructor. rewrite d_trace_scale_not_0.
rewrite d_trace_scale_not_0. 
unfold d_trace. simpl.
rewrite Rdiv_unfold. rewrite Rmult_1_l.
rewrite Rinv_l. rewrite Rmult_1_r. reflexivity.
assert((s_trace p + d_trace_aux d= d_trace_aux (p::d))).
reflexivity. rewrite H21.
apply WWF_dstate_not_0.
discriminate. apply WWF_dstate_aux_to_WF_dstate_aux. 
apply WF_sat_State in H9. destruct H9. inversion_clear H22.
 intuition.  
rewrite Rdiv_unfold.
rewrite Rmult_1_l.
apply Rinv_0_lt_compat. 
apply WF_dstate_in01'. discriminate.
apply WF_sat_State in H9. destruct H9. inversion_clear H21.
 intuition. 
  apply WF_dstate_in01'. assumption.
 inversion_clear H. assumption.
econstructor. rewrite d_trace_scale_not_0.
rewrite d_trace_scale_not_0. 
unfold d_trace. simpl.
rewrite Rdiv_unfold. rewrite Rmult_1_l.
rewrite Rinv_l. rewrite Rmult_1_r. reflexivity.
assert((s_trace p0 + d_trace_aux d0= d_trace_aux (p0::d0))).
reflexivity. rewrite H21.
apply WWF_dstate_not_0.
discriminate. apply WWF_dstate_aux_to_WF_dstate_aux. 
apply WF_sat_State in H14. destruct H14. inversion_clear H22.
 intuition.  
rewrite Rdiv_unfold.
rewrite Rmult_1_l.
apply Rinv_0_lt_compat. 
apply WF_dstate_in01'. discriminate.
apply WF_sat_State in H14. destruct H14.
 inversion_clear H21.
 intuition. 
apply WF_dstate_in01'. assumption.
 inversion_clear H. assumption.
apply Forall_nil.


-injection H8. intros. 
inversion_clear H3.  inversion_clear H12. inversion_clear H14.
simpl in *. clear H15. 
repeat rewrite sum_over_list_cons_formula in *. rewrite sum_over_list_nil_formula in *.
rewrite Rplus_0_r in *.  simpl in *. destruct H9. destruct H14.
econstructor.
assert(length ([((r/ d_trace_aux mu) * d_trace_aux ((c0,q0)::d)); (r0/ d_trace_aux mu) * d_trace_aux (d0)]) = length [F0; F1]).
reflexivity. apply H17. simpl.
assert(distribution_formula[(r / d_trace_aux mu *
(s_trace (c0, q0) + d_trace_aux d), F0);
(r0 / d_trace_aux mu * d_trace_aux d0, F1)]). 
simpl. econstructor.  simpl. econstructor.
  simpl. apply Rmult_le_pos. 
apply Rcomplements.Rdiv_le_0_compat. lra.
apply WF_dstate_in01'. assumption.  inversion H. assumption.
assert(s_trace (c0, q0) + d_trace_aux d=d_trace_aux ((c0,q0)::d)).
 reflexivity. rewrite H17.
 apply WF_dstate_in01_aux.  apply WF_sat_State in H9.
 intuition. 
 econstructor. simpl.
 apply Rmult_le_pos. 
apply Rcomplements.Rdiv_le_0_compat. lra.
apply WF_dstate_in01'. assumption.  inversion H. assumption.
 apply WF_dstate_in01_aux.  apply WF_sat_State in H14.
 destruct H14. inversion_clear H17. intuition. 
 
 apply Forall_nil.
repeat rewrite sum_over_list_cons_formula.
rewrite sum_over_list_nil_formula. 
rewrite Rplus_0_r.  simpl. 
repeat rewrite Rdiv_unfold. 
 rewrite (Rmult_comm r).   rewrite (Rmult_comm r0).
 repeat rewrite Rmult_assoc. rewrite <-Rmult_plus_distr_l.
  assert(r * ((s_trace (c0, q0) + d_trace_aux d)) + r0 * ( d_trace_aux d0)= d_trace_aux mu).
  rewrite H5. rewrite app_fix. rewrite d_trace_app_aux. simpl.
   repeat rewrite d_trace_scale_aux.
  rewrite s_trace_scale. rewrite Rmult_plus_distr_l. reflexivity.
  lra. lra. lra.  
 econstructor.  apply WWF_state_scale. 
 split. lra.     apply WF_sat_State in H9.
 destruct H9. inversion_clear H17.
 unfold WWF_state. split.
 apply Mixed_State_aux_to_Mix_State. simpl. apply H18. apply H18.
 apply WWF_d_scale_aux. lra.  apply WWF_dstate_aux_to_WF_dstate_aux. 
  apply WF_sat_State in H9.
 destruct H9. inversion_clear H17. assumption.
 apply WWF_d_scale_aux. lra. 
 apply WWF_dstate_aux_to_WF_dstate_aux. apply WF_sat_State in H14.
 destruct H14.  inversion_clear H17. assumption.
 rewrite <-H17. apply Rinv_l.  rewrite H17. 
 apply WWF_dstate_not_0. assumption.
 inversion_clear H. apply WWF_dstate_aux_to_WF_dstate_aux. 
 assumption. simpl. 
 econstructor. inversion_clear H. assumption. 
simpl. apply H17.


destruct d0.
 simpl in *. rewrite Rmult_0_r in *.
inversion_clear H17. repeat rewrite sum_over_list_cons_formula in H19.
rewrite sum_over_list_nil_formula in *. rewrite Rplus_0_r in *.
simpl in *. rewrite Rplus_0_r in *. rewrite H19.

apply npro_formula_cons.
econstructor. inversion_clear H. assumption.
simpl.  
rewrite H5. simpl. inversion_clear H9.
inversion_clear H20. econstructor. 
assert((@pair StateMap.Raw.key (qstate s e) c0
(@scale (Nat.pow (S (S O)) (e-s)) (Nat.pow (S (S O)) (e-s))
   (RtoC r) q0))= s_scale r (c0,q0)). reflexivity.
rewrite H20. apply s_seman_scale. lra.
 assumption.
rewrite map2_l_refl. destruct d. apply Forall_nil.
apply State_eval_dstate_Forall. destruct p. simpl.  discriminate.
apply d_seman_scale_aux. lra.  apply State_eval_dstate_Forall. discriminate.
apply H21. 

exists (d_scale_not_0 (d_trace_aux mu) (d_scale_not_0 ( / (d_trace_aux ([(c,q)]) )) 
(StateMap.Build_slist IHd0))).
simpl. split.  rewrite d_trace_scale_not_0.
rewrite d_trace_scale_not_0.
rewrite Rplus_0_r. unfold d_trace. simpl. 
rewrite Rplus_0_r. rewrite Rinv_l.
rewrite Rmult_1_r. reflexivity.
apply WF_state_not_0. inversion_clear H14.
apply WF_state_dstate. apply H17.
rewrite Rplus_0_r. apply Rinv_0_lt_compat.
apply WF_state_in01. apply WF_state_dstate.
inversion_clear H14. apply H17.
apply WF_dstate_in01'. assumption. inversion_clear H. assumption. 
apply d_seman_scalar. 
apply WF_dstate_in01'. assumption. inversion_clear H. assumption.
rewrite Rplus_0_r.
assert(s_trace (c, q)= d_trace ({|
  StateMap.this := [(c, q)];
  StateMap.sorted := IHd0
|})). unfold d_trace. simpl. rewrite Rplus_0_r. reflexivity.
rewrite H17. apply d_seman_scale''. intuition.
assumption.

inversion_clear IHd0.

econstructor. 
assert(big_dapp'
([r / d_trace_aux mu * d_trace_aux (((c0,q0)::d));
 r0 / d_trace_aux mu * ( d_trace_aux ((p :: d0)))])

 ([d_scale_not_0 (d_trace_aux mu ) (d_scale_not_0 (R1/d_trace_aux ((c0,q0)::d)) (StateMap.Build_slist IHd));
 d_scale_not_0 (d_trace_aux mu ) (d_scale_not_0 (R1/d_trace_aux ((p :: d0))) (StateMap.Build_slist H18))
 ])
 
 (d_app (d_scale_not_0 (r / d_trace_aux mu * d_trace_aux (((c0,q0)::d))) 
       (d_scale_not_0 (d_trace_aux mu ) (d_scale_not_0 (R1/d_trace_aux ((c0,q0)::d)) (StateMap.Build_slist IHd)))
 ) (d_app (d_scale_not_0 (r0 / d_trace_aux mu * (d_trace_aux ((p :: d0)))) (d_scale_not_0 (d_trace_aux mu ) (d_scale_not_0 (R1/d_trace_aux ((p :: d0))) (StateMap.Build_slist H18))) ) (d_empty s e)))).

 econstructor. apply d_scalar_r.
 assert(
r / d_trace_aux mu * d_trace_aux ((c0,q0) :: d) > 0).
apply Rmult_gt_0_compat.
apply Rdiv_lt_0_compat.
lra. apply WF_dstate_in01'.
assumption. inversion_clear H. assumption.
apply WF_dstate_in01'. discriminate.
apply WF_sat_State in H9. intuition.
 lra.
 econstructor.  
 apply d_scalar_r. 
 assert(
r0 / d_trace_aux mu * d_trace_aux (p :: d0) > 0).
apply Rmult_gt_0_compat.
apply Rdiv_lt_0_compat.
lra. apply WF_dstate_in01'.
assumption. inversion_clear H. assumption.
apply WF_dstate_in01'. discriminate.
apply WF_sat_State in H14.
destruct H14. inversion_clear H20.
assumption. lra.
 apply big_app_nil.
apply H20. 
apply dstate_eq_trans with (d_app (d_scale_not_0 r (StateMap.Build_slist IHd))
(d_scale_not_0 r0 (StateMap.Build_slist (H18)))).
unfold dstate_eq. unfold d_app.
unfold StateMap.map2. unfold d_scale_not_0.
unfold StateMap.map. simpl. assumption.
apply d_app_eq. 
apply dstate_eq_sym. 
eapply dstate_eq_trans. 
apply d_scale_assoc'. 
eapply dstate_eq_trans. 
apply d_scale_assoc'.
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
 inversion_clear H9. inversion_clear H21.
 assumption.
 
 eapply dstate_eq_trans.
 apply dstate_eq_sym. 
 apply d_app_empty_l.
 eapply dstate_eq_trans.
 apply d_app_comm.
 apply d_app_eq.
 apply dstate_eq_sym. 
eapply dstate_eq_trans. 
apply d_scale_assoc'. 
eapply dstate_eq_trans. 
apply d_scale_assoc'.
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
 apply WWF_dstate_aux_to_WF_dstate_aux.
 inversion_clear H14. inversion_clear H20.
 assumption. reflexivity.
 
 simpl.  split.  apply d_seman_scalar.
 apply WF_dstate_in01'. assumption.
 inversion_clear H. 
 assumption.


 assert((R1 / (s_trace (c0,q0) + d_trace_aux d))=
/d_trace ({|
  StateMap.this :=  (c0, q0) :: d;
  StateMap.sorted := IHd
|})).  rewrite Rdiv_unfold.
unfold d_trace. rewrite Rmult_1_l. simpl. reflexivity.
rewrite H20.
 apply d_seman_scale''. intuition. 
 assumption. 

 split. 
 apply d_seman_scalar.
 apply WF_dstate_in01'. assumption.
 inversion_clear H.  assumption.


 assert((R1 / (s_trace p + d_trace_aux d0))=
/d_trace ({|
  StateMap.this :=  p :: d0;
  StateMap.sorted := H18
|})).  rewrite Rdiv_unfold.
unfold d_trace. rewrite Rmult_1_l. simpl. reflexivity.
rewrite H20.
 apply d_seman_scale''. intuition. 
 apply (ruleState _ _ _ c q IHd0).
 assumption. discriminate. 
 assumption.
 econstructor. rewrite d_trace_scale_not_0. 

 rewrite d_trace_scale_not_0. 
 unfold d_trace. simpl.
 rewrite Rdiv_unfold. rewrite Rmult_1_l.
 rewrite Rinv_l. rewrite Rmult_1_r. reflexivity.
 assert((s_trace (c0,q0) + d_trace_aux d= d_trace_aux ((c0,q0)::d))).
 reflexivity. rewrite H20.
 apply WWF_dstate_not_0.
 discriminate. apply WWF_dstate_aux_to_WF_dstate_aux. 
 apply WF_sat_State in H9. 
  intuition.  
 rewrite Rdiv_unfold.
 rewrite Rmult_1_l.
 apply Rinv_0_lt_compat. 
 apply WF_dstate_in01'. discriminate.
 apply WF_sat_State in H9. intuition. 
  apply WF_dstate_in01'. assumption.
  inversion_clear H. assumption.
 econstructor. rewrite d_trace_scale_not_0.
 rewrite d_trace_scale_not_0. 
 unfold d_trace. simpl.
 rewrite Rdiv_unfold. rewrite Rmult_1_l.
 rewrite Rinv_l. rewrite Rmult_1_r. reflexivity.
 assert((s_trace p + d_trace_aux d0= d_trace_aux (p::d0))).
 reflexivity. rewrite H20.
 apply WWF_dstate_not_0.
 discriminate. apply WWF_dstate_aux_to_WF_dstate_aux. 
 apply WF_sat_State in H14. 
 destruct H14. inversion_clear H21. 
  intuition.  
 rewrite Rdiv_unfold.
 rewrite Rmult_1_l.
 apply Rinv_0_lt_compat. 
 apply WF_dstate_in01'.
 discriminate. 
 apply WF_sat_State in H14. 
 destruct H14. inversion_clear H20. 
  intuition.  
 apply WF_dstate_in01'. assumption.
  inversion_clear H. assumption.
 apply Forall_nil.

reflexivity. intuition. assumption.
assumption.
inversion_clear H7.
inversion_clear H11.
inversion_clear H12.
discriminate H3.
Qed.
