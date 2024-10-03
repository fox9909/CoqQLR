Require Import Reals.
Require Import Coquelicot.Complex.
Require Import Strings.String.
Require Import Lists.List.
Import ListNotations.

Require Import Coq.Init.Datatypes.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Arith.PeanoNat. Import Nat. 
From Coq Require Import Lia.

Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Arith.Peano_dec.

From Quan Require Import Matrix.
From Quan Require Import Quantum.
From Quan Require Import ParDensityO.
From Quan Require Import QState_L.
From Quan Require Import QIMP_L.
From Quan Require Import QAssert_L.
From Quan Require Import Par_trace.
From Quan Require Import QRule_Q_L.
From Quan Require Import QRule_E_L.
From Quan Require Import QRule_I_L.
From Quan Require Import QSepar.

Local Open Scope com_scope.

Local Open Scope nat_scope.


Fixpoint dstate_eq_qstate{s e:nat} (mu:list (cstate * qstate s e)) (q:qstate s e):=
  match mu with 
  |nil=> False
  |(c1, q1)::mu' => and (exists p1:R, and (0<p1)%R (q1 = p1 .* q)) (dstate_eq_qstate mu' q)
  end.
  
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
  Proof. induction a; intros. reflexivity.
         unfold cstate_eq in H. simpl in H.
         simpl. apply H. 
         apply NSet.add_1.
         reflexivity.
         simpl in *. 
         apply cstate_eq_union in H.
         rewrite IHa1. rewrite IHa2.
         reflexivity. intuition.
         intuition. 
         simpl in *. 
         apply cstate_eq_union in H.
          rewrite IHa1. rewrite IHa2.
         reflexivity. intuition. intuition. 
         simpl in *. 
         apply cstate_eq_union in H.
          rewrite IHa1. rewrite IHa2.
         reflexivity. intuition. intuition.
         simpl in *. 
         apply cstate_eq_union in H.
          rewrite IHa1. rewrite IHa2.
         reflexivity. intuition. intuition.
         simpl in *. 
         apply cstate_eq_union in H.
          rewrite IHa1. rewrite IHa2.
         reflexivity. intuition. intuition.
         simpl in *. 
         apply cstate_eq_union in H.
          rewrite IHa1. rewrite IHa2.
         reflexivity. intuition. intuition.
         simpl in *. 
         apply cstate_eq_union in H.
          rewrite IHa1. rewrite IHa2.
         reflexivity. intuition. intuition.     
  Qed.
  
  
  Lemma cstate_eq_b{ s e:nat}: forall c1 c2 (b:bexp) (q: qstate s e),
  cstate_eq c1 c2 (Free_bexp b)->
  beval (c1, q) b=beval (c2,q) b.
  Proof. induction b; intros. 
         reflexivity. reflexivity.
         simpl in *. 
         apply cstate_eq_union in H.
         rewrite (cstate_eq_a c1 c2 a1).
         rewrite (cstate_eq_a c1 c2 a2).
         reflexivity. intuition. intuition. 
         simpl in *. 
         apply cstate_eq_union in H.
         rewrite (cstate_eq_a c1 c2 a1).
         rewrite (cstate_eq_a c1 c2 a2).
         reflexivity. intuition. intuition.
         simpl in *. 
         apply cstate_eq_union in H.
         rewrite (cstate_eq_a c1 c2 a1).
         rewrite (cstate_eq_a c1 c2 a2).
         reflexivity. intuition. intuition.
         simpl in *. 
         apply cstate_eq_union in H.
         rewrite (cstate_eq_a c1 c2 a1).
         rewrite (cstate_eq_a c1 c2 a2).
         reflexivity. intuition. intuition.   
         simpl in *.
         rewrite IHb. reflexivity. assumption. 
         simpl in *. apply cstate_eq_union in H.
         rewrite IHb1. rewrite IHb2.
         reflexivity. intuition. intuition.   
  Admitted.
  
  
  Lemma cstate_eq_P{ s e:nat}: forall c1 c2 P (q: qstate s e),
  cstate_eq c1 c2 (Free_pure P)->
  State_eval P (c1, q)->
  State_eval P (c2, q).
  Proof. induction P; intros. 
         simpl. simpl in H0.
         rewrite<- (cstate_eq_b c1).
         assumption. assumption.
         simpl in *.
  Admitted.
  
  
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
         destruct a. simpl in *. destruct H.
         destruct a.
         simpl in *. destruct H.
         destruct mu2. 
         destruct a. destruct a0.
         econstructor.
         simpl in H.
         apply cstate_eq_P with c.
         intuition.
         simpl.
         rewrite (state_eq_Pure _  _ (c,q)).
         inversion_clear H0.
         assumption. reflexivity.
         econstructor.
         destruct a.
         destruct a0. 
         econstructor.
         simpl in H.
         apply cstate_eq_P with c.
         intuition.
         simpl.
         rewrite (state_eq_Pure _  _ (c,q)).
         inversion_clear H0.
         assumption.
         reflexivity.
         rewrite <-State_eval_dstate_Forall.
         apply IHmu1.
         simpl in H. 
         intuition. destruct mu1. simpl in *.
         destruct H. destruct H1.
         inversion_clear H0.
         rewrite State_eval_dstate_Forall.
         assumption. discriminate. discriminate.
  Qed. 
  
  Lemma cstate_eq_F{ s e:nat}: forall c1 c2 F (q: qstate s e),
  cstate_eq c1 c2 (fst (Free_state F))->
  State_eval F (c1, q)->
  State_eval F (c2, q).
  Proof. induction F; intros.
         apply cstate_eq_P with c1.
         assumption. assumption.
         apply qstate_eq_Qexp with (c1,q).
         reflexivity. assumption.
         simpl in *. 
         split. intuition.
         split. apply IHF1. 
         apply cstate_eq_union in H.
         intuition. intuition.
         apply IHF2.
         apply cstate_eq_union in H.
         intuition. intuition.
         simpl in *. 
         split. apply IHF1. 
         apply cstate_eq_union in H.
         intuition. intuition.
         apply IHF2.
         apply cstate_eq_union in H.
         intuition. intuition.
  Qed.

  (*----------------------------------------------------*)


Lemma  le_min: forall s e, 
s<=e -> min s e= s .
Proof. induction s; intros. simpl. reflexivity.
       destruct e. 
       simpl. lia. 
       simpl. f_equal. apply IHs.
       lia.
Qed.

Lemma  le_max: forall s e, 
s<=e -> max s e= e .
Proof. induction s; intros. simpl. reflexivity.
       destruct e. 
       simpl. lia. 
       simpl. f_equal. apply IHs.
       lia.
Qed.


  Lemma min_le: forall s0 e0 s1 e1, 
  s0<=e0 /\ e0=s1 /\ s1<=e1 ->
  min s0 s1 = s0 /\
  max e0 e1= e1.
  Proof. intros. split; [apply le_min| apply le_max]; lia. 
  Qed.

  Fixpoint Free_QExp'(qs :QExp) := 
  match qs with 
  |QExp_s s e v => (s, e) 
  |QExp_t qs1 qs2 => (min (fst (Free_QExp' qs1)) (fst (Free_QExp' qs2)),
                      max  (snd (Free_QExp' qs1))  (snd (Free_QExp' qs2) ))
  end.

Fixpoint Free_State(F:State_formula):=
  match F with 
    |SPure P => (0, 0)
    |SQuan qs=> Free_QExp' qs 
    |SOdot F1 F2=> if  (fst (Free_State F1) =? snd (Free_State F1))
                   then Free_State F2 
                   else if (fst (Free_State F2)=?snd (Free_State F2))
                   then Free_State F1
                   else (min (fst (Free_State F1)) (fst (Free_State F2)),
                    max  (snd (Free_State F1))  (snd (Free_State F2) ))
    |SAnd F1 F2 =>  if  (fst (Free_State F1) =? snd (Free_State F1))
                    then Free_State F2 
                    else if (fst (Free_State F2)=?snd (Free_State F2))
                    then Free_State F1
                    else (min (fst (Free_State F1)) (fst (Free_State F2)),
                      max  (snd (Free_State F1))  (snd (Free_State F2) ))
    (* |SNot F'=> Free_state F'
    | Assn_sub X a F => Free_state F *)
  end.

  Fixpoint Considered_QExp (qs:QExp) : Prop :=
  match qs with 
  |QExp_s s e v => s<e  
  |QExp_t qs1 qs2 => Considered_QExp qs1 /\ Considered_QExp qs2 /\ 
                    (((snd (Free_QExp' qs1))=(fst (Free_QExp' qs2)))
                    \/ ((snd (Free_QExp' qs2))=(fst (Free_QExp' qs1))))
  end.

  Fixpoint Considered_Formula (F:State_formula) : Prop:=
  match F with
  | SPure P => True 
  | SQuan s => Considered_QExp s
  | SOdot F1 F2 =>  if  (fst (Free_State F1) =? snd (Free_State F1))
  then Considered_Formula F2 
  else if (fst (Free_State F2)=?snd (Free_State F2))
  then Considered_Formula F1
  else  ( Considered_Formula F1 /\ Considered_Formula F2 
                   /\ (((snd (Free_State F1))=(fst (Free_State F2)))
                   \/ ((snd (Free_State F2))=(fst (Free_State F1)))))
  |SAnd F1 F2 =>     if  (fst (Free_State F1) =? snd (Free_State F1))
  then Considered_Formula F2 
  else if (fst (Free_State F2)=?snd (Free_State F2))
  then Considered_Formula F1
  else
                      (Considered_Formula F1 /\ Considered_Formula F2 
                  /\  ((((fst (Free_State F1))=(fst (Free_State F2)))/\
                      ((snd (Free_State F1))=(snd (Free_State F2))))
                      \/ ((snd (Free_State F1))=(fst (Free_State F2))) 
                      \/ (((snd (Free_State F2))=(fst (Free_State F1))))))
  end. 



(*--------------------------------------------*)


Fixpoint dstate_qstate_eq {s e:nat} (mu1 mu2: list(cstate * qstate s e)):=
match mu1, mu2 with 
| nil , nil => True
|(c1,q1)::mu'1 , (c2,q2)::mu'2 => and (q1=q2) (dstate_qstate_eq mu'1 mu'2)
| _, _ => False 
end.
  

Lemma Considered_QExp_dom: forall qs,
Considered_QExp qs ->
fst (Free_QExp' qs) <  snd (Free_QExp' qs) .
Proof. induction qs; 
simpl. intuition.
simpl; intros.
destruct H. 
destruct H0.
destruct H1.

apply IHqs1  in H.
apply IHqs2 in H0.
assert(min (fst (Free_QExp' qs1))
(fst (Free_QExp' qs2))=(fst (Free_QExp' qs1))/\
max (snd (Free_QExp' qs1))
  (snd (Free_QExp' qs2))=(snd (Free_QExp' qs2))).
apply min_le. intuition.
destruct H2. rewrite H2. rewrite H3.
apply lt_trans with  (snd (Free_QExp' qs1)).
assumption. rewrite H1.
assumption.

apply IHqs1  in H.
apply IHqs2 in H0.
rewrite min_comm.
rewrite max_comm.
assert(min (fst (Free_QExp' qs2))
(fst (Free_QExp' qs1))=(fst (Free_QExp' qs2))/\
max (snd (Free_QExp' qs2))
  (snd (Free_QExp' qs1))=(snd (Free_QExp' qs1))).
apply min_le. intuition.
destruct H2. rewrite H2. rewrite H3.
apply lt_trans with  (snd (Free_QExp' qs2)).
assumption. rewrite H1.
assumption.
Qed.



Lemma Considered_Formula_dom: forall F,
Considered_Formula F ->
fst (Free_State F) <=  snd (Free_State F) .
Proof. induction F; intros.
       simpl. intuition.
       apply Considered_QExp_dom in H.
       simpl. lia.  
  
       simpl in H.
       destruct (eq_dec (fst (Free_State F1))  (snd (Free_State F1))).
       apply Nat.eqb_eq in e. 
       simpl. 
       rewrite e in *.  auto.
       apply Nat.eqb_neq in n. 
       destruct (eq_dec (fst (Free_State F2))  (snd (Free_State F2))).
       apply Nat.eqb_eq in e.
       simpl. 
       rewrite e in *. rewrite n in *.  auto.
       apply Nat.eqb_neq in n0.
       simpl.
       rewrite n in *. rewrite n0 in *.

       destruct H.
       destruct H0.
       destruct H1.
       
simpl.  
apply IHF1  in H.
apply IHF2 in H0.
assert(min (fst (Free_State F1))
(fst (Free_State F2))=(fst (Free_State F1))/\
max (snd (Free_State F1))
  (snd (Free_State F2))=(snd (Free_State F2))).
apply min_le. intuition.
destruct H2. rewrite H2. rewrite H3.
apply le_trans with  (snd (Free_State F1)).
assumption. rewrite H1.
assumption.

simpl.
apply IHF1  in H.
apply IHF2 in H0.
rewrite min_comm.
rewrite max_comm.
assert(min (fst (Free_State F2))
(fst (Free_State F1))=(fst (Free_State F2))/\
max (snd (Free_State F2))
  (snd (Free_State F1))=(snd (Free_State F1))).
apply min_le. intuition.
destruct H2. rewrite H2. rewrite H3.
apply le_trans with  (snd (Free_State F2)).
assumption. rewrite H1.
assumption.

simpl in H.

destruct (eq_dec (fst (Free_State F1))  (snd (Free_State F1))).
       apply Nat.eqb_eq in e. 
       simpl. 
       rewrite e in *.  auto.
       apply Nat.eqb_neq in n. 
       destruct (eq_dec (fst (Free_State F2))  (snd (Free_State F2))).
       apply Nat.eqb_eq in e.
       simpl. 
       rewrite e in *. rewrite n in *.  auto.
       apply Nat.eqb_neq in n0.
       simpl.
       rewrite n in *. rewrite n0 in *.



destruct H.
destruct H0.
destruct H1.

simpl.
apply IHF1  in H.
apply IHF2 in H0.
destruct H1. rewrite H1. rewrite H2.
rewrite min_id.
rewrite max_id. intuition.

destruct H1.

simpl.
apply IHF1  in H.
apply IHF2 in H0.
assert(min (fst (Free_State F1))
(fst (Free_State F2))=(fst (Free_State F1))/\
max (snd (Free_State F1))
  (snd (Free_State F2))=(snd (Free_State F2))).
apply min_le. intuition.
destruct H2. rewrite H2. rewrite H3.
apply le_trans with  (snd (Free_State F1)).
assumption. rewrite H1.
assumption.


simpl.
apply IHF1  in H.
apply IHF2 in H0.
rewrite min_comm.
rewrite max_comm.
assert(min (fst (Free_State F2))
(fst (Free_State F1))=(fst (Free_State F2))/\
max (snd (Free_State F2))
(snd (Free_State F1))=(snd (Free_State F1))).
apply min_le. intuition.
destruct H2. rewrite H2. rewrite H3.
apply le_trans with  (snd (Free_State F2)).
assumption. rewrite H1.
assumption. 
Qed.

Require Import OrderedType.
Module MD := OrderedTypeFacts(D).

Lemma QExp_eval_dom{ s e:nat}: forall qs c (q:qstate s e),
QExp_eval qs (c,q) -> s<=fst (Free_QExp' qs) /\ 
fst (Free_QExp' qs) < snd (Free_QExp' qs) /\ snd (Free_QExp' qs) <=e.
Proof. induction qs; intros.
       simpl in *. intuition.
       simpl in *.
       destruct H. destruct H0.
       apply IHqs1 in H0.
       apply IHqs2 in H1.
       split. 
       apply min_glb.
       intuition. intuition.
       split.
       destruct (D.compare (snd (Free_QExp' qs1)) (fst (Free_QExp' qs2))) eqn: E;
       try unfold D.lt in l.
       rewrite min_l; try lia. 
       rewrite max_r; try lia.  
      
       unfold D.eq in e0. lia.
       destruct (D.compare (snd (Free_QExp' qs2)) (fst (Free_QExp' qs1))) eqn: E';
       try unfold D.lt in l0.
       rewrite min_r; try lia. 
       rewrite max_l; try lia.
      
       unfold D.eq in e0. lia.
       apply min_lt_iff.
       left. 
       apply max_lt_iff. left. lia.
       
       apply max_lub_iff.
       intuition.
Qed.


Lemma State_eval_dom{ s e:nat}: forall F c (q:qstate s e),
State_eval F (c,q) ->(fst (Free_State F) = snd (Free_State F) )\/ 
(s<=fst (Free_State F) /\ fst (Free_State F) < snd (Free_State F) /\ snd (Free_State F) <=e).
Proof. induction F; intros.
       simpl in *. left. intuition. 
       simpl in *. right.
       apply QExp_eval_dom with c q.
       assumption.

       destruct H. destruct H0.
       apply IHF1 in H0.
       apply IHF2 in H1.
       destruct H0.
       destruct H1.
       apply Nat.eqb_eq in H0.
       left. simpl.
       rewrite H0. assumption.
       right. 
       
       apply Nat.eqb_eq in H0.
       simpl. rewrite H0.
       assumption.
       destruct H1.

       assert(fst (Free_State F1) <> snd (Free_State F1)).
       lia. apply Nat.eqb_neq in H2.
       apply Nat.eqb_eq in H1.
       right.
       simpl. rewrite H1. rewrite H2.
       assumption. 

       assert(fst (Free_State F1) <> snd (Free_State F1)).
       lia. apply Nat.eqb_neq in H2.
       assert(fst (Free_State F2) <> snd (Free_State F2)).
       lia. apply Nat.eqb_neq in H3.
       right. 
       simpl. rewrite H2. rewrite H3.
       simpl. 
       split. 
       apply min_glb.
       intuition. intuition.
       split.
       
       destruct (D.compare (snd (Free_State F1)) (fst (Free_State F2))) eqn: E;
       try unfold D.lt in l.
       rewrite min_l; try lia. 
       rewrite max_r; try lia.  
      
       unfold D.eq in e0. lia.
       destruct (D.compare (snd (Free_State F2)) (fst (Free_State F2))) eqn: E';
       try unfold D.lt in l0.
       rewrite min_r; try lia. 
       rewrite max_l; try lia.
      
       unfold D.eq in e0. lia.
       apply min_lt_iff.
       left. 
       apply max_lt_iff. left. lia.
       apply max_lub_iff.
       intuition.
       destruct H.
       apply IHF1 in H.
       apply IHF2 in H0.

       destruct H.
       destruct H0.
       apply Nat.eqb_eq in H.
       left. simpl.
       rewrite H. assumption.
       right. 
       
       apply Nat.eqb_eq in H.
       simpl. rewrite H.
       assumption.
       destruct H0.

       assert(fst (Free_State F1) <> snd (Free_State F1)).
       lia. apply Nat.eqb_neq in H1.
       apply Nat.eqb_eq in H0.
       right.
       simpl. rewrite H0. rewrite H1.
       assumption. 

       assert(fst (Free_State F1) <> snd (Free_State F1)).
       lia. apply Nat.eqb_neq in H1.
       assert(fst (Free_State F2) <> snd (Free_State F2)).
       lia. apply Nat.eqb_neq in H2.
       right. 
       simpl. rewrite H1. rewrite H2.
       simpl. 
       split. 
       apply min_glb.
       intuition. intuition.
       split.
       
       destruct (D.compare (snd (Free_State F1)) (fst (Free_State F2))) eqn: E;
       try unfold D.lt in l.
       rewrite min_l; try lia. 
       rewrite max_r; try lia.  
      
       unfold D.eq in e0. lia.
       destruct (D.compare (snd (Free_State F2)) (fst (Free_State F2))) eqn: E';
       try unfold D.lt in l0.
       rewrite min_r; try lia. 
       rewrite max_l; try lia.
      
       unfold D.eq in e0. lia.
       apply min_lt_iff.
       left. 
       apply max_lt_iff. left. lia.
       apply max_lub_iff.
       intuition.
Qed.


Lemma dstate_eval_dom{ s e:nat}: forall F (mu:list (cstate * qstate s e)),
State_eval_dstate F mu  -> (fst (Free_State F) = snd (Free_State F) )\/ 
(s<=fst (Free_State F) /\ fst (Free_State F) < snd (Free_State F) /\ snd (Free_State F) <=e).
Proof. induction mu; intros. destruct H.
     inversion H; subst. destruct a. 
     apply State_eval_dom with c q.
     assumption. 
Qed.


Lemma QExp_eval_pure: forall qs s e c (q: qstate s e) ,
Considered_QExp qs ->
WF_qstate q->
QExp_eval qs (c, q)->
@Par_Pure_State (2^((snd (Free_QExp' qs))- ((fst (Free_QExp' qs)))))
(@PMpar_trace s e q ((fst (Free_QExp' qs))) (((snd (Free_QExp' qs)))) ).
Proof. induction qs; intros. unfold Par_Pure_State. 
       simpl in H1. 
       exists ((Cmod (@trace (2^(e0-s0)) q))%R).
       exists (outer_product v v).
       simpl. 
       rewrite <-PMtrace_scale in H1.
       unfold outer_product in H1.
       destruct H1. destruct H2.
       destruct H3. destruct H4. 
       split. 
       apply mixed_state_Cmod_1.
       apply H0. split.
       econstructor. split. 
       apply H1. unfold outer_product.
       reflexivity.
       unfold outer_product.
       rewrite <-H5. 
       rewrite Mscale_assoc.
       rewrite RtoC_mult.
       rewrite Rdiv_unfold.
       rewrite Rmult_1_l.
       rewrite Rinv_r. 
       rewrite Mscale_1_l.
       reflexivity. 
       assert((Cmod (@trace (2^(e0-s0)) q) > 0)%R).
       apply mixed_state_Cmod_1.
       apply H0. lra.

       simpl QExp_eval in H1.  
       destruct H1. 
       destruct H2.
       pose H2 as H2'. pose H3 as H3'.
       apply IHqs1 in H2'.
       apply IHqs2 in H3'.
       simpl in H.
       destruct H.
       destruct H4.
       destruct H5.
       simpl.
       assert(min (fst (Free_QExp' qs1))
       (fst (Free_QExp' qs2))=(fst (Free_QExp' qs1))/\
       max (snd (Free_QExp' qs1))
         (snd (Free_QExp' qs2))=(snd (Free_QExp' qs2))).
       apply min_le. split. 
       pose (Considered_QExp_dom qs1 H).
       lia. 
       split. intuition.

       pose (Considered_QExp_dom qs2 H4).
       lia.  
       destruct H6. rewrite H6. rewrite H7.
     apply (Par_Pure_State_wedge) with (snd (Free_QExp' qs1)).
     pose (QExp_eval_dom qs1 c q H2). 
     pose (QExp_eval_dom qs2 c q H3).
     split.  intuition.
    split. pose (Considered_QExp_dom qs1 H). lia. 
     split. rewrite H5. pose (Considered_QExp_dom qs2 H4). lia.
      intuition.  assumption. assumption. 
       rewrite H5. assumption.
      
       simpl.
       rewrite min_comm.
       rewrite max_comm.
       assert(min (fst (Free_QExp' qs2))
       (fst (Free_QExp' qs1))=(fst (Free_QExp' qs2))/\
       max (snd (Free_QExp' qs2))
         (snd (Free_QExp' qs1))=(snd (Free_QExp' qs1))).
       apply min_le. split. 
       pose (Considered_QExp_dom qs2 H4). lia. 
       split. intuition.
       pose (Considered_QExp_dom qs1 H). lia. 
      destruct H6. rewrite H6. rewrite H7.
     apply (Par_Pure_State_wedge) with (snd (Free_QExp' qs2)).
     pose (QExp_eval_dom qs1 c q H2). 
     pose (QExp_eval_dom qs2 c q H3).
     split.  intuition.
    split. pose (Considered_QExp_dom qs1 H). lia. 
     split. rewrite H5. pose (Considered_QExp_dom qs2 H4). lia.
      intuition.  assumption. assumption. 
       rewrite H5. assumption.
        apply H.
        assumption.
        apply H.
        assumption.
Qed.


Lemma State_eval_pure: forall F s e c (q: qstate s e) ,
Considered_Formula F ->
WF_qstate q->
State_eval F (c, q)->
((fst (Free_State F)) = (snd (Free_State F))) \/ @Par_Pure_State (2^((snd (Free_State F))- ((fst (Free_State F)))))
(@PMpar_trace s e q ((fst (Free_State F))) (((snd (Free_State F)))) ).
Proof. induction F; intros.
       simpl. left. reflexivity.
       right. 
       apply QExp_eval_pure with c.
       assumption. assumption.
       assumption.
        
        
       destruct H1. 
       destruct H2.
       destruct (Nat.eq_dec (fst (Free_State F1)) (snd (Free_State F1))).
       apply Nat.eqb_eq in e0.
       simpl in *. rewrite e0 in *. 
       apply IHF2 with c; assumption.
       
       pose H2 as H2'.  
       apply IHF1 in H2'. 
       destruct H2'. 
       lia. apply Nat.eqb_neq in n.
       destruct (Nat.eq_dec (fst (Free_State F2)) (snd (Free_State F2))).
       apply Nat.eqb_eq in e0.
       simpl in *. rewrite e0 in *. rewrite n in *.
       right. assumption.
       pose H3 as H3'. 
       apply IHF2 in H3'.
       destruct H3'. lia.
       apply Nat.eqb_neq in n0.
       simpl in *. rewrite n in *. rewrite n0 in*.   
       simpl in *.
      
       right. rewrite Nat.eqb_neq in *.
       destruct H.
       destruct H6.
       destruct H7.
       simpl.
       assert(min (fst (Free_State F1))
(fst (Free_State F2))=(fst (Free_State F1))/\
max (snd (Free_State F1))
  (snd (Free_State F2))=(snd (Free_State F2))).
apply min_le. split.
pose (Considered_Formula_dom F1 H). lia. 
split. assumption.
apply Considered_Formula_dom. assumption.
destruct H8. rewrite H8. rewrite H9.
     apply Par_Pure_State_wedge with (snd (Free_State F1)).
     pose (State_eval_dom F1 c q H2).
     destruct o. lia.  
     pose (State_eval_dom F2 c q H3).
     destruct o. lia.  
     split. intuition. 
     split. 
     apply Considered_Formula_dom. assumption.
     split. 
     rewrite H7. 
     apply Considered_Formula_dom. assumption.
     intuition. assumption. assumption.
     rewrite H7.
     assumption.
       
     simpl.
     rewrite min_comm.
     rewrite max_comm.
     assert(min (fst (Free_State F2))
     (fst (Free_State F1))=(fst (Free_State F2))/\
     max (snd (Free_State F2))
       (snd (Free_State F1))=(snd (Free_State F1))).
     apply min_le. split. 
     apply Considered_Formula_dom. assumption.
     split. intuition.
     apply Considered_Formula_dom. assumption.
     destruct H8. rewrite H8. rewrite H9.
   apply (Par_Pure_State_wedge) with (snd (Free_State F2)).
   pose (State_eval_dom F1 c q H2).
     destruct o. lia.  
     pose (State_eval_dom F2 c q H3).
     destruct o. lia.  
     split. intuition. 
     split. 
     apply Considered_Formula_dom. assumption.
     split. 
     rewrite H7. 
     apply Considered_Formula_dom. assumption.
     intuition. assumption. assumption.
     rewrite H7.
     assumption. 
       
     apply Nat.eqb_neq in n0. 
     simpl in *.  rewrite n in *.
     rewrite n0 in *.

        apply H.
        assumption.
        apply Nat.eqb_neq in n. 
     simpl in *.  rewrite n in *.
     destruct (Nat.eq_dec (fst (Free_State F2)) (snd (Free_State F2))).
     apply Nat.eqb_eq in e0. rewrite e0 in *.
        apply H. 
        apply Nat.eqb_neq in n0. rewrite n0 in *.
        apply H.
        assumption.

simpl in H. destruct H1.


destruct (Nat.eq_dec (fst (Free_State F1)) (snd (Free_State F1))).
       apply Nat.eqb_eq in e0.
       simpl in *. rewrite e0 in *. 
       apply IHF2 with c; assumption.
       
       pose H1 as H1'.  
       apply IHF1 in H1'. 
       destruct H1'. 
       lia. apply Nat.eqb_neq in n.
       destruct (Nat.eq_dec (fst (Free_State F2)) (snd (Free_State F2))).
       apply Nat.eqb_eq in e0.
       simpl in *. rewrite e0 in *. rewrite n in *.
       right. assumption.
       pose H2 as H2'. 
       apply IHF2 in H2'.
       destruct H2'. lia.
       apply Nat.eqb_neq in n0.
       simpl in *. rewrite n in *. rewrite n0 in*.   
       simpl in *.
      
       right. rewrite Nat.eqb_neq in *.

destruct H.
destruct H5.
destruct H6.
destruct H6.
simpl. rewrite H6. rewrite H7.
rewrite min_id. rewrite max_id.
assumption.

destruct H6.

simpl.
assert(min (fst (Free_State F1))
(fst (Free_State F2))=(fst (Free_State F1))/\
max (snd (Free_State F1))
  (snd (Free_State F2))=(snd (Free_State F2))).
apply min_le. split.
apply Considered_Formula_dom. assumption.
split. assumption.
apply Considered_Formula_dom. assumption.
destruct H7. rewrite H7. rewrite H8.
     apply Par_Pure_State_wedge with (snd (Free_State F1)).
    
     pose (State_eval_dom F1 c q H1).
     destruct o. lia.  
     pose (State_eval_dom F2 c q H2).
     destruct o. lia.  
     split. intuition. 
     split. 
     apply Considered_Formula_dom. assumption.
     split. 
     rewrite H6. 
     apply Considered_Formula_dom. assumption.
     intuition. assumption. assumption.
     rewrite H6.
     assumption.
    
     simpl.
     rewrite min_comm.
     rewrite max_comm.
     assert(min (fst (Free_State F2))
     (fst (Free_State F1))=(fst (Free_State F2))/\
     max (snd (Free_State F2))
       (snd (Free_State F1))=(snd (Free_State F1))).
     apply min_le. split. 
     apply Considered_Formula_dom. assumption.
     split. intuition.
     apply Considered_Formula_dom. assumption.
     destruct H7. rewrite H7. rewrite H8.
     apply Par_Pure_State_wedge with (snd (Free_State F2)).
    
     pose (State_eval_dom F1 c q H1).
     destruct o. lia.  
     pose (State_eval_dom F2 c q H2).
     destruct o. lia.  
     split. intuition. 
     split. 
     apply Considered_Formula_dom. assumption.
     split. 
     rewrite H6. 
     apply Considered_Formula_dom. assumption.
     intuition. assumption. assumption.
     rewrite H6.
     assumption.


     apply Nat.eqb_neq in n0. 
     simpl in *.  rewrite n in *.
     rewrite n0 in *.

        apply H.
        assumption.
        apply Nat.eqb_neq in n. 
     simpl in *.  rewrite n in *.
     destruct (Nat.eq_dec (fst (Free_State F2)) (snd (Free_State F2))).
     apply Nat.eqb_eq in e0. rewrite e0 in *.
        apply H. 
        apply Nat.eqb_neq in n0. rewrite n0 in *.
        apply H.
        assumption.
Qed.




Lemma QExp_free_eval{s e:nat}:forall (qs: QExp) (st: state s e) s' e',
s<=s'/\ s'<=e' /\ e'<=e ->
s'<=(fst (Free_QExp' qs)) /\ (snd (Free_QExp' qs))<=e'->
@WF_Matrix (2^(e-s)) (2^(e-s)) (snd st)->
QExp_eval qs st <-> QExp_eval qs (fst st, (PMpar_trace (snd st) s' e')).
Proof. induction qs; split; intros. 
        simpl in *. rewrite PMtrace_scale.
        rewrite PMpar_trace_assoc. 
        split. intuition. split. lia.
        split. lia. split. lia. 
        rewrite Ptrace_trace. intuition.
        lia. assumption. lia.  
        simpl in *. 
        rewrite PMtrace_scale in H2.
        rewrite PMpar_trace_assoc in H2.
        rewrite Ptrace_trace in H2.
        split. intuition. 
        split. lia. split. lia. split. lia. 
        intuition. lia. assumption.  lia.
        simpl in H2. 
        simpl. split.  intuition.
        destruct st. simpl in *.
  
        split. 
        apply (IHqs1 (c, q)).  assumption.
        intuition. assumption.
        intuition. 
        apply (IHqs2 (c,q)). assumption.
        intuition. assumption.
        intuition. 
        simpl in *. split.  intuition.
        destruct H2.
        destruct H3.
  
        split.
        apply IHqs1 in H3. 
        assumption. intuition.
        pose (QExp_eval_dom qs1 (fst st) (PMpar_trace (snd st) s' e') H3).
        lia. 
        assumption.
        apply IHqs2 in H4. assumption.
        intuition.
        pose (QExp_eval_dom qs2 (fst st) (PMpar_trace (snd st) s' e') H4).
        lia. 
        assumption. 
Qed.
        

Definition option_nat (n:option nat):nat :=
  match n with 
  |None => 0
  |Some x => x
   end .

   Lemma min_max_eq: forall x1 x2 y1 y2,
   min x1 x2= max y1 y2->
   x1<=y1 /\ x2<=y2->
   x1=y1 /\ x2 = y2.
   Proof. intros. lia. Qed.


   Lemma Pure_free_eval'{s e s' e':nat}:forall  (F: State_formula) c (q : qstate s e) (q0: qstate s' e'),
   (fst (Free_State F)) = (snd (Free_State F))->
   State_eval F (c, q) -> 
   State_eval F (c, q0).
   Proof. induction F;   intros.
           eapply state_eq_Pure with (c, q). 
           reflexivity. apply H0.
          apply QExp_eval_dom in H0.
          unfold Free_State in *.
          lia.
   
          simpl in *;
          split. intuition.
          destruct H0. destruct H1.
       bdestruct (fst (Free_State F1) =? snd (Free_State F1)).
       split.  apply IHF1 with q; try assumption. 
       apply IHF2 with q; try assumption. 
   
       bdestruct (fst (Free_State F2) =? snd (Free_State F2)).
       split. eapply IHF1 with q; try assumption. 
       apply IHF2 with q; try assumption. 
       simpl in *. 
       simpl in H. 
       apply min_max_eq in H. lia. 
         apply State_eval_dom in H1. lia.  
      
     simpl in *. 
     destruct H0.
     bdestruct (fst (Free_State F1) =? snd (Free_State F1)).
     split. apply IHF1 with q; try assumption. 
     apply IHF2 with q; try assumption. 
 
     bdestruct (fst (Free_State F2) =? snd (Free_State F2)).
     split. eapply IHF1 with q; try assumption. 
     apply IHF2 with q; try assumption. 
     simpl in *.
     apply min_max_eq in H. lia. 
         apply State_eval_dom in H1. lia.  
Qed. 

(*对于一个连续的而言*)  
Lemma State_free_eval{s e:nat}:forall (F: State_formula) (st: state s e) s' e',
s<=s'/\ s'<=e' /\ e'<=e ->
s'<=(fst (Free_State F)) /\ (snd (Free_State F))<=e' ->
@WF_Matrix (2^(e-s)) (2^(e-s)) (snd st) ->
State_eval F st <-> 
State_eval F (fst st, (PMpar_trace (snd st) s' e')).
Proof. induction F. split; intros. destruct st. 
    eapply state_eq_Pure with (c, q). 
    reflexivity. apply H2.
    destruct st. simpl in *.
    eapply state_eq_Pure with (c, PMpar_trace q s' e'). 
    reflexivity. intuition. destruct st.
    split; intros.
    apply (QExp_free_eval _  (c, q)) .
    intuition. intuition. intuition.
    assumption.
    simpl in *.
    rewrite QExp_free_eval. apply H2. 
    intuition. intuition. intuition.


    intros.
    simpl in *.
    bdestruct (fst (Free_State F1) =? snd (Free_State F1)).
    split; intros.
    split. intuition.
    split. destruct st. simpl.  
    apply (@Pure_free_eval' s e) with q; try assumption.
 intuition.
    apply IHF2; try assumption. intuition.
    split. intuition. 
    split. 
    destruct st. simpl.  
    apply (@Pure_free_eval' s' e') with (PMpar_trace (snd (c, q)) s' e'); try assumption.
           intuition.
    eapply IHF2; try assumption. apply H. assumption.
    intuition.
    bdestruct (fst (Free_State F2) =? snd (Free_State F2)).
    split. intros.
    split. intuition.
    split. apply IHF1; try assumption. intuition.
    destruct st. simpl.  
    apply (@Pure_free_eval' s e) with q; try assumption.
 intuition.
    split. intuition.
    split. eapply IHF1; try assumption. apply H.
    assumption. intuition.
    destruct st. simpl.  
    apply (@Pure_free_eval' s' e') with (PMpar_trace (snd (c, q)) s' e'); try assumption.
           intuition.

    split. intros. 
    simpl in *. split. intuition.
    split. apply IHF1. assumption.
    split.
    apply min_glb_l with (fst (Free_State F2)).
    intuition.
    eapply max_lub_iff.  rewrite max_comm. apply H0.
    assumption. intuition.
    apply IHF2. assumption.
    split.
    apply min_glb_l with (fst (Free_State F2)).
    intuition.
    eapply max_lub_iff.   apply H0.
    assumption. intuition.
    split. intuition.
    simpl in *.
    split. eapply IHF1; try assumption. apply H.
    split.
    apply min_glb_l with (fst (Free_State F2)).
    intuition.
    eapply max_lub_iff.  rewrite max_comm. apply H0.
    intuition.
    eapply IHF2; try assumption. apply H. 
    split.
    apply min_glb_l with (fst (Free_State F2)).
    intuition.
    eapply max_lub_iff.  apply H0. intuition.
    

    intros.
    simpl in *.
    bdestruct (fst (Free_State F1) =? snd (Free_State F1)).
    split; intros.
    split.
    destruct st. simpl.  
    apply (@Pure_free_eval' s e) with q; try assumption.
 intuition.
    apply IHF2; try assumption. intuition.
    split.
    destruct st. simpl.  
    apply (@Pure_free_eval' s' e') with (PMpar_trace (snd (c, q)) s' e'); try assumption.
           intuition.
    eapply IHF2; try assumption. apply H. assumption.
    intuition.
    bdestruct (fst (Free_State F2) =? snd (Free_State F2)).
    split. intros.
    split. apply IHF1; try assumption. intuition.
    destruct st. simpl.  
    apply (@Pure_free_eval' s e) with q; try assumption.
 intuition.
    split. eapply IHF1; try assumption. apply H.
    assumption. intuition.
    destruct st. simpl.  
    apply (@Pure_free_eval' s' e') with (PMpar_trace (snd (c, q)) s' e'); try assumption.
           intuition.
    simpl in *.
    split; intros.
    split.  apply IHF1. assumption.
    split.
    apply min_glb_l with (fst (Free_State F2)).
    intuition.
    eapply max_lub_iff.  rewrite max_comm. apply H0.
    assumption. intuition.
    apply IHF2. assumption.
    split.
    apply min_glb_l with (fst (Free_State F2)).
    intuition.
    eapply max_lub_iff.  apply H0.
    assumption. intuition.
    split. eapply IHF1; try assumption. apply H.
    split.
    apply min_glb_l with (fst (Free_State F2)).
    intuition.
    eapply max_lub_iff.  rewrite max_comm. apply H0.
    intuition.
  
    eapply IHF2; try assumption. apply H. 
    split.
    apply min_glb_l with (fst (Free_State F2)).
    intuition.
    eapply max_lub_iff.   apply H0.
    intuition.
Qed.


Lemma State_dstate_free_eval{s e:nat}:forall  (mu: list (cstate * qstate s e)) (F: State_formula) s' e',
s<=s'/\ s'<=e' /\ e'<=e ->
s'<=(fst (Free_State F)) /\
 (snd (Free_State F))<=e'->
WF_Matrix_dstate mu ->
State_eval_dstate F mu <-> 
State_eval_dstate F (d_par_trace mu s' e').
Proof. induction mu; intros. simpl. intuition.
       destruct mu; destruct a. 
       split; intros.
       inversion_clear H2. 
       econstructor.
       apply (State_free_eval _ (c, q)).  
       assumption. assumption. 
       inversion_clear H1. intuition.
       assumption. econstructor.
       
       inversion_clear H2.
       econstructor.
       apply (State_free_eval _ (c, q)) in H3.
       assumption. assumption. assumption.
       inversion_clear H1. intuition.
       econstructor.

       split; intros.
       inversion_clear H2.
       econstructor. 
       apply (State_free_eval _ (c, q)).  
       assumption. assumption. 
       inversion_clear H1. intuition.
       assumption.
       rewrite <-State_eval_dstate_Forall in H4. 
       rewrite (IHmu _ s' e') in H4.
       rewrite <-State_eval_dstate_Forall.
       apply H4. destruct p.  discriminate.
       assumption. assumption. 
       inversion_clear H1. intuition.
       discriminate. 
       
       econstructor. 
       inversion_clear H2.
       apply (State_free_eval _ (c, q)) in H3.  
       assumption. assumption. assumption. 
       inversion_clear H1. intuition.
       destruct p. 
       inversion_clear H2.
       rewrite <-State_eval_dstate_Forall. 
       rewrite (IHmu _ s' e').
       simpl. assumption. assumption.
       assumption.
       inversion_clear H1. intuition.
       discriminate.
Qed.



Lemma In_inter_empty: forall x y a,
NSet.Equal (NSet.inter x y) (NSet.empty)->
NSet.In a  y ->
~(NSet.In a x) .
Proof. intros. intro.  
pose (NSet.inter_3 H1 H0) .
apply H in i. apply In_empty in i. destruct i.   
Qed.

Lemma d_par_trace_trace{s e:nat}: forall (l r : nat) (mu: list (cstate * qstate s e)),
s <= l /\ l <= r <= e -> 
WF_Matrix_dstate mu ->
 d_trace_aux mu =
 d_trace_aux (d_par_trace mu l r).
Proof. induction mu; intros. simpl. reflexivity.
      destruct a. simpl. unfold s_trace.
      simpl.  rewrite  Ptrace_trace.
      rewrite IHmu. reflexivity.
      intuition. inversion_clear H0. intuition.
      intuition. inversion_clear H0. 
       intuition.


       
Qed.


Lemma WF_Mixed_dstate{ s e: nat}: forall (mu : list (cstate * qstate s e)), 
WF_dstate_aux mu -> WF_Matrix_dstate mu.
Proof. induction mu; intros. econstructor.
      destruct a. inversion H; subst.
      econstructor. apply WF_Mixed.
      apply H2.
      apply IHmu.
      apply H3.       
Qed.


Lemma WF_d_par_trace: forall (s e l r : nat) (mu: list (cstate * qstate s e)),
s <= l /\ l <= r <= e -> WF_dstate_aux mu ->
 WF_dstate_aux (d_par_trace mu l r).
Proof. induction mu; intros. simpl. econstructor.
destruct a. simpl. econstructor.
unfold WF_state. simpl. apply Mix_par_trace.
intuition. inversion_clear H0. assumption.
apply IHmu. intuition. inversion_clear H0.
assumption. assert((((c, PMpar_trace q l r) :: d_par_trace mu l r)=
d_par_trace ((c, q) :: mu) l r)).
simpl. reflexivity.
unfold state.
rewrite H1. 
rewrite <-d_par_trace_trace.
inversion_clear H0. assumption.
intuition.
apply WF_Mixed_dstate.
assumption.



       
Qed.


Lemma big_sum_sum'':forall n m a1 a2 b1 b2 (f: nat -> Matrix a1 a2)
 (g:nat->Matrix b1 b2),
 big_sum f n .+ big_sum g m =
 big_sum (fun i=> if i <?n then f i else g (i-n)) (n+m).
 Proof. intros. rewrite big_sum_sum'.
        f_equal. 
        apply big_sum_eq_bounded.
        intros. 
        apply Lt_n_i in H.
        rewrite H. reflexivity.
        apply big_sum_eq_bounded.
        intros. 
        assert(n + x >= n). lia.
        apply ltb_ge in H0.
        rewrite H0. 
        rewrite add_comm.
        rewrite add_sub.
       reflexivity.
Qed.


Inductive q_combin'{s0 e0 s1 e1 s2 e2}: (qstate s0 e0) -> (qstate s1 e1)-> (qstate s2 e2)->Prop:=
|q_combin'': forall q0 q1, e0 = s1-> s0 = s2 -> e1 = e2 -> WF_qstate q0 ->
             WF_qstate q1->
            q_combin' q0 q1 (@kron (2^(e0-s0)) (2^(e0-s0)) (2^(e1-s1))  
            (2^(e1-s1)) q0 q1).

Inductive dstate_Separ{ s e: nat}: (list (cstate *qstate s e)) -> nat -> nat -> nat-> nat-> Prop :=
|dstate_Separ_nil: forall s0 e0 s1 e1,  dstate_Separ nil s0 e0 s1 e1
|dstate_Separ_cons: forall s0 e0 s1 e1 c q mu' (q0_i: nat->qstate s0 e0) (q1_i:nat-> qstate s1 e1) n, 
                    e0 = s1-> s0 = s -> e1 = e ->
  (forall i, (WF_qstate (q0_i i))\/  (q0_i i)= Zero) ->
(forall i, (WF_qstate (q1_i i)) \/ (q1_i i)= Zero)->
(q= big_sum (fun i=>@kron (2^(e0-s0)) (2^(e0-s0))  (2^(e1-s1)) (2^(e1-s1)) (q0_i i ) (q1_i i)) n)->
dstate_Separ mu' s0 e0 s1 e1->
dstate_Separ ((c,q)::mu') s0 e0 s1 e1.


Lemma dstate_Separ_map2{s e:nat}: forall (mu1 mu2: list (cstate *qstate s e))  s0 e0 s1 e1 ,
 s<=s1<=e->
 dstate_Separ mu1 s0 e0 s1 e1->
 dstate_Separ mu2 s0 e0 s1 e1->
 dstate_Separ (StateMap.Raw.map2 option_app mu1 mu2) s0 e0 s1 e1 .
 Proof. induction mu1; induction mu2; intros s0 e0 s1 e1 Hs ; intros.
        simpl. intuition.
        destruct a.
        rewrite map2_nil_l.
        assumption.
        rewrite map2_nil_r.
        assumption.
        destruct a. 
        destruct a0. 
        simpl in *.
        inversion H; subst.
        inversion  H0; subst.
        destruct (Cstate_as_OT.compare c c0).
        econstructor; try assumption.
        
        apply H7. apply H8.
        reflexivity. intuition.

        econstructor; try assumption.
        
        assert(forall i : nat, WF_qstate ((fun i:nat =>
        if i<?n then q0_i i else q0_i0  (i-n)) i) \/ 
        ((fun i:nat =>
        if i<?n then q0_i i else q0_i0  (i-n)) i) = Zero).
        intros. bdestruct (i<?n). 
        apply H7. apply H9.
        apply H1. 
        assert(forall i : nat, WF_qstate ((fun i:nat =>
        if i<?n then q1_i i else q1_i0  (i-n)) i) \/
        ((fun i:nat =>
        if i<?n then q1_i i else q1_i0  (i-n)) i) = Zero).
        intros. bdestruct (i<?n). 
        apply H8. apply H10.
        apply H1. 
        assert(2^(e-s) =2 ^ (s1 - s) * 2 ^ (e- s1)).
        type_sovle'. destruct H1.
        rewrite big_sum_sum''.
        apply big_sum_eq_bounded.
        intros. 
        bdestruct (x<?n).
        reflexivity.
        reflexivity.

       apply IHmu1. intuition. intuition. intuition.

      econstructor; try assumption.
      apply H9. apply H10.
      reflexivity.
       apply IHmu2. intuition.
       apply H.
       intuition. 
Qed.


Lemma dstate_qstate_eq_Separ{s e:nat}:forall (mu1 mu2: list(cstate * qstate s e))
s0 e0 s1 e1,
s<=s1<=e->
dstate_qstate_eq mu1 mu2 ->
dstate_Separ mu1 s0 e0 s1 e1->
dstate_Separ mu2 s0 e0 s1 e1.
Proof. induction mu1; intros mu2 s0 e0 s1 e1 Hs; intros. destruct mu2. intuition.
       destruct H. 
       destruct mu2. destruct a. destruct H.
       destruct a. destruct p. 
       simpl in H. destruct H. subst.
       inversion H0; subst.
       econstructor; try reflexivity.
       apply H7. apply H8.
       apply IHmu1. assumption.
       assumption. intuition.
Qed.


Lemma  super_0{ m n:nat}:  forall (M: Matrix m n) , 
super M Zero = Zero.
Proof. unfold super. intros. 
rewrite Mmult_0_r. rewrite Mmult_0_l.
reflexivity.     
Qed.



Lemma QInit_fun_sum{s' e':nat}: forall n s e (q: nat-> qstate s' e'), 
s'<=s/\s<=e/\e<=e'->
QInit_fun s e (@big_sum (Matrix (2^(e'-s')) (2^(e'-s'))) _ q n) =
@big_sum  (Matrix (2^(e'-s')) (2^(e'-s'))) _ (fun i => QInit_fun s e (q i)) n .
Proof. induction n;  intros; unfold q_update; unfold super; unfold qstate.
simpl.  unfold QInit_fun. 
apply (@big_sum_0_bounded (Matrix (2 ^ (e' - s')) (2 ^ (e' - s')))).
intros.
assert(2^(e'-s')= (2^(s-s')) * (2^(e-s)) * (2^(e'-e))).
type_sovle'. destruct H1. unfold q_update.
rewrite super_0. reflexivity.  
simpl.  rewrite <-IHn.
rewrite <-QInit_fun_plus. f_equal.
assumption. assumption.
Qed.


Lemma QUnit_One_fun_sum{s' e':nat}: forall n s e U (q: nat-> qstate s' e'), 
s'<=s/\s<=e/\e<=e'->
QUnit_One_fun s e U (big_sum q n) =
big_sum (fun i => QUnit_One_fun s e U (q i)) n .
Proof. induction n;  intros.
simpl. unfold QUnit_One_fun. unfold q_update.
apply (@super_0 (2 ^ (e' - s')) (2 ^ (e' - s'))).
simpl. rewrite <-IHn.
symmetry.
apply QUnit_One_fun_plus. 
assumption. assumption.
Qed.  




Lemma QUnit_Ctrl_fun_sum{s' e':nat}: forall n s0 e0 s1 e1 U (q: nat-> qstate s' e'), 
s'<=s0/\ s0<=e0 /\ e0<=s1 /\ s1 <= e1 /\ e1 <=e'->
QUnit_Ctrl_fun s0 e0 s1 e1  U (big_sum q n) =
big_sum (fun i => QUnit_Ctrl_fun s0 e0 s1 e1  U (q i)) n .
Proof. induction n;  intros;
simpl. unfold QUnit_Ctrl_fun. unfold q_update.
apply (@super_0 (2 ^ (e' - s')) (2 ^ (e' - s'))).
rewrite <-IHn.
symmetry.
apply QUnit_Ctrl_fun_plus. 
assumption. assumption.
Qed.

Lemma QMeas_fun_sum{s' e':nat}: forall n s e j (q: nat-> qstate s' e'), 
s'<=s /\ s<=e /\ e <=e'->
QMeas_fun s e j (big_sum q n) =
big_sum (fun i => QMeas_fun s e j (q i)) n .
Proof. induction n;  intros.
simpl. unfold QMeas_fun . unfold q_update.
apply (@super_0 (2 ^ (e' - s')) (2 ^ (e' - s'))).
simpl. rewrite <-IHn.
symmetry.
apply QMeas_fun_plus. 
assumption. assumption.
Qed.


Lemma dstate_Separ_Qinit{s e:nat}: forall c (q:qstate s e) s0 e0 s1 e1 s' e',
dstate_Separ [(c, q)] s0 e0 s1 e1 ->
s=s0 /\s0<=s' /\ s'<=e'/\ e'<=e0 /\ e0=s1 /\ s1<=e1 /\
e1=e->
@dstate_Separ s e [(c, QInit_fun s' e' q)] s0 e0 s1 e1.
Proof.
intros.  inversion H; subst. clear H14. 
econstructor; try reflexivity.
assert(forall i : nat, @WF_qstate s s1 ((fun i=> QInit_fun s' e' (q0_i i)) i) \/
((fun i=> QInit_fun s' e' (q0_i i)) i)= Zero).
intros. pose (H7 i). destruct o. 
left. apply WF_qstate_init. lia.  apply H1.
right. rewrite H1. 
apply (@big_sum_0_bounded (Matrix (2 ^ (e - s)) (2 ^ (e- s)))).
intros.  
assert(2^(s1-s)= (2^(s'-s)) * (2^(e'-s')) * (2^(s1-e'))).
type_sovle'. destruct H3. unfold q_update.
rewrite super_0. reflexivity.  
apply H1. apply H8.
rewrite (@QInit_fun_sum s e).
subst. 
apply big_sum_eq_bounded. 
intros.
  apply (@QInit_fun_kron s s1 e).
  pose (H8 x). destruct o. apply WF_Mixed.
  apply H2. rewrite H2. auto_wf. 
intuition.
intuition. econstructor; try reflexivity. 
Qed.


Lemma dstate_Separ_QUnit_One{s e:nat}: forall c (q:qstate s e) U s0 e0 s1 e1 s' e',
dstate_Separ [(c, q)] s0 e0 s1 e1 ->
s=s0 /\s0<=s' /\ s'<=e'/\ e'<=e0 /\ e0=s1 /\ s1<=e1 /\
e1=e->
@WF_Unitary (2^(e'-s')) U->
@dstate_Separ s e [(c, QUnit_One_fun s' e' U q)] s0 e0 s1 e1.
Proof.
intros.  inversion H; subst. clear H15. 
econstructor; try reflexivity.
assert(forall i : nat, @WF_qstate s s1 ((fun i=>QUnit_One_fun s' e' U (q0_i i)) i)\/
((fun i=>QUnit_One_fun s' e' U (q0_i i)) i) = Zero).
intros.   pose (H8 i). destruct o. 
left.
 apply WF_qstate_QUnit_One. lia. assumption.   apply H2.
 right. rewrite H2. unfold QUnit_One_fun. unfold q_update.
  rewrite super_0. reflexivity.
apply H2. apply H9.
rewrite (@QUnit_One_fun_sum s e).
subst. 
apply big_sum_eq_bounded.
intros.   apply (@QUnit_One_fun_kron s s1 e).
apply H1. pose (H9 x). destruct o. apply WF_Mixed. apply H3.
rewrite H3. auto_wf. 
intuition. 
intuition.
econstructor; try reflexivity.
Qed.


Lemma dstate_Separ_QUnit_Ctrl{s e:nat}: forall c (q:qstate s e)  
s0 e0 s1 e1 s0' e0' s1' e1' (U: nat -> Square (2 ^ (e1' - s1'))),
dstate_Separ [(c, q)] s0 e0 s1 e1 ->
(forall j, WF_Unitary (U j))->
s=s0 /\s0<=s0' /\ s0'<=e0'/\ e0'<= s1' /\ s1'<=e1' /\e1'<=e0 /\ e0=s1 /\ s1<=e1 /\
e1=e->
@dstate_Separ s e [(c, QUnit_Ctrl_fun s0' e0' s1' e1' U q)] s0 e0 s1 e1.
Proof.
intros.  inversion H; subst. clear H15. 
econstructor; try reflexivity.
assert(forall i : nat, @WF_qstate s s1 ((fun i=>QUnit_Ctrl_fun s0' e0' s1' e1' U (q0_i i)) i)
\/ ((fun i=>QUnit_Ctrl_fun s0' e0' s1' e1' U (q0_i i)) i) = Zero).
intros. pose (H8 i). destruct o. 
left. apply WF_qstate_QUnit_Ctrl; try assumption. lia.
right. rewrite H2. unfold QUnit_Ctrl_fun. unfold q_update.
  rewrite super_0. reflexivity. 
apply H2. apply H9.
rewrite (@QUnit_Ctrl_fun_sum s e).
subst. 
apply big_sum_eq_bounded.
intros. apply (@QUnit_Ctrl_fun_kron s s1 e).
intros. apply H0. pose (H9 x). destruct o. 
 apply WF_Mixed. apply H3. rewrite H3. auto_wf. 
lia. lia.  
econstructor; try reflexivity.
Qed.


Lemma dstate_Separ_QMeas{s e:nat}: forall c (q:qstate s e)  
s0 e0 s1 e1 s' e' j,
QMeas_fun s' e' j q <> Zero->
dstate_Separ [(c, q)] s0 e0 s1 e1 ->
s=s0 /\s0<=s' /\ s'<=e' /\e'<=e0 /\ e0=s1 /\ s1<=e1 /\
e1=e->
(j<(2^(e'-s')))->
@dstate_Separ s e [(c, QMeas_fun s' e' j q)] s0 e0 s1 e1.
Proof.
intros. inversion H0; subst. clear H16.
rewrite (@QMeas_fun_sum  s e) in *.
econstructor; try reflexivity.
assert(forall i : nat, @WF_qstate s s1 ((fun i=>QMeas_fun s' e' j (q0_i i)) i)\/
((fun i=>QMeas_fun s' e' j (q0_i i)) i) = Zero).
intros. pose (H9 i). 
assert(QMeas_fun s' e' j (q0_i i) = Zero \/
QMeas_fun s' e' j (q0_i i) <> Zero).
apply Classical_Prop.classic. 
destruct H3. right. assumption. left.
apply WF_qstate_QMeas. intuition. intuition. lia.
assumption. assumption. destruct o. assumption.
rewrite H4 in H3. unfold QMeas_fun in H3.
unfold q_update in H3. rewrite super_0 in H3.
destruct H3. reflexivity.  
apply H3. apply H10.
apply big_sum_eq_bounded.
intros. 
apply (@QMeas_fun_kron s s1 e).
assumption. 
pose (H10 x). destruct o.  
apply WF_Mixed. 
apply H4. rewrite H4. auto_wf.

intuition. econstructor; reflexivity.
intuition. intuition.
Qed.


Lemma dstate_Separ_big_app{s e:nat}: forall (f: nat -> list(cstate *qstate s e)) n s0 e0 s1 e1 ,
 s<=s1<=e-> 
 (forall i, i< n -> dstate_Separ (f i) s0 e0 s1 e1)->
 dstate_Separ (big_app f n) s0 e0 s1 e1 .
 Proof. induction n;  intros s0 e0 s1 e1 Hs ; intros.
        simpl. econstructor; try reflexivity.
        simpl. apply dstate_Separ_map2.
        assumption. apply IHn.
        assumption. intros. apply H. lia.
        apply H. lia. 
Qed.

Lemma dstate_Separ_big_app'{s e:nat}: forall (f: nat -> (cstate *qstate s e)) n s0 e0 s1 e1 mu,
 s<=s1<=e-> 
 (forall i, i< n -> snd (f i) <> Zero-> dstate_Separ [(f i)] s0 e0 s1 e1)->
 (big_app' f n mu) ->
 dstate_Separ mu s0 e0 s1 e1 .
 Proof. induction n;  intros s0 e0 s1 e1 Hs ; intros;
        inversion_clear H1.  econstructor; try reflexivity.
        apply IHn; try assumption.  intros. apply H0. lia.
        assumption.
        apply dstate_Separ_map2; try assumption.
        apply IHn; try assumption.  intros. apply H0. lia.
        assumption.
        apply H0. lia. assumption. 
Qed.


Lemma WF_Mixed_Zero{s e:nat}:forall (q: Square (2^(e-s))),
WF_qstate q \/ q= Zero ->
WF_Matrix q .
Proof. intros. destruct H. destruct H. auto_wf. 
rewrite H. auto_wf.
Qed.
#[export] Hint Resolve WF_Mixed WF_Mixed_Zero : wf_db.

Lemma WF_QInit{s' e'}: forall s e (rho:qstate s' e'),
s'<=s/\s<=e/\ e<=e'-> 
@WF_Matrix (2^(e'-s'))  (2^(e'-s')) rho-> 
@WF_Matrix (2^(e'-s'))  (2^(e'-s')) (QInit_fun s e rho).
Proof. intros. unfold QInit_fun. unfold q_update.
apply (@WF_Msum (2^(e'-s')) (2^(e'-s'))). intros.
apply (WF_super (2^(e'-s')) (2^(e'-s'))).
apply WF_kron; type_sovle'. apply WF_kron; type_sovle'.
auto_wf. apply WF_mult. apply WF_vec. apply pow_gt_0.
 auto_wf. auto_wf. assumption.
Qed. 


Lemma WF_QUnit_One{s' e'}: forall s e (rho:qstate s' e') (U:Square (2^(e-s))),
s'<=s/\s<=e/\ e<=e'-> 
WF_Unitary U->
@WF_Matrix (2^(e'-s'))  (2^(e'-s')) rho-> 
@WF_Matrix (2^(e'-s')) ((2^(e'-s'))) (QUnit_One_fun s e U rho).
Proof. intros. unfold QUnit_One_fun. unfold q_update. destruct H0.
auto_wf.
Qed.


Lemma WF_QUnit_Ctrl{s' e'}: forall s0 e0 s1 e1  (rho:qstate s' e') (U:nat ->Square (2^(e1-s1))),
s'<=s0/\s0<=e0/\ e0<=s1/\ s1<=e1 /\ e1<= e'-> 
(forall j, WF_Unitary (U j))->
@WF_Matrix (2^(e'-s'))  (2^(e'-s')) rho-> 
@WF_Matrix (2^(e'-s'))  (2^(e'-s')) (QUnit_Ctrl_fun s0 e0 s1 e1 U rho).
Proof. 
intros. unfold QUnit_Ctrl_fun. unfold q_update.
apply WF_super. apply WF_Msum.
intros. pose (H0 i). destruct w. auto_wf. assumption.
Qed.

Lemma WF_QMeas{s' e'}: forall s e (rho:qstate s' e') j,
s'<=s/\s<=e/\ e<=e'-> 
QMeas_fun s e j rho <> Zero ->
(j<2^(e-s))->
@WF_Matrix (2^(e'-s'))  (2^(e'-s')) rho-> 
@WF_Matrix (2^(e'-s'))  (2^(e'-s')) (QMeas_fun s e j rho).
Proof. intros.
intros. unfold QMeas_fun. unfold q_update. auto_wf. 
Qed.
#[export] Hint Resolve WF_QInit WF_QUnit_One WF_QUnit_Ctrl WF_QMeas : wf_db.

Lemma PMpar_trace_QInit{ s e:nat}: forall c (q:qstate s e) s' e' s0 e0 s1 e1,
dstate_Separ [(c, q)] s0 e0 s1 e1->
s=s0 /\s0<=s' /\ s'<=e'/\ e'<=e0 /\ e0=s1 /\ s1<=e1 /\
e1=e->
@PMpar_trace s e (QInit_fun s' e' q) s1 e1=
PMpar_trace q s1 e1.
Proof. intros. simpl in H. inversion H; subst.
clear H.
rewrite  (@QInit_fun_sum s e ).
repeat rewrite (big_sum_par_trace).
apply big_sum_eq_bounded.
intros.  destruct H0.
 destruct H1.
 destruct H2.
destruct H3. destruct H4.
destruct H5.
subst. 
rewrite (@QInit_fun_kron s s1 e); auto_wf.

repeat rewrite PMpar_trace_R; try reflexivity; auto_wf.
rewrite (PMpar_trace_r _ ((QInit_fun s' e' (q0_i x))) (q1_i x)); try reflexivity; auto_wf.
rewrite (PMpar_trace_r _ (q0_i x) (q1_i x)); try reflexivity; auto_wf.
rewrite QInit_trace; auto_wf. reflexivity. 
intuition. 
 intuition. intuition. intuition.
 intuition.
Qed.


Lemma PMpar_trace_QUnit_one{ s e:nat}: forall c (q:qstate s e)  s' e' (U:Square (2^(e'-s'))) s0 e0 s1 e1,
dstate_Separ [(c, q)] s0 e0 s1 e1->
s=s0 /\s0<=s' /\ s'<=e'/\ e'<=e0 /\ e0=s1 /\ s1<=e1 /\
e1=e->
WF_Unitary U->
@PMpar_trace s e (QUnit_One_fun s' e' U q) s1 e1=
PMpar_trace q s1 e1.
Proof. intros. inversion H; subst. clear H.
rewrite  (@QUnit_One_fun_sum s e ).
repeat rewrite (big_sum_par_trace).
apply big_sum_eq_bounded.
intros.  destruct H0.
destruct H2. destruct H3.
destruct H4. destruct H5.
destruct H6. 
subst. 
rewrite (@QUnit_One_fun_kron s s1 e); auto_wf.
repeat rewrite PMpar_trace_R; try reflexivity; auto_wf.
rewrite (PMpar_trace_r _ ((QUnit_One_fun s' e' U (q0_i x))) (q1_i x)); try reflexivity; auto_wf.
rewrite (PMpar_trace_r _ (q0_i x) (q1_i x)); try reflexivity; auto_wf.
rewrite QUnit_One_trace; auto_wf. reflexivity.
intuition. intuition. apply H1.
 intuition. intuition. intuition.
 intuition.
Qed.


Lemma PMpar_trace_QUnit_Ctrl{ s e:nat}: forall c (q:qstate s e)  s0' e0' s1' e1' (U:nat -> Square (2^(e1'-s1'))) s0 e0 s1 e1,
dstate_Separ [(c, q)] s0 e0 s1 e1->
s=s0 /\s0<=s0' /\ s0'<=e0'/\ e0'<= s1' /\ s1'<=e1' /\e1'<=e0 /\ e0=s1 /\ s1<=e1 /\
e1=e ->
(forall j, WF_Unitary (U j))->
@PMpar_trace s e (QUnit_Ctrl_fun s0' e0' s1' e1' U q) s1 e1=
PMpar_trace q s1 e1.
Proof. intros. 
inversion H; subst. clear H.
rewrite  (@QUnit_Ctrl_fun_sum s e ).
repeat rewrite (big_sum_par_trace).
apply big_sum_eq_bounded.
intros.  destruct H0.
destruct H2. destruct H3.
destruct H4. destruct H5.
destruct H6. destruct H7.
destruct H10. 
subst.    
rewrite (@QUnit_Ctrl_fun_kron s s1 e); auto_wf.
repeat rewrite PMpar_trace_R; try reflexivity; auto_wf.
rewrite (PMpar_trace_r _ ((QUnit_Ctrl_fun s0' e0' s1' e1' U (q0_i x))) (q1_i x)); try reflexivity; auto_wf.
rewrite (PMpar_trace_r _ (q0_i x) (q1_i x)); try reflexivity; auto_wf.
rewrite QUnit_Ctrl_trace; auto_wf. reflexivity.
intuition. intuition. assumption.
apply H1. 
lia. lia. lia. lia.    
Qed.

Lemma r3{s e:nat}: forall c s0 e0 s1 e1
(mu mu':list (cstate *qstate s e)) F ,
s<=s1<=e-> 
ceval_single c mu mu'-> 
dstate_Separ mu s0 e0 s1 e1->
NSet.Equal (NSet.inter (fst (Free_state F)) (fst (MVar c))) (NSet.empty)  ->
NSet.Subset (snd (MVar c)) (Qsys_to_Set s0 e0) ->
dstate_Separ mu' s0 e0 s1 e1 .
Proof.
induction c. 
-- {intros s0 e0 s1 e1 mu mu' F Hs . intros. apply ceval_skip_1 in H. subst. intuition. }
-- admit.
-- induction mu; intros mu' F Hs ; intros.
  {inversion  H; subst. intuition.  }
   {destruct a0. inversion H; subst. clear H.
   apply dstate_Separ_map2. intuition. 
   apply dstate_qstate_eq_Separ with [(c,q)].
   intuition.
   simpl. intuition.
   inversion H0; subst.
   econstructor; try reflexivity. 
   assumption. assumption. econstructor; try reflexivity.
   apply IHmu with F. assumption. 
   assumption.
   inversion H0; subst. assumption.
   assumption. assumption. }
--admit.
  {intros s0 e0 s1 e1 mu mu' F Hs.  intros. inversion H; subst. intuition.
    apply IHc2 with mu1 F.
    assumption. assumption. 
    apply IHc1 with  ((sigma, rho) :: mu0) F.
    assumption.
    assumption. assumption. 
    simpl in H1. rewrite inter_union_dist in H1.
    rewrite union_empty in H1. intuition.
    simpl in H2. apply subset_union in H2.
    intuition.
    simpl in H1. rewrite inter_union_dist in H1.
    rewrite union_empty in H1. intuition.
    simpl in H2. apply subset_union in H2.
    intuition.
   }
--{ induction mu; intros mu' F Hs; intros. inversion_clear H. intuition.
    inversion H; subst.
    apply dstate_Separ_map2. assumption. 
    apply IHc1 with  [(sigma, rho)] F.
    assumption. 
    assumption. inversion H0; subst.
    econstructor; try reflexivity.
    assumption. assumption. econstructor; try reflexivity.
    simpl in H1. rewrite inter_union_dist in H1.
    rewrite union_empty in H1. intuition.
    simpl in H2. apply subset_union in H2.
    intuition.
    apply IHmu with F. assumption.
    assumption. 
    inversion H0; subst. intuition.
    assumption. assumption.
    apply dstate_Separ_map2. assumption. 
    apply IHc2 with [(sigma, rho)] F.
    assumption. assumption. 
    inversion H0; subst. 
    econstructor; try reflexivity.
    assumption. assumption. econstructor; try reflexivity.
    simpl in H1. rewrite inter_union_dist in H1.
    rewrite union_empty in H1. intuition.
    simpl in H2. apply subset_union in H2.
    intuition.
    apply IHmu with F. 
    assumption. assumption.
    inversion H0; subst. intuition.
    assumption. assumption. }
-- admit. 

-- induction mu; intros mu' F Hs ; intros.
{inversion  H; subst. intuition.  }
 {destruct a. inversion H; subst. clear H.
 apply dstate_Separ_map2. assumption. 
 simpl in H2.
 apply dstate_Separ_Qinit.
 inversion H0; subst.
    econstructor; try reflexivity.
    assumption. assumption. econstructor.
    inversion_clear H0.
     apply subset_Qsys in H2.
     lia.  lia. 
 apply IHmu with F. assumption. assumption.
 inversion H0; subst. intuition.
 assumption. assumption. }
 -- induction mu; intros mu' F Hs ; intros.
{inversion  H; subst. intuition.  }
 {destruct a. inversion H; subst. clear H.
  apply inj_pair2_eq_dec in H5.
  apply inj_pair2_eq_dec in H5.
  destruct H5.
 apply dstate_Separ_map2. assumption. 
 apply dstate_Separ_QUnit_One.
 inversion H0; subst.
    econstructor; try reflexivity.
    assumption. assumption. econstructor.
    inversion_clear H0.
     apply subset_Qsys in H2.
     lia. lia.  apply H11.
 apply IHmu with F. assumption. 
 assumption.
 inversion H0; subst. intuition.
 assumption. assumption.
 apply Nat.eq_dec. apply Nat.eq_dec.
   } 

 -- induction mu; intros mu' F Hs ; intros.
 {inversion  H; subst. intuition.  }
  {destruct a. inversion H; subst. clear H.
   apply inj_pair2_eq_dec in H8.
   apply inj_pair2_eq_dec in H8.
   destruct H8.
  apply dstate_Separ_map2. assumption. 
  apply dstate_Separ_QUnit_Ctrl.
  inversion H0; subst.
  econstructor; try reflexivity.
  assumption. assumption. econstructor.
  assumption.
  inversion_clear H0. simpl in H2.
  apply subset_union in H2. destruct H2.
     apply subset_Qsys in H0.
     apply subset_Qsys in H2.
     lia. lia. lia.     
  apply IHmu with F. assumption.
  assumption.
  inversion H0; subst. intuition.
  assumption. assumption.
  apply Nat.eq_dec. apply Nat.eq_dec.
   }

  -- induction mu; intros mu' F Hs ; intros.
  {inversion  H; subst. intuition.  }
   {destruct a. inversion H; subst. clear H.
   apply dstate_Separ_map2. assumption.
   eapply (dstate_Separ_big_app'  (fun j : nat =>
   (c_update i j c, QMeas_fun s0 e0 j q)) (2 ^ (e0 - s0))) . lia.  
   intros.  apply dstate_Separ_QMeas. simpl in H3.
   assumption.  
   inversion H0; subst.
  econstructor; try reflexivity.
  assumption. assumption. econstructor.
  inversion_clear H0. simpl in H2.
     apply subset_Qsys in H2.
     lia.    
   lia.  assumption. assumption.
   apply IHmu with F. 
   assumption. assumption.
   inversion H0; subst.  intuition.
   assumption. assumption. }
Admitted.


Lemma big_app_seman{ s e:nat}: forall n (f:nat -> (cstate * qstate s e)) F mu, 
(forall j, j<n -> snd (f j) <> Zero-> ((WF_dstate_aux [f j]) /\ State_eval_dstate F [f j]))->
(big_app' f n mu) -> WF_dstate_aux mu ->
n>0->mu <>[]->
State_eval_dstate F mu .
Proof. induction n;   intros. lia.
       destruct n. inversion H0; subst. 
       inversion H7; subst. destruct H3.
       reflexivity. inversion H7; subst.
       rewrite  map2_nil_l. apply H. lia. assumption.  
       inversion H0; subst. 
       eapply (IHn f). intros. apply H. lia.
       assumption. assumption. assumption. lia. 
       assumption. 
       assert( l = [] \/ l <> []). 
       apply Classical_Prop.classic. destruct H4.
       rewrite H4. rewrite map2_nil_l. apply H. lia. assumption.  
       assert( WF_dstate_aux l).
       apply WWF_dstate_aux_to_WF_dstate_aux.
       split. eapply (WWF_dstate_big_app' _ _ (S n) f). intros.
       assert( snd (f i) = Zero \/ snd (f i) <> Zero).
       apply Classical_Prop.classic. destruct H8.
       right. assumption. left. 
        pose (H i). destruct a.  lia. assumption. 
       inversion_clear H9. unfold WWF_state.
       split.  apply Mixed_State_aux_to_Mix_State. apply H11.
       apply H11.  apply H7. apply Rle_trans with 
       (d_trace_aux  (StateMap.Raw.map2 option_app l [f (S n)])).
       rewrite d_trace_app_aux. rewrite <-Rplus_0_r at 1.
       apply Rplus_le_compat_l.
       apply WF_dstate_in01_aux. apply H. lia.
       assumption.    
       eapply (WWF_dstate_big_app' _ _ (S n) f). intros.
       assert( snd (f i) = Zero \/ snd (f i) <> Zero).
       apply Classical_Prop.classic. destruct H8.
       right. assumption. left. 
        pose (H i). destruct a.  lia. assumption. 
       inversion_clear H9. unfold WWF_state.
       split.  apply Mixed_State_aux_to_Mix_State. apply H11.
       apply H11.  apply H7.
      apply WWF_dstate_aux_to_WF_dstate_aux.
      apply H. lia. assumption.
      apply WF_dstate_in01_aux. assumption. 
       apply d_seman_app_aux. assumption.
       apply H. lia. assumption. 
       eapply (IHn f); try assumption; try lia.  intros.
        apply H. lia. assumption.  
        apply H. lia. assumption. 
Qed.

Lemma WF_qstate_plus{s e:nat}: forall (q1 q2: qstate s e),
@Mixed_State_aux (2^(e-s))q1 \/ q1=Zero ->
@Mixed_State_aux (2^(e-s)) q2 \/ q2= Zero->
(@Mplus (2^(e-s)) (2^(e-s)) q1  q2 <> Zero)->
@Mixed_State_aux (2^(e-s)) (q1.+ q2).
Proof. intros. destruct H. destruct H0. 
       apply Mix_S_aux; assumption.
       rewrite H0. rewrite Mplus_0_r.
       assumption. destruct H0.
       rewrite H. rewrite Mplus_0_l.
       assumption. rewrite H in *. rewrite H0 in *.
       rewrite Mplus_0_l in H1. destruct H1.
       reflexivity.
  
Qed.


Lemma WF_qstate_big_sum{s e}:forall (f:nat -> qstate s e) i n,
(forall i, i<n ->@Mixed_State_aux  (2^(e-s)) (f i) \/ (f i)= Zero)->
(exists j, and (j<i) ( (f j) <> Zero))->
WF_qstate (@big_sum (Matrix (2^(e-s)) (2^(e-s))) _  f n)->
i<=n /\ i>0
->WF_qstate (@big_sum (Matrix (2^(e-s)) (2^(e-s))) _  f i).
Proof. intros.   destruct H1. econstructor.  
       rewrite<- Mixed_State_aux_to_Mix_State in *.
       destruct H1. split. apply Mixed_State_aux_big_sum.
       lia. intros. apply H. lia. destruct H0.
       exists x.  intuition. apply Rle_trans with (Cmod (@trace (2^(e-s)) (big_sum f n))).
       admit. assumption. assumption.
Admitted.


Lemma  State_eval_plus'{s e:nat}: forall F c (q q0: qstate s e),
@Mixed_State_aux (2^(e-s))q ->
@Mixed_State_aux (2^(e-s)) q0 ->
State_eval F (c, q)->
State_eval F (c,q0) ->
@State_eval s e F (c, q .+ q0) .
Proof.   
       induction F; intros;  intros.
      -apply state_eq_Pure with  (c, q0). 
       reflexivity. intuition.   
      -induction qs. simpl in *.
        rewrite Rdiv_unfold in *.
        rewrite trace_plus_dist.
        rewrite <-PMtrace_scale.
        assert(q= (Cmod (@trace (2^(e-s)) q))%R .* (((R1 /  (Cmod (@trace  (2^(e-s)) q))))%R .* q) ).
        rewrite Mscale_assoc. 
         rewrite Rdiv_unfold.
         rewrite RtoC_mult. 
       rewrite <-Rmult_assoc . 
       rewrite Rmult_comm.  
         rewrite <-Rmult_assoc . 
         rewrite Rinv_l.   
         rewrite Rmult_1_r . 
         rewrite Mscale_1_l. reflexivity.
        unfold not. intros. apply mixed_state_Cmod_1_aux in H.
        rewrite H3 in H. lra. 
        assert(q0= (Cmod (@trace (2^(e-s)) q0))%R .* (((R1 /  (Cmod (@trace  (2^(e-s)) q0))))%R .* q0) ).
        rewrite Mscale_assoc. 
         rewrite Rdiv_unfold.
         rewrite RtoC_mult. 
       rewrite <-Rmult_assoc . 
       rewrite Rmult_comm.  
         rewrite <-Rmult_assoc . 
         rewrite Rinv_l.   
         rewrite Rmult_1_r . 
         rewrite Mscale_1_l. reflexivity.
        unfold not. intros. apply mixed_state_Cmod_1_aux in H0.
        rewrite H4 in H0. lra. 
         rewrite H3. rewrite H4.
          rewrite PMtrace_plus. 
          rewrite <-PMtrace_scale. 
          rewrite Rdiv_unfold in *.
          destruct H1. destruct H5. destruct H6. destruct H2.
          destruct H8. destruct H9.
          split. intuition. split. intuition.
          split. intuition. split. intuition.
           destruct H7.
          rewrite H11.
          rewrite <-PMtrace_scale. 
          rewrite Rdiv_unfold. destruct H10. rewrite H12.
        rewrite <-Mscale_plus_distr_l.
        rewrite Mscale_assoc. 
        rewrite<-H4. rewrite <-H3.
        rewrite <-RtoC_plus.
       rewrite RtoC_mult.
         rewrite Rmult_assoc.
         rewrite <-trace_plus_dist.
         rewrite mixed_state_Cmod_plus_aux.
         rewrite Rinv_l. rewrite Rmult_1_l.
         rewrite Mscale_1_l. reflexivity.
         assert((Cmod (@trace (2^(e-s)) q) + Cmod (@trace  (2^(e-s)) q0) )%R<> 0%R).
         apply tech_Rplus. assert(Cmod(@trace (2^(e-s)) q)%R>0%R)%R.
         apply mixed_state_Cmod_1_aux. apply H.
         intuition.  apply mixed_state_Cmod_1_aux. apply H0.
         assumption.
         apply H. apply H0. 
       
        simpl in *. split. intuition.
        destruct H2. destruct H3. 
        destruct H1. destruct H5. 
        apply IHqs1 in H5. apply IHqs2 in H6.
        split. assumption. assumption. assumption.
        assumption.  
      -simpl in *. split. intuition.  split. intuition. intuition. 
      - simpl in *.  split. intuition. intuition. 
Qed.


Lemma State_eval_sum{ s e:nat}: forall n c (f:nat -> qstate s e) F , 
(forall j, j<n -> ((@Mixed_State_aux (2^(e-s))  (f j) ) /\ State_eval F (c, (f j))) \/ (f j)= Zero)->
(exists j, and (j<n) (f j <> Zero)) ->
State_eval F (c, @big_sum  (Matrix (2^(e-s)) (2^(e-s))) (M_is_monoid (2^(e-s)) (2^(e-s))) f n)  .
Proof.
     induction n;   intros. simpl in *. destruct H0. destruct H0.  lia.
      simpl in *. destruct H0. 
      destruct(eq_dec x n). rewrite e0 in *.  
      assert( @big_sum  (Matrix (2^(e-s)) (2^(e-s))) (M_is_monoid (2^(e-s)) (2^(e-s))) f ( n)= Zero
      \/  @big_sum  (Matrix (2^(e-s)) (2^(e-s))) (M_is_monoid (2^(e-s)) (2^(e-s))) f (n) <> Zero).
     apply Classical_Prop.classic. destruct H1.
     rewrite H1 in *. rewrite Mplus_0_l in *.
     pose (H (n)). destruct o. lia. apply H2.

     rewrite H2 in *.  destruct H0. destruct H3.
     reflexivity. 
     assert(Mixed_State_aux (@big_sum  (Matrix (2^(e-s)) (2^(e-s))) _ f (n))).
     apply Mixed_State_aux_big_sum. intro. rewrite H2 in *.
     simpl in *. destruct H1. reflexivity.
     intros. pose (H (i)). destruct o. lia.
     left. intuition. right. assumption.  
     apply (@big_sum_not_0 (2^(e-s))). assumption.
     
     pose (H (n)). destruct o. lia. 
     apply State_eval_plus'; try auto. intuition.
     apply IHn. intros. apply H. lia.
     apply (@big_sum_not_0 (2^(e-s))). assumption.
     intuition. destruct H0. rewrite H3 in *.
     destruct H4. reflexivity.

     pose (H (n)). destruct o. lia. 
     assert( @big_sum  (Matrix (2^(e-s)) (2^(e-s))) (M_is_monoid (2^(e-s)) (2^(e-s))) f ( n)= Zero
     \/  @big_sum  (Matrix (2^(e-s)) (2^(e-s))) (M_is_monoid (2^(e-s)) (2^(e-s))) f (n) <> Zero).
    apply Classical_Prop.classic. destruct H2.
    rewrite H2 in *. rewrite Mplus_0_l in *.
    intuition. 

    assert(Mixed_State_aux (@big_sum  (Matrix (2^(e-s)) (2^(e-s))) _ f (n))).
    apply Mixed_State_aux_big_sum. intro. rewrite H3 in *.
    simpl in *. destruct H2. reflexivity.
    intros. pose (H (i)). destruct o. lia.
    left. intuition. right. assumption.  
    apply (@big_sum_not_0 (2^(e-s))). assumption.


    apply State_eval_plus'; try auto. intuition.
    apply IHn. intros. apply H. lia.
    apply (@big_sum_not_0 (2^(e-s))). assumption.
    intuition.  
    
    rewrite H1.
    rewrite Mplus_0_r. apply IHn.
    intros. apply H. lia. exists x.
    intuition.  
Qed. 

Lemma normalize_eq{n:nat}:forall (A B:Square n),
trace (B)= C1 ->
(exists (c:C), and (c <> C0) (A = c .* B))->
/(trace A) .* A =B.
Proof. intros. destruct H0. destruct H0. rewrite H1.
      rewrite trace_mult_dist. 
      rewrite Mscale_assoc.
      rewrite Cinv_mult_distr.
      rewrite Cmult_comm. rewrite Cmult_assoc.
      rewrite Cinv_r. rewrite H.
      rewrite Cinv_r.  rewrite Mscale_1_l.
      reflexivity. intro. injection H2. lra.
      assumption. assumption. 
      rewrite H. intro. injection H2.
      lra.
Qed.



Lemma QInit_Zero{ s' e':nat}: forall s e ,
 (@QInit_fun s' e' s e Zero) = @Zero s' e'.
Proof.  intros.  unfold QInit_fun. unfold q_update.
apply (@big_sum_0_bounded (Matrix (2^(e'-s')) (2^(e'-s')))).
intros. apply super_0. 
Qed. 


Lemma QUnit_One_Zero{s' e'}: forall s e (U:Square (2^(e'-s'))),
 (@QUnit_One_fun s' e' s e U Zero) = Zero.
Proof. intros. unfold QUnit_One_fun. unfold q_update.
apply (@super_0 (2^(e'-s'))). 
Qed.


Lemma QUnit_Ctrl_Zero{s' e'}: forall s0 e0 s1 e1  (U:nat ->Square (2^(e1-s1))),
(@QUnit_Ctrl_fun s' e' s0 e0 s1 e1 U Zero= Zero).
Proof. 
intros. unfold QUnit_Ctrl_fun. unfold q_update.
apply (@super_0 (2^(e'-s'))).
Qed.

Lemma QMeas_Zero{s' e'}: forall s e  j,
@QMeas_fun s' e' s e j Zero = Zero.
Proof. intros. unfold QMeas_fun. unfold q_update.
apply (@super_0 (2^(e'-s'))).
Qed.

Lemma Par_trace_Zero{s' e'}: forall l r,
@PMpar_trace s' e' Zero l r = Zero.
Proof. unfold PMpar_trace.  intros.
unfold PMRpar_trace. 
apply (@big_sum_0_bounded (Matrix (2^(e'-s')) (2^(e'-s')))).
intros. 
unfold PMLpar_trace.
rewrite  (@big_sum_0_bounded (Matrix (2^(e'-s')) (2^(e'-s')))).
Msimpl. reflexivity.
intros. Msimpl. reflexivity.
Qed.


Lemma QExp_eval_sub: forall (qs: QExp) s e c (q1 q2 q': qstate s e) ,
@Mixed_State (2^(e-s)) q1 ->
@Mixed_State (2^(e-s)) q2->
@Mixed_State (2^(e-s)) (q')->
@Mplus (2^(e-s)) (2^(e-s)) q1  q2= q'->
State_eval qs (c, q')->
State_eval qs (c, q1) /\
State_eval qs (c, q2).
Proof. induction qs; intros s0 e0 c q1 q2 q' Hq1 Hq2 Hq'; intros.
       destruct H. 
       simpl in H0. destruct H0.
       destruct H0. destruct H1. destruct H2.
       assert(trace (outer_product v v) = C1).
       destruct H.  unfold outer_product.
       rewrite trace_mult'. rewrite H4.
       rewrite trace_I. reflexivity.
      rewrite Mscale_plus_distr_r in H3.
      rewrite PMtrace_plus in H3.
      apply (@Mixed_pure (2^(e-s))
      (PMpar_trace ((R1 / Cmod (trace (q1 .+ q2)))%R .* q1) s e) 
      (PMpar_trace ((R1 / Cmod (trace (q1 .+ q2)))%R .* q2) s e) ) in H3.
      destruct H3. destruct H3.
      destruct H3. 
      repeat rewrite <-PMtrace_scale in H5.
      rewrite Rdiv_unfold in H5.
      rewrite Rmult_1_l in H5. 
      destruct H5. 

       simpl. repeat rewrite Rdiv_unfold.
      repeat  rewrite Rmult_1_l. repeat rewrite <-PMtrace_scale.
       split. split. auto.
       split. auto. split. auto.
       assert( RtoC (Cmod (@trace (2^(e0-s0)) q1)) = @trace (2^(e0-s0)) q1).
       assert(@trace (2^(e0-s0)) (q1) = (fst (@trace (2^(e0-s0)) (q1 )), snd (@trace (2^(e0-s0)) (q1)))).
       destruct (@trace (2^(e0-s0)) (q1) ).
       reflexivity. rewrite H7. 
       rewrite mixed_state_trace_real.
       rewrite Cmod_snd_0. simpl. reflexivity.
       simpl. apply mixed_state_trace_gt0. assumption.
       simpl. reflexivity. assumption.
       rewrite RtoC_inv. split. intuition. 
       rewrite H7. rewrite <-(Ptrace_trace _ _ _ s e).
       apply (@normalize_eq (2^(e-s))).
       assumption. 
       exists (Cmod (@trace (2^(e0-s0)) (q1 .+ q2)) * x)%R.
       split. 
       apply RtoC_neq. apply Rmult_integral_contrapositive_currified.
       rewrite mixed_state_Cmod_plus; try assumption.
       apply Rgt_neq_0.
       apply Rplus_lt_0_compat; apply mixed_state_Cmod_1; assumption.
       lra. rewrite <-RtoC_mult. rewrite<- Mscale_assoc.
       unfold outer_product.
       rewrite <-H5. rewrite Mscale_assoc.
       rewrite RtoC_mult. rewrite Rinv_r.
       rewrite Mscale_1_l. reflexivity.
       assert(Cmod (@trace (2^(e0-s0)) (q1 .+ q2)) >0)%R.
       apply mixed_state_Cmod_1. assumption. lra.
       lia. apply WF_Mixed. assumption.
       assert(Cmod (@trace (2^(e0-s0)) (q1 )) >0)%R.
       apply mixed_state_Cmod_1. assumption.
       lra. 
       
       split.  auto.
       split. auto. split. auto.
       assert( RtoC (Cmod (@trace (2^(e0-s0)) q2)) = @trace (2^(e0-s0)) q2).
       assert(@trace (2^(e0-s0)) (q2) = (fst (@trace (2^(e0-s0)) (q2)), snd (@trace (2^(e0-s0)) (q2)))).
       destruct (@trace (2^(e0-s0)) (q2) ).
       reflexivity. rewrite H7. 
       rewrite mixed_state_trace_real.
       rewrite Cmod_snd_0. simpl. reflexivity. 
       simpl. apply mixed_state_trace_gt0.
       assumption.
       simpl. reflexivity. assumption.
       rewrite RtoC_inv. split. intuition.
       rewrite H7. rewrite <-(Ptrace_trace _ _ _ s e).
       apply (@normalize_eq (2^(e-s))).
       assumption. 
       exists (Cmod (@trace (2^(e0-s0)) (q1 .+ q2)) * x0)%R.
       split. apply RtoC_neq. apply Rmult_integral_contrapositive_currified.
       rewrite mixed_state_Cmod_plus; try assumption.
       apply Rgt_neq_0.
       apply Rplus_lt_0_compat; apply mixed_state_Cmod_1; assumption.
       lra. rewrite <-RtoC_mult. rewrite<- Mscale_assoc.
       unfold outer_product.
       rewrite <-H6. rewrite Mscale_assoc.
       rewrite RtoC_mult. rewrite Rinv_r.
       rewrite Mscale_1_l. reflexivity.
       assert(Cmod (@trace (2^(e0-s0)) (q1 .+ q2)) >0)%R.
       apply mixed_state_Cmod_1. assumption. lra.
       lia. apply WF_Mixed. assumption.
       assert(Cmod (@trace (2^(e0-s0)) (q2)) >0)%R.
       apply mixed_state_Cmod_1. assumption. lra.
       apply Mix_par_trace. lia.
       split. apply Mixed_State_aux_to_01'.
       apply Mixed_State_aux_to_Mix_State. assumption.
       rewrite Rdiv_unfold. rewrite Rmult_1_l.
       apply Rinv_0_lt_compat. apply mixed_state_Cmod_1.
       assumption. 
       rewrite trace_mult_dist. rewrite Cmod_mult.
       rewrite Rdiv_unfold. rewrite Rmult_1_l.
       rewrite Cmod_R. rewrite Rabs_right.
       rewrite mixed_state_Cmod_plus; try assumption. 
       rewrite Rmult_comm. rewrite <-Rdiv_unfold.
       apply Rdiv_in01; apply mixed_state_Cmod_1; assumption.
       assert((/ Cmod (@trace (2^(e0-s0)) (q1 .+ q2)) > 0)%R).
       apply Rinv_0_lt_compat. apply mixed_state_Cmod_1.
       assumption. lra.   lia.   
       apply Mix_par_trace. lia.
       split. apply Mixed_State_aux_to_01'.
       apply Mixed_State_aux_to_Mix_State.
       assumption. 
       rewrite Rdiv_unfold. rewrite Rmult_1_l.
       apply Rinv_0_lt_compat. apply mixed_state_Cmod_1.
       assumption. 
       rewrite trace_mult_dist. rewrite Cmod_mult.
       rewrite Rdiv_unfold. rewrite Rmult_1_l.
       rewrite Cmod_R. rewrite Rabs_right.
       rewrite mixed_state_Cmod_plus; try assumption. 
       rewrite Rmult_comm. rewrite <-Rdiv_unfold.
       rewrite Rplus_comm.
       apply Rdiv_in01; apply mixed_state_Cmod_1; assumption.
       assert((/ Cmod (@trace (2^(e0-s0)) (q1 .+ q2)) > 0)%R).
       apply Rinv_0_lt_compat. apply mixed_state_Cmod_1.
       assumption. lra. 
       lia. 
       rewrite <-PMtrace_plus.
       rewrite <-Mscale_plus_distr_r.
       rewrite Rdiv_unfold. rewrite Rmult_1_l.
       rewrite <-PMtrace_scale. 
       rewrite <-(Ptrace_trace _ _ _ s e).
       apply Mixed_State_aux_to01.
       apply Mixed_State_aux_to_Mix_State.
       apply Mix_par_trace. lia.
       split. assumption. lia.  
       lia. apply WF_Mixed. assumption.
       assumption. 
      destruct H.
      simpl in H0.
      destruct H0. destruct H0.
      apply (IHqs1 _ _ _  q1 q2) in H0 .
      apply (IHqs2 _ _ _  q1 q2) in H1 .
      
      simpl. split. 
      intuition. intuition. assumption.
      assumption. assumption. reflexivity.
      assumption. assumption. assumption.
      reflexivity. 
Qed.



Lemma QExp_eval_sub': forall F s e c (q1 q2 q': qstate s e) ,
@Mixed_State (2^(e-s)) q1 ->
@Mixed_State (2^(e-s)) q2->
@Mixed_State (2^(e-s)) (q')->
@Mplus (2^(e-s)) (2^(e-s)) q1  q2= q'->
State_eval F (c, q')->
State_eval F (c, q1) /\
State_eval F (c, q2).
Proof. induction F; intros s0 e0 c q1 q2 q' Hq1 Hq2 Hq'; intros.
       split;
       apply state_eq_Pure with (c,q');
       try reflexivity; try assumption. 
        
       apply QExp_eval_sub with q'.
       assumption.
       assumption. assumption. assumption.
       assumption. 
      
      simpl in H0.
      destruct H0. destruct H1.
      apply (IHF1 _ _ _  q1 q2) in H1 .
      apply (IHF2 _ _ _  q1 q2) in H2 .
      
      simpl. split. 
      intuition. intuition. assumption. assumption.
      assumption. assumption. assumption.
      assumption. assumption. assumption. 

      simpl in H0.
      destruct H0. 
      apply (IHF1 _ _ _  q1 q2) in H0 .
      apply (IHF2 _ _ _  q1 q2) in H1 .
      
      simpl. split. 
      intuition. intuition. assumption. assumption.
      assumption. assumption. assumption.
      assumption. assumption. assumption.
Qed.


Lemma State_eval_sub_sum{ s e:nat}: forall n c (f:nat -> qstate s e) F , 
(forall i, i<n -> WF_qstate (f i) \/ (f i) = Zero)->
(WF_qstate (@big_sum  (Matrix (2^(e-s)) (2^(e-s))) (M_is_monoid (2^(e-s)) (2^(e-s)))  f n)) ->
State_eval F (c, @big_sum  (Matrix (2^(e-s)) (2^(e-s))) (M_is_monoid (2^(e-s)) (2^(e-s))) f n)->
(forall j, j<n-> WF_qstate (f j) -> State_eval F (c, (f j))).
Proof. induction n; intros. simpl in *. lia.
       simpl in H1. 
       assert(j =  n\/ j<  n).  lia. destruct H4.
       rewrite H4 in *.
       assert( @big_sum  (Matrix (2^(e-s)) (2^(e-s))) (M_is_monoid (2^(e-s)) (2^(e-s))) f (n)= Zero
       \/  @big_sum  (Matrix (2^(e-s)) (2^(e-s))) (M_is_monoid (2^(e-s)) (2^(e-s))) f (n) <> Zero).
      apply Classical_Prop.classic. destruct H5. rewrite H5 in *.
      rewrite Mplus_0_l in *. assumption.

      apply (QExp_eval_sub' F _ _ _ 
      (big_sum f (n)) (f ( n))) in H1.
      intuition. eapply WF_qstate_big_sum with (S n).
      intros. pose (H i). destruct o. lia.
      left. apply Mixed_State_aux_to_Mix_State.
      apply H7. right. assumption.
       apply (@big_sum_not_0 (2^(e-s))). assumption.
       apply H0. split. lia. assert( n<>0).
       intro. rewrite H6 in *. simpl in *. destruct H5.
       reflexivity. lia.     
      apply H3. apply H0.
      reflexivity. 
      apply IHn. intros. apply H. lia.

      eapply WF_qstate_big_sum with (S n).
      intros. pose (H i). destruct o. lia.
      left. apply Mixed_State_aux_to_Mix_State.
      apply H6. right. assumption. exists j.
      split. lia. apply (@Mixed_not_Zero (2^(e-s))).
      apply H3. apply H0. lia.    

      assert(f n = Zero \/ (f n) <> Zero). 
      apply Classical_Prop.classic. destruct H5.
      rewrite H5 in *. rewrite Mplus_0_r in *.
      assumption. 
      apply (QExp_eval_sub' F _ _ _ 
       (big_sum f (n)) (f (n))) in H1. 
       intuition.

       eapply WF_qstate_big_sum with (S n).
       intros. pose (H i). destruct o. lia.
       left. apply Mixed_State_aux_to_Mix_State.
       apply H7. right. assumption. exists j.
       split. lia. apply (@Mixed_not_Zero (2^(e-s))).
       apply H3. apply H0. lia.
       
       pose (H n). destruct o. lia. apply H6.
       rewrite H6 in H5. destruct H5. reflexivity.  
       
        apply H0.
       reflexivity. lia. assumption.   
Qed.




Lemma r10{ s e:nat}: forall c (q: qstate s e) s0 e0 s1 e1 s2 e2 i j F,
s1 <= s0 /\ s0 <= e0 /\ e0 <= e1 /\ s2 <= e2 ->
j < (2^(e0-s0))->
QMeas_fun s0 e0 j (q) <> Zero ->
WF_qstate q->
dstate_Separ [(c, q)] s1 e1 s2 e2 ->
NSet.Subset (Qsys_to_Set s0 e0) (Qsys_to_Set s1 e1)->
NSet.Equal
(NSet.inter (fst (Free_state F))
(fst (MVar <{ i :=M [[s0 e0]] }>))) NSet.empty ->
State_eval F (c, PMpar_trace q s2 e2)->
State_eval F (c_update i j c, PMpar_trace (QMeas_fun s0 e0 j q) s2 e2).
Proof. intros c q s0 e0 s1 e1 s2 e2 i j F Hj Hq Hw. intros.  
simpl in *. 
inversion H0; subst.
clear H0. clear H17.
rewrite big_sum_par_trace in *.
rewrite (@QMeas_fun_sum s e).
rewrite big_sum_par_trace.
destruct n. simpl in H.
destruct H. 
apply Mixed_not_Zero in H.
destruct H. reflexivity.
apply State_eval_sum.
intros.
pose (H10 j0). pose(H11 j0).
assert(@QMeas_fun s e s0 e0 j ((@kron (2 ^ (s2 - s)) (2 ^ (s2 - s)) (2 ^ (e - s2)) (2 ^ (e - s2)) 
(q0_i j0)  (q1_i j0))) = Zero 
\/ @QMeas_fun s e s0 e0 j ((@kron (2 ^ (s2 - s)) (2 ^ (s2 - s)) (2 ^ (e - s2)) (2 ^ (e - s2)) 
(q0_i j0)  (q1_i j0))) <> Zero).
apply Classical_Prop.classic.  destruct H4.
right. 
rewrite H4.
apply Par_trace_Zero. 
destruct o. destruct o0.  
left. split.
apply Mixed_State_aux_to_Mix_State.
apply Mix_par_trace. lia. 
apply WF_qstate_QMeas. intuition.
intuition. lia. assumption. assumption.
apply WF_qstate_kron; assumption.
assert(@State_eval s2 e F
(c, ((fun i : nat => 
@PMpar_trace s e
(@kron (2 ^ (s2 - s)) (2 ^ (s2 - s)) (2 ^ (e - s2)) (2 ^ (e - s2)) 
(q0_i i)  (q1_i i)) s2 e) j0))).
eapply (@State_eval_sub_sum s2 e (S n) c 
((fun i : nat => 
@PMpar_trace s e
(@kron (2 ^ (s2 - s)) (2 ^ (s2 - s)) (2 ^ (e - s2)) (2 ^ (e - s2)) 
(q0_i i)  (q1_i i)) s2 e))).
intros.
rewrite PMpar_trace_R .
rewrite (PMpar_trace_r _ (q0_i i0) (q1_i i0)).
pose (H10 i0). 
pose (H11 i0).
destruct o.  destruct o0.
left. econstructor.
 apply Mixed_State_scale_c.
 apply H9. apply mixed_state_trace_in01.
 apply H8. apply mixed_state_trace_real.
 apply H8. apply H9.
right. rewrite H9. rewrite Mscale_0_r.
reflexivity. rewrite H8.
right. rewrite Zero_trace. rewrite Mscale_0_l.
reflexivity.  auto_wf.  auto_wf. auto_wf. 
 reflexivity.
reflexivity. auto_wf.
rewrite <-(@big_sum_par_trace s e  _  _ s2 e).
apply Mix_par_trace. lia. assumption.
lia.  assumption. lia. 
apply Mix_par_trace. lia.
apply WF_qstate_kron; assumption.
simpl in *.
rewrite PMpar_trace_R in *; try reflexivity; auto_wf.
rewrite (PMpar_trace_r _ (q0_i j0 )  (q1_i j0)) in H7 ; try reflexivity; auto_wf.
rewrite QMeas_fun_kron; auto_wf.
rewrite (PMpar_trace_r _ (QMeas_fun s0 e0 j (q0_i j0))  (q1_i j0)) ;try reflexivity; auto_wf.
apply s_seman_scale_c. 
assert (@Mixed_State (2^(s2-s)) (QMeas_fun s0 e0 j (q0_i j0))).
apply WF_qstate_QMeas. intuition. intuition.
lia.  
rewrite (@QMeas_fun_kron s s2 e) in H4.
intro. rewrite H8 in H4. rewrite kron_0_l in H4.
destruct H4. reflexivity. assumption. auto_wf.
lia. lia. assumption.
split.   
apply mixed_state_trace_in01.
assumption.  
apply mixed_state_trace_real.
assumption.   
rewrite <-s_seman_scale_c in H7.
apply cstate_eq_F with c.
   simpl in H1. 
   unfold cstate_eq.
   intros. rewrite c_update_find_not.
   reflexivity.
   unfold not.
   intros. rewrite<-H9 in *.
   apply (In_inter_empty _ _ i) in H2.
   destruct H2. assumption. 
   apply NSet.add_1. reflexivity.
   assumption.
split.
apply mixed_state_trace_gt0. apply H5.
apply mixed_state_trace_real. apply H5.
unfold QMeas_fun. unfold q_update.
apply WF_super. auto_wf.  auto_wf.
unfold QMeas_fun. unfold q_update.
unfold super. auto_wf. lia. lia.  
unfold QMeas_fun. unfold q_update.
apply WF_super. auto_wf. auto_wf.
right. rewrite H6. rewrite kron_0_r.
rewrite QMeas_Zero. apply Par_trace_Zero.
right. rewrite H5. rewrite kron_0_l.
rewrite QMeas_Zero. apply Par_trace_Zero.
apply (@big_sum_not_0 (2^(e-s2))).
rewrite <-(@big_sum_par_trace s e  _  _ s2 e).
apply Mixed_not_Zero. 
apply (Mix_par_trace ).
lia.
rewrite <-(@QMeas_fun_sum s  e).
apply WF_qstate_QMeas.
intuition. intuition. lia.
assumption. assumption. 
assumption. 
lia. lia. lia. lia. lia.     
Qed.



Lemma r4{s e:nat}: forall c s0 e0 s1 e1
(mu mu':list (cstate *qstate s e)) F ,
s <= s1 /\ s1 <= e1 <= e->
WF_dstate_aux mu ->
ceval_single c mu mu'-> 
dstate_Separ mu s0 e0 s1 e1->
NSet.Equal (NSet.inter (fst (Free_state F)) (fst (MVar c))) (NSet.empty)  ->
(NSet.Subset (snd (MVar c)) (Qsys_to_Set s0 e0)) ->
State_eval_dstate F (d_par_trace mu s1 e1) ->
State_eval_dstate F (d_par_trace mu' s1 e1).
Proof. induction c. 
-- {intros s0 e0 s1 e1 mu mu' F Hs Hw. intros. apply ceval_skip_1 in H. subst. intuition. }
-- admit.
-- induction mu; intros mu' F Hs Hw; intros. 
  {inversion  H; subst. intuition.  }
   {destruct a0. inversion H; subst. clear H.
   rewrite d_par_trace_map2.
   inversion_clear H3.
   destruct mu. inversion_clear H10.
   simpl.
   econstructor. 
   apply cstate_eq_F with c.
   simpl in H1. 
   unfold cstate_eq.
   intros. rewrite c_update_find_not.
   reflexivity.
   unfold not.
   intros. rewrite<-H5 in *.
   apply (In_inter_empty _ _ i) in H1.
   destruct H1. assumption. 
   apply NSet.add_1. reflexivity.
    assumption. 
   econstructor.
   apply d_seman_app_aux.
   apply WF_d_par_trace. lia. 
    apply WF_state_dstate_aux.
   apply WF_state_eq with (c, q).
   reflexivity. inversion_clear Hw. assumption.
   apply WF_d_par_trace. lia. 
    apply WF_ceval with <{ i := a }> (p :: mu).
   inversion_clear Hw. assumption.
   assumption. 
   simpl. econstructor.
   apply cstate_eq_F with c.
   simpl in H1. 
   unfold cstate_eq.
   intros. rewrite c_update_find_not.
   reflexivity. intro. rewrite H5 in *.
   apply (In_inter_empty _ _ j) in H1.
   destruct H1. assumption. 
   apply NSet.add_1. reflexivity.
    assumption. econstructor.
apply IHmu. assumption. inversion_clear Hw. assumption.
assumption. 
inversion H0; subst.   intuition.
assumption. assumption.
destruct p. simpl. assumption. } 
-- admit.
--{ intros s0 e0 s1 e1 mu mu'  F Hs  Hw. intros. inversion H; subst. intuition.
    (* assert(State_eval_dstate F (d_par_trace mu1 s1 e1) ).
    apply IHc1 with s0 e0 ((sigma, rho) :: mu0).
    assumption. assumption.
    admit. admit.
    assumption. *)
   apply IHc2 with s0 e0 mu1. assumption.
   apply WF_ceval with c1 ((sigma, rho) :: mu0).
   assumption. assumption. 
   assumption. 
   apply r3 with c1 ((sigma, rho) :: mu0)  F.
   lia. 
   assumption. assumption.
   simpl in H1. 
   rewrite inter_union_dist in H1.
   rewrite union_empty in H1. intuition.
   simpl in H2. 
   apply subset_union in H2.
   intuition. simpl in H1.
   rewrite inter_union_dist in H1.
   rewrite union_empty in H1. intuition.
   simpl in H2. 
   apply subset_union in H2.
   intuition.
   apply IHc1 with s0 e0  ((sigma, rho) :: mu0).
   assumption.
   assumption.
   assumption.
   assumption.
   simpl in H1.
   rewrite inter_union_dist in H1.
   rewrite union_empty in H1. intuition.
   simpl in H2. 
   apply subset_union in H2.
   intuition.
   assumption.
   }
   {induction mu; intros mu' F Hs Hw; intros. inversion_clear H. intuition.
   destruct a. inversion H; subst; clear H;
   rewrite d_par_trace_map2;
   inversion_clear H3.
   destruct mu. inversion H12;subst.
   simpl. repeat rewrite map2_nil_r.
   apply IHc1 with s0 e0 [(c,q)].
   assumption.
   assumption. assumption. assumption.
   simpl in H1.
   rewrite inter_union_dist in H1.
   rewrite union_empty in H1. intuition.
   simpl in H2. 
   apply subset_union in H2.
   intuition.
   simpl. econstructor. assumption. 
   econstructor.  
   apply d_seman_app_aux.
   apply WF_d_par_trace.
   lia.  apply WF_ceval  with c1 [(c, q)].
   apply WF_state_dstate_aux.
   inversion_clear Hw. assumption.
   assumption.
   apply WF_d_par_trace. lia.  
   apply WF_ceval with <{ if b then c1 else c2 end }> (p :: mu).
   inversion_clear Hw.
   assumption. assumption.
   apply IHc1 with s0 e0 [(c,q)].
   assumption.
   apply WF_state_dstate_aux. 
   inversion_clear Hw. intuition. 
   assumption. inversion_clear H0; subst.
   econstructor; try reflexivity. assumption.
   assumption. econstructor.
   simpl in H1.
   rewrite inter_union_dist in H1.
   rewrite union_empty in H1. intuition.
   simpl in H2. 
   apply subset_union in H2.
   intuition.
   simpl. econstructor. assumption.
   econstructor.
   apply IHmu. assumption. inversion_clear Hw; intuition.
   assumption. inversion_clear H0. assumption.
   assumption.
   assumption.
   destruct p. 
   simpl. assumption.

   destruct mu. inversion H12;subst.
   simpl. repeat rewrite map2_nil_r.
   apply IHc2 with s0 e0 [(c,q)].
   assumption.
   assumption. assumption.
   assumption. 
   simpl in H1.
   rewrite inter_union_dist in H1.
   rewrite union_empty in H1. intuition.
   simpl in H2. 
   apply subset_union in H2.
   intuition.
   simpl. econstructor. assumption. 
   econstructor.  
   apply d_seman_app_aux. 
   apply WF_d_par_trace. lia. 
    apply WF_ceval  with c2 [(c, q)].
   apply WF_state_dstate_aux.
   inversion_clear Hw. assumption.
   assumption.
   apply WF_d_par_trace. lia. 
   apply WF_ceval with <{ if b then c1 else c2 end }> (p :: mu).
   inversion_clear Hw.
   assumption. assumption.
   apply IHc2 with s0 e0 [(c,q)].
   lia. 
   apply WF_state_dstate_aux. 
   inversion_clear Hw. intuition. 
   assumption.
   inversion_clear H0; subst.
   econstructor; try reflexivity. assumption.
   assumption. econstructor. 
   simpl in H1.
   rewrite inter_union_dist in H1.
   rewrite union_empty in H1. intuition.
   simpl in H2. 
   apply subset_union in H2.
   intuition.
   simpl. econstructor. assumption.
   econstructor.
   apply IHmu. assumption. inversion_clear Hw.
   assumption. assumption.
   inversion_clear H0. assumption. 
   assumption.
   assumption.
   destruct p. 
   simpl. assumption. }
{ admit. }
{induction mu; intros mu' F Hs Hw; intros.
{inversion  H; subst. intuition.  }
 {destruct a. inversion H; subst. clear H.
 rewrite d_par_trace_map2.
 inversion_clear H3.
 destruct mu. inversion_clear H11.
 simpl.
 econstructor. 
 rewrite (PMpar_trace_QInit c _ _ _ s1 e1).
 assumption. assumption. 
 simpl in H2. apply subset_Qsys in H2.
 inversion_clear H0. 
 lia. lia.  
 econstructor.
 apply d_seman_app_aux.
 apply WF_d_par_trace. lia.  
 apply WF_ceval  with <{ (s0 e0) :Q= 0 }>  [(c, q)]. 
 apply WF_state_dstate_aux.
 inversion_clear Hw. assumption.
 apply ceval_Qinit. assumption.
 apply WF_d_par_trace. lia. 
 apply WF_ceval with <{ (s0 e0) :Q= 0 }> (p :: mu).
 inversion_clear Hw.
 assumption. assumption.

 simpl. econstructor. 
 rewrite (PMpar_trace_QInit c _ _ _ s1 e1).
 assumption. inversion H0; subst. econstructor; try reflexivity.
 assumption. assumption. econstructor.
 inversion_clear H0. 
 simpl in H2. apply subset_Qsys in H2.
 lia. lia.  
 econstructor.
apply IHmu. assumption. inversion_clear Hw. assumption. 
assumption. 
inversion H0; subst.  intuition.
assumption. assumption.
destruct p. simpl. assumption. }  }

{induction mu; intros mu' F Hs Hw; intros.
{inversion  H; subst. intuition.  }
 {destruct a. inversion H; subst. clear H.
 apply inj_pair2_eq_dec in H6.
 apply inj_pair2_eq_dec in H6.
 destruct H6.
 rewrite d_par_trace_map2.
 inversion_clear H3.
 destruct mu. inversion_clear H13.
 simpl.
 econstructor. 
 rewrite (PMpar_trace_QUnit_one c _ _ _ _ s1 e1).
 assumption. assumption. 
 simpl in H2. apply subset_Qsys in H2.
 inversion_clear H0.
 lia. lia.    
 assumption. 
 econstructor.
 apply d_seman_app_aux.
 apply WF_d_par_trace. lia. 
  apply WF_ceval  with (QUnit_One s0 e0 U1)  [(c, q)]. 
 apply WF_state_dstate_aux.
 inversion_clear Hw. assumption.
 apply ceval_QUnit_One. assumption. assumption.
 apply WF_d_par_trace. lia. 
 apply WF_ceval with (QUnit_One s0 e0 U1) (p :: mu).
 inversion_clear Hw.
 assumption. assumption.
 simpl. econstructor. 
 rewrite (PMpar_trace_QUnit_one c _ _ _ _ s1 e1).
 assumption. inversion H0; subst. econstructor; try reflexivity.
 assumption. assumption. econstructor. 
 simpl in H2. apply subset_Qsys in H2.
 inversion_clear H0.
 lia. lia.
 assumption.
 econstructor. 
apply IHmu. assumption. inversion_clear Hw. assumption.
assumption. 
inversion H0; subst. intuition.
assumption. assumption.
destruct p. simpl. assumption.
apply Nat.eq_dec. apply Nat.eq_dec. }  }


{induction mu; intros mu' F Hs Hw; intros.
{inversion  H; subst. intuition.  }
 {destruct a. inversion H; subst. clear H.
 apply inj_pair2_eq_dec in H9.
 apply inj_pair2_eq_dec in H9.
 destruct H9.
 rewrite d_par_trace_map2.
 inversion_clear H3.
 destruct mu. inversion_clear H15.
 simpl.
 econstructor. 
 rewrite (PMpar_trace_QUnit_Ctrl c _ _ _ _ _ _  s2 e2).
 assumption. assumption.
 simpl in H2. apply subset_union in H2.
 destruct H2.  apply subset_Qsys in H2.
 apply subset_Qsys in H3.
 inversion_clear H0.  lia. 
  lia. lia.  
 assumption. econstructor.
 apply d_seman_app_aux.
 apply WF_d_par_trace. lia. 
  apply WF_ceval  with (QUnit_Ctrl s0 e0 s1 e1 U1)  [(c, q)]. 
 apply WF_state_dstate_aux.
 inversion_clear Hw. assumption.
 apply ceval_QUnit_Ctrl. assumption.
 assumption. 
 apply WF_d_par_trace. lia.  
 apply WF_ceval with (QUnit_Ctrl s0 e0 s1 e1 U1) (p :: mu).
 inversion_clear Hw.
 assumption. assumption. 
 simpl. econstructor.  
 rewrite (PMpar_trace_QUnit_Ctrl c _ _ _ _ _ _ s2 e2).
 assumption. inversion H0; subst. econstructor; try reflexivity.
 assumption. assumption. econstructor. 
 simpl in H2. apply subset_union in H2.
 destruct H2.  apply subset_Qsys in H2.
 apply subset_Qsys in H3.
 inversion_clear H0.  lia. 
  lia. lia.  
 assumption.
 econstructor.
apply IHmu. lia.  inversion_clear Hw; assumption.
assumption. 
inversion H0; subst. intuition.
assumption. assumption.
destruct p. simpl. assumption.
apply Nat.eq_dec. apply Nat.eq_dec. }  }

{induction mu; intros mu' F Hs Hw; intros.
{inversion  H; subst. intuition.  }
 {destruct a. inversion H; subst. clear H.
 rewrite d_par_trace_map2.
 inversion_clear H3.
 destruct mu. inversion_clear H12.
 simpl. rewrite map2_nil_r. pose H13.
 apply (d_par_trace_app' _ s2 e2) in b.
 destruct b. destruct H3. rewrite H5.
 simpl in H3. 
 eapply (big_app_seman ((2 ^ (e0 - s0))) (fun j : nat =>
 (c_update i j c,
  PMpar_trace (QMeas_fun s0 e0 j q) s2 e2))); try assumption. 
 intros. split.
 assert([(c_update i j c,
 PMpar_trace (QMeas_fun s0 e0 j q) s2 e2)] 
 = d_par_trace  [(c_update i j c, (QMeas_fun s0 e0 j q))] s2 e2).
 reflexivity. rewrite H8.
 apply WF_d_par_trace. lia.
 apply WF_state_dstate_aux.
 unfold WF_state. simpl. 
 apply WF_qstate_QMeas. intuition.
 intuition. lia. simpl in H7. intro.
 rewrite H9 in H7. rewrite Par_trace_Zero in H7.
 destruct H7. reflexivity. assumption.
 inversion_clear Hw. assumption.
 simpl. econstructor.
 apply r10 with s1 e1. 
 simpl in H2. apply subset_Qsys in H2.
 inversion_clear H0.
 lia. lia. assumption. simpl in H7.
 intro.
 rewrite H8 in H7. rewrite Par_trace_Zero in H7.
 destruct H7. reflexivity. 
  inversion_clear Hw. intuition.
   assumption. 
 simpl in *. assumption.
 assumption. assumption.
  econstructor. 
  rewrite <-H5. apply WF_d_par_trace. lia.
  eapply (WF_qstate_QMeas_app s0 e0 q c i (2 ^ (e0 - s0)) ). lia.  
 lia.    inversion_clear Hw. assumption.  assumption.
   apply pow_gt_0. admit.
 apply d_seman_app_aux.
 apply WF_d_par_trace. lia.  
 apply WF_ceval  with <{ i :=M [[s0 e0]] }>  [(c, q)]. 
 apply WF_state_dstate_aux.
 inversion_clear Hw. assumption.
 apply ceval_QMeas. assumption. assumption. 
 apply WF_d_par_trace. lia.  
 apply WF_ceval with <{ i :=M [[s0 e0]] }> (p :: mu).
 inversion_clear Hw.
 assumption. assumption.  pose H13.
 apply (d_par_trace_app' _ s2 e2) in b.
 destruct b. destruct H3. rewrite H5.
 eapply (big_app_seman ((2 ^ (e0 - s0))) (fun j : nat =>
 (c_update i j c,
  PMpar_trace (QMeas_fun s0 e0 j q) s2 e2))); try assumption. 
 intros. split.
 assert([(c_update i j c,
 PMpar_trace (QMeas_fun s0 e0 j q) s2 e2)] 
 = d_par_trace  [(c_update i j c, (QMeas_fun s0 e0 j q))] s2 e2).
 reflexivity. rewrite H8.
 apply WF_d_par_trace. lia.   
 apply WF_state_dstate_aux.
 unfold WF_state. simpl. 
 apply WF_qstate_QMeas. intuition.
 intuition. lia. simpl in H7. intro.
 rewrite H9 in H7. rewrite Par_trace_Zero in H7.
 destruct H7. reflexivity. assumption.
 inversion_clear Hw. assumption.
 simpl. econstructor.
 apply r10 with s1 e1. 
 simpl in H2. apply subset_Qsys in H2.
 inversion_clear H0.
 lia. lia. assumption. simpl in H7.
 intro.
 rewrite H8 in H7. rewrite Par_trace_Zero in H7.
 destruct H7. reflexivity.  
  inversion_clear Hw. intuition.
   inversion_clear H0; subst.
 econstructor; try reflexivity.
 assumption. assumption. econstructor. 
 simpl in *. assumption.
 assumption. assumption. 
econstructor. rewrite <-H5.
apply WF_d_par_trace. lia.    
eapply (WF_qstate_QMeas_app s0 e0 q c i (2 ^ (e0 - s0)) ). lia.  
lia.  inversion_clear Hw.
assumption. assumption. 
 apply pow_gt_0. admit.
apply IHmu. lia.  inversion_clear Hw. assumption.
assumption. 
inversion  H0; subst. intuition.
assumption. assumption.
destruct p. simpl. assumption.
 }  }
Admitted.


Lemma Odot_Sepear'''{ s x e:nat}: forall (q: qstate s e),
s<=x/\x<=e ->
@Mixed_State (2^(e-s)) q->
@Par_Pure_State (2^(e-x)) (PMpar_trace q x e)->
exists (q1:qstate s x) (q2: qstate x e), 
and (@WF_qstate  s x q1 /\ @WF_qstate x e q2) 
(q = @kron (2^(x-s)) (2^(x-s)) (2^(e-x))  (2^(e-x)) q1 q2).
Proof. Admitted.

Lemma seman_eq_two'''{s e:nat}: forall F r c (q:qstate s e),
Considered_Formula (F) /\
(r <= e /\ snd (Free_State F) <=r /\ fst (Free_State F) < snd (Free_State F))->
WF_qstate q->
State_eval F (c, q) -> 
exists 
(q1:qstate (fst (Free_State F)) (snd (Free_State F)))
(q2:qstate  (snd (Free_State F)) r), 
(q_combin' q1 q2 (@PMpar_trace s e q  (fst (Free_State F)) r)).
Proof. intros F r c q H Hw. intros. 
       assert(s<=fst (Free_State F)). 
       pose (State_eval_dom F c q H0). destruct o.
       subst. lia. apply H1.  
        remember ((snd (Free_State F))) as x.
        remember ((fst (Free_State F))) as s'.
        simpl.  
        remember ((PMpar_trace q s' r)).
       assert(exists (q1:qstate s' x) (q2: qstate x r), 
       and (WF_qstate q1 /\ WF_qstate q2)
       (q0 = @kron (2^(x-s')) (2^(x-s')) (2^(r-x))  (2^(r-x)) q1 q2)).
       apply Odot_Sepear''; try lia. 
       rewrite Heqq0. apply Mix_par_trace; try lia. 
       assumption. 
       rewrite Heqq0. rewrite PMpar_trace_assoc; try lia. 
       apply State_eval_pure  in H0. destruct H0.
       subst. lia. rewrite Heqs'. rewrite Heqx. apply H0.
      apply H. assumption. 
       destruct H2. destruct H2.
       destruct H2. rewrite H3. 
       exists x0. exists x1.
       econstructor; try reflexivity; try apply H2.
Qed.


Lemma seman_eq_two''{s e:nat}: forall F l  c (q:qstate s e),
Considered_Formula (F) /\
(s <= l /\ l <= fst (Free_State F) /\ fst (Free_State F) < snd (Free_State F))->
WF_qstate q->
State_eval F (c, q) -> 
exists 
(q1:qstate l (fst (Free_State F)))
(q2:qstate (fst (Free_State F)) (snd (Free_State F))), 
(q_combin' q1 q2 (@PMpar_trace s e q l (snd (Free_State F)))).
Proof. intros F l c q H Hw. intros. 
        assert(snd (Free_State F)<=e). 
        pose (State_eval_dom F c q H0). destruct o.
        subst. lia. apply H1.  
        remember ((fst (Free_State F))) as x.
        remember ((snd (Free_State F))) as e'.
        simpl.  
        remember ((PMpar_trace q l e')).
       assert(exists (q1:qstate l x) (q2: qstate x e'), 
       and (WF_qstate q1 /\ WF_qstate q2)
       (q0 = @kron (2^(x-l)) (2^(x-l)) (2^(e'-x))  (2^(e'-x)) q1 q2)).
       apply Odot_Sepear'''; try lia.  
       rewrite Heqq0. apply Mix_par_trace; try lia; try assumption.
       rewrite Heqq0. rewrite PMpar_trace_assoc; try lia. 
       apply State_eval_pure  in H0; try assumption; try apply H. 
       destruct H0. subst. lia. rewrite Heqx. rewrite Heqe'. apply H0.
       destruct H2. destruct H2.
       destruct H2. rewrite H3. 
       exists x0. exists x1.
       econstructor; try reflexivity; try apply H2.
Qed.


Lemma r1{s e:nat}: forall (mu : list (cstate *qstate s e)) F l,
Considered_Formula F /\
(s <= l /\ l <= fst (Free_State F) /\ fst (Free_State F) < snd (Free_State F))->
State_eval_dstate F mu->
WF_dstate_aux mu ->
(dstate_Separ (d_par_trace mu l (snd (Free_State F))) 
l (fst (Free_State (F))) (fst (Free_State (F))) (snd (Free_State (F)))).
Proof. induction mu; intros. 
      simpl. intuition.
      destruct mu. 
      destruct a. 
      simpl.

      assert(exists (q1:qstate l (fst (Free_State F)))
      (q2:qstate (fst (Free_State F)) (snd (Free_State F))), 
      (q_combin' q1 q2 (@PMpar_trace s e q l (snd (Free_State F))))).
      apply seman_eq_two'' with c.
      assumption. inversion_clear  H1. intuition.
      inversion_clear H0. assumption.

      destruct H2. destruct H2.
      inversion H2; subst.
      econstructor; try reflexivity.
      assert((forall i : nat, WF_qstate ((fun i:nat=> x) i) \/  ((fun i:nat=> x) i) = Zero)).
      intuition. apply H8.
      assert(forall i : nat, WF_qstate ((fun i=>x0) i) \/ ((fun i=>x0) i)= Zero).
      intuition.  apply H8.
      apply Logic.eq_trans with 
      (big_sum
      (fun i : nat =>
      (fun _ : nat => x) i ⊗ (fun _ : nat => x0) i) 
      1). simpl. 
      rewrite Mplus_0_l.
      reflexivity. intuition.

      econstructor.
      destruct a. destruct p.

      simpl.
      assert(exists (q1:qstate l (fst (Free_State F)))
      (q2:qstate (fst (Free_State F)) (snd (Free_State F))), 
      (q_combin' q1 q2 (@PMpar_trace s e q l (snd (Free_State F))))).
      apply seman_eq_two'' with c.
      assumption. inversion_clear  H1. intuition.
      inversion_clear H0. assumption. 
      destruct H2. destruct H2. 
      inversion H2; subst.

      econstructor; try assumption.

      assert((forall i : nat, WF_qstate ((fun i:nat=> x) i) \/  ((fun i:nat=> x) i) = Zero)).
      intuition. apply H8.
      assert(forall i : nat, WF_qstate ((fun i=>x0) i) \/ ((fun i=>x0) i)= Zero).
      intuition.  apply H8.
      apply Logic.eq_trans with 
      (big_sum
      (fun i : nat =>
      (fun _ : nat => x) i ⊗ (fun _ : nat => x0) i) 
      1). simpl. 
      rewrite Mplus_0_l.
      reflexivity. intuition.

      apply IHmu.
      assumption.
      inversion_clear H0.
      apply H9.
      inversion_clear H1. assumption.  
Qed.


Lemma r1'{s e:nat}: forall (mu : list (cstate *qstate s e)) F r,
Considered_Formula F /\
(r <= e /\ snd (Free_State F) <=r /\ fst (Free_State F) < snd (Free_State F))->
State_eval_dstate F mu->
WF_dstate_aux mu ->
(dstate_Separ (d_par_trace mu  (fst (Free_State F)) r) 
(fst (Free_State (F))) (snd (Free_State (F))) (snd (Free_State (F))) r).
Proof. induction mu; intros. 
      simpl. intuition.
      destruct mu. 
      destruct a. 
      simpl.

      assert(exists 
      (q1:qstate (fst (Free_State F)) (snd (Free_State F)))
      (q2:qstate  (snd (Free_State F)) r), 
      (q_combin' q1 q2 (@PMpar_trace s e q  (fst (Free_State F)) r))).
      apply seman_eq_two''' with c.
      assumption. inversion_clear  H1. intuition.
      inversion_clear H0. assumption.

      destruct H2. destruct H2.
      inversion H2; subst.
      econstructor; try reflexivity.
      assert((forall i : nat, WF_qstate ((fun i:nat=> x) i) \/  ((fun i:nat=> x) i) = Zero)).
      intuition. apply H8.
      assert(forall i : nat, WF_qstate ((fun i=>x0) i) \/ ((fun i=>x0) i)= Zero).
      intuition.  apply H8.
      apply Logic.eq_trans with 
      (big_sum
      (fun i : nat =>
      (fun _ : nat => x) i ⊗ (fun _ : nat => x0) i) 
      1). simpl. 
      rewrite Mplus_0_l.
      reflexivity. intuition.

      econstructor.
      destruct a. destruct p.

      simpl.
      assert(exists 
      (q1:qstate (fst (Free_State F)) (snd (Free_State F)))
      (q2:qstate  (snd (Free_State F)) r), 
      (q_combin' q1 q2 (@PMpar_trace s e q  (fst (Free_State F)) r))).
      apply seman_eq_two''' with c.
      assumption. inversion_clear  H1. intuition.
      inversion_clear H0. assumption. 
      destruct H2. destruct H2. 
      inversion H2; subst.

      econstructor; try assumption.

      assert((forall i : nat, WF_qstate ((fun i:nat=> x) i) \/  ((fun i:nat=> x) i) = Zero)).
      intuition. apply H8.
      assert(forall i : nat, WF_qstate ((fun i=>x0) i) \/ ((fun i=>x0) i)= Zero).
      intuition.  apply H8.
      apply Logic.eq_trans with 
      (big_sum
      (fun i : nat =>
      (fun _ : nat => x) i ⊗ (fun _ : nat => x0) i) 
      1). simpl. 
      rewrite Mplus_0_l.
      reflexivity. intuition.

      apply IHmu.
      assumption.
      inversion_clear H0.
      apply H9.
      inversion_clear H1. assumption.  
Qed.


Lemma r4'{s e:nat}: forall c s0 e0 s1 e1
(mu mu':list (cstate *qstate s e)) F ,
s <= s1 /\ s1 <= e1 <= e->
WF_dstate_aux mu ->
ceval_single c mu mu'-> 
dstate_Separ mu s0 e0 s1 e1->
NSet.Equal (NSet.inter (fst (Free_state F)) (fst (MVar c))) (NSet.empty)  ->
(NSet.Subset (snd (MVar c)) (Qsys_to_Set s1 e1)) ->
State_eval_dstate F (d_par_trace mu s0 e0) ->
State_eval_dstate F (d_par_trace mu' s0 e0).
Proof. Admitted.


Lemma subset_trans:
forall x y z,
 NSet.Subset x y ->
 NSet.Subset y z ->
 NSet.Subset x z.
Proof. intros. unfold NSet.Subset in *.
       intros. intuition.
       
Qed.

Lemma Qsys_to_Set_empty: forall s,
Qsys_to_Set_aux s s (NSet.empty)= NSet.empty .
Proof.  destruct s. simpl. reflexivity. simpl.
      assert(S s <? S s = false).
      rewrite ltb_ge. lia. 
      rewrite H. reflexivity.  
Qed.

Lemma Qsys_subset: 
forall r s e l  : nat,
s <=l /\ l <= r /\ r <= e
->NSet.Subset (Qsys_to_Set l r) (Qsys_to_Set s e).
Proof.
       unfold Qsys_to_Set. induction r; intros. 
      simpl. admit.
      simpl. 
      destruct H. destruct H0.
      assert(l=S r \/ l<> S r).
      apply Classical_Prop.classic.
      destruct H2.
      rewrite H2. 
       assert(S r <? S r =false).
       apply ltb_ge. lia. 
       rewrite H3.   admit.
       assert(l < S r).
       lia. apply Lt_n_i in H3. 
       rewrite H3.
       unfold NSet.Subset.
       intros.
       unfold NSet.Subset in IHr.
       assert(a= r \/ a<>r).
       apply Classical_Prop.classic.
       destruct H5. rewrite H5 in *.
       apply In_Qsys. lia.  
       lia. 
       assert(l = r \/ l<>r).  
       apply Classical_Prop.classic .
       destruct H6. rewrite H6 in *.
       rewrite Qsys_to_Set_empty in H4.
       apply NSet.add_3 in H4.
       admit. lia. 
       apply IHr with l.
       lia.
       apply NSet.add_3 in H4.
       assumption.
       lia.  
Admitted.


Lemma min_le_max: forall (s: NSet.t),
(option_nat (NSet.min_elt s)) <= option_nat (NSet.max_elt s).
Proof.  Admitted. 

Lemma In_min_max: forall (s: NSet.t),
NSet.Subset s 
(Qsys_to_Set (option_nat (NSet.min_elt s)) (option_nat (NSet.max_elt s))).
Proof.  intros. unfold NSet.Subset. intros. 
Admitted. 

Lemma rule_f: forall  F c s e (mu mu':list (cstate * qstate s e )) ,
(Considered_Formula F /\ fst (Free_State F) < snd (Free_State F))->
WF_dstate_aux mu ->
State_eval_dstate F mu->
ceval_single c mu mu'-> 
NSet.Equal (NSet.inter (fst (Free_state F)) (fst (MVar c))) (NSet.empty) ->
((option_nat (NSet.max_elt (snd (MVar c)))) <=  (fst (Free_State F))
\/((snd (Free_State F))) <=  ((option_nat (NSet.min_elt (snd (MVar c)))))) ->
State_eval_dstate F mu'.
Proof. 
    intros.
    destruct H4.  
    assert(s <= option_nat (NSet.min_elt (snd (MVar c))) /\
    option_nat (NSet.min_elt (snd (MVar c))) <=
    fst (Free_State F) /\
    fst (Free_State F) < snd (Free_State F) /\ snd (Free_State F) <= e).
    admit.
    rewrite (State_dstate_free_eval _ _ (fst (Free_State (F)))
    (snd (Free_State (F)))); try lia. 
    rewrite <-(d_par_trace_assoc   mu' 
    (option_nat (NSet.min_elt (snd (MVar c))))
    (snd (Free_State F))); try lia.   
    remember ((d_par_trace mu'
    (option_nat (NSet.min_elt (snd (MVar c))))
    (snd (Free_State F)))).
    remember ((d_par_trace mu
    (option_nat (NSet.min_elt (snd (MVar c))))
    (snd (Free_State F)))).
    apply r4 with c (option_nat (NSet.min_elt (snd (MVar c))))
    (fst (Free_State F)) l0; try assumption; try lia. 
    rewrite Heql0. apply WF_d_par_trace; try lia; try assumption. 
    rewrite Heql. rewrite Heql0. 
    apply Par_trace_ceval_swap; try lia; try assumption.
    apply subset_trans with ((Qsys_to_Set
    (option_nat (NSet.min_elt (snd (MVar c))))
       (option_nat (NSet.max_elt (snd (MVar c)))))).
    apply In_min_max. apply Qsys_subset.
    split. lia. split. apply min_le_max.
    apply le_trans with  (fst (Free_State F)).
    assumption. lia. 
    apply WF_Mixed_dstate. assumption.
    rewrite Heql0. apply r1; try assumption; try split; [apply H |try lia].
    apply subset_trans with ((Qsys_to_Set
    (option_nat (NSet.min_elt (snd (MVar c))))
       (option_nat (NSet.max_elt (snd (MVar c)))))).
    apply In_min_max. apply Qsys_subset.
    split. lia. split. apply min_le_max.
    assumption.
    rewrite Heql0. rewrite d_par_trace_assoc; try lia. 
    apply State_dstate_free_eval; try assumption; try lia. 
     apply WF_Mixed_dstate; assumption.
    apply WF_Mixed_dstate.
    apply WF_ceval with c mu. 
    assumption. assumption.

    assert(s <= fst (Free_State F) /\
    fst (Free_State F) <= fst (Free_State F) /\
    fst (Free_State F) <= snd (Free_State F) /\
    snd (Free_State F) <=
    option_nat (NSet.max_elt (snd (MVar c))) <= e).
    admit.
    rewrite (State_dstate_free_eval _ _ (fst (Free_State (F)))
    (snd (Free_State (F)))); try lia. 
    rewrite <-(d_par_trace_assoc   mu' 
    (fst (Free_State F)) (option_nat (NSet.max_elt (snd (MVar c))))); try lia.   
    remember ( (d_par_trace mu' (fst (Free_State F))
    (option_nat (NSet.max_elt (snd (MVar c)))))).
    remember ((d_par_trace mu
    (fst (Free_State F))
    (option_nat (NSet.max_elt (snd (MVar c)))))).
    apply r4' with c (snd (Free_State F))
    (option_nat (NSet.max_elt (snd (MVar c)))) l0; try assumption; try lia. 
    rewrite Heql0. apply WF_d_par_trace; try lia; try assumption. 
    rewrite Heql. rewrite Heql0. 
    apply Par_trace_ceval_swap; try lia; try assumption.
    apply subset_trans with ((Qsys_to_Set 
    (option_nat (NSet.min_elt (snd (MVar c))))
    (option_nat (NSet.max_elt (snd (MVar c)))))).
    apply In_min_max. apply  Qsys_subset .  split.
    apply le_trans with (snd (Free_State F)).
    lia. assumption. split. 
    apply min_le_max. lia.  
    apply WF_Mixed_dstate. assumption.
    rewrite Heql0. apply r1'; try assumption; try split; [apply H |try lia].
    apply subset_trans with ((Qsys_to_Set
    (option_nat (NSet.min_elt (snd (MVar c))))
       (option_nat (NSet.max_elt (snd (MVar c)))))).
    apply In_min_max. apply Qsys_subset.
    split. lia. split. apply min_le_max.
    lia. 
    rewrite Heql0. rewrite d_par_trace_assoc; try lia. 
    apply State_dstate_free_eval; try assumption; try lia. 
     apply WF_Mixed_dstate; assumption.
    apply WF_Mixed_dstate.
    apply WF_ceval with c mu. 
    assumption. assumption.
Admitted.


Lemma State_eval_odot:forall (s e : nat) (mu : list (cstate * qstate s e)) (F1 F2 : State_formula),
State_eval_dstate ((F1 ⊙ F2)) mu <->
State_eval_dstate F1 mu /\ State_eval_dstate F2 mu /\ 
NSet.Equal (NSet.inter (snd (Free_state F1))
         (snd (Free_state F2)))
     NSet.empty  .
Proof.
intros. split; intros; 
       induction mu; 
       simpl in H. destruct H.
       -destruct mu; destruct a; inversion_clear H; simpl;
        intuition.  
      -destruct H. destruct H. 
      -destruct a. destruct mu. simpl. econstructor. 
       destruct H. inversion_clear H. inversion_clear H0.
      split; inversion_clear H. intuition. intuition.  apply Forall_nil.
      simpl. econstructor.  destruct H. inversion_clear H.
      destruct H0.
      inversion_clear H. intuition.
      apply IHmu. destruct H. inversion_clear H. destruct H0.
      inversion_clear H. split. 
      intuition. intuition.  
Qed.


(* Definition Considered_Formula_Com (c:com) (F:State_formula):=
  option_nat (Nset) *)
(* Lemma Pure_eval_preserve'{s e:nat}:forall c (mu1 mu2: list (cstate * qstate s e)) F,
@WF_Matrix_dstate (2^(e-s)) (2^(e-s)) mu1 ->
ceval_single c mu1 mu2->
NSet.Equal (NSet.inter (fst (Free_state F)) (fst (MVar c))) NSet.empty  ->
dstate_eq_cstate mu1 mu2 ((fst (Free_state F))). 
Proof. induction c. intros.
  - apply ceval_skip_1 in H0. subst. admit.
  - admit.
  -induction mu1; intros.
   inversion_clear H0. econstructor.
   destruct a0. inversion_clear H0.
   
   simpl in *. inversion H0; subst. inversion H3; subst.
   injection H8. intros. subst. clear H8. clear H3.
   rewrite c_update_find_not; try reflexivity.
   intro. subst. destruct H1. apply NSet.add_1.
   reflexivity. 
  -admit.
   inversion_clear H0. cstate_eq_F *)






Lemma Pure_eval''{s e:nat}:forall  (F: State_formula) c0 c1 (q q0: qstate s e),
(fst (Free_State F)) = (snd (Free_State F))->
cstate_eq c0 c1 (fst (Free_state F))->
State_eval F (c0, q) -> 
State_eval F (c1, q0).
Proof. induction F;   intros.
        eapply cstate_eq_P. apply H0.
        apply state_eq_Pure with (c0,q).
        reflexivity. apply H1.
       apply QExp_eval_dom in H1.
       unfold Free_State in *.
       lia.



       apply cstate_eq_union in H0. destruct H0.
       simpl in *;
       split. intuition.
       destruct H1. destruct H3. 
    bdestruct (fst (Free_State F1) =? snd (Free_State F1)).
    split. apply IHF1 with c0 q; try assumption.
    apply IHF2 with c0 q; try assumption. 
    bdestruct (fst (Free_State F2) =? snd (Free_State F2)).
    split. apply IHF1 with c0 q; try assumption.
   apply IHF2 with c0 q; try assumption. 
   simpl in H. 
   apply min_max_eq in H. lia.
   apply State_eval_dom in H3. lia.  

  apply cstate_eq_union in H0. destruct H0.
  simpl in *.
  destruct H1. 
  bdestruct (fst (Free_State F1) =? snd (Free_State F1)).
  split. apply IHF1 with c0 q; try assumption.
 apply IHF2 with c0 q; try assumption. 

 bdestruct (fst (Free_State F2) =? snd (Free_State F2)).
 split. apply IHF1 with c0 q; try assumption.
 apply IHF2 with c0 q; try assumption.
 simpl in H. 
 apply min_max_eq in H. lia. 
   apply State_eval_dom in H1. lia.  
Qed.
 


Lemma Pure_eval_preserve{s e:nat}:forall  c (mu1 mu2: list (cstate* qstate s e)) (F: State_formula) ,
(fst (Free_State F)) = (snd (Free_State F))->
NSet.Equal (NSet.inter (fst (Free_state F)) (fst (MVar c))) NSet.empty  ->
WF_dstate_aux mu1 ->
ceval_single c mu1 mu2->
State_eval_dstate F mu1 ->
State_eval_dstate F mu2.
Proof. induction c. 
-- {intros F mu1 mu2  Hs Hm Hw. intros. apply ceval_skip_1 in H. subst. intuition. }
-- admit.
-- induction mu1; intros mu2 F Hs Hm Hw; intros. 
  {inversion  H; subst. intuition.  }
   {destruct a0. inversion H; subst. clear H.
   destruct mu1. inversion_clear H7.
   simpl.
   econstructor. 
   apply cstate_eq_F with c.
   simpl in Hm. 
   unfold cstate_eq.
   intros. rewrite c_update_find_not.
   reflexivity.
   unfold not.
   intros. rewrite<-H1 in *.
   apply (In_inter_empty _ _ i) in Hm.
   destruct Hm. assumption. 
   apply NSet.add_1. reflexivity. 
   inversion_clear H0.
    assumption. 
   econstructor.
   apply d_seman_app_aux. 
    apply WF_state_dstate_aux.
   apply WF_state_eq with (c, q).
   reflexivity. inversion_clear Hw. assumption.
    apply WF_ceval with <{ i := a }> (p :: mu1).
   inversion_clear Hw. assumption.
   assumption. 
   simpl. econstructor.
   apply cstate_eq_F with c.
   simpl in Hm. 
   unfold cstate_eq.
   intros. rewrite c_update_find_not.
   reflexivity. intro. rewrite H1 in *.
   apply (In_inter_empty _ _ j) in Hm.
   destruct Hm. assumption. 
   apply NSet.add_1. reflexivity.
  inversion_clear H0. assumption. econstructor.
apply IHmu1. assumption. assumption.
 inversion_clear Hw. assumption.
assumption. 
inversion H0; subst.   intuition. } 
-- admit.
--{ intros mu1 mu2  F Hs Hm  Hw. intros. inversion H; subst. intuition.
   apply IHc2 with mu0. assumption. 
   simpl in Hm. 
   rewrite inter_union_dist in Hm.
   rewrite union_empty in Hm. intuition.
   apply WF_ceval  with c1 (((sigma, rho) :: mu)); try assumption.
   assumption.
   apply IHc1 with ((sigma, rho) :: mu); try assumption.
   simpl in Hm. 
   rewrite inter_union_dist in Hm.
   rewrite union_empty in Hm. intuition.
   }
   {induction mu1; intros mu2 F Hs Hm Hw; intros. inversion_clear H. intuition.
   destruct a. inversion H; subst; clear H.
   destruct mu1. inversion H9;subst.
   simpl. repeat rewrite map2_nil_r.
   apply IHc1 with  [(c,q)]; try assumption.
   simpl in Hm.
   rewrite inter_union_dist in Hm.
   rewrite union_empty in Hm. intuition.
   apply d_seman_app_aux.
   apply WF_ceval  with c1 [(c, q)]; try assumption.
   apply WF_state_dstate_aux.
   inversion_clear Hw. assumption.
   apply WF_ceval with <{ if b then c1 else c2 end }> (p :: mu1); try assumption.
   inversion_clear Hw.
   assumption.
   apply IHc1 with [(c,q)]; try assumption.
   simpl in Hm.
   rewrite inter_union_dist in Hm.
   rewrite union_empty in Hm. intuition.
   apply WF_state_dstate_aux.
   inversion_clear Hw. assumption.
   inversion_clear H0. econstructor. assumption.
   econstructor. 
   apply IHmu1; try assumption. inversion_clear Hw; intuition.
   inversion_clear H0. assumption.
  
   destruct mu1. inversion H9;subst.
   simpl. repeat rewrite map2_nil_r.
   apply IHc2 with  [(c,q)]; try assumption.
   simpl in Hm.
   rewrite inter_union_dist in Hm.
   rewrite union_empty in Hm. intuition.
   apply d_seman_app_aux.
   apply WF_ceval  with c2 [(c, q)]; try assumption.
   apply WF_state_dstate_aux.
   inversion_clear Hw. assumption.
   apply WF_ceval with <{ if b then c1 else c2 end }> (p :: mu1); try assumption.
   inversion_clear Hw.
   assumption.
   apply IHc2 with [(c,q)]; try assumption.
   simpl in Hm.
   rewrite inter_union_dist in Hm.
   rewrite union_empty in Hm. intuition.
   apply WF_state_dstate_aux.
   inversion_clear Hw. assumption.
   inversion_clear H0. econstructor. assumption.
   econstructor. 
   apply IHmu1; try assumption. inversion_clear Hw; intuition.
   inversion_clear H0. assumption. }
{ admit. }
{  induction mu1; intros mu2 F Hs Hm Hw; intros.
{inversion  H; subst. intuition.  }
 {destruct a. inversion H; subst. clear H.
 destruct mu1. inversion_clear H8.
 simpl.
 econstructor. apply (@Pure_free_eval' s e) with q; try assumption.
 inversion_clear H0. assumption.  econstructor.
 apply d_seman_app_aux.
 apply WF_ceval  with <{ (s0 e0) :Q= 0 }>  [(c, q)]. 
 apply WF_state_dstate_aux.
 inversion_clear Hw. assumption.
 apply ceval_Qinit. assumption.
 apply WF_ceval with <{ (s0 e0) :Q= 0 }> (p :: mu1).
 inversion_clear Hw.
 assumption. assumption.
 simpl. econstructor. 
 apply (@Pure_free_eval' s e) with q; try assumption.
 inversion_clear H0. assumption.
 econstructor.
apply IHmu1; try  assumption. inversion_clear Hw. assumption. 
inversion H0; subst.  intuition. }  }

{  induction mu1; intros mu2 F Hs Hm Hw; intros.
{inversion  H; subst. intuition.  }
 {destruct a. inversion H; subst. clear H.
 apply inj_pair2_eq_dec in H3.
 apply inj_pair2_eq_dec in H3.
 destruct H3.
 destruct mu1. inversion_clear H10.
 simpl.
 econstructor. apply (@Pure_free_eval' s e) with q; try assumption.
 inversion_clear H0. assumption.  econstructor.
 apply d_seman_app_aux.
 apply WF_ceval  with (QUnit_One s0 e0 U1) [(c, q)]. 
 apply WF_state_dstate_aux.
 inversion_clear Hw. assumption.
 apply ceval_QUnit_One. assumption.
 assumption.
 apply WF_ceval with (QUnit_One s0 e0 U1) (p :: mu1).
 inversion_clear Hw.
 assumption. assumption.
 simpl. econstructor. 
 apply (@Pure_free_eval' s e) with q; try assumption.
 inversion_clear H0. assumption.
 econstructor.
apply IHmu1; try  assumption. inversion_clear Hw. assumption. 
inversion H0; subst.  
assumption.  apply Nat.eq_dec. apply Nat.eq_dec. }  }

{  induction mu1; intros mu2 F Hs Hm Hw; intros.
{inversion  H; subst. intuition.  }
 {destruct a. inversion H; subst. clear H.
 apply inj_pair2_eq_dec in H6.
 apply inj_pair2_eq_dec in H6.
 destruct H6.
 destruct mu1. inversion_clear H12.
 simpl.
 econstructor. apply (@Pure_free_eval' s e) with q; try assumption.
 inversion_clear H0. assumption.  econstructor.
 apply d_seman_app_aux.
 apply WF_ceval  with (QUnit_Ctrl s0 e0 s1 e1 U1) [(c, q)]. 
 apply WF_state_dstate_aux.
 inversion_clear Hw. assumption.
 apply ceval_QUnit_Ctrl. assumption.
 assumption.
 apply WF_ceval with (QUnit_Ctrl s0 e0 s1 e1 U1)  (p :: mu1).
 inversion_clear Hw.
 assumption. assumption.
 simpl. econstructor. 
 apply (@Pure_free_eval' s e) with q; try assumption.
 inversion_clear H0. assumption.
 econstructor.
apply IHmu1; try  assumption. inversion_clear Hw. assumption. 
inversion H0; subst.  intuition.
apply Nat.eq_dec. apply Nat.eq_dec. }  }

{induction mu1; intros mu2 F Hs Hm Hw; intros.
{inversion  H; subst. intuition.  }
 {destruct a. inversion H; subst. clear H.
 destruct mu1. inversion_clear H9.
 simpl. rewrite map2_nil_r.
 apply (big_app_seman ((2 ^ (e0 - s0)))  (fun j : nat =>
 (c_update i j c, QMeas_fun s0 e0 j q))).
 intros. split.
 apply WF_state_dstate_aux.
 unfold WF_state. simpl. 
 apply WF_qstate_QMeas. intuition.
 intuition. lia. simpl in H1. assumption.  
  assumption. inversion_clear Hw.
 assumption.
 simpl. econstructor.
 apply Pure_eval'' with c q; try assumption.
 simpl in Hm. 
 unfold cstate_eq.
 intros. rewrite c_update_find_not.
 reflexivity. 
 unfold not.
 intros. rewrite<-H3 in *.
 apply (In_inter_empty _ _ i) in Hm.
 destruct Hm. assumption.
 apply NSet.add_1. reflexivity.
 inversion_clear H0. assumption.
  econstructor. intros. assumption.
  apply (WF_qstate_QMeas_app s0 e0 q c i ((2 ^ (e0 - s0)))).
  lia. lia. inversion_clear Hw.
  assumption.   assumption.
   apply pow_gt_0. admit.
 apply d_seman_app_aux.
 apply WF_ceval  with <{ i :=M [[s0 e0]] }>  [(c, q)]. 
 apply WF_state_dstate_aux.
 inversion_clear Hw. assumption.
 apply ceval_QMeas. assumption. assumption. 
 apply WF_ceval with <{ i :=M [[s0 e0]] }> (p :: mu1).
 inversion_clear Hw.
 assumption. assumption.
 apply (big_app_seman ((2 ^ (e0 - s0)))  (fun j : nat =>
 (c_update i j c, QMeas_fun s0 e0 j q))).
 intros. split.
 apply WF_state_dstate_aux.
 unfold WF_state. simpl. 
 apply WF_qstate_QMeas. intuition.
 intuition. lia. simpl in H1. assumption.  
  assumption. inversion_clear Hw.
 assumption. 
 simpl. econstructor.
 apply Pure_eval'' with c q; try assumption.
 simpl in Hm. 
 unfold cstate_eq.
 intros. rewrite c_update_find_not.
 reflexivity.
 unfold not. 
 intros. rewrite<-H3 in *.
 apply (In_inter_empty _ _ i) in Hm.
 destruct Hm. assumption.
 apply NSet.add_1. reflexivity.
 inversion_clear H0. assumption.
econstructor. assumption.
apply (WF_qstate_QMeas_app s0 e0 q c i ((2 ^ (e0 - s0)))).
lia. lia. inversion_clear Hw.
assumption.   assumption.
 apply pow_gt_0. admit.
apply IHmu1. lia.  inversion_clear Hw. assumption.
inversion_clear Hw. assumption.
assumption.
inversion_clear H0. assumption. 
 }  }
Admitted.


Theorem rule_qframe: forall (F1 F2 F3: State_formula) c,
Considered_Formula F3 ->
({{F1}} c {{F2}}) 
/\ (NSet.Equal (NSet.inter (fst (Free_state F3)) (fst (MVar c))) (NSet.empty) )
/\ ((option_nat (NSet.max_elt (snd (MVar c)))) <=  fst (Free_State F3) \/
snd (Free_State F3) <= ((option_nat (NSet.min_elt (snd (MVar c))))))
->  {{F1 ⊙ F3}} c {{F2 ⊙ F3}}.
Proof.  unfold hoare_triple.  intros F1 F2 F3 c HF3. intros. destruct H.
        assert(sat_Assert mu F1 -> sat_Assert mu' F2).
        apply H. assumption. 
        destruct mu as [mu IHmu].
        destruct mu' as [mu' IHmu'].
        inversion_clear H0. simpl in H6.
        repeat rewrite sat_Assert_to_State in *.
        inversion_clear H1.  simpl in *.
        econstructor. assumption. simpl in *.
        pose H7.
        rewrite State_eval_odot in s0.
        rewrite State_eval_odot.
        destruct s0. destruct H8.
        split. 
        assert(sat_Assert (StateMap.Build_slist IHmu') F2).
        apply H with (StateMap.Build_slist IHmu).
        apply E_com. assumption. assumption.
        assumption. rewrite sat_Assert_to_State.
        econstructor. assumption. assumption.
        rewrite sat_Assert_to_State in *.
        inversion_clear H10. assumption.
        split. 
        bdestruct (fst (Free_State F3) =? snd (Free_State F3)).
        apply Pure_eval_preserve with c mu;
        try assumption.  apply H2.
        apply rule_f  with  c mu; try assumption.
        split. assumption. 
        apply Considered_Formula_dom in HF3.
        lia. apply H2. apply H2.  
         admit.
Admitted.







(* Lemma rule_f: forall  F1 F2 c n (mu mu':list (cstate * qstate n )) ,
State_eval_dstate (F1 ⊙ F2) mu->
ceval_single c mu mu'-> 
NSet.Subset (fst (MVar c)) (fst (Free_state F1))->
NSet.Subset (snd (MVar c)) (snd (Free_state F1))->
State_eval_dstate F2 mu'.
Proof. induction c. intros. 
-(*skip*) apply ceval_skip_1 in H0. rewrite <-H0.
  rewrite State_eval_odot in H.  intuition.
-admit.
-intros. inversion H0; subst.  assumption. *)
(* Lemma rule_f': forall a s e sigma (rho:qstate s e) i a',
NSet.Equal (NSet.inter (NSet.add i NSet.empty)
       ((Free_aexp a))) (NSet.empty) ->
 aeval 
  (c_update i (aeval (sigma, rho) a') sigma, rho) a =
  aeval 
  (sigma, rho) a .
Proof. induction a; intros.
       simpl. reflexivity.   
       simpl in *. 
       assert(i0<>i). admit.
       rewrite c_update_find_not.
       reflexivity. assumption.
       simpl in *. rewrite IHa1.
       rewrite IHa2. reflexivity.
       admit. admit.
       simpl in *. rewrite IHa1.
       rewrite IHa2. reflexivity.
       admit. admit.
       simpl in *. rewrite IHa1.
       rewrite IHa2. reflexivity.
       admit. admit.
       simpl in *. rewrite IHa1.
       rewrite IHa2. reflexivity.
       admit. admit.
       simpl in *. rewrite IHa1.
       rewrite IHa2. reflexivity.
       admit. admit.
       simpl in *. rewrite IHa1.
       rewrite IHa2. reflexivity.
       admit. admit.
       simpl in *. rewrite IHa1.
       rewrite IHa2. reflexivity.
       admit. admit.
Admitted.

Lemma rule_f_b: forall b s e sigma (rho:qstate s e) i a,
NSet.Equal (NSet.inter (NSet.add i NSet.empty)
       ((Free_bexp b))) (NSet.empty) ->
beval 
  (c_update i (aeval (sigma, rho) a) sigma, rho) b=
beval 
  (sigma, rho) b .
Proof. induction b; intros.
       simpl. reflexivity.
       simpl. reflexivity.   
       simpl in *. repeat rewrite rule_f'.
       reflexivity. admit. admit.
       simpl in *. repeat rewrite rule_f'.
       reflexivity. admit. admit.
       simpl in *. repeat rewrite rule_f'.
       reflexivity. admit. admit.
       simpl in *. repeat rewrite rule_f'.
       reflexivity. admit. admit.
       simpl in *.  rewrite IHb.
       reflexivity. assumption.
       simpl in *. rewrite IHb1. rewrite IHb2.
       reflexivity. admit. admit.
       simpl in *. rewrite IHb1. rewrite IHb2.
       reflexivity. admit. admit.
Admitted.

(* Lemma Free_map: forall (P:nat->Pure_formula) (x y:nat) ,
(Free_pure (P x))= (Free_pure (P y)).
Proof. induction P. simpl. intros. induction (P x); induction (P y).
       destruct b; destruct b0. reflexivity.

  
Qed. *)


Lemma rule_f'_p: forall  P s e sigma (rho:qstate s e) i a,
NSet.Equal (NSet.inter (NSet.add i NSet.empty)
       ((Free_pure P))) (NSet.empty) ->
Pure_eval P
  (c_update i (aeval (sigma, rho) a) sigma, rho)<->
Pure_eval P
  (sigma, rho) .
Proof. induction P; intros.
       simpl. rewrite rule_f_b. reflexivity.    
       assumption. admit. admit.
       split. 
       simpl in *. intros.
       remember (c_update i (aeval (sigma, rho) a) sigma).
       apply (IHP _ _ c rho i0 a0).
       assumption.
       rewrite Heqc. admit.
       intros.
       simpl in *.
       remember (c_update i (aeval (sigma, rho) a) sigma).
       apply (IHP _ _ c rho i0 a0) in H0.
Admitted.

Lemma rule_f_assn: forall  F s e sigma (rho:qstate s e) i a,
NSet.Equal (NSet.inter (fst (MVar <{ i := a }>)) (fst (Free_state F))) NSet.empty ->
State_eval F (c_update i (aeval (sigma, rho) a) sigma, rho) <-> State_eval F (sigma, rho) .
Proof. induction F; intros; simpl in *. 
       apply rule_f'_p. assumption. 
       admit.
Admitted. *)




(* Fixpoint QExp_dom (qs:QExp) :=
  match qs with 
  | QExp_s s e v => (s, e) 
  | QExp_t qs1 qs2 =>  (QExp_dom qs1) .+ (QExp_dom qs2)
  end .

Fixpoint QExp_vec (qs: QExp) (s e:nat) :=
  match qs with 
  | QExp_s s e v => v 
  | QExp_t qs1 qs2 =>  (QExp_vec qs1) .+ (QExp_vec qs2)
  end . *)

(* Lemma QExp_pure: forall (qs: QExp) s e c (q : qstate s e) ,
State_eval qs (c, q)->
exists (q': Density (2^(e-s))) (p:R), and (Pure_State q')
(q=p .* q').
Proof. induction qs. intros. 
       simpl in H. 
  
Qed.


Lemma QExp_eval_sub: forall (qs: QExp) s e c (q q': qstate s e) ,
q_subseq q q'->
State_eval qs (c, q')->
State_eval qs (c, q).
Proof. induction qs; intros.
      inversion_clear H. subst. intuition.
      admit.
      inversion_clear H. subst. intuition.
      destruct H1. subst.
      simpl in H0.
      destruct H0. destruct H.
      destruct H. destruct H.
      destruct H. destruct H.
      destruct H. 
      inversion H; subst.
      simpl.
Admitted.



Lemma QExp_eval_sub': forall F s e c (q q': qstate s e) ,
q_subseq q q'->
State_eval F (c, q')->
State_eval F (c, q).
Proof. induction F; intros.
       apply state_eq_Pure with (c,q').
       reflexivity. intuition.
       inversion_clear H.
       subst. intuition.
       destruct H1.  subst.
       induction qs.
       simpl in H0. 
       simpl.  
       split. intuition.
       split. intuition.
       split. intuition.
       rewrite <-PMtrace_scale in *.
       rewrite PMtrace_plus in *.
       rewrite Mscale_plus_distr_r in *.
       destruct H0. destruct H0.
       destruct H1. 
       admit. lia. lia.
       admit.

       

      



Lemma State_eval_sub: forall s e (mu mu': list (state s e)) F,
d_subseq mu mu'->
State_eval_dstate F mu'->
State_eval_dstate F mu.
Proof. induction mu.  intros. destruct mu'.
       simpl in H0. destruct H0.
       simpl in H. destruct H.
       intros. destruct mu'.
       destruct a.
       simpl in H. destruct H.
       destruct mu; destruct mu';
       destruct a; destruct s0.
       simpl in H. 
       simpl. econstructor.
       inversion_clear H0.
       admit. 
       
       econstructor.

       simpl in H. intuition.
       destruct s1.
       simpl in H. intuition.
       simpl. econstructor.
       admit.
       apply IHmu with (s2 :: mu').
       destruct s1. destruct s2.
       simpl in H. econstructor. intuition.
       split. intuition. intuition.
       inversion_clear H0. intuition.   
 Admitted. *)



(* Lemma rule_f_qinit_qs: forall  F1 F2 s' e' (st st': (cstate * qstate s' e' )) s e,
State_eval (F1 ⊙ F2) st->
ceval_single (QInit s e) [st] [st']-> 
NSet.Subset (snd (MVar (QInit s e))) (snd (Free_state F1))->
State_eval F1 st'.
Proof. induction qs. intros. 
       inversion H0; subst. inversion H8; subst.
       inversion_clear H8. injection H7.
       intros. rewrite <-H2.  clear H7. clear H2.


       assert(e < s0 \/ s> e0)%nat. admit.
       destruct H2.
       simpl in *. split. intuition.
       split. intuition.  
        admit.
        intros.
        simpl in *.
        split.  intuition.
        split. apply (IHqs1 F1  n st st' s e).
        split. admit. intuition.
        assumption. assumption.
        apply (IHqs2 F1  n st st' s e).
        split. admit. intuition.
        assumption. assumption.
Admitted. *)




(* Lemma rule_f_qinit: forall  F1 F2 F3 s' e' (st st': (cstate * qstate s' e' )) s e,
(forall (s0 e0: nat) (st st':(cstate * qstate s' e' )), 
State_eval F1 st -> 
ceval_single (QInit s e) [st] [st']-> 
State_eval F2 st') -> 
State_eval (F1 ⊙ F3) st->
ceval_single (QInit s e) [st] [st']-> 
NSet.Subset (snd (MVar (QInit s e))) (snd (Free_state F1))->
State_eval (F2 ⊙ F3) st'.
Proof. intros. inversion H0; subst. destruct st.
       destruct st'.  destruct H3.
       destruct H3. destruct H3. destruct H3.
       destruct H3. destruct H3. 
       inversion H3; subst. simpl in H10. 
       rewrite <-H10 in H1. simpl in H2.
       inversion H1; subst. inversion H13; subst.
       clear H13. injection H12. intros; subst.
       clear H12. simpl in H4. 
Admitted. *)

(* Inductive d_combin {s0 e0 s1 e1 s2 e2:nat}: (list (cstate * qstate s0 e0))-> (list (cstate * qstate s1 e1))-> (list (cstate * qstate s2 e2))-> Prop:=
|combin_nil: d_combin nil nil nil 
|combin_cons: forall sigma rho0  rho1  rho' mu0 mu1 mu',
              q_combin rho0 rho1 rho'->
              d_combin mu0 mu1 mu'->
               d_combin ((sigma, rho0)::mu0) ((sigma, rho1)::mu1) ((sigma, rho')::mu'). *)

(* Inductive q_combin{s0 e0 s1 e1 s2 e2}: (qstate s0 e0) -> (qstate s1 e1)-> (qstate s2 e2)->Prop:=
|combin_l: forall q0 q1, e0 = s1-> s0 = s2 -> e1 = e2 ->
            q_combin q0 q1 (@kron (2^(e0-s0)) (2^(e0-s0)) (2^(e1-s1))  
            (2^(e1-s1)) q0 q1)
|combin_r: forall q0 q1, e1 = s0-> s1= s2 -> e0 =e2 ->
            q_combin q0 q1 (@kron  (2^(e1-s1))  
            (2^(e1-s1)) (2^(e0-s0)) (2^(e0-s0)) q1 q0). *)

(* Inductive d_combin {s0 e0 s1 e1 s2 e2:nat}: (list (cstate * qstate s0 e0))-> (list (cstate * qstate s1 e1))-> (list (cstate * qstate s2 e2))-> Prop:=
|combin_nil: d_combin nil nil nil 
|combin_cons: forall sigma rho0  rho1  rho' mu0 mu1 mu',
      q_combin rho0 rho1 rho'->
      d_combin mu0 mu1 mu'->
        d_combin ((sigma, rho0)::mu0) ((sigma, rho1)::mu1) ((sigma, rho')::mu').

Fixpoint d_subseq{s e: nat} (mu0 mu1: list (cstate *qstate s e)): Prop:=
match mu0, mu1 with 
|nil , nil=> True
|(c0,q0)::mu0', (c1,q1)::(mu1')=>c0=c1 /\ q_subseq q0 q1 /\ d_subseq mu0' mu1'
|_, _=> False
end.

(* Lemma State_eval_combin: forall s e (mu:list(cstate * qstate s e)) (F1 F2:State_formula),
State_eval_dstate (F1 ⊙ F2) mu <->
(exists s0 e0 s1 e1 (mu0:list(cstate * qstate s0 e0)) (mu1:list(cstate * qstate s1 e1)), 
and (d_combin mu0 mu1 mu ) 
((State_eval_dstate F1 mu0 /\ State_eval_dstate F2 mu1)))
.
Proof. 
Admitted. *)


Lemma rule_6: forall c s e s0 e0 s1 e1
(q:qstate s0 e0) (q0:qstate s1 e1) (rho': qstate s e)
(x:list(cstate * qstate s0 e0))(x0:list(cstate * qstate s1 e1))
(x1:list(cstate * qstate s e)),
q_combin q q0 rho'->
d_combin x x0 x1 ->
exists (mu:list (cstate * qstate s e)),
d_combin (StateMap.Raw.map2 option_app [(c, q)] x)
    (StateMap.Raw.map2 option_app [(c, q0)] x0) mu.
Proof. 
induction x; intros. inversion_clear H0.
simpl. exists [(c, rho')].
econstructor. assumption. econstructor.
destruct a. 
inversion_clear H0.
simpl. destruct (Cstate_as_OT.compare c c0).
exists ((c,rho')::(c0,rho'0)::mu').
econstructor. assumption.
econstructor. assumption.
repeat rewrite map2_r_refl.
assumption.
inversion H; subst.
exists ((c,@kron (2^(s1-s)) (2^(s1-s))
(2^(e-s1)) (2^(e-s1)) (q .+ q1) (q0 .+ rho1))::mu').
apply (@combin_cons s s1 s1 e s e).
econstructor; try reflexivity.
repeat rewrite map2_r_refl.
assumption.
exists ((c,@kron  (2^(s0-s)) (2^(s0-s)) (2^(e-s0)) (2^(e-s0))
 (q0 .+ rho1) (q .+ q1))::mu').
apply (@combin_cons s0 e s s0 s e).
econstructor; try reflexivity.
repeat rewrite map2_r_refl.
assumption.
apply IHx in H2.
destruct H2.
exists ((c0,rho'0)::x2).
econstructor. 
assumption.
apply H0.
assumption.
Qed.

Lemma rule_7: forall s e s0 e0 s1 e1
(x mu1:list(cstate * qstate s0 e0))(x0 mu2:list(cstate * qstate s1 e1))
(x1 mu3:list(cstate * qstate s e)),
d_combin mu1 mu2 mu3->
d_combin x x0 x1 ->
exists (mu:list (cstate * qstate s e)),
d_combin (StateMap.Raw.map2 option_app mu1 x)
    (StateMap.Raw.map2 option_app mu2 x0) mu.
Proof. 
induction x; induction mu1; intros.
{ inversion_clear H0. inversion_clear H.
simpl. exists nil.
econstructor. }
{ destruct a. 
inversion_clear H0. inversion_clear H.
simpl. repeat rewrite map2_l_refl.
exists ((c,rho')::mu').
econstructor. assumption. assumption. }
{destruct a. 
inversion_clear H0. inversion_clear H.
simpl. repeat rewrite map2_r_refl.
exists ((c,rho')::mu').
econstructor. assumption. assumption. }
{destruct a0. destruct a.
inversion_clear H. inversion_clear H0. 
simpl. destruct (Cstate_as_OT.compare c c0).
assert (exists mu : list (cstate * qstate s e),
d_combin (StateMap.Raw.map2 option_app mu1 ((c0, q0) :: x))
(StateMap.Raw.map2 option_app mu4 ((c0, rho2) :: mu5)) mu ).
apply IHmu1 with ((c0, rho'0)::mu'0) mu'.
assumption. econstructor. assumption.
assumption. destruct H0.
exists ((c,rho')::x2).
econstructor. assumption.
assumption.

assert(exists mu'1 : list (cstate * qstate s e),
d_combin (StateMap.Raw.map2 option_app mu1 x)
(StateMap.Raw.map2 option_app mu4 mu5) mu'1).
apply IHx with mu'0 mu'.
assumption. assumption.
destruct H0.
inversion H1; subst.
exists ((c,@kron (2^(s1-s)) (2^(s1-s))
(2^(e-s1)) (2^(e-s1)) (q .+ q0) (rho1 .+ rho2))::x2).
apply (@combin_cons s s1 s1 e s e).
econstructor; try reflexivity.
assumption.
exists ((c,@kron  (2^(s0-s)) (2^(s0-s)) (2^(e-s0)) (2^(e-s0))
(rho1 .+ rho2)(q .+ q0) )::x2).
apply (@combin_cons s0 e s s0 s e).
econstructor; try reflexivity.
assumption.

assert (exists mu : list (cstate * qstate s e),
d_combin (StateMap.Raw.map2 option_app ((c, q)::mu1) x)
    (StateMap.Raw.map2 option_app ((c, rho1)::mu4) mu5) mu).
apply IHx with  mu'0 ((c, rho') ::mu').
econstructor. assumption.
assumption. assumption.
destruct H0. 
exists ((c0,rho'0)::x2).
econstructor.
assumption.
assumption. }
Qed.

Lemma q_combin_eq:forall s e s0 e0 s1 e1
(q:qstate s0 e0) (q0:qstate s1 e1) (rho rho': qstate s e),
q_combin q q0 rho->
q_combin q q0 rho'->
rho=rho'.
Proof. intros. inversion H; subst. 
       inversion H0; subst. reflexivity.
       assert(1=2^(s-s))%nat. rewrite Nat.sub_diag.
       rewrite pow_0_r. lia. unfold qstate. destruct H1.
       admit. 
       inversion H0; subst.
       admit.
       reflexivity.
Admitted.

Lemma d_combin_eq:forall s e s0 e0 s1 e1
(mu:list (state s0 e0)) (mu0: list (state s1 e1)) (mu1 mu2: list (state s e)),
d_combin mu mu0 mu1->
d_combin mu mu0 mu2->
mu1=mu2.
Proof. induction mu; intros. inversion H; subst. 
       inversion H0; subst. reflexivity.
       inversion H; subst.
       inversion H0; subst. f_equal.
       f_equal. apply q_combin_eq with 
       s0 e0 s1 e1 rho0 rho1; assumption.
       apply IHmu with mu4; assumption.
Qed.

Lemma q_subseq_eq:forall s e  (q q':qstate s e),
q=q'-> q_subseq q q'.
Proof. intros. subst. unfold q_subseq.
       left. reflexivity. 
Qed.

Lemma d_subseq_eq:forall s e (mu mu':list (state s e)),
mu=mu'-> d_subseq mu mu'.
Proof. induction mu; destruct mu'; intros.
      econstructor. destruct H. econstructor.
      destruct H. 
      destruct a. econstructor. reflexivity.
      split.
      apply q_subseq_eq. reflexivity.
      apply IHmu. reflexivity.
      injection H; intros; subst.
      destruct s0. 
      econstructor. reflexivity.
      split.  
      apply q_subseq_eq. reflexivity.
      apply IHmu. reflexivity.

Qed.

Lemma rule_three:  forall s e s0 e0 s1 e1
(x:list(cstate * qstate s0 e0))(x0:list(cstate * qstate s1 e1))
(q:qstate s0 e0) (q0:qstate s1 e1) (rho': qstate s e)
(mu'1 mu:list(cstate * qstate s e)) c ,
q_combin q q0 rho'->
d_combin x x0 mu'1->
(d_combin
  (StateMap.Raw.map2 option_app
     [(c,q)] x)
  (StateMap.Raw.map2 option_app
     [(c, q0)] x0) mu)
  -> d_subseq (StateMap.Raw.map2 option_app
  [(c,
    rho')] mu'1) mu.
Proof. induction x; intros.
--inversion H0; subst.  clear H0. simpl in H1. 
  simpl StateMap.Raw.map2. inversion_clear H1.
  inversion_clear H2. econstructor. reflexivity.
  split. 
  apply q_subseq_eq. apply q_combin_eq with s0
  e0 s1 e1 q q0. assumption. assumption. econstructor.
--destruct a. inversion H0; subst. clear H0.
  simpl in H1.  
  destruct (Cstate_as_OT.compare c c0);
  repeat rewrite map2_r_refl in H1.
  inversion_clear H1; inversion_clear H2;
  simpl; MC.elim_comp;
  econstructor. reflexivity.  split. apply q_subseq_eq.
  apply q_combin_eq with s0
  e0 s1 e1 q q0. assumption. assumption.
  econstructor. reflexivity.  split. 
  apply q_subseq_eq.
  apply q_combin_eq with s0
  e0 s1 e1 q1 rho1. assumption. assumption.
  rewrite map2_r_refl.
  apply d_subseq_eq.
  apply d_combin_eq with s0 e0 s1 e1 x mu1; assumption.

  inversion_clear H1. simpl. MC.elim_comp. 
  econstructor. reflexivity.  split. 
  inversion H0; subst. inversion H; subst.
  inversion H7; subst.
  repeat rewrite kron_plus_distr_l.
  repeat rewrite kron_plus_distr_r. unfold q_subseq.
  right.  
   admit. admit. admit. admit.
   rewrite map2_r_refl. 
   apply d_subseq_eq.
   apply d_combin_eq with s0 e0 s1 e1 x mu1; assumption.

  inversion_clear H1. simpl. MC.elim_comp.
  econstructor. reflexivity.  split.  apply q_subseq_eq.
  apply q_combin_eq with s0
  e0 s1 e1 q1 rho1. assumption. assumption.
  apply IHx with mu1 q q0. 
  assumption. assumption.
  apply H2.
Admitted.


Lemma rule_for:  forall s e s0 e0 s1 e1
(x mu1:list(cstate * qstate s0 e0))(x0 mu2:list(cstate * qstate s1 e1))
(mu3 mu'1 mu:list(cstate * qstate s e)),
d_combin mu1 mu2 mu3->
d_combin x x0 mu'1->
(d_combin (StateMap.Raw.map2 option_app
     mu1 x)
(StateMap.Raw.map2 option_app
   mu2 x0)mu)
-> d_subseq (StateMap.Raw.map2 option_app
  mu3 mu'1) mu.
Proof. induction x; induction mu1; intros.
--inversion H0; subst.  clear H0.
  inversion H; subst. clear H.
  simpl in H1. 
  simpl StateMap.Raw.map2. inversion_clear H1.
   econstructor. 
 { inversion H0; subst.  clear H0.
 inversion H; subst. clear H.
  simpl in H1. repeat rewrite map2_l_refl in H1.
  inversion H1; subst. clear H1.
  simpl. rewrite map2_l_refl. intuition. apply q_subseq_eq.
  apply q_combin_eq with s0 e0 s1 e1 rho0 rho1.
  intuition. intuition. apply d_subseq_eq.
  apply d_combin_eq with s0 e0 s1 e1 mu1 mu4.
  assumption. assumption. }
  { inversion H0; subst.  clear H0.
  inversion H; subst. clear H.
   simpl in H1. repeat rewrite map2_r_refl in H1.
   inversion H1; subst. clear H1.
   simpl. rewrite map2_r_refl. intuition. apply q_subseq_eq.
   apply q_combin_eq with s0 e0 s1 e1 rho0 rho1.
   intuition. intuition. apply d_subseq_eq.
   apply d_combin_eq with s0 e0 s1 e1 x mu1.
   assumption. assumption. }
   {destruct a0; destruct a. inversion H0; subst. clear H0.
   inversion H; subst. clear H.  simpl in H1.
  destruct (Cstate_as_OT.compare c c0);
  repeat rewrite map2_r_refl in H1;
  inversion_clear H1;
  simpl; MC.elim_comp;
  econstructor; try reflexivity. 
  split. apply q_subseq_eq.
  apply q_combin_eq with s0
  e0 s1 e1 q rho2. assumption. assumption.
  apply IHmu1 with ((c0, rho1) :: mu4) mu5.
  assumption.  econstructor.
  assumption. assumption.
  assumption.


  
  split.  inversion H7; subst.
  inversion H6; subst. inversion H; subst.
  repeat rewrite kron_plus_distr_l.
  repeat rewrite kron_plus_distr_r.
  unfold q_subseq.
   admit. admit. admit. admit.
   apply IHx with mu1 mu4 mu5.
   assumption. assumption.
   assumption.

   split. apply q_subseq_eq.
  apply q_combin_eq with s0
  e0 s1 e1 q0 rho1. assumption. assumption.
  repeat rewrite app_fix in *.
  apply IHx with  ((c,q)::mu1) mu4 ((c,rho2)::mu5) .
  econstructor. assumption.
  assumption. 
  assumption. assumption. }
Admitted.


Lemma q_subseq_trans:forall s e  (q0 q1 q2: qstate s e),
 q_subseq q0 q1->
 q_subseq q1 q2->
 q_subseq q0 q2. 
Proof. intros. unfold q_subseq in *.
       destruct H; destruct H0. 
       left. subst. reflexivity.
       destruct H0. 
       right. exists x. subst. reflexivity.
       destruct H.
       right. exists x. subst. reflexivity.
       destruct H. destruct H0.
       right.
       exists (x .+ x0).
       subst. rewrite Mplus_assoc.
       reflexivity.
Qed.

Lemma d_subseq_trans:forall s e (mu0 mu1 mu2:list (state s e)),
 d_subseq mu0 mu1->
 d_subseq mu1 mu2->
 d_subseq mu0 mu2. 
Proof.  induction mu0;destruct mu1; destruct mu2;
       intros.
      {assumption. }
      {destruct s0; intuition. }
      {destruct s0; intuition. }
      {destruct s0; intuition. }
      {destruct a; intuition. }
      {destruct s0; intuition. }
      {destruct s0; intuition. }
      {destruct a. destruct s0. destruct s1. simpl in *.
       split. destruct H. rewrite H. intuition.
       split. apply q_subseq_trans with  q0.
       intuition. intuition.
       apply IHmu0 with mu1; intuition.
        }
Qed.


Lemma d_subseq_map2: forall s e
(mu1 mu2 mu1' mu2':list (cstate *qstate s e)),
d_subseq mu1 mu1'-> 
d_subseq mu2 mu2'->
d_subseq (StateMap.Raw.map2 option_app mu1 mu2)
  (StateMap.Raw.map2 option_app mu1' mu2').
Proof. induction mu1; induction mu2; intros;
       destruct mu1'; destruct mu2';
       try destruct p; try destruct a; 
       try destruct a0; try intuition.
       simpl in *.
       repeat rewrite map2_r_refl.
       intuition.
       simpl in *. 
       repeat rewrite map2_l_refl.
       intuition.
       destruct p0. 
       simpl in *. destruct H. destruct H0.
       subst. 
       destruct (Cstate_as_OT.compare c c2).
       simpl. split. intuition.
       split. intuition.
      apply IHmu1. intuition. 
      simpl. intuition. 
      
     
      econstructor. reflexivity.
      split.  admit. 
      apply IHmu1. intuition.
      intuition. 
     
      simpl. 
      repeat rewrite app_fix.
      split. reflexivity.
      split. intuition.
      apply IHmu2.
      split. reflexivity.
      intuition. intuition.
Admitted. *)




(* Lemma d_q_eq_map2: forall s e
(mu1 mu2 mu1' mu2':list (cstate *qstate s e)),
qstate_eqdstate_ mu1 mu1'->
dstate_qstate_eq mu2 mu2'->
dstate_qstate_eq (StateMap.Raw.map2 option_app mu1 mu2)
  (StateMap.Raw.map2 option_app mu1' mu2').
Proof.   induction mu1; induction mu2; intros;
destruct mu1'; destruct mu2';
try destruct p; try destruct a; 
try destruct a0; try intuition.
simpl in *.
repeat rewrite map2_r_refl.
intuition.
simpl in *. 
repeat rewrite map2_l_refl.
intuition.
destruct p0. 
simpl in *. destruct H. destruct H0.
subst. 
destruct (Cstate_as_OT.compare c c2).
simpl. split. intuition.
apply IHmu1. intuition.
simpl. intuition.

simpl. split. intuition.
apply IHmu1. intuition. intuition.

split. reflexivity.
repeat rewrite app_fix in *.
apply IHmu2.
split. reflexivity.
intuition. intuition.
Qed.  *)
(* Local Open Scope nat_scope.
Lemma QInit_fun_sub{s' e':nat}: forall s e (q q': qstate s' e'), 
s'<=s/\s<=e/\e<=e'->
q_subseq q q'->
@q_subseq s' e' (QInit_fun s e q) (QInit_fun s e q').
Proof. intros. inversion_clear H0. subst.  
       apply q_subseq_eq. reflexivity.
      destruct H1. subst.
      rewrite <-QInit_fun_plus.
      unfold q_subseq. right.
      exists (QInit_fun s e x).
      reflexivity. intuition.
Qed.


Lemma QUnit_Ctrl_fun_sub{s' e':nat}: forall s0 e0 s1 e1 (q q0: qstate s' e') (U: nat-> Square (2^(e1-s1))), 
s'<=s0/\s0<=e0 /\ e0<=s1/\s1<=e1/\e1<=e'->
q_subseq q0 q->
q_subseq (QUnit_Ctrl_fun s0 e0 s1 e1 U q0) 
(QUnit_Ctrl_fun s0  e0 s1 e1 U q).
Proof. intros. inversion_clear H0. subst. 
apply q_subseq_eq. reflexivity.
destruct H1. subst.
rewrite <-QUnit_Ctrl_fun_plus.
unfold q_subseq. right.
exists (QUnit_Ctrl_fun s0 e0 s1 e1 U x).
reflexivity. intuition.
Qed.


Lemma QUnit_One_fun_sub{s' e':nat}: forall s e U (q q': qstate s' e'), 
s'<=s/\s<=e/\e<=e'->
q_subseq q q'->
@q_subseq s' e' (QUnit_One_fun s e U q) (QUnit_One_fun s e U q').
Proof. intros. inversion_clear H0. subst. 
       apply q_subseq_eq. reflexivity.
      destruct H1. subst.
      rewrite <-QUnit_One_fun_plus.
      unfold q_subseq. right.
      exists (QUnit_One_fun s e U x).
      reflexivity. intuition.
Qed.

Lemma QMeas_fun_sub{s' e':nat}: forall s e i (q q': qstate s' e'), 
s'<=s/\s<=e/\e<=e'->
q_subseq q q'->
@q_subseq s' e' (QMeas_fun s e i q) (QMeas_fun s e i q').
Proof. intros. inversion_clear H0. subst. 
       apply q_subseq_eq. reflexivity.
      destruct H1. subst.
      rewrite <-QMeas_fun_plus.
      unfold q_subseq. right.
      exists (QMeas_fun s e i x).
      reflexivity. intuition.
Qed. *)

(* Lemma rule_two: forall c s0 e0 s1 e1 
(mu1:list (cstate *qstate s0 e0))
(mu2:list (cstate *qstate s1 e1))
s e
(mu0 mu mu':list (cstate *qstate s e)) F ,
ceval_single c mu mu'-> 
d_combin mu1 mu2 mu0  ->
d_subseq mu mu0 ->
NSet.inter (fst (Free_state F)) (fst (MVar c)) = NSet.empty ->
NSet.Subset (snd (MVar c)) (Qsys_to_Set s0 e0) ->
State_eval_dstate F mu2 ->
(exists (mu1' :list (cstate *qstate s0 e0))
( mu2': list (cstate *qstate s1 e1))
( mu'': list (cstate *qstate s e)), and 
(ceval_single c mu1 mu1')
(State_eval_dstate F mu2' /\
d_combin mu1' mu2' mu''  /\
 d_subseq mu' mu'')).
Proof. induction c. 
-- induction mu1; intros. 
   {inversion  H0; subst. 
   exists nil. exists nil. exists nil. 
   split. apply E_nil. destruct H4. }
    { destruct a. 
    inversion H0; subst. clear H0.
    assert(ceval_single <{ skip }> (mu'0) (mu'0)).
    apply ceval_skip. 
    assert(exists  (mu1' : list (cstate * qstate s0 e0)) 
    (mu2' : list (cstate * qstate s1 e1)) 
    (mu'' :  list (cstate * qstate s e)),
    and (ceval_single <{ skip }> mu1 mu1') 
    (State_eval_dstate F mu2' /\
    d_combin mu1' mu2' mu'' /\ d_subseq mu'0 mu'')).
    apply (IHmu1 _ _ _ _ _ _ _ H0 H11). apply d_subseq_eq.
    reflexivity. assumption. assumption. admit.
    destruct H5. destruct H5. destruct H5. 
    destruct H5. apply ceval_skip_1 in H5.
    subst.
    exists (((c, q) :: x)). exists (((c, rho1) :: x0)).
    exists ((c, rho')::x1).
    split.  apply E_Skip. split. simpl.
    econstructor. inversion_clear H4. assumption.
    admit.
    split. econstructor.  intuition.  intuition.
    apply ceval_skip_1 in H. rewrite <-H. 
    apply d_subseq_trans with ((c, rho') :: mu'0).
    assumption. simpl. split. reflexivity.
    split. apply q_subseq_eq. reflexivity.
    intuition.
     }
-- admit.
--induction mu1; intros.
  {inversion  H0; subst. 
   exists nil. exists nil. exists nil.
   split. econstructor. destruct H4. }
   {destruct a0. inversion H0; subst. clear H0.
    destruct mu. simpl in H1. intuition.
    destruct p. inversion H; subst. simpl in H1.
    destruct H1. subst. 
  assert(exists
  (mu1' : list (cstate * qstate s0 e0)) 
  (mu2' : list (cstate * qstate s1 e1)) 
  (mu'' : list  (cstate * qstate s e)),
  (and (ceval_single <{ i := a }> mu1 mu1') 
   (State_eval_dstate F mu2'/\
   d_combin mu1' mu2' mu'' /\ d_subseq mu'1 mu''))).
  apply (IHmu1 _ _ _ _ _ _ _ H12 H11). intuition.
  assumption. assumption. admit. 
  destruct H0. destruct H0. destruct H0.
  exists (StateMap.Raw.map2 option_app 
  [(c_update i (aeval (c,q) a) c, q)] x).
  exists (StateMap.Raw.map2 option_app 
  [(c_update i (aeval (c,rho1) a) c,rho1)] x0).
  assert(exists (mu'': list (cstate *qstate s e)),
  d_combin
  (StateMap.Raw.map2 option_app
     [(c_update i (aeval (c, q) a) c, q)] x)
  (StateMap.Raw.map2 option_app
     [(c_update i (aeval (c, q) a) c, rho1)] x0) mu'').
  apply rule_6 with  (rho') x1. assumption. intuition. 
   destruct H5. exists x2. 
  split. apply E_Asgn. intuition.
  split. admit.
  split. rewrite (state_eq_aexp (c, rho1) (c,q)).
  intuition. reflexivity. 
  apply d_subseq_trans with 
  ((StateMap.Raw.map2 option_app
  [(c_update i (aeval (c, q) a) c, rho')] x1)).
  apply d_subseq_map2. simpl.
  rewrite (state_eq_aexp (c, q0) (c, q)).
  intuition. reflexivity. intuition.  
  apply rule_three with s0 e0 s1 e1 x x0 q rho1.
  assumption. intuition. assumption. } 
 --admit.
 --intros. destruct mu1; intros.
   { inversion  H0; subst.
     exists nil. exists nil. exists nil. 
     split; econstructor. destruct H4. 
     destruct H4. }
   { inversion H0; subst. clear H0.
     destruct mu. intuition.
     destruct p.   inversion H; subst.
      simpl in H1. destruct H1. destruct H0.
assert(exists
(mu1' : list (cstate * qstate s0 e0)) 
(mu2' : list (cstate * qstate s1 e1))
(mu'' : list (cstate * qstate s e)),
(and (ceval_single c1 (((c, rho0) :: mu1)) mu1') 
 (State_eval_dstate F mu2'  /\
 d_combin mu1' mu2' mu''  /\ d_subseq mu2 mu''))).
apply IHc1 with ((c, rho1) :: mu4) ((c, rho') :: mu'0) (((c, q) :: mu)) .
intuition. econstructor.  intuition.
intuition. simpl. split. reflexivity. apply H1.
admit.
admit. assumption.  
destruct H0. destruct H0. destruct H0.
assert( exists
(mu1' : list (cstate * qstate s0 e0)) 
(mu2' : list (cstate * qstate s1 e1))
(mu'' : list (cstate * qstate s e)),
(and (ceval_single c2 x mu1') 
 (State_eval_dstate F mu2' /\
 d_combin mu1' mu2' mu'' /\ d_subseq mu' mu'' ))).
 apply IHc2 with x0 x1 mu2. intuition. intuition.
 intuition. admit. admit. intuition.
 destruct H5. destruct H5. destruct H5.
 exists x2. exists x3. exists x4. split.
  apply E_Seq with x. 
  intuition. intuition. intuition. }

--induction mu1; intros.
{inversion  H0; subst. 
 exists nil. exists nil. exists nil.
 split. econstructor. destruct H4.
  } 
 { destruct a. inversion H0; subst. clear H0.
  destruct mu. simpl in H1. intuition.
  destruct p. inversion H; subst; simpl in H1.
  destruct H1; subst.
   {assert(exists
  (mu1' : list (cstate * qstate s0 e0)) 
  (mu2' : list (cstate * qstate s1 e1)) 
  (mu''0 : list  (cstate * qstate s e)),
  (and (ceval_single <{ if b then c1 else c2 end }> mu1 mu1') 
   (State_eval_dstate F mu2' /\
   d_combin mu1' mu2' mu''0 /\ d_subseq mu'' mu''0))).
  apply (IHmu1 _ _ _ _ _ _ _ H14 H11). intuition.
   assumption. assumption. admit.
  destruct H0. destruct H0. destruct H0.
  assert(exists
  (mu1' : list (cstate * qstate s0 e0)) 
  (mu2' : list (cstate * qstate s1 e1)) 
  (mu''0 : list  (cstate * qstate s e)),
  (and (ceval_single c1 [(c,q)] mu1') 
   (State_eval_dstate F mu2' /\
   d_combin mu1' mu2' mu''0 /\ d_subseq mu'1 mu''0))).
   apply IHc1 with [(c, rho1)] [(c,rho')] [(c,q0)]. intuition.
   econstructor. intuition. econstructor.
   simpl. intuition. admit. admit. simpl.
   econstructor. inversion_clear H4. assumption.
   econstructor.
   destruct H5. destruct H5. destruct H5. 
  exists (StateMap.Raw.map2 option_app 
  x2 x).
  exists (StateMap.Raw.map2 option_app 
  x3 x0).
  assert(exists (mu'': list (cstate *qstate s e)),
  d_combin (StateMap.Raw.map2 option_app x2 x)
  (StateMap.Raw.map2 option_app x3 x0) mu'').
  apply rule_7 with x1 x4. intuition. intuition.
   destruct H6. exists x5. 
   split. apply E_IF_true.
  rewrite (state_eq_bexp _ (c, q0)). intuition.
  reflexivity. intuition.
   intuition.
   split. admit.
   split. intuition. 
  apply d_subseq_trans with 
  ((StateMap.Raw.map2 option_app x4 x1)).
  apply d_subseq_map2. intuition. intuition. 
  apply rule_for with s0 e0 s1 e1 x x2 x0 x3.
  intuition. intuition. assumption. 
 }
 { admit. }
}
--admit.
--induction mu1; intros.
{inversion  H0; subst. 
 exists nil. exists nil. exists nil.
 split. econstructor. destruct H4. }
 {destruct a. inversion H0; subst. clear H0.
  destruct mu. simpl in H1. intuition.
  destruct p. inversion H; subst. simpl in H1. 
  destruct H1; subst.
assert(exists
(mu1' : list (cstate * qstate s0 e0)) 
(mu2' : list (cstate * qstate s1 e1)) 
(mu'' : list  (cstate * qstate s2 e2)),
(and (ceval_single <{ (s e) :Q= 0 }> mu1 mu1') 
 (State_eval_dstate F mu2' /\
 d_combin mu1' mu2' mu'' /\ d_subseq mu'1 mu''))).
apply (IHmu1 _ _ _ _ _ _ _ H13 H11). intuition.
assumption. assumption. admit. 
destruct H0. destruct H0. destruct H0.
exists (StateMap.Raw.map2 option_app 
[(c,(QInit_fun s e q))] x).
exists (StateMap.Raw.map2 option_app 
[(c,rho1)] x0).
assert(exists (mu'': list (cstate *qstate s2 e2)),
d_combin
(StateMap.Raw.map2 option_app
[(c,(QInit_fun s e q))] x)
(StateMap.Raw.map2 option_app
[(c,rho1)]  x0) mu'').
inversion H10; subst.
apply (rule_6 _ s2 e2 s2 s1 s1 e2 _ _ 
 (@kron (2^(s1-s2)) (2^(s1-s2)) (2^(e2-s1))
 (2^(e2-s1)) (QInit_fun s e q) rho1)_ _ x1).
apply combin_l; econstructor. intuition. 
apply (rule_6 _ s2 e2 s0 e2 s2 s0 _ _ 
 (@kron (2^(s0-s2))
 (2^(s0-s2)) (2^(e2-s0)) (2^(e2-s0))  rho1 (QInit_fun s e q) )_ _ x1).
apply combin_r; econstructor. intuition.
destruct H5. exists x2. 
split. apply E_Qinit. 
simpl in H2. admit.  intuition.
split. apply d_seman_app_aux. admit. admit.
simpl. econstructor. inversion_clear H4. assumption.
econstructor. intuition. 
split. 
intuition.  
inversion H10; subst.
apply d_subseq_trans with 
((StateMap.Raw.map2 option_app
[(c,(@kron (2^(s1-s2)) (2^(s1-s2)) (2^(e2-s1))
(2^(e2-s1)) (QInit_fun s e q) rho1) )] x1)).
apply d_subseq_map2.
simpl. split. reflexivity. split.
apply q_subseq_trans with ((@QInit_fun s2 e2 s e 
(@kron (2^(s1-s2)) (2^(s1-s2)) (2^(e2-s1))
(2^(e2-s1)) q rho1))).
apply QInit_fun_sub. intuition. intuition.
apply q_subseq_eq. 
apply QInit_fun_kron. 
admit. admit. intuition. intuition.
apply (rule_three s2 e2 s2 s1 s1 e2 x x0 (QInit_fun s e q) rho1).
econstructor; reflexivity.  intuition. assumption. 
apply d_subseq_trans with 
((StateMap.Raw.map2 option_app
[(c,(@kron (2^(s0-s2))
(2^(s0-s2)) (2^(e2-s0)) (2^(e2-s0))  rho1 (QInit_fun s e q) ) )] x1)).
apply d_subseq_map2.
simpl. split. reflexivity. split.
apply q_subseq_trans with ((@QInit_fun s2 e2 s e 
(@kron (2^(s0-s2))
 (2^(s0-s2)) (2^(e2-s0)) (2^(e2-s0))  rho1 q ))).
apply QInit_fun_sub. intuition. intuition.
apply q_subseq_eq. admit. 
 intuition. intuition.
apply (rule_three s2 e2 s0 e2 s2 s0 x x0 (QInit_fun s e q) rho1).
econstructor; reflexivity.  intuition. assumption. 
}

--induction mu1; intros.
{inversion  H0; subst. 
 exists nil. exists nil. exists nil.
 split. econstructor. destruct H4. }
 {destruct a. inversion H0; subst. clear H0.
  destruct mu. simpl in H1. intuition.
  destruct p. inversion H; subst. simpl in H1.
  destruct H1; subst.
  apply inj_pair2_eq_dec in H6.
  apply inj_pair2_eq_dec in H6.
  subst. 
assert(exists
(mu1' : list (cstate * qstate s0 e0)) 
(mu2' : list (cstate * qstate s1 e1)) 
(mu'' : list  (cstate * qstate s2 e2)),
(and (ceval_single (QUnit_One s e U) mu1 mu1') 
 (State_eval_dstate F mu2' /\
 d_combin mu1' mu2' mu'' /\ d_subseq mu'1 mu''))).
apply (IHmu1 _ _ _ _ _ _ _ H15 H11). intuition.
assumption. assumption.  admit.
destruct H0. destruct H0. destruct H0.
exists (StateMap.Raw.map2 option_app 
[(c,(QUnit_One_fun s e U q))] x).
exists (StateMap.Raw.map2 option_app 
[(c,rho1)] x0).
assert(exists (mu'': list (cstate *qstate s2 e2)),
d_combin
(StateMap.Raw.map2 option_app
[(c,(QUnit_One_fun s e U q))] x)
(StateMap.Raw.map2 option_app
[(c,rho1)]  x0) mu'').
apply (rule_6 _ s2 e2 s0 e0 s1 e1 _ _ 
 (@kron (2^(e0-s0)) (2^(e0-s0)) (2^(e1-s1))
 (2^(e1-s1)) (QUnit_One_fun s e U q) rho1)_ _ x1).
  admit. intuition. 
 destruct H5. exists x2. 
split. apply E_Qunit_One.  
simpl in H2. admit.  intuition.
intuition.
split. admit. 
split. 
intuition. 
apply d_subseq_trans with 
((StateMap.Raw.map2 option_app
[(c,(@kron (2^(e0-s0)) (2^(e0-s0)) (2^(e1-s1))
(2^(e1-s1)) (QUnit_One_fun s e U q) rho1) )] x1)).
apply d_subseq_map2.
simpl. split. reflexivity. split. 
admit. intuition. intuition. 
apply (rule_three s2 e2 s0 e0 s1 e1 x x0 (QUnit_One_fun s e U q) rho1).
admit. intuition. assumption. 
apply Nat.eq_dec. apply Nat.eq_dec. }

--induction mu1; intros.
{inversion  H0; subst. 
 exists nil. exists nil. exists nil.
 split. econstructor. destruct H4. }
 {destruct a. inversion H0; subst. clear H0.
  destruct mu. simpl in H1. intuition.
  destruct p. inversion H; subst. simpl in H1.
  destruct H1; subst.
  apply inj_pair2_eq_dec in H9.
  apply inj_pair2_eq_dec in H9.
  subst. 
assert(exists
(mu1' : list (cstate * qstate s2 e2)) 
(mu2' : list (cstate * qstate s3 e3)) 
(mu'' : list  (cstate * qstate s e)),
(and (ceval_single (QUnit_Ctrl s0 e0 s1 e1 U) mu1 mu1') 
 (State_eval_dstate F mu2' /\
 d_combin mu1' mu2' mu'' /\ d_subseq mu'1 mu''))).
apply (IHmu1 _ _ _ _ _ _ _ H17 H11). intuition.
assumption. assumption. admit. 
destruct H0. destruct H0. destruct H0.
exists (StateMap.Raw.map2 option_app 
[(c,(QUnit_Ctrl_fun s0 e0 s1 e1 U q))] x).
exists (StateMap.Raw.map2 option_app 
[(c,rho1)] x0).
assert(exists (mu'': list (cstate *qstate s e)),
d_combin
(StateMap.Raw.map2 option_app
[(c,(QUnit_Ctrl_fun s0 e0 s1 e1 U q))] x)
(StateMap.Raw.map2 option_app
[(c,rho1)]  x0) mu'').
apply (rule_6 _ s e s2 e2 s3 e3 _ _ 
 (@kron (2^(e2-s2)) (2^(e2-s2)) (2^(e3-s3))
 (2^(e3-s3)) (QUnit_Ctrl_fun s0 e0 s1 e1 U q)
  rho1)_ _ x1).
  admit. intuition. 
 destruct H5. exists x2. 
split. apply E_QUnit_Ctrl.  
simpl in H2. admit.  intuition.
intuition.
split. admit.
split. 
intuition. 
apply d_subseq_trans with 
((StateMap.Raw.map2 option_app
[(c,(@kron (2^(e2-s2)) (2^(e2-s2)) (2^(e3-s3))
(2^(e3-s3)) (QUnit_Ctrl_fun s0 e0 s1 e1 U q) rho1) )] x1)).
apply d_subseq_map2.
simpl. split. reflexivity.
split.
admit. intuition. intuition. 
apply (rule_three s e s2 e2 s3 e3 x x0 (QUnit_Ctrl_fun s0 e0 s1 e1 U q) rho1).
admit. intuition. assumption.
apply Nat.eq_dec. apply Nat.eq_dec. }

--induction mu1; intros.
{inversion  H0; subst. 
 exists nil. exists nil. exists nil.
 split. econstructor. destruct H4. }
 {destruct a. inversion H0; subst. clear H0.
  destruct mu. simpl in H1. intuition.
  destruct p. inversion H; subst. simpl in H1.
  destruct H1; subst.
assert(exists
(mu1' : list (cstate * qstate s0 e0)) 
(mu2' : list (cstate * qstate s1 e1)) 
(mu'' : list  (cstate * qstate s2 e2)),
(and (ceval_single (QMeas i s e ) mu1 mu1') 
 (State_eval_dstate F mu2' /\
 d_combin mu1' mu2' mu'' /\ d_subseq mu'1 mu''))).
apply (IHmu1 _ _ _ _ _ _ _ H14 H11). intuition.
assumption. assumption. admit. 
destruct H0. destruct H0. destruct H0.
exists (StateMap.Raw.map2 option_app 
(big_app (fun j : nat => [(c_update i j c, QMeas_fun s e j q)])
          (2 ^ (e - s))) x).
exists (StateMap.Raw.map2 option_app 
(big_app (fun j : nat => [(c_update i j c, rho1)])
          (2 ^ (e - s))) x0).
assert(exists (mu'': list (cstate *qstate s2 e2)),
d_combin
(StateMap.Raw.map2 option_app
(big_app (fun j : nat => [(c_update i j c, QMeas_fun s e j q)])
          (2 ^ (e - s))) x)
(StateMap.Raw.map2 option_app
(big_app (fun j : nat => [(c_update i j c, rho1)])
(2 ^ (e - s))) x0) mu'').
apply (rule_7 s2 e2 s0 e0 s1 e1 _ _  _ _
 x1 (big_app
(fun j : nat =>
 [(c_update i j c, @kron (2^(e0-s0)) (2^(e0-s0)) (2^(e1-s1))
 (2^(e1-s1)) (QMeas_fun s e j q) rho1 )])
(2 ^ (e - s))) ). 
  admit. intuition. 
 destruct H5. exists x2. 
split. apply E_Meas.   
simpl in H2. admit.  intuition.
split. admit.
split. 
intuition. 
apply d_subseq_trans with 
((StateMap.Raw.map2 option_app
(big_app
(fun j : nat =>
 [(c_update i j c, @kron (2^(e0-s0)) (2^(e0-s0)) (2^(e1-s1))
 (2^(e1-s1)) (QMeas_fun s e j q) rho1 )])
(2 ^ (e - s))) x1)).
apply d_subseq_map2. 
admit. intuition. 
apply (rule_for s2 e2 s0 e0 s1 e1 x (big_app (fun j : nat => [(c_update i j c, QMeas_fun s e j q)])
(2 ^ (e - s))) x0 (big_app (fun j : nat => [(c_update i j c, rho1)]) (2 ^ (e - s)))).
admit. intuition. assumption. }
Admitted.

 *)


(* Lemma QExp_eval_sub: forall (qs: QExp) s e c (q q': qstate s e) ,
q_subseq q q'->
State_eval qs (c, q')->
State_eval qs (c, q).
Proof. Admitted.



Lemma QExp_eval_sub: forall F s e c (q q': qstate s e) ,
q_subseq q q'->
State_eval F (c, q')->
State_eval F (c, q).
Proof. induction F; intros.
       apply state_eq_Pure with (c,q').
       reflexivity. intuition.
       inversion_clear H.
       subst. intuition.
       destruct H1.  subst.
       induction qs.
       simpl in H0. 
       simpl.  
       split. intuition.
       split. intuition.
       split. intuition.
       rewrite <-PMtrace_scale in *.
       rewrite PMtrace_plus in *.
       rewrite Mscale_plus_distr_r in *.
       destruct H0. destruct H0.
       destruct H1. 
       admit. lia. lia.
       

      



Lemma State_eval_sub: forall s e (mu mu': list (state s e)) F,
d_subseq mu mu'->
State_eval_dstate F mu'->
State_eval_dstate F mu.
Proof. induction mu.  intros. destruct mu'.
       simpl in H0. destruct H0.
       simpl in H. destruct H.
       intros. destruct mu'.
       destruct a.
       simpl in H. destruct H.
       destruct mu; destruct mu';
       destruct a; destruct s0.
       simpl in H. 
       simpl. econstructor.
       inversion_clear H0.
       admit. 
       
       econstructor.

       simpl in H. intuition.
       destruct s1.
       simpl in H. intuition.
       simpl. econstructor.
       admit.
       apply IHmu with (s2 :: mu').
       destruct s1. destruct s2.
       simpl in H. econstructor. intuition.
       split. intuition. intuition.
       inversion_clear H0. intuition.   
 Admitted. *)







(* Lemma QExp_eval_pure: forall qs s e c (q: qstate s e) ,
QExp_eval qs (c, q)->
exists (p:R) (φ: Vector (2^((snd (Free_QExp' qs))-(fst (Free_QExp' qs))))),
p .* (@PMpar_trace s e q ((fst (Free_QExp' qs))) (((snd (Free_QExp' qs)))) )
= φ  × φ†.
Proof. induction qs; intros. 
       simpl in H. 
       exists ((R1 / Cmod (@trace (2^(e0-s0)) q))%R).
       exists v.
       simpl. 
       rewrite PMtrace_scale.
       unfold outer_product in H.
       intuition.
       simpl QExp_eval in H.  
       destruct H. 
       destruct H0.
       apply IHqs1 in H0.
       apply IHqs2 in H1.
       destruct H0.
       destruct H0.
       destruct H1.
       destruct H1.
Admitted. *)








(* Lemma Mixed_pure: forall {n:nat} (ρ1 ρ2: Density n), 
Mixed_State ρ1 ->
Mixed_State ρ2 ->

Par_Pure_State (ρ1 .+  ρ2) ->
exists (p1 p2:R),  and ( and (0<p1)%R  (0<p2)%R) 
(ρ1 = p1 .* (ρ1 .+  ρ2) 
/\ ρ2 = p2 .* (ρ1 .+  ρ2)) .
Proof. 
Admitted. *)








(* Lemma seman_eq_two{s e:nat}: forall F1 F2  c (q:qstate s e),
Considered_Formula (F1 ⊙ F2) ->
WF_qstate q->
State_eval (F1 ⊙ F2) (c, q) -> 
exists 
(q1:qstate (fst (Free_State F1)) (snd (Free_State F1)))
(q2:qstate (fst (Free_State F2)) (snd (Free_State F2))), 
and (WF_qstate q1  /\ WF_qstate q2)
 ((s<= (fst (Free_State (F1 ⊙ F2))) /\ (snd (Free_State (F1 ⊙ F2))) <=e)
/\ ((State_eval F1 (c, q1) /\ State_eval F2 (c, q2))  /\
(q_combin q1 q2 (@PMpar_trace s e q (fst (Free_State (F1 ⊙ F2))) (snd (Free_State (F1 ⊙ F2))))))).
Proof. intros F1 F2 c q H Hw. 
       exists ((C1/ (@trace (2^(e-s)) q) .* (PMpar_trace q (fst (Free_State F1)) (snd (Free_State F1))))).
       exists (PMpar_trace q (fst (Free_State F2)) (snd (Free_State F2))).
       split. 
       split. rewrite <-(Ptrace_trace _ _  _ ((fst (Free_State F1)))
       ((snd (Free_State F1)))).
       unfold WF_qstate.
       split. admit.
       apply Considered_Formula_dom.
       apply H.  admit. apply WF_Mixed. apply Hw.
       apply WF_par_trace.
       admit. assumption.
       split. admit.
       split. admit.
       simpl in H. 
       destruct H. destruct H1. 
       destruct H2.
       simpl. 
       pose H2.
       rewrite <-Nat.eqb_eq in e0.
       rewrite e0. simpl. rewrite H2.
       (* assert((PMpar_trace q (fst (Free_State F1)) (fst (Free_State F2))) = 
              PMpar_trace (PMpar_trace q (fst (Free_State F1)) (snd (Free_State F2))) (fst (Free_State F1)) (fst (Free_State F2))). *)
       rewrite  <-(PMpar_trace_assoc _ (fst (Free_State F1)) (snd (Free_State F2)) (fst (Free_State F1)) (fst (Free_State F2))).
       rewrite  <-(PMpar_trace_assoc _ (fst (Free_State F1)) (snd (Free_State F2)) (fst (Free_State F2)) (snd (Free_State F2))).
       remember ((fst (Free_State F1))) as s'.
       remember ((fst (Free_State F2))) as x.
       remember ((snd (Free_State F2))) as e'.
       remember (PMpar_trace q s' e').
       assert((@trace (2^(e'-s')) q0) .* q0 =
       @kron (2^(x-s')) (2^(x-s')) (2^(e'-x))  (2^(e'-x)) (PMpar_trace q0 s' x) (PMpar_trace q0 x e') ).
       apply Odot_Sepear'. 
       rewrite Heqs'. rewrite Heqx. rewrite Heqe'.
       split. rewrite <-Heqx. rewrite<- H2.
       apply Considered_Formula_dom. apply H.
       apply Considered_Formula_dom. apply H1.
       rewrite Heqq0. apply WF_par_trace.
       rewrite Heqs'. rewrite Heqe'.
       admit. assumption. 
       admit.  
       assert( q0 =@kron (2^(x-s')) (2^(x-s')) (2^(e'-x))  (2^(e'-x)) (C1 / (@trace (2^(e'-s')) q0) .* (PMpar_trace q0 s' x)) (PMpar_trace q0 x e') ).
       rewrite Mscale_kron_dist_l.
       rewrite <-H3.
       rewrite Cdiv_unfold.
       rewrite Cmult_1_l.
       rewrite Mscale_assoc.
       rewrite Cinv_l.
       rewrite Mscale_1_l.
       reflexivity.
       admit. 
       assert((@trace (2^(e'-s')) q0) = (@trace (2^(e-s)) q)).
       rewrite Heqq0. 
       rewrite Ptrace_trace.
       reflexivity. 
       rewrite Heqs'. rewrite Heqe'. admit. 
       apply WF_Mixed. apply Hw.
       rewrite <-H5.
       remember ((C1 / (@trace (2^(e'-s')) q0) .* (PMpar_trace q0 s' x))).
       remember ((PMpar_trace q0 x e')).
       rewrite H4.
       apply combin_l; try reflexivity.

       split. admit.
       split. rewrite <-H2. apply Considered_Formula_dom.
       assumption.
       split. apply Considered_Formula_dom. 
       assumption. intuition. admit.

       split. admit.
       split. intuition. 
       split. rewrite<-H2. apply Considered_Formula_dom.
       assumption.
       split. apply Considered_Formula_dom. assumption.
       admit.

      
Admitted.


Lemma seman_eq_two'{s e:nat}: forall F1 F2  c (q:qstate s e),
Considered_Formula (F1 ⊙ F2) ->
@WF_Matrix  (2^(e-s)) (2^(e-s)) q->
(exists (s0 e0 s1 e1 s2 e2: nat)
(q1:qstate s0 e0)
(q2:qstate s1 e1), and (s<=s2 /\ e2 <= e)
( (State_eval F1 (c, q1) /\ State_eval F2 (c, q2))  /\
(q_combin q1 q2 (@PMpar_trace s e q s2 e2)))) 
-> State_eval (F1 ⊙ F2) (c, q).
Proof. intros.  
       destruct H1.
       destruct H1.
       destruct H1.
       destruct H1.
       destruct H1.
       destruct H1.
       destruct H1.
       destruct H1.
       destruct H1.
       destruct H2.
       inversion H3; subst.

       simpl. split. 
       admit.

       split.
       rewrite (State_free_eval _ _ x3 x1).
       simpl. 
       assert(PMpar_trace q x3 x1 = 
       PMpar_trace (PMpar_trace q x3 x4) x3 x1).
       rewrite PMpar_trace_assoc.
       reflexivity. admit.
       rewrite H5.
       rewrite PMpar_trace_L.
       rewrite <-H4.
       rewrite (PMpar_trace_l x1 x5 x6).
      admit.
      admit. admit.
      rewrite H4.  admit.
      reflexivity.
      admit. admit.
      admit.
      admit.
      admit.

      rewrite (State_free_eval _ _ x1 x4).
      simpl. 
      assert(PMpar_trace q x1 x4 = 
      PMpar_trace (PMpar_trace q x3 x4) x1 x4).
      rewrite PMpar_trace_assoc.
      reflexivity. admit.
      rewrite H5.
      rewrite PMpar_trace_R.
      rewrite <-H4.
      rewrite (PMpar_trace_r x1 x5 x6).
     admit.
     admit. admit.
     rewrite H4.  admit.
     reflexivity. reflexivity.
     admit. admit.
     admit.
     admit.
     

     simpl. split. 
       admit.

       split.
       rewrite (State_free_eval _ _ x x4).
       simpl. 
       assert(PMpar_trace q x x4 = 
       PMpar_trace (PMpar_trace q x3 x4) x x4).
       rewrite PMpar_trace_assoc.
       reflexivity. admit.
       rewrite H5.
       rewrite PMpar_trace_R.
       rewrite <-H4.
       rewrite (PMpar_trace_r x x6 x5).
      admit.
      admit. admit.
      rewrite H4.  admit.
      reflexivity. reflexivity.
      admit. admit.
      admit.
      admit.

      rewrite (State_free_eval _ _ x3 x).
      simpl. 
      assert(PMpar_trace q x3 x = 
      PMpar_trace (PMpar_trace q x3 x4) x3 x).
      rewrite PMpar_trace_assoc.
      reflexivity. admit.
      rewrite H5.
      rewrite PMpar_trace_L.
      rewrite <-H4.
      rewrite (PMpar_trace_l x x6 x5).
     admit.
     admit. admit.
     rewrite H4.  admit.
     reflexivity. 
     admit. admit.
     admit.
     admit.
     admit.
Admitted.



Lemma seman_eq_three{s e:nat}: forall  (mu: list (cstate * qstate s e)) F1 F2,
WF_dstate_aux mu ->
Considered_Formula (F1 ⊙ F2) ->
State_eval_dstate (F1 ⊙ F2) mu -> 
exists 
(mu0:list(cstate * qstate (fst (Free_State F1)) (snd (Free_State F1)))) 
(mu1:list(cstate * qstate (fst (Free_State F2)) (snd (Free_State F2)))),
 and  (WF_dstate_aux mu0 /\ WF_dstate_aux mu1)
 (and (s<= (fst (Free_State (F1 ⊙ F2))) /\ (snd (Free_State (F1 ⊙ F2))) <=e)
 ((d_combin mu0 mu1 (d_par_trace mu (fst (Free_State (F1 ⊙ F2))) (snd (Free_State (F1 ⊙ F2)))))
  /\ ((State_eval_dstate F1 mu0 /\ State_eval_dstate F2 mu1)))).
Proof. induction mu;  intros F1 F2 Hw; intros.
       destruct H0.
       destruct mu. 
       inversion H0; subst.
       destruct a.
       apply seman_eq_two in H3.
       destruct H3.  destruct H1.
       destruct H1. destruct H1.
       exists [(c,x)]. exists [(c,x0)].
       split. split. 
       apply WF_state_dstate_aux. 
       apply H1. apply WF_state_dstate_aux.
       apply H3. 
       split. intuition.  
       split. econstructor. intuition.
       econstructor. simpl. intuition. 
       intuition. inversion_clear Hw. intuition. 
        assert(exists
        (mu0 : list
                 (cstate *
                  qstate (fst (Free_State F1))
                    (snd (Free_State F1)))) 
      (mu1 : list
               (cstate *
                qstate (fst (Free_State F2)) (snd (Free_State F2)))),
         and ( WF_dstate_aux mu0 /\ WF_dstate_aux mu1)
        (and (s <= fst (Free_State (F1 ⊙ F2)) /\
          snd (Free_State (F1 ⊙ F2)) <= e) 
         (d_combin mu0 mu1
           (d_par_trace (p :: mu) (fst (Free_State (F1 ⊙ F2)))
              (snd (Free_State (F1 ⊙ F2)))) /\
         State_eval_dstate F1 mu0 /\ State_eval_dstate F2 mu1))).
       apply IHmu. inversion_clear Hw. assumption. intuition. inversion_clear H0.
       apply State_eval_dstate_Forall. discriminate.
       intuition.
       destruct H1. destruct H1.
       destruct H1. 
       destruct a. destruct p. 
       assert(exists 
       (q1:qstate (fst (Free_State F1)) (snd (Free_State F1)))
       (q2:qstate (fst (Free_State F2)) (snd (Free_State F2))), 
       and (WF_qstate q1 /\ WF_qstate q2)
        ((s<= (fst (Free_State (F1 ⊙ F2))) /\ (snd (Free_State (F1 ⊙ F2))) <=e)
       /\ ((State_eval F1 (c, q1) /\ State_eval F2 (c, q2))  /\
       (q_combin q1 q2 (@PMpar_trace s e q (fst (Free_State (F1 ⊙ F2))) (snd (Free_State (F1 ⊙ F2)))))))).
       apply seman_eq_two. intuition.
       inversion_clear Hw. intuition.
       inversion_clear H0. intuition.
       destruct H3. destruct H3.
       destruct H3. 
       exists ((c,x1)::x). exists ((c,x2)::x0).
       split. split. econstructor.
       intuition. intuition.
       admit.
       econstructor. intuition.
       intuition. 
       admit.
       split. intuition. 
       split. econstructor.  intuition.
       apply H2. 
       split. econstructor. intuition.
       destruct x. econstructor.
       apply H2. econstructor. intuition.
       destruct x0. econstructor. 
       apply H2. 
Admitted.










Lemma seman_eq_three'{s e:nat}: forall  (mu: list (cstate * qstate s e)) F1 F2,
WF_Matrix_dstate mu ->
Considered_Formula (F1 ⊙ F2) ->
(exists (s0 e0 s1 e1 s2 e2: nat)
(mu0:list(cstate * qstate s0 e0)) 
(mu1:list(cstate * qstate s1 e1)),
 (and (s<= s2 /\ e2 <=e)
 ((d_combin mu0 mu1 (d_par_trace mu s2 e2))
  /\ ((State_eval_dstate F1 mu0 /\ State_eval_dstate F2 mu1)))))
  -> State_eval_dstate (F1 ⊙ F2) mu.
Proof.
       
induction mu;  intros F1 F2 Hw; intros.
destruct H0. 
destruct H0. 
destruct H0. destruct H0.
destruct H0. destruct H0.
destruct H0. destruct H0.
destruct H0. 
destruct H1. inversion H1; subst.
destruct H2. destruct H2.
destruct H0. destruct H0.
destruct H0. destruct H0.
destruct H0. destruct H0.
destruct H0. destruct H0.
destruct H0.  destruct H1.
destruct mu. 
destruct a.  inversion H1; subst.
simpl d_par_trace in *.
inversion H9; subst. 
econstructor.
apply seman_eq_two'.
intuition. simpl in Hw. intuition.  
exists x. exists x0.
exists x1. exists x2.
exists x3. exists x4.
exists rho0. exists rho1.
split. intuition.
destruct H2. inversion_clear H2.
inversion_clear H3.
split. intuition. intuition. econstructor.
destruct a. destruct p.  
inversion H1; subst. clear H1.
inversion H9; subst. clear H9.
econstructor.
apply seman_eq_two'.
intuition. simpl in Hw. intuition. 
exists x. exists x0.
exists x1. exists x2.
exists x3. exists x4.
exists rho0. exists rho1.
split. intuition.
destruct H2. inversion_clear H1.
inversion_clear H2.
split. intuition. intuition.
apply IHmu.
simpl in Hw. simpl. intuition.
intuition.
exists x. exists x0.
exists x1. exists x2.
exists x3. exists x4.
exists ((c0,rho2)::mu2).
exists ((c0,rho3)::mu3).
split. intuition. 
split. econstructor. intuition.
intuition. 
destruct H2. inversion_clear H1.
inversion_clear H2.
split. intuition. intuition. 
Qed.







Lemma QExp_eval_sub: forall (qs: QExp) s e c (q q': qstate s e) ,
WF_qstate q ->
WF_qstate q'->
q_subseq q q'->
State_eval qs (c, q')->
State_eval qs (c, q).
Proof. induction qs; intros.
      inversion_clear H1. subst. intuition.
      destruct H3. subst.
      simpl in *.  
      split. intuition.
      split. intuition.
      split. intuition.
      rewrite <-PMtrace_scale in *.
      rewrite PMtrace_plus in *.
      rewrite Mscale_plus_distr_r in *.
      destruct H2. destruct H2.
      destruct H3. unfold outer_product in H4.
      remember ((R1 / Cmod (trace (q .+ x)))%R .* PMpar_trace q s e).
      remember ((R1 / Cmod (trace (q .+ x)))%R .* PMpar_trace x s e).
      apply (ParDensityO.Mixed_pure m m0) in H4.
      destruct H4. destruct H4. 
      subst. destruct H4.   
      admit. rewrite Heqm.
      apply Mixed_State_scale.   admit.
      admit. rewrite Heqm0.
      apply Mixed_State_scale.   admit.
      admit. 
      rewrite Heqm. rewrite Heqm0.
      rewrite <-Mscale_plus_distr_r.
      rewrite <-PMtrace_plus.
      rewrite <-(Ptrace_trace s0 e0 (q .+ x) s e).
      apply Mixed_State_aux_to01. admit.
      intuition. apply WF_Mixed. apply H0.
      admit. 
      simpl in *.
      split. intuition.
      split. apply IHqs1 with (q').
     intuition. intuition. intuition.
     intuition.
     apply IHqs2 with q'.
     intuition. intuition.
     intuition. intuition.
Admitted.

Lemma State_eval_sub: forall F s e c (q q': qstate s e) ,
WF_qstate q ->
WF_qstate q' ->
q_subseq q q'->
State_eval F (c, q')->
State_eval F (c, q).
Proof. induction F; intros.
       apply state_eq_Pure with (c,q').
       reflexivity. intuition.
       apply QExp_eval_sub with q'.
       intuition. intuition. intuition.
       intuition.
       simpl in *.
       split. intuition.
       split. apply IHF1 with (q').
      intuition. intuition. intuition.
      intuition.
      apply IHF2 with q'.
      intuition. intuition. intuition.
      intuition.
      simpl in *.
       split. apply IHF1 with (q').
      intuition. intuition.
      intuition. intuition.
      apply IHF2 with q'.
      intuition. intuition.
      intuition. intuition.
Qed.



Lemma State_eval_sub': forall s e (mu mu': list (state s e)) F,
WF_dstate_aux mu ->
WF_dstate_aux mu'->
d_subseq mu mu'->
State_eval_dstate F mu'->
State_eval_dstate F mu.
Proof.
induction mu.  intros. destruct mu'.
       destruct H2.
       simpl in H1. destruct H1.  
       intros. destruct mu'.
       destruct a.
       simpl in H1. destruct H1.
       destruct mu; destruct mu';
       destruct a; destruct s0.
       simpl in H1. 
       simpl. econstructor.
       inversion_clear H2.
       apply State_eval_sub with q0.
       inversion_clear H. intuition.
       inversion_clear H0. intuition.
       intuition. destruct H1. subst.
       intuition. 
       
       econstructor.

       simpl in H1. intuition.
       destruct s1.
       simpl in H1. intuition.
       simpl. econstructor.
       destruct H1. subst.
       apply State_eval_sub with q0.
       inversion_clear H. intuition.
       inversion_clear H0. intuition.
       intuition. 
       inversion_clear H2. intuition.
       apply IHmu with (s2 :: mu').
       inversion_clear H. assumption.
       inversion_clear H0. assumption.
       simpl in H1. intuition.
       destruct s1. destruct s2.
       simpl in H2. 
       inversion_clear H2. intuition.
Qed.

(* Lemma State_eval_combin: forall s e (mu:list(cstate * qstate s e)) (F1 F2:State_formula),
(exists s0 e0 s1 e1 (mu0:list(cstate * qstate s0 e0)) (mu1:list(cstate * qstate s1 e1)), 
and (d_combin mu0 mu1 mu ) 
((State_eval_dstate F1 mu0 /\ State_eval_dstate F2 mu1)))
-> State_eval_dstate (F1 ⊙ F2) mu.
Proof. 
induction mu; intros. destruct H. destruct H.
destruct H. destruct H. destruct H.
destruct H. destruct H. inversion H; subst.
destruct H0. destruct H0.

simpl. 
econstructor.

Admitted. *) *)


       



(* 
Lemma rule':  forall c (F1 F2:State_formula),
(forall (s e : nat) (mu mu' : dstate s e),
ceval c mu mu' -> sat_Assert mu F1 -> sat_Assert mu' F2)
->
(forall (s0 e0 : nat) (mu0 mu'0 : list (cstate * qstate s0 e0)),
Sorted (StateMap.Raw.PX.ltk (elt:=qstate s0 e0)) mu0->
WF_dstate_aux mu0 ->
ceval_single c mu0 mu'0 ->
State_eval_dstate F1 mu0 -> State_eval_dstate F2 mu'0).
Proof. intros.   
       assert(Sorted (StateMap.Raw.PX.ltk (elt:=qstate s0 e0)) mu'0
       ).
       apply ceval_sorted with c mu0.
       assumption.
       assumption.
       assert(sat_Assert (StateMap.Build_slist H4) F2).
       apply H with (StateMap.Build_slist H0).
       econstructor.
       intuition.
       apply WF_ceval with c mu0.
        intuition. intuition.
        intuition.
        rewrite sat_Assert_to_State.
        econstructor.
        assumption.
        assumption.
        rewrite sat_Assert_to_State in H5.
        inversion_clear H5.
        assumption.
Qed.




 *)







      


        




(* Theorem rule_qframe_aux: forall (c : com) (F1 F2 F3 : State_formula)
(s e : nat) ( mu mu' :list (cstate *qstate s e)),
Considered_Formula ((F1 ⊙ F3))->
Considered_Formula ((F2 ⊙ F3))->
Sorted (StateMap.Raw.PX.ltk (elt:=qstate s e)) mu->
WF_dstate_aux mu ->
(forall (s e : nat) (mu mu' : dstate s e),
    ceval c mu mu' -> sat_Assert mu F1 -> sat_Assert mu' F2)->
NSet.inter (fst (Free_state F3)) (fst (MVar c)) = NSet.empty ->
NSet.Subset (snd (MVar c)) (Qsys_to_Set (fst (Free_State F1))  (snd  (Free_State F1)) ) ->
ceval_single c mu mu' ->
State_eval_dstate (F1 ⊙ F3) mu ->
State_eval_dstate (F2 ⊙ F3) mu'.
Proof.  induction mu; intros mu' Hc1 Hc2 Hs Hw; intros.
         simpl in *. destruct H3.
       inversion_clear H3. destruct mu.
       destruct a. 
       apply (ceval_4  c _ _ _ mu') in Hs.
       destruct Hs. destruct H3. destruct H3.
       destruct H6. inversion H6; subst. 
       rewrite map2_nil_r.
       apply seman_eq_two in H4.
       remember ((PMpar_trace q (fst (Free_State (F1 ⊙ F3)))
       (snd (Free_State (F1 ⊙ F3))))).
       remember (d_par_trace x (fst (Free_State (F1 ⊙ F3)))
       (snd (Free_State (F1 ⊙ F3)))).
       destruct H4. destruct H4. destruct H4.
       assert(exists
       (mu1' : list (cstate * qstate (fst (Free_State F1))
       (snd (Free_State F1)))) 
     (mu2' : list (cstate * qstate (fst (Free_State F3))
     (snd (Free_State F3)))) 
     (mu'' : list (cstate * qstate (fst (Free_State (F1 ⊙ F3)))
     (snd (Free_State (F1 ⊙ F3))))),
       and (ceval_single c [(c0,x0)] mu1')
       (State_eval_dstate F3 mu2' /\
       d_combin mu1' mu2' mu'' /\ d_subseq l mu'')).
       apply rule_two with [(c0,x1)] [(c0, q0)] [(c0, q0)].
       rewrite Heql. 
       rewrite Heqq0.
       assert([(c0,
       PMpar_trace q (fst (Free_State (F1 ⊙ F3)))
         (snd (Free_State (F1 ⊙ F3))))]=
      d_par_trace [(c0, q)] (fst (Free_State (F1 ⊙ F3)))
      (snd (Free_State (F1 ⊙ F3)))).
      reflexivity. rewrite H8.
       apply Par_trace_ceval_swap.
       split. intuition.
       split. apply Considered_Formula_dom.
       assumption. intuition.
       apply subset_trans with (Qsys_to_Set (fst (Free_State F1)) (snd (Free_State F1))).
       assumption.
       admit. admit.
       intuition.
       econstructor. intuition.
      econstructor. apply d_subseq_eq.
      reflexivity. assumption.
      assumption.
      econstructor. intuition. econstructor.
      destruct H8. destruct H8. destruct H8.
      assert(State_eval_dstate (F2 ⊙ F3) l).
      apply State_eval_sub' with x4.
      admit. admit. 
      intuition. apply seman_eq_three'.
      admit.
      intuition. 
      exists  (fst (Free_State F1)).
      exists  (snd (Free_State F1)).
      exists (fst (Free_State F3)).
      exists  (snd (Free_State F3)).
      exists (fst (Free_State (F1 ⊙ F3))).
      exists (snd (Free_State (F1 ⊙ F3))).
      (* exists (fst (Free_State F1)). exists (snd (Free_State F1)).
       exists (fst (Free_State (F3))). exists (snd (Free_State (F3))). *)
      exists x2. exists x3. split. intuition.
      split. 
      rewrite (d_par_trace_refl ((fst (Free_State (F1 ⊙ F3))))  ((snd (Free_State (F1 ⊙ F3)))) x4).
      intuition. intuition. admit.
      split. 
     
      apply rule' with c F1 [(c0, x0)].
      intros. apply H with mu. intuition.
      assumption.
      apply Sorted_cons.
      apply Sorted_nil. apply HdRel_nil.
      admit. intuition. 
      econstructor. intuition.
      econstructor.
       intuition.
       
      apply (State_dstate_free_eval 
      _ _ (fst (Free_State (F1 ⊙ F3))) (snd (Free_State (F1 ⊙ F3)))).
      split. intuition.
      split. apply Considered_Formula_dom.
      assumption. intuition.
      admit. admit. subst. apply H9.
      intuition. intuition. 
      destruct a. destruct p.  
      inversion Hs; subst.
       apply (ceval_4  c _ _ _ mu') in Hs.
       destruct Hs. destruct H3. destruct H3.
       destruct H6. subst. 
       apply seman_eq_two in H4.
       remember ((PMpar_trace q (fst (Free_State (F1 ⊙ F3)))
       (snd (Free_State (F1 ⊙ F3))))).
       remember ((d_par_trace x (fst (Free_State (F1 ⊙ F3)))
       (snd (Free_State (F1 ⊙ F3))))). 
       apply d_seman_app_aux.
       apply WF_ceval with c [(c0, q)].
       inversion_clear Hw. apply WF_state_dstate_aux. intuition.
       intuition. 
       apply WF_ceval with c ((c1, q0) :: mu).
       inversion_clear Hw. intuition.
       intuition.
       destruct H4. destruct H4. destruct H4. 
       assert(exists
       (mu1' : list (cstate * qstate (fst (Free_State F1)) (snd (Free_State F1)))) 
     (mu2' : list (cstate * qstate (fst (Free_State F3)) (snd (Free_State F3)))) 
     (mu'' : list (cstate * qstate (fst (Free_State (F1 ⊙ F3)))
     (snd (Free_State (F1 ⊙ F3))))),
       and (ceval_single c [(c0,x1)] mu1' )
       (State_eval_dstate F3 mu2' /\
       d_combin mu1' mu2' mu'' /\ d_subseq l mu'')).
       apply rule_two with [(c0,x2)] [(c0, q1)] [(c0, q1)].
       rewrite Heql. 
       rewrite Heqq1.
       assert([(c0,
       PMpar_trace q (fst (Free_State (F1 ⊙ F3)))
         (snd (Free_State (F1 ⊙ F3))))]=
      d_par_trace [(c0, q)] (fst (Free_State (F1 ⊙ F3)))
      (snd (Free_State (F1 ⊙ F3)))).
      reflexivity. rewrite H10.
       apply Par_trace_ceval_swap.
       split. 
       intuition. split.
       apply Considered_Formula_dom.
       assumption. intuition.
       apply subset_trans with 
       ((Qsys_to_Set (fst (Free_State F1)) (snd (Free_State F1)))).
       assumption.
       admit. admit.
       intuition.
       econstructor. intuition. econstructor. apply d_subseq_eq.
      reflexivity. assumption.
       assumption.
      econstructor. intuition. econstructor.
      assert(State_eval_dstate (F2 ⊙ F3) l).
      destruct H10. destruct H10. destruct H10.
      apply State_eval_sub' with x5.
      admit. admit.
      intuition. apply seman_eq_three'.
      admit.
      intuition. 
      exists (fst (Free_State F1)). exists (snd (Free_State F1)). 
      exists (fst (Free_State F3)). exists (snd (Free_State F3)).
      exists (fst (Free_State (F1 ⊙ F3))).
      exists (snd (Free_State (F1 ⊙ F3))). 
      exists x3. exists x4. split.
      intuition. split.  
      rewrite d_par_trace_refl. 
      intuition. intuition. admit.
      split. 

      apply rule' with c F1 [(c0, x1)].
      intros. apply H with mu0. intuition.
      assumption.
      apply Sorted_cons.
      apply Sorted_nil. apply HdRel_nil.
      admit. intuition. 
      econstructor. intuition.
      econstructor.
       intuition.
      
      apply (State_dstate_free_eval 
      _ _ (fst (Free_State (F1 ⊙ F3))) (snd (Free_State (F1 ⊙ F3)))).
      split. 
      intuition.
      split. apply Considered_Formula_dom.
      assumption.
      intuition.
      admit. 
      admit. subst. intuition. apply IHmu.
      intuition. intuition.
      assumption. inversion_clear Hw.
      assumption. apply H.
      intuition. intuition.
      intuition. apply H5. 
      intuition. intuition.
Admitted.




Theorem rule_qframe: forall (F1 F2 F3: State_formula) c,
         Considered_Formula ((F1 ⊙ F3))->
         Considered_Formula ((F2 ⊙ F3))->
         ({{F1}} c {{F2}}) /\ 
          (NSet.inter (fst (Free_state F3)) (fst (MVar c)) =NSet.empty) 
         /\ NSet.Subset (snd (MVar c)) (snd (Free_state F1))
         ->  {{F1 ⊙ F3}} c {{F2 ⊙ F3}}.
Proof. unfold hoare_triple. intros F1 F2 F3 c. intros Hc1 Hc2 H.
       intros s e (mu ,IHmu) (mu', IHmu');
       intros. inversion_clear H0. simpl in H4.
       rewrite sat_Assert_to_State in *.
       inversion_clear H1. econstructor.
       intuition. simpl in H5. apply rule_qframe_aux with c F1 mu.
       intuition. intuition.  intuition. intuition.
       destruct H. assumption.
       intuition. intuition. assumption.
       assumption.
Qed. *)

              



(* Inductive derivable : Assertion -> com -> Assertion-> Type :=
  | H_Skip : forall D,
      derivable D <{skip}> D
  | H_Asgn : forall D X a,
      derivable (Assn_sub X a D) <{X := a}> D
  | H_Seq : forall P Q R c1 c2,
      derivable Q c2 R -> derivable P c1 Q -> derivable P <{c1;c2}> R
  | H_conseq: forall (P P' Q Q': Assertion) c,
      derivable P' c Q' -> (P ->> P') -> (Q'->> Q) -> derivable P c Q
  | H_conj: forall (F1 F1' F2 F2': State_formula) c,
     derivable F1 c F1' -> derivable F2 c F2' -> derivable (F1 /\ F2) c (F1' /\ F2')
  | H_If: forall (F1 F1' F2 F2': State_formula) (c1 c2:com) (b:bexp) (p:R),
      0<p<1->
     derivable (F1 /\ b) c1 (F1') -> derivable (F2 /\ (BNot b)) c2 (F2')
  -> derivable (APro [(p, (F1 /\ b)) ; ((1 - p), (F2 /\ (BNot b)))])
                <{if b then c1 else c2 end}>
                (APro [(p, F1') ; ((1 - p), F2')])
  |H_while: forall F0 F1 (b:bexp) (c:com),
         derivable (F0 /\ (b)) c (ANpro[(F0 /\ b); (F1/\ (BNot b))])
      -> derivable (ANpro[(F0 /\ b); (F1/\ (BNot b))])
                   <{while b do c end}>
                   (F1 /\ (BNot b))
  | H_sum': forall (nF1 nF2:npro_formula) p_n  c,
                    (Forall (fun x=> x<>0%R) p_n)->
                    length nF1 = length p_n -> 
                    (big_hoare nF1 nF2 c)
        -> derivable (npro_to_pro_formula nF1 p_n) c
                    (npro_to_pro_formula nF2 p_n)
  | H_Init: forall s e , derivable (BTrue) <{( s e ) :Q= 0}> ((QExp_s s e  (Vec (2^(e-s)) 0)))
  | H_QUnit: forall s' e' s e (U: Square (2^(e'-s'))) (v: Vector (2^(e-s))), (s<=s')%nat /\ (e' <=e)%nat ->WF_Matrix v->
             derivable   (QExp_s s  e  (U_v s' e' s e U† v)) (QUnit_One s' e' U) (QExp_s s  e  v)
  | H_QMeas: forall s' e' s e (v: Vector (2^(e-s))) x (P :nat-> (Pure_formula)),
             (s<=s')%nat /\ (e'<=e)%nat->(norm v = 1)%R -> WF_Matrix v->
   derivable ((QExp_s  s  e  v) /\ big_Sand (fun i:nat => (Assn_sub_P x i (P i))) (2^(e'-s')) )
             (QMeas x s' e')
             (big_pOplus (fun i:nat=> (@norm (2^(e-s)) ((U_v s' e' s e (∣ i ⟩_ (e'-s') × ⟨ i ∣_ (e'-s')) v))) ^ 2)%R
   (fun i:nat=> SAnd ((P i))  (QExp_s  s  e ((R1 / ( (@norm (2^(e-s)) ((U_v s' e' s e (∣ i ⟩_ (e'-s') × ⟨ i ∣_ (e'-s')) v)))))%R.* 
   (U_v s' e' s e (∣ i ⟩_ (e'-s') × ⟨ i ∣_ (e'-s')) v)))) (2^(e'-s')))
  | H_Absurd: forall D c, derivable (BFalse) c D
  | H_QFrame: forall (F1 F2 F3: State_formula) c,
  (NSet.inter (fst (Free_state F3)) (fst (MVar c)) = NSet.empty /\
   NSet.Subset (snd (MVar c)) (snd (Free_state F1))) ->
   derivable F1 c F2
  ->derivable (F1 ⊙ F3) c (F2 ⊙ F3).

  (* Theorem rule_qframe: forall c (F1 F2 F3: State_formula) ,
          derivable F1 c F2 ->
         (NSet.inter (fst (Free_state F3)) (fst (MVar c)) =NSet.empty) 
         /\ (NSet.inter (snd (Free_state F3)) (snd (MVar c)) =NSet.empty) 
         ->  {{F1 ⊙ F3}} c {{F2 ⊙ F3}}.
Proof.  unfold hoare_triple. induction c; intros;
        inversion_clear H1.
     --admit.
     --admit.
     -- admit.
     -- admit.
     --inversion H.
       F1 F2 F3 c. intros H.
       intros s e (mu ,IHmu). induction mu; intros (mu', IHmu');
       intros. destruct H. destruct H2.
       inversion_clear H1. inversion_clear H4.
       inversion_clear H1. simpl in H5. destruct H5. 
       constructor. constructor. constructor.
       admit. destruct mu. 
      inversion_clear H0. simpl in H4.
      simpl. inversion_clear H1. 
      inversion_clear H0. inversion_clear H1.
      destruct a.
      inversion H4;subst;   simpl in H5.
        simpl. admit.  admit. inversion H10; subst.
        rewrite map2_nil. rewrite map2_l_refl.
        simpl. admit.
        inversion H12; subst.
        rewrite map2_nil. rewrite map2_l_refl.
        simpl. 
destruct H5. destruct H1.  
destruct H1. destruct H1.
destruct H1. destruct H1. 
destruct H1. inversion H1;subst.
simpl in H.
exists s. exists x1. exists x1. existn.
exists (fst x3, q_update ((I (2 ^ (s' - s)) ⊗ U ⊗ I (2 ^ (x1 - e')))) (snd x3)).
exists (fst x3, q_update (I (2 ^ (e - x1))) (snd x4)).
split. admit. split. admit. split. admit.
split. admit. admit.


exists s. exists x. exists x. existn.
exists((fst x3, q_update ((I (2 ^ (s' - x)) ⊗ U ⊗ I (2 ^ (e - e')))) (snd x3))).
exists ((fst x3, q_update ((I (2 ^ (x - s)))) (snd x4))).

 split.   admit. 
 split. admit. split. admit.
 split. admit. admit. *)



  Theorem  soundness: forall F1 F2 c,
   derivable F1 c F2 -> {{F1}} c {{F2}} .
  Proof. intros. induction H. 
  -- apply rule_skip.
  -- apply QRule_Q_L.rule_assgn.
  --apply rule_seq with Q. assumption. assumption.
  --apply rule_conseq with P' Q'. assumption. assumption. assumption.
  --apply rule_conj. assumption. assumption.
  -- apply rule_cond. assumption. split.  assumption.
      assumption.
  -- apply rule_while. assumption. 
  --apply rule_sum. assumption. assumption. assumption.
  --apply rule_QInit.
  --apply rule_QUnit_One; assumption.
  --apply rule_QMeas; assumption.
  --admit.
  --  unfold hoare_triple. induction c; intros;
  inversion_clear H1.
--admit.
--admit.
-- admit.
-- admit.
  Qed.
  
   *)

(* Theorem rule_qframe: forall (F1 F2 F3: State_formula) c,
         ({{F1}} c {{F2}}) /\  (NSet.inter (fst (Free_state F3)) (fst (MVar c)) =NSet.empty) 
         /\ (NSet.inter (snd (Free_state F3)) (snd (MVar c)) =NSet.empty) 
         ->  {{F1 ⊙ F3}} c {{F2 ⊙ F3}}.
Proof. unfold hoare_triple. intros F1 F2 F3 c. intros H.
       intros s e (mu ,IHmu). induction mu; intros (mu', IHmu');
       intros. destruct H. destruct H2.
       inversion_clear H1. inversion_clear H4.
       inversion_clear H1. simpl in H5. destruct H5. 
       constructor. constructor. constructor.
       admit. destruct mu. 
      inversion_clear H0. simpl in H4.
      simpl. inversion_clear H1. 
      inversion_clear H0. inversion_clear H1.
      destruct a.
      inversion H4;subst;   simpl in H5.
        simpl. admit.  admit. inversion H10; subst.
        rewrite map2_nil. rewrite map2_l_refl.
        simpl. admit.
        inversion H12; subst.
        rewrite map2_nil. rewrite map2_l_refl.
        simpl. 
destruct H5. destruct H1.  
destruct H1. destruct H1.
destruct H1. destruct H1. 
destruct H1. inversion H1;subst.
simpl in H.
exists s. exists x1. exists x1. existn.
exists (fst x3, q_update ((I (2 ^ (s' - s)) ⊗ U ⊗ I (2 ^ (x1 - e')))) (snd x3)).
exists (fst x3, q_update (I (2 ^ (e - x1))) (snd x4)).
split. admit. split. admit. split. admit.
split. admit. admit.


exists s. exists x. exists x. existn.
exists((fst x3, q_update ((I (2 ^ (s' - x)) ⊗ U ⊗ I (2 ^ (e - e')))) (snd x3))).
exists ((fst x3, q_update ((I (2 ^ (x - s)))) (snd x4))).

 split.   admit. 
 split. admit. split. admit.
 split. admit. admit.


 inversion H12; subst.
 rewrite map2_nil. rewrite map2_l_refl.
 simpl.  
destruct H5. destruct H1.  
destruct H1. destruct H1.
destruct H1. destruct H1. 
destruct H1. inversion H1;subst.
simpl in H. admit. admit. admit.









      
Admitted.   *)


(* Theorem rule_qframe_aux: forall (c : com) (F1 F2 F3 : State_formula)
(s e : nat) ( mu mu' :list (cstate *qstate s e)),
(forall (s e : nat) (mu mu' : list (cstate *qstate s e)),
 ceval_single c mu mu' -> State_eval_dstate  F1 mu -> State_eval_dstate  F2 mu')->
NSet.inter (fst (Free_state F3)) (fst (MVar c)) = NSet.empty ->
NSet.Subset (snd (MVar c)) (snd (Free_state F1)) ->
ceval_single c mu mu' ->
State_eval_dstate (F1 ⊙ F3) mu ->
State_eval_dstate (F2 ⊙ F3) mu'.
Proof. induction c; intros.
--admit.
--admit.
--admit.
--admit.
--inversion H2; subst. admit.
   apply IHc2 with F1 mu1.


--assert (ceval_single <{ abort }>
[(fst x3, snd x3)] []). apply E_Abort. 
apply H in H4. simpl in H4. destruct H4. 
simpl. admit.

assert (ceval_single <{ abort }>
[(fst x3, snd x3)] []). apply E_Abort. 
apply H in H4. simpl in H4. destruct H4. 
simpl. admit.

--inversion H8; subst.  rewrite map2_nil. rewrite map2_l_refl.
simpl. exists s. exists x1. exists x1. existn.
exists ((c_update i (aeval (fst x3, snd x3 ) a)
(fst x3), snd x3)). 
exists (c_update i (aeval (fst x3,snd x4) a)
(fst x3), snd x4). split. admit.
split. admit. split. admit. split. 
assert( ceval_single <{ i := a }>
[(fst x3, snd x3)]
(StateMap.Raw.map2 option_app
   [(c_update i
       (aeval (fst x3, snd x3) a)
       (fst x3), snd x3)] [])). apply E_Asgn.
apply E_nil. rewrite map2_nil in H4. rewrite map2_l_refl in H4.
simpl in H4. apply H in H4. simpl in H4. intuition.
simpl. admit.  admit.

inversion H8; subst.  rewrite map2_nil. rewrite map2_l_refl.
simpl. exists x. existn. exists s. exists x.
exists ((c_update i (aeval (fst x3, snd x3 ) a)
(fst x3), snd x3)). 
exists (c_update i (aeval (fst x3,snd x4) a)
(fst x3), snd x4).
 split. admit.
split. admit. split. admit. split. 
assert( ceval_single <{ i := a }>
[(fst x3, snd x3)]
(StateMap.Raw.map2 option_app
   [(c_update i
       (aeval (fst x3, snd x3) a)
       (fst x3), snd x3)] [])). apply E_Asgn.
apply E_nil. rewrite map2_nil in H4. rewrite map2_l_refl in H4.
simpl in H4. apply H in H4. simpl in H4. intuition.
simpl. admit.  admit.

--admit. admit.

--admit. admit.
   admit. admit.
-- admit. admit.
   admit. admit.
(* --inversion H8; subst.  rewrite map2_nil. rewrite map2_l_refl.
simpl. exists s. exists x1. exists x1. existn.
exists (fst x3, q_update ((I (2 ^ (s' - s)) ⊗ U ⊗ I (2 ^ (x1 - e')))) (snd x3)).
exists (fst x3, q_update (I (2 ^ (e - x1))) (snd x4)).
split. admit. split. admit. split. admit.
split. admit. admit. *)
Admitted. *)
(* 

Theorem rule_qframe: forall (F1 F2 F3: State_formula) c,
         ({{F1}} c {{F2}}) /\  (NSet.inter (fst (Free_state F3)) (fst (MVar c)) =NSet.empty) 
         /\ (NSet.inter (snd (Free_state F3)) (snd (MVar c)) =NSet.empty) 
         ->  {{F1 ⊙ F3}} c {{F2 ⊙ F3}}.
Proof.  unfold hoare_triple.  intros. destruct H.
        assert(sat_Assert mu F1 -> sat_Assert mu' F2).
        apply H. assumption. 
        destruct mu as [mu IHmu].
        destruct mu' as [mu' IHmu'].
        inversion_clear H0. simpl in H5.
        repeat rewrite sat_Assert_to_State in *.
        inversion_clear H1.  simpl in *.
        econstructor. assumption. simpl in *.
        inversion_clear H3.  
        simpl in H6.
        rewrite State_eval_odot in *.
        destruct H6. destruct H6.
        split. 
        assert(sat_Assert (StateMap.Build_slist IHmu') F2).
        apply H with (StateMap.Build_slist IHmu).
        apply E_com. assumption. assumption.
        assumption. rewrite sat_Assert_to_State.
        econstructor. assumption. assumption.
        rewrite sat_Assert_to_State in *.
        inversion_clear H8. assumption.
        split. apply rule_f with c mu.
        assumption. assumption. 
        assumption. admit.
Admitted. *)