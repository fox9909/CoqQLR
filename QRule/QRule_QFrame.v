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
From Quan Require Import Mixed_State.
From Quan Require Import QState.
From Quan Require Import QIMP_L.
From Quan Require Import QAssert.
From Quan Require Import Reduced.
From Quan Require Import QRule_Q_L.
From Quan Require Import QRule_E_L.
From Quan Require Import QRule_I_L.
From Quan Require Import QSepar.

Local Open Scope com_scope.

Local Open Scope nat_scope.
 

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

Definition option_beq (a b:option (nat * nat)) :=
       match a, b with 
       |None, None =>true
       |None , _ => false  
       |_, None => false
       |Some (x,y), Some (x',y') => (x=?x') && (y=?y') 
       end. 

Definition option_free(a:option (nat*nat)):=
match a with 
|None  => (0, 0)
|Some x => x 
end.


Fixpoint Free_State(F:State_formula): option (nat * nat):=
match F with 
|SPure P => None
|SQuan qs=> Some (Free_QExp' qs) 
|SOdot F1 F2=>if  (option_beq (Free_State F1)  None) 
              then Free_State F2 
              else if (option_beq (Free_State F2)  None)
              then Free_State F1 
              else let a:= option_free (Free_State F1) in let b:=option_free (Free_State F2) in 
              Some (min (fst a) (fst b),
              max  (snd a)  (snd b))
|SAnd F1 F2 => if  (option_beq (Free_State F1)  None) 
              then Free_State F2 
              else if (option_beq (Free_State F2)  None)
              then Free_State F1 
              else let a:= option_free (Free_State F1) in let b:=option_free (Free_State F2) in 
              Some (min (fst a) (fst b),
              max  (snd a)  (snd b))
|SAssn i a F => Free_State F
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
| SOdot F1 F2 =>  if  (option_beq (Free_State F1)  None) 
then Considered_Formula F2 
else if (option_beq (Free_State F2)  None)
then Considered_Formula F1
else   let a:= option_free (Free_State F1) in let b:=option_free (Free_State F2) in 
      ( Considered_Formula F1 /\ Considered_Formula F2 
              /\ (((snd a)=(fst b))
              \/ ((snd b)=(fst a))))
|SAnd F1 F2 =>   if  (option_beq (Free_State F1)  None) 
then Considered_Formula F2 
else if (option_beq (Free_State F2)  None)
then  Considered_Formula F1
else  let a:= option_free (Free_State F1) in let b:=option_free (Free_State F2) in 
                     (Considered_Formula F1 /\ Considered_Formula F2 
              /\  ((((fst a)=(fst b))/\
                     ((snd a)=(snd b)))
                     \/ ((snd a)=(fst b)) 
                    \/ (((snd b)=(fst a)))))
|SAssn i a F => Considered_Formula F
end. 

(*--------------------------------------------*)


Fixpoint dstate_qstate_eq {s e:nat} (mu1 mu2: list(cstate * qstate s e)):=
match mu1, mu2 with 
| nil , nil => True
|(c1,q1)::mu'1 , (c2,q2)::mu'2 => and (q1=q2) (dstate_qstate_eq mu'1 mu'2)
| _, _ => False 
end.

Lemma option_edc{A: Type}: forall (a b:option A),
 a = b \/ a<> b .
Proof. intros. apply Classical_Prop.classic.
Qed.

Lemma option_eqb_neq(a b:option (nat *nat)):
a <> b <-> option_beq a b = false.
Proof. intros; split; intros; destruct a; destruct b.
       destruct p. destruct p0.   
       simpl.    
       destruct (eq_dec n n1);
       destruct (eq_dec n0 n2).  rewrite e in *. 
       rewrite e0 in *. 
       destruct H. reflexivity.  
       apply Nat.eqb_neq in n3. rewrite n3.
       apply Nat.eqb_eq in e. rewrite e.
       simpl. reflexivity.
       apply Nat.eqb_neq in n3. rewrite n3.
       apply Nat.eqb_eq in e. rewrite e.
       simpl. reflexivity.
       apply Nat.eqb_neq in n3. rewrite n3.
       apply Nat.eqb_neq in n4. rewrite n4.
       reflexivity. 
       destruct p. simpl. reflexivity.
       destruct p. simpl. reflexivity.  
       destruct H. reflexivity.
       destruct p; destruct p0. 
       simpl in *. 
       destruct (eq_dec n n1);
       destruct (eq_dec n0 n2).  
       apply Nat.eqb_eq in e. rewrite e in *.
       apply Nat.eqb_eq in e0. rewrite e0 in *.
       simpl in H. discriminate H.
       intro. injection H0.  intros. subst. destruct n3; reflexivity.
       intro. injection H0.  intros. subst. destruct n3; reflexivity.
       intro. injection H0.  intros. subst. destruct n3; reflexivity.
       intro. discriminate H0. 
       intro. discriminate H0. 
       simpl in H. discriminate H.
       
       
Qed.

  
Lemma Considered_QExp_dom: forall qs,
Considered_QExp qs ->
fst (Free_QExp' qs) < snd (Free_QExp' qs) .
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
fst (option_free (Free_State F)) <=  snd (option_free (Free_State F)).
Proof. induction F; intros.
       simpl. intuition.
       apply Considered_QExp_dom in H.
       simpl. lia.  
  
       simpl in H. simpl. 
       destruct (option_edc (Free_State F1) None). 
       rewrite H0 in *. simpl in *. apply IHF2. 
       assumption.
       apply option_eqb_neq in H0. rewrite H0 in *.

       destruct (option_edc (Free_State F2) None).
       rewrite H1 in *. simpl in *. 
       apply IHF1. assumption. 
       apply option_eqb_neq in H1. rewrite H1 in *.

       simpl.
       destruct H.
       destruct H2.
       destruct H3;
       
apply IHF1  in H;
apply IHF2 in H2.
pose (min_le ( (fst (option_free (Free_State F1))))
(snd (option_free (Free_State F1)))
(fst (option_free (Free_State F2)))
  (snd (option_free (Free_State F2)))). 
destruct a. intuition.  rewrite H4. 
rewrite H5. 
apply le_trans with  (snd (option_free (Free_State F1))).
assumption. rewrite H3.
assumption.

rewrite min_comm.
rewrite max_comm.
pose (min_le ( (fst (option_free (Free_State F2))))
(snd (option_free (Free_State F2)))
(fst (option_free (Free_State F1)))
  (snd (option_free (Free_State F1)))). 
destruct a. intuition.
rewrite H4.  rewrite H5. 
apply le_trans with  (snd (option_free (Free_State F2))).
assumption. rewrite H3.
assumption.

simpl in *.
       destruct (option_edc (Free_State F1) None). 
       rewrite H0 in *. simpl in *. apply IHF2. 
       assumption.
       apply option_eqb_neq in H0. rewrite H0 in *.

       destruct (option_edc (Free_State F2) None).
       rewrite H1 in *. simpl in *. 
       apply IHF1. assumption. 
       apply option_eqb_neq in H1. rewrite H1 in *.

simpl.
destruct H.
destruct H2.
destruct H3;

apply IHF1  in H;
apply IHF2 in H2.
destruct H3. rewrite H3. rewrite H4.
rewrite min_id.
rewrite max_id. intuition.

destruct H3;
simpl.
pose (min_le ( (fst (option_free (Free_State F1))))
(snd (option_free (Free_State F1)))
(fst (option_free (Free_State F2)))
  (snd (option_free (Free_State F2)))). 
destruct a. intuition.  rewrite H4. 
rewrite H5. 
apply le_trans with  (snd (option_free (Free_State F1))).
assumption. rewrite H3.
assumption.

rewrite min_comm.
rewrite max_comm.
pose (min_le ( (fst (option_free (Free_State F2))))
(snd (option_free (Free_State F2)))
(fst (option_free (Free_State F1)))
  (snd (option_free (Free_State F1)))). 
destruct a. intuition.
rewrite H4.  rewrite H5. 
apply le_trans with  (snd (option_free (Free_State F2))).
assumption. rewrite H3.
assumption. 

simpl in *. apply IHF. assumption. 
Qed.

Require Import OrderedType.
Module MD := OrderedTypeFacts(D).

Lemma QExp_eval_dom{ s e:nat}: forall qs c (q:qstate s e),
QExp_eval qs (c,q) -> s<= fst (Free_QExp' qs) /\ 
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
State_eval F (c,q) ->( (Free_State F)= None )\/ 
let a:= option_free ((Free_State F)) in 
(s<=fst a /\ fst a < snd a /\ snd a <=e).
Proof. induction F; intros.
       simpl in *. left. intuition. 
       simpl in *. right.
       apply QExp_eval_dom with c q.
       assumption.

       destruct H. destruct H0.
       apply IHF1 in H0.
       apply IHF2 in H1.
       destruct H0.
       destruct H1. simpl. left. rewrite H0. simpl. 
       assumption. simpl. right. rewrite H0. simpl. 
       assumption. 

       destruct H1. 

       assert(Free_State F1 <> None). intro. rewrite H2 in *.
       simpl in H0. lia. apply option_eqb_neq in H2. 
       simpl. right. rewrite H1. rewrite H2. simpl. 
       assumption. 

       assert(Free_State F1 <> None). intro. rewrite H2 in *.
       simpl in H0. lia. apply option_eqb_neq in H2. 
       assert(Free_State F2 <> None). intro. rewrite H3 in *.
       simpl in H1. lia. apply option_eqb_neq in H3.
       simpl. right.  rewrite H2. rewrite H3.
       simpl.  split. 
       apply min_glb.
       intuition. intuition.
       split. simpl in *. 
       
       destruct (D.compare (snd (option_free (Free_State F1))) (fst (option_free (Free_State F2)) )) eqn: E;
       try unfold D.lt in l.
       rewrite min_l; try lia. 
       rewrite max_r; try lia.  
      
       unfold D.eq in e0. lia.
       destruct (D.compare (snd (option_free (Free_State F2)) ) (fst (option_free (Free_State F2)) )) eqn: E';
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
       destruct H0; simpl. left. rewrite H.
       simpl. assumption. 
       right. rewrite H.  simpl. 
       assumption. 
       destruct H0. 

       assert(Free_State F1 <> None). intro. rewrite H1 in *.
       simpl in H. lia. apply option_eqb_neq in H1. 
       simpl. right. rewrite H0. rewrite H1. simpl. 
       assumption. 

       assert(Free_State F1 <> None). intro. rewrite H1 in *.
       simpl in H. lia. apply option_eqb_neq in H1. 
       assert(Free_State F2 <> None). intro. rewrite H2 in *.
       simpl in H0. lia. apply option_eqb_neq in H2.
       simpl. right.  rewrite H2. rewrite H1.
       simpl.  split. 
       apply min_glb.
       intuition. intuition.
       split. simpl in *. 
       
       destruct (D.compare (snd (option_free (Free_State F1))) (fst (option_free (Free_State F2)) )) eqn: E;
       try unfold D.lt in l.
       rewrite min_l; try lia. 
       rewrite max_r; try lia.  
      
       unfold D.eq in e0. lia.
       destruct (D.compare (snd (option_free (Free_State F2)) ) (fst (option_free (Free_State F2)) )) eqn: E';
       try unfold D.lt in l0.
       rewrite min_r; try lia. 
       rewrite max_l; try lia.
      
       unfold D.eq in e0. lia.
       apply min_lt_iff.
       left. 
       apply max_lt_iff. left. lia.
       apply max_lub_iff.
       intuition. 

       simpl in *. eapply IHF. apply H.
Qed.


Lemma dstate_eval_dom{ s e:nat}: forall F (mu:list (cstate * qstate s e)),
State_eval_dstate F mu  -> ( (Free_State F)= None )\/ 
let a:= option_free ((Free_State F)) in 
(s<=fst a /\ fst a < snd a /\ snd a <=e).
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
(@Reduced s e q ((fst (Free_QExp' qs))) (((snd (Free_QExp' qs))))).
Proof. induction qs; intros. unfold Par_Pure_State. 
       simpl in H1. 
       exists ((Cmod (@trace (2^(e0-s0)) q))%R).
       exists (outer_product v v).
       simpl. 
       rewrite <-Reduced_scale in H1.
       unfold outer_product in H1.
       destruct H1. destruct H2.
       destruct H3. destruct H4. 
       split. 
       apply nz_mixed_state_Cmod_1.
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
       apply nz_mixed_state_Cmod_1.
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
((Free_State F = None) 
\/ @Par_Pure_State (2^((snd (option_free (Free_State F)))- ((fst (option_free (Free_State F))))))
(@Reduced s e q ((fst (option_free (Free_State F)))) (((snd (option_free (Free_State F))))) )).
Proof. induction F; intros.
       simpl. left. reflexivity.
       right. 
       apply QExp_eval_pure with c.
       assumption. assumption.
       assumption.
        
        
       destruct H1. 
       destruct H2.   
       destruct (option_edc (Free_State F1) None).
       simpl in *. rewrite H4 in *. simpl in *.  
       apply IHF2 with c; assumption. 
       
       pose H2 as H2'.  
       apply IHF1 in H2'. 
       destruct H2'. destruct H4. assumption. 
       apply option_eqb_neq in H4. 
       destruct (option_edc (Free_State F2) None).
       simpl in *. rewrite H6 in *. rewrite H4 in *. simpl in *.
       right. assumption. 
       pose H3 as H3'. 
       apply IHF2 in H3'. 
       destruct H3'. destruct H6. assumption.
       apply option_eqb_neq in H6. 
       simpl in *. rewrite H4 in *. rewrite H6 in*.   
       simpl in *.
      
       right. simpl in *.  apply option_eqb_neq in H4.
       apply option_eqb_neq in H6.
       destruct H.
       destruct H8.
       destruct H9.
       simpl.
       pose (min_le ( (fst (option_free (Free_State F1))))
       (snd (option_free (Free_State F1)))
       (fst (option_free (Free_State F2)))
         (snd (option_free (Free_State F2)))).  
       destruct a.  split.
pose (Considered_Formula_dom F1 H). lia. 
split. assumption.
apply Considered_Formula_dom. assumption.
 rewrite H10. rewrite H11.
     apply Par_Pure_State_wedge with (snd (option_free (Free_State F1))).
     pose (State_eval_dom F1 c q H2). 
     destruct o. destruct H4. assumption.
     pose (State_eval_dom F2 c q H3).
     destruct o. destruct H6; assumption. 
     split. intuition. 
     split. 
     apply Considered_Formula_dom. assumption.
     split. 
     rewrite H9. 
     apply Considered_Formula_dom. assumption.
     intuition. assumption. assumption.
     rewrite H9.
     assumption.
       
     simpl.
     rewrite min_comm.
     rewrite max_comm.
     pose (min_le ( (fst (option_free (Free_State F2))))
       (snd (option_free (Free_State F2)))
       (fst (option_free (Free_State F1)))
         (snd (option_free (Free_State F1)))).  
       destruct a.  split.
pose (Considered_Formula_dom F2 H8).  lia. 
split. assumption.
apply Considered_Formula_dom. assumption.
 rewrite H10. rewrite H11.
   apply (Par_Pure_State_wedge) with (snd (option_free (Free_State F2))).
   pose (State_eval_dom F1 c q H2).
     destruct o. destruct H4; assumption. 
     pose (State_eval_dom F2 c q H3).
     destruct o. destruct H6; assumption.  
     split. intuition. 
     split. 
     apply Considered_Formula_dom. assumption.
     split. 
     rewrite H9. 
     apply Considered_Formula_dom. assumption.
     intuition. assumption. assumption.
     rewrite H9.
     assumption. 
       
     apply option_eqb_neq in H6. 
     simpl in *.  rewrite H4 in *.
     rewrite H6 in *. 

        apply H.
        assumption.
        apply option_eqb_neq in H4. 
        simpl in *.  rewrite H4 in *.
        destruct (option_edc (Free_State F2) None).
        rewrite H5 in *. simpl in *.
        apply H.  
        apply option_eqb_neq in H5. rewrite H5 in *.
        apply H.
        assumption.

simpl in H. destruct H1.


destruct (option_edc (Free_State F1) None).
simpl in *. rewrite H3 in *. simpl in *.  
apply IHF2 with c; assumption. 

pose H1 as H1'.  
apply IHF1 in H1'. 
destruct H1'. destruct H3. assumption. 
apply option_eqb_neq in H3. 
destruct (option_edc (Free_State F2) None).
simpl in *. rewrite H5 in *. rewrite H3 in *. simpl in *.
right. assumption. 
pose H2 as H2'. 
apply IHF2 in H2'. 
destruct H2'. destruct H5. assumption.
apply option_eqb_neq in H5. 
simpl in *. rewrite H3 in *. rewrite H5 in*.   
simpl in *.
      
right. simpl in *.  apply option_eqb_neq in H3.
apply option_eqb_neq in H5.
destruct H.
destruct H7.
destruct H8.
destruct H8.
simpl. rewrite H8. rewrite H9.
rewrite min_id. rewrite max_id.
assumption.

destruct H8.
simpl.
       pose (min_le ( (fst (option_free (Free_State F1))))
       (snd (option_free (Free_State F1)))
       (fst (option_free (Free_State F2)))
         (snd (option_free (Free_State F2)))).  
       destruct a.  split.
pose (Considered_Formula_dom F1 H). lia. 
split. assumption.
apply Considered_Formula_dom. assumption.
 rewrite H10. rewrite H9.
     apply Par_Pure_State_wedge with (snd (option_free (Free_State F1))).
     pose (State_eval_dom F1 c q H1). 
     destruct o. destruct H3. assumption.
     pose (State_eval_dom F2 c q H2).
     destruct o. destruct H5; assumption. 
     split. intuition. 
     split. 
     apply Considered_Formula_dom. assumption.
     split. 
     rewrite H8. 
     apply Considered_Formula_dom. assumption.
     intuition. assumption. assumption.
     rewrite H8.
     assumption.
simpl.
rewrite min_comm.
rewrite max_comm.
pose (min_le ( (fst (option_free (Free_State F2))))
  (snd (option_free (Free_State F2)))
  (fst (option_free (Free_State F1)))
    (snd (option_free (Free_State F1)))).  
  destruct a.  split.
pose (Considered_Formula_dom F2 H7).  lia. 
split. assumption.
apply Considered_Formula_dom. assumption.
rewrite H10. rewrite H9.
apply (Par_Pure_State_wedge) with (snd (option_free (Free_State F2))).
pose (State_eval_dom F1 c q H1).
destruct o. destruct H3; assumption. 
pose (State_eval_dom F2 c q H2).
destruct o. destruct H5; assumption.  
split. intuition. 
split. 
apply Considered_Formula_dom. assumption.
split. 
rewrite H8. 
apply Considered_Formula_dom. assumption.
intuition. assumption. assumption.
rewrite H8.
assumption. 
  
apply option_eqb_neq in H5. 
simpl in *.  rewrite H3 in *.
rewrite H5 in *. 

   apply H.
   assumption.
   apply option_eqb_neq in H3. 
   simpl in *.  rewrite H3 in *.
   destruct (option_edc (Free_State F2) None).
   rewrite H4 in *. simpl in *.
   apply H.  
   apply option_eqb_neq in H4. rewrite H4 in *.
   apply H.
   assumption.

   simpl Free_State.  eapply IHF. apply H. 
   assumption. apply H1. 
Qed.




Lemma QExp_free_eval{s e:nat}:forall (qs: QExp) (st: state s e) s' e',
s<=s'/\ s'<=e' /\ e'<=e ->
s'<=(fst (Free_QExp' qs)) /\ (snd (Free_QExp' qs))<=e'->
@WF_Matrix (2^(e-s)) (2^(e-s)) (snd st)->
QExp_eval qs st <-> QExp_eval qs (fst st, (Reduced (snd st) s' e')).
Proof. induction qs; split; intros. 
        simpl in *. rewrite Reduced_scale.
        rewrite Reduced_assoc. 
        split. intuition. split. lia.
        split. lia. split. lia. 
        rewrite Reduced_trace. intuition.
        lia. assumption. lia.  
        simpl in *. 
        rewrite Reduced_scale in H2.
        rewrite Reduced_assoc in H2.
        rewrite Reduced_trace in H2.
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
        pose (QExp_eval_dom qs1 (fst st) (Reduced (snd st) s' e') H3).
        lia. 
        assumption.
        apply IHqs2 in H4. assumption.
        intuition.
        pose (QExp_eval_dom qs2 (fst st) (Reduced (snd st) s' e') H4).
        lia. 
        assumption. 
Qed.
        



   Lemma min_max_eq: forall x1 x2 y1 y2,
   min x1 x2= max y1 y2->
   x1<=y1 /\ x2<=y2->
   x1=y1 /\ x2 = y2.
   Proof. intros. lia. Qed.

Lemma Pure_free_eval'{s e s' e':nat}:forall  (F: State_formula) c (q : qstate s e) (q0: qstate s' e'),
(Free_State F)= None->
State_eval F (c, q) -> 
State_eval F (c, q0).
Proof. induction F;   intros.
       eapply state_eq_Pure with (c, q). 
       reflexivity. apply H0.
       apply QExp_eval_dom in H0.
       unfold Free_State in *. discriminate H.

       simpl in *;
       split. intuition.
       destruct H0. destruct H1.
destruct (option_edc (Free_State F1) None).
split.  apply IHF1 with q; try assumption. 
apply IHF2 with q; try assumption. 
rewrite H3 in *. simpl in *. assumption. 
apply option_eqb_neq in H3. rewrite H3 in *.
destruct (option_edc (Free_State F2) None); try assumption.
rewrite H4 in *. simpl in *. rewrite H in *. simpl in *. discriminate H3.
apply option_eqb_neq in H4. 
rewrite H4 in *. discriminate H.

destruct H0. simpl in H. 
destruct (option_edc (Free_State F1) None).
rewrite H2 in *. simpl in *. 
split. apply IHF1 with q; try assumption. reflexivity. 
apply IHF2 with q; try assumption.  

apply option_eqb_neq in H2. rewrite H2 in *.
destruct (option_edc (Free_State F2) None); try assumption.
rewrite H3 in *. simpl in *. rewrite H in *. simpl in *. discriminate H2.
apply option_eqb_neq in H3. 
rewrite H3 in *. discriminate H.

eapply IHF. apply H. simpl in H0. rewrite (state_eq_aexp _ (c, q)). apply H0.
reflexivity.
Qed. 

(*对于一个连续的而言*)  
Lemma State_free_eval{s e:nat}:forall (F: State_formula) (st: state s e) s' e',
s<=s'/\ s'<=e' /\ e'<=e ->
s'<=(fst (option_free (Free_State F))) /\ (snd (option_free (Free_State F)))<=e' ->
@WF_Matrix (2^(e-s)) (2^(e-s)) (snd st) ->
State_eval F st <-> 
State_eval F (fst st, (Reduced (snd st) s' e')).
Proof. induction F. split; intros. destruct st. 
    eapply state_eq_Pure with (c, q). 
    reflexivity. apply H2.
    destruct st. simpl in *.
    eapply state_eq_Pure with (c, Reduced q s' e'). 
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
    destruct (option_edc (Free_State F1) None). 
    split; intros.
    split. intuition.
    split. destruct st. simpl.  
    apply (@Pure_free_eval' s e) with q; try assumption.
 intuition.  rewrite H2 in *. simpl in *.
    apply IHF2; try assumption. intuition.
    split. intuition. 
    split. 
    destruct st. simpl.  
    apply (@Pure_free_eval' s' e') with (Reduced (snd (c, q)) s' e'); try assumption.
           intuition. rewrite H2 in *.  simpl in *.
    eapply IHF2; try assumption. apply H. assumption.
    intuition. 
    apply option_eqb_neq in H2.  rewrite H2 in *.
    destruct (option_edc (Free_State F2) None).
    rewrite H3 in *. simpl in *.
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
    apply (@Pure_free_eval' s' e') with (Reduced (snd (c, q)) s' e'); try assumption.
           intuition.


           apply option_eqb_neq in H3.  rewrite H3 in *. simpl in *.
    split. intros. 
    simpl in *. split. intuition.
    split. apply IHF1. assumption.
    split.
    apply min_glb_l with (fst (option_free(Free_State F2))).
    intuition.
    eapply max_lub_iff.  rewrite max_comm. apply H0.
    assumption. intuition.
    apply IHF2. assumption.
    split.
    apply min_glb_l with (fst (option_free(Free_State F2))).
    intuition.
    eapply max_lub_iff.   apply H0.
    assumption. intuition.
    split. intuition.
    simpl in *.
    split. eapply IHF1; try assumption. apply H.
    split.
    apply min_glb_l with (fst (option_free(Free_State F2))).
    intuition.
    eapply max_lub_iff.  rewrite max_comm. apply H0.
    intuition.
    eapply IHF2; try assumption. apply H. 
    split.
    apply min_glb_l with (fst (option_free(Free_State F2))).
    intuition.
    eapply max_lub_iff.  apply H0. intuition.
    

    intros.
    simpl in *.
    destruct (option_edc (Free_State F1) None). 
    rewrite H2 in *. simpl in *. 
    split; intros.
    split.
    destruct st. simpl.  
    apply (@Pure_free_eval' s e) with q; try assumption.
 intuition.
    apply IHF2; try assumption. intuition.
    split.
    destruct st. simpl.  
    apply (@Pure_free_eval' s' e') with (Reduced (snd (c, q)) s' e'); try assumption.
           intuition.
    eapply IHF2; try assumption. apply H. assumption.
    intuition.
    destruct (option_edc (Free_State F2) None).
    apply option_eqb_neq in H2. 
    rewrite H2 in *. rewrite H3 in *. simpl in *.
    split. intros.
    split. apply IHF1; try assumption. intuition.
    destruct st. simpl.  
    apply (@Pure_free_eval' s e) with q; try assumption.
 intuition.
    split. eapply IHF1; try assumption. apply H.
    assumption. intuition.
    destruct st. simpl.  
    apply (@Pure_free_eval' s' e') with (Reduced (snd (c, q)) s' e'); try assumption.
           intuition.
           apply option_eqb_neq in H2. 
           rewrite H2 in *.
           apply option_eqb_neq in H3. 
           rewrite H3 in *. simpl in *.
    simpl in *.
    split; intros.
    split.  apply IHF1. assumption.
    split.
    apply min_glb_l with (fst (option_free(Free_State F2))).
    intuition.
    eapply max_lub_iff.  rewrite max_comm. apply H0.
    assumption. intuition.
    apply IHF2. assumption.
    split.
    apply min_glb_l with (fst (option_free(Free_State F2))).
    intuition.
    eapply max_lub_iff.  apply H0.
    assumption. intuition.
    split. eapply IHF1; try assumption. apply H.
    split.
    apply min_glb_l with (fst (option_free(Free_State F2))).
    intuition.
    eapply max_lub_iff.  rewrite max_comm. apply H0.
    intuition.
  
    eapply IHF2; try assumption. apply H. 
    split.
    apply min_glb_l with (fst (option_free(Free_State F2))).
    intuition.
    eapply max_lub_iff.   apply H0.
    intuition.

    intros. destruct st. simpl. rewrite (state_eq_aexp ((c, Reduced q s' e')) (c,q)); try reflexivity.
    eapply IHF; try assumption.
Qed.


Lemma State_dstate_free_eval{s e:nat}:forall  (mu: list (cstate * qstate s e)) (F: State_formula) s' e',
s<=s'/\ s'<=e' /\ e'<=e ->
s'<=(fst (option_free (Free_State F))) /\ (snd (option_free (Free_State F)))<=e' ->
WF_Matrix_dstate mu ->
State_eval_dstate F mu <-> 
State_eval_dstate F (d_reduced mu s' e').
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

Lemma d_reduced_trace{s e:nat}: forall (l r : nat) (mu: list (cstate * qstate s e)),
s <= l /\ l <= r <= e -> 
WF_Matrix_dstate mu ->
 d_trace_aux mu =
 d_trace_aux (d_reduced mu l r).
Proof. induction mu; intros. simpl. reflexivity.
      destruct a. simpl. unfold s_trace.
      simpl. unfold q_trace.  rewrite  Reduced_trace.
      rewrite IHmu. reflexivity.
      intuition. inversion_clear H0. intuition.
      intuition. inversion_clear H0. 
       intuition.  
Qed.


Lemma WF_NZ_Mixed_dstate{ s e: nat}: forall (mu : list (cstate * qstate s e)), 
WF_dstate_aux mu -> WF_Matrix_dstate mu.
Proof. induction mu; intros. econstructor.
      destruct a. inversion H; subst.
      econstructor. apply WF_NZ_Mixed.
      apply H2.
      apply IHmu.
      apply H3.       
Qed.


Lemma WF_d_reduced: forall (s e l r : nat) (mu: list (cstate * qstate s e)),
s <= l /\ l <= r <= e -> WF_dstate_aux mu ->
 WF_dstate_aux (d_reduced mu l r).
Proof. induction mu; intros. simpl. econstructor.
destruct a. simpl. econstructor.
unfold WF_state. simpl. apply WF_qstate_Reduced.
intuition. inversion_clear H0. assumption.
apply IHmu. intuition. inversion_clear H0.
assumption. assert((((c, Reduced q l r) :: d_reduced mu l r)=
d_reduced ((c, q) :: mu) l r)).
simpl. reflexivity.
unfold state.
rewrite H1. 
rewrite <-d_reduced_trace.
inversion_clear H0. assumption.
intuition.
apply WF_NZ_Mixed_dstate.
assumption.
 
Qed.

Import Basic.
Local Open Scope nat_scope. 
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
        type_sovle'. destruct H1. unfold q_plus.
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
dstate_qstate_eq mu1 mu2 ->
dstate_Separ mu1 s0 e0 s1 e1->
dstate_Separ mu2 s0 e0 s1 e1.
Proof. induction mu1; intros mu2 s0 e0 s1 e1 ; intros. destruct mu2. intuition.
       destruct H. 
       destruct mu2. destruct a. destruct H.
       destruct a. destruct p. 
       simpl in H. destruct H. subst.
       inversion H0; subst.
       econstructor; try reflexivity.
       apply H7. apply H8.
       apply IHmu1. assumption.
       assumption. 
Qed.

Local Open Scope nat_scope.
Lemma dstate_Separ_Qinit_r{s e:nat}: forall c (q:qstate s e) s0 e0 s1 e1 s' e',
dstate_Separ [(c, q)] s0 e0 s1 e1 ->
s=s0 /\ s0<=s' /\ s'<=e'/\ e'<=e0 /\ e0<=s1 /\ s1<=e1 /\
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
  apply (@QInit_fun_kron_r s s1 e).
  pose (H8 x). destruct o. apply WF_NZ_Mixed.  
  apply H2. rewrite H2. auto_wf. 
intuition. apply (@dstate_Separ_nil s e). 
Qed.

Lemma dstate_Separ_Qinit_l{s e:nat}: forall c (q:qstate s e) s0 e0 s1 e1 s' e',
dstate_Separ [(c, q)] s0 e0 s1 e1 ->
s=s0 /\ s0<=e0 /\ e0<=s1/\ s1<=s' /\ s'<=e' /\ e'<=e1 /\
e1=e->
@dstate_Separ s e [(c, QInit_fun s' e' q)] s0 e0 s1 e1.
Proof.
intros.  inversion H; subst. clear H14. 
econstructor; try reflexivity. 
apply H7.
assert(forall i : nat, WF_qstate  ((fun i=> QInit_fun s' e' (q1_i i)) i) \/
((fun i=> QInit_fun s' e' (q1_i i)) i)= Zero).
intros. pose (H8 i). destruct o. 
left. apply WF_qstate_init. lia.  apply H1.
right. rewrite H1. apply (@QInit_Zero s1 e). apply H1. 
rewrite (@QInit_fun_sum s e). subst. 
apply big_sum_eq_bounded. intros.
apply (@QInit_fun_kron_l s s1 e).
pose (H7 x). destruct o. apply WF_NZ_Mixed.  
apply H2. rewrite H2. auto_wf. 
intuition. apply (@dstate_Separ_nil s e). 
Qed.


Lemma dstate_Separ_QUnit_One_r{s e:nat}: forall c (q:qstate s e) U s0 e0 s1 e1 s' e',
dstate_Separ [(c, q)] s0 e0 s1 e1 ->
s=s0 /\ s0<=s' /\ s'<=e'/\ e'<=e0 /\ e0=s1 /\ s1<=e1 /\
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
intros.   apply (@QUnit_One_fun_kron_r s s1 e).
apply H1. pose (H9 x). destruct o. apply WF_NZ_Mixed. apply H3.
rewrite H3. auto_wf. 
intuition. 
econstructor; try reflexivity.
Qed.



Lemma dstate_Separ_QUnit_One_l{s e:nat}: forall c (q:qstate s e) U s0 e0 s1 e1 s' e',
dstate_Separ [(c, q)] s0 e0 s1 e1 ->
s=s0 /\ s0<=e0 /\ e0<=s1/\ s1<=s' /\ s'<=e' /\ e'<=e1 /\
e1=e->
@WF_Unitary (2^(e'-s')) U->
@dstate_Separ s e [(c, QUnit_One_fun s' e' U q)] s0 e0 s1 e1.
Proof.
intros.  inversion H; subst. clear H15. 
econstructor; try reflexivity.
apply H8. 
assert(forall i : nat, @WF_qstate s1 e ((fun i=>QUnit_One_fun s' e' U (q1_i i)) i)\/
((fun i=>QUnit_One_fun s' e' U (q1_i i)) i) = Zero).
intros.   pose (H9 i). destruct o. 
left.
 apply WF_qstate_QUnit_One. lia. assumption.   apply H2.
 right.   rewrite H2. apply (@QUnit_One_Zero s1 e).
apply H2.
rewrite (@QUnit_One_fun_sum s e).
subst. 
apply big_sum_eq_bounded.
intros.   apply (@QUnit_One_fun_kron_l s s1 e).
apply H1. pose (H8 x). destruct o. apply WF_NZ_Mixed. apply H3.
rewrite H3. auto_wf. 
intuition. econstructor. 
Qed.

Lemma dstate_Separ_QUnit_Ctrl_r{s e:nat}: forall c (q:qstate s e)  
s0 e0 s1 e1 s0' e0' s1' e1' (U: nat -> Square (2 ^ (e1' - s1'))),
dstate_Separ [(c, q)] s0 e0 s1 e1 ->
(forall j, WF_Unitary (U j))->
s=s0 /\ s0<=s0' /\ s0'<=e0'/\ e0'<= s1' /\ s1'<=e1' /\e1'<=e0 /\ e0=s1 /\ s1<=e1 /\
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
intros. apply (@QUnit_Ctrl_fun_kron_r s s1 e).
intros. apply H0. pose (H9 x). destruct o. 
 apply WF_NZ_Mixed. apply H3. rewrite H3. auto_wf. 
lia. 
econstructor; try reflexivity.
Qed.



Lemma dstate_Separ_QUnit_Ctrl_l{s e:nat}: forall c (q:qstate s e)  
s0 e0 s1 e1 s0' e0' s1' e1' (U: nat -> Square (2 ^ (e1' - s1'))),
dstate_Separ [(c, q)] s0 e0 s1 e1 ->
(forall j, WF_Unitary (U j))->
s=s0 /\ s0<=e0 /\ e0<=s1/\ s1<= s0' /\ s0'<=e0' /\e0'<=s1' /\ s1'<=e1' /\ e1'<=e1 /\
e1=e->
@dstate_Separ s e [(c, QUnit_Ctrl_fun s0' e0' s1' e1' U q)] s0 e0 s1 e1.
Proof.
intros.  inversion H; subst. clear H15. 
econstructor; try reflexivity. apply H8.
assert(forall i : nat, @WF_qstate s1 e ((fun i=>QUnit_Ctrl_fun s0' e0' s1' e1' U (q1_i i)) i)
\/ ((fun i=>QUnit_Ctrl_fun s0' e0' s1' e1' U (q1_i i)) i) = Zero).
intros. pose (H9 i). destruct o. 
left. apply (WF_qstate_QUnit_Ctrl); try assumption. lia.
right. rewrite H2. apply QUnit_Ctrl_Zero. 
apply H2. 
rewrite (@QUnit_Ctrl_fun_sum s e).
subst. 
apply big_sum_eq_bounded.
intros. apply (@QUnit_Ctrl_fun_kron_l s s1 e).
intros. apply H0. pose (H8 x). destruct o. 
 apply WF_NZ_Mixed. apply H3. rewrite H3. auto_wf. 
lia. 
econstructor; try reflexivity.
Qed.

Lemma dstate_Separ_QMeas_r{s e:nat}: forall c (q:qstate s e)  
s0 e0 s1 e1 s' e' j,
QMeas_fun s' e' j q <> Zero->
dstate_Separ [(c, q)] s0 e0 s1 e1 ->
s=s0 /\ s0<=s' /\ s'<=e' /\e'<=e0 /\ e0<=s1 /\ s1<=e1 /\
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
apply (@QMeas_fun_kron_r s s1 e).
assumption. 
pose (H10 x). destruct o.  
apply WF_NZ_Mixed. 
apply H4. rewrite H4. auto_wf.

intuition. econstructor; reflexivity.
Qed.


Lemma dstate_Separ_QMeas_l{s e:nat}: forall c (q:qstate s e)  
s0 e0 s1 e1 s' e' j,
QMeas_fun s' e' j q <> Zero->
dstate_Separ [(c, q)] s0 e0 s1 e1 ->
s=s0 /\ s0<=e0 /\ e0<=s1/\ s1<=s' /\ s'<=e' /\ e'<=e1 /\
e1=e->
(j<(2^(e'-s')))->
@dstate_Separ s e [(c, QMeas_fun s' e' j q)] s0 e0 s1 e1.
Proof.
intros. inversion H0; subst. clear H16.
rewrite (@QMeas_fun_sum  s e) in *.
econstructor; try reflexivity. apply H9.
assert(forall i : nat, @WF_qstate s1 e ((fun i=>QMeas_fun s' e' j (q1_i i)) i)\/
((fun i=>QMeas_fun s' e' j (q1_i i)) i) = Zero). 
intros. pose (H10 i). 
assert(QMeas_fun s' e' j (q1_i i) = Zero \/
QMeas_fun s' e' j (q1_i i) <> Zero).
apply Classical_Prop.classic. 
destruct H3. right. assumption. left.
apply WF_qstate_QMeas. intuition. intuition. lia.
assumption. assumption. destruct o. assumption.
rewrite H4 in H3. unfold QMeas_fun in H3.
unfold q_update in H3. rewrite super_0 in H3.
destruct H3. reflexivity.  
apply H3. 
apply big_sum_eq_bounded.
intros. 
apply (@QMeas_fun_kron_l s s1 e).
assumption. 
pose (H9 x). destruct o.  
apply WF_NZ_Mixed. 
apply H4. rewrite H4. auto_wf. lia. 
 econstructor; reflexivity.
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




Lemma Reduced_QInit_r{ s e:nat}: forall c (q:qstate s e) s' e' s0 e0 s1 e1,
dstate_Separ [(c, q)] s0 e0 s1 e1->
s=s0 /\ s0<=s' /\ s'<=e'/\ e'<=e0 /\ e0=s1 /\ s1<=e1 /\
e1=e->
@Reduced s e (QInit_fun s' e' q) s1 e1=
Reduced q s1 e1.
Proof. intros. simpl in H. inversion H; subst.
clear H.
rewrite  (@QInit_fun_sum s e ). 
repeat rewrite (big_sum_Reduced); try lia. 
apply big_sum_eq_bounded.
intros.  destruct H0.
 destruct H1.
 destruct H2.
destruct H3. destruct H4.
destruct H5.
subst. 
rewrite (@QInit_fun_kron_r s s1 e); auto_wf; try lia. 

repeat rewrite Reduced_R; try reflexivity; auto_wf.
rewrite (Reduced_tensor_r _ ((QInit_fun s' e' (q0_i x))) (q1_i x)); try reflexivity; auto_wf.
rewrite (Reduced_tensor_r _ (q0_i x) (q1_i x)); try reflexivity; auto_wf.
rewrite QInit_trace; auto_wf; try lia.  reflexivity. 
Qed.


Lemma Reduced_QInit_l{ s e:nat}: forall c (q:qstate s e) s' e' s0 e0 s1 e1,
dstate_Separ [(c, q)] s0 e0 s1 e1->
s=s0 /\ s0<=e0 /\ e0<=s1/\ s1<=s' /\ s'<=e' /\ e'<=e1 /\
e1=e->
@Reduced s e (QInit_fun s' e' q) s0 e0=
Reduced q s0 e0.
Proof. intros. simpl in H. inversion H; subst.
clear H.
rewrite  (@QInit_fun_sum s e ).
repeat rewrite (big_sum_par_trace); try lia. 
apply big_sum_eq_bounded.
intros.  destruct H0.
 destruct H1.
 destruct H2.
destruct H3. destruct H4.
destruct H5.
subst. 
rewrite (@QInit_fun_kron_l s s1 e); auto_wf; try lia. 

repeat rewrite Reduced_L; try reflexivity; auto_wf; try lia. 
rewrite (Reduced_l _  (q0_i x) ((QInit_fun s' e' (q1_i x)))); try reflexivity; auto_wf.
rewrite (Reduced_l _ (q0_i x) (q1_i x)); try reflexivity; auto_wf.
rewrite QInit_trace; auto_wf; try lia.  reflexivity. 
Qed.

Lemma Reduced_QUnit_one_r{ s e:nat}: forall c (q:qstate s e)  s' e' (U:Square (2^(e'-s'))) s0 e0 s1 e1,
dstate_Separ [(c, q)] s0 e0 s1 e1->
s=s0 /\ s0<=s' /\ s'<=e'/\ e'<=e0 /\ e0<=s1 /\ s1<=e1 /\
e1=e->
WF_Unitary U->
@Reduced s e (QUnit_One_fun s' e' U q) s1 e1=
Reduced q s1 e1.
Proof. intros. inversion H; subst. clear H.
rewrite  (@QUnit_One_fun_sum s e ).
repeat rewrite (big_sum_par_trace); try lia.
apply big_sum_eq_bounded.
intros.  destruct H0.
destruct H2. destruct H3.
destruct H4. destruct H5.
destruct H6. 
subst. 
rewrite (@QUnit_One_fun_kron_r s s1 e); auto_wf; try lia.
repeat rewrite Reduced_R; try reflexivity; auto_wf.
rewrite (Reduced_r _ ((QUnit_One_fun s' e' U (q0_i x))) (q1_i x)); try reflexivity; auto_wf.
rewrite (Reduced_r _ (q0_i x) (q1_i x)); try reflexivity; auto_wf.
rewrite QUnit_One_trace; auto_wf; try lia.  reflexivity. assumption.
apply H1.
Qed.


Lemma Reduced_QUnit_one_l{ s e:nat}: forall c (q:qstate s e)  s' e' (U:Square (2^(e'-s'))) s0 e0 s1 e1,
dstate_Separ [(c, q)] s0 e0 s1 e1->
s=s0 /\ s0<=e0 /\ e0<=s1/\ s1<=s' /\ s'<=e' /\ e'<=e1 /\
e1=e->
WF_Unitary U->
@Reduced s e (QUnit_One_fun s' e' U q) s0 e0=
Reduced q s0 e0.
Proof. intros. inversion H; subst. clear H.
rewrite  (@QUnit_One_fun_sum s e ).
repeat rewrite (big_sum_par_trace); try lia.
apply big_sum_eq_bounded.
intros.  destruct H0.
destruct H2. destruct H3.
destruct H4. destruct H5.
destruct H6. 
subst. 
rewrite (@QUnit_One_fun_kron_l s s1 e); auto_wf; try lia; auto_wf.
repeat rewrite Reduced_L; try reflexivity; auto_wf; try lia. 
rewrite (Reduced_l _ (q0_i x) ((QUnit_One_fun s' e' U (q1_i x))) ); try reflexivity; auto_wf.
rewrite (Reduced_l _ (q0_i x) (q1_i x)); try reflexivity; auto_wf.
rewrite QUnit_One_trace; auto_wf; try lia.  reflexivity. assumption.
apply H1.
Qed.


Lemma Reduced_QUnit_Ctrl_r{ s e:nat}: forall c (q:qstate s e)  s0' e0' s1' e1' (U:nat -> Square (2^(e1'-s1'))) s0 e0 s1 e1,
dstate_Separ [(c, q)] s0 e0 s1 e1->
s=s0 /\ s0<=s0' /\ s0'<=e0'/\ e0'<= s1' /\ s1'<=e1' /\e1'<=e0 /\ e0=s1 /\ s1<=e1 /\
e1=e ->
(forall j, WF_Unitary (U j))->
@Reduced s e (QUnit_Ctrl_fun s0' e0' s1' e1' U q) s1 e1=
Reduced q s1 e1.
Proof. intros. 
inversion H; subst. clear H.
rewrite  (@QUnit_Ctrl_fun_sum s e ).
repeat rewrite (big_sum_par_trace); try lia.
apply big_sum_eq_bounded.
intros.  destruct H0.
destruct H2. destruct H3.
destruct H4. destruct H5.
destruct H6. destruct H7.
destruct H10. 
subst.    
rewrite (@QUnit_Ctrl_fun_kron_r s s1 e); auto_wf; try lia.
repeat rewrite Reduced_R; try reflexivity; auto_wf.
rewrite (Reduced_r _ ((QUnit_Ctrl_fun s0' e0' s1' e1' U (q0_i x))) (q1_i x)); try reflexivity; auto_wf.
rewrite (Reduced_r _ (q0_i x) (q1_i x)); try reflexivity; auto_wf.
rewrite QUnit_Ctrl_trace; auto_wf; try lia. reflexivity. assumption. 

apply H1.    
Qed.



Lemma Reduced_QUnit_Ctrl_l{ s e:nat}: forall c (q:qstate s e)  s0' e0' s1' e1' (U:nat -> Square (2^(e1'-s1'))) s0 e0 s1 e1,
dstate_Separ [(c, q)] s0 e0 s1 e1->
s=s0 /\ s0<=e0 /\ e0<=s1/\ s1<= s0' /\ s0'<=e0' /\e0'<=s1' /\ s1'<=e1' /\ e1'<=e1 /\
e1=e->
(forall j, WF_Unitary (U j))->
@Reduced s e (QUnit_Ctrl_fun s0' e0' s1' e1' U q) s0 e0=
Reduced q s0 e0.
Proof. intros. 
inversion H; subst. clear H.
rewrite  (@QUnit_Ctrl_fun_sum s e ).
repeat rewrite (big_sum_par_trace); try lia.
apply big_sum_eq_bounded.
intros.  destruct H0.
destruct H2. destruct H3.
destruct H4. destruct H5.
destruct H6. destruct H7.
destruct H10. 
subst.    
rewrite (@QUnit_Ctrl_fun_kron_l s s1 e); auto_wf; try lia.
repeat rewrite Reduced_L; try reflexivity; auto_wf; try lia.
rewrite (Reduced_l _  (q0_i x) ((QUnit_Ctrl_fun s0' e0' s1' e1' U (q1_i x)))); try reflexivity; auto_wf.
rewrite (Reduced_l _ (q0_i x) (q1_i x)); try reflexivity; auto_wf.
rewrite QUnit_Ctrl_trace; auto_wf; try lia. reflexivity. assumption. 

apply H1.    
Qed.


Ltac r3_solve_1 F:=
       try  match goal with 
       H:ceval_single ?x ?y ?z |-_ => inversion H; subst; clear H end;
       try  match goal with 
       H: existT ?a ?b ?c = existT ?x ?y ?z|-_ => apply inj_pair2_eq_dec in H end;
       try  match goal with 
       H: existT ?a ?b ?c = existT ?x ?y ?z|-_ => apply inj_pair2_eq_dec in H; destruct H end;
       try apply Nat.eq_dec;
       try  match goal with 
       H:dstate_Separ ?x ?y ?z ?k ?j|-_ => inversion H; subst; clear H end;
       apply dstate_Separ_map2; [ | | match goal with IHmu: _ |- _ => apply IHmu with F end]; try assumption;
       try match goal with 
       H2: NSet.Subset ?a ?b \/ NSet.Subset ?c ?d |- _ => destruct H2 as [H2|H2];
       simpl in H2 end. 
       Ltac r3_solve_2:=     
       try econstructor; try reflexivity; try
       assumption; try apply dstate_Separ_nil;
       try match goal with 
       H2: NSet.Subset (NSet.union ?a ?b) ?c |- _ => apply subset_union in H2;
       destruct H2 as [H2 H2']; apply subset_Qsys in H2 end; 
       try match goal with 
       H2: NSet.Subset ?a ?b |- _ =>  apply subset_Qsys in H2 end;  try lia;
       try match goal with 
       H: WF_Unitary ?U |- _ => try apply H end;  
       try match goal with 
       H: forall i, WF_Unitary (?U i) |- _ => try apply H end.

Lemma r3{s e:nat}: forall c s0 e0 s1 e1
(mu mu':list (cstate *qstate s e)) F ,
s<=s1<=e->
ceval_single c mu mu'-> 
dstate_Separ mu s0 e0 s1 e1->
NSet.Equal (NSet.inter (fst (Free_state F)) (fst (MVar c))) (NSet.empty)  ->
NSet.Subset (snd (MVar c)) (Qsys_to_Set s0 e0) \/
NSet.Subset (snd (MVar c)) (Qsys_to_Set s1 e1) ->
dstate_Separ mu' s0 e0 s1 e1 .
Proof.
induction c. 
-- {intros s0 e0 s1 e1 mu mu' F Hs. intros. apply ceval_skip_1 in H. subst. intuition. }
-- induction mu; intros mu' F  Hs; intros.
  {inversion  H; subst. intuition.  }
   {destruct a0. inversion H; subst. clear H.
   apply dstate_Separ_map2. intuition. 
   apply dstate_qstate_eq_Separ with [(c,q)].
   intuition.
   simpl. intuition.
   inversion H0; subst.
   econstructor; try reflexivity.
   inversion_clear H0.  
   econstructor; try reflexivity; try assumption.
   apply H5. apply H6. apply H7. econstructor.
   apply IHmu with F. assumption. 
   assumption.
   inversion H0; subst. assumption.
   assumption. assumption. }
-- induction mu; intros. inversion_clear H0. econstructor. 
    destruct a0. inversion H0; subst. assumption. 
  {intros s0 e0 s1 e1 mu mu' F Hs.  intros. inversion H; subst. intuition.
    apply IHc2 with mu1 F.
    assumption. assumption. 
    apply IHc1 with  ((sigma, rho) :: mu0) F.
    assumption.
    assumption. assumption. 
    simpl in H1. rewrite inter_union_dist in H1.
    rewrite union_empty in H1. intuition.
    destruct H2;  [left|right];
    simpl in H2; apply subset_union in H2;
    intuition.
    simpl in H1. rewrite inter_union_dist in H1.
    rewrite union_empty in H1. intuition.
    destruct H2;  [left|right];
    simpl in H2; apply subset_union in H2;
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
    destruct H2;  [left|right];
    simpl in H2; apply subset_union in H2;
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
    destruct H2;  [left|right];
    simpl in H2; apply subset_union in H2;
    intuition.
    apply IHmu with F. 
    assumption. assumption.
    inversion H0; subst. intuition.
    assumption. assumption. }
-- intros.  remember <{while b do c end}> as original_command eqn:Horig. 
   induction H0;  try inversion Horig; subst. 
    econstructor.
    apply dstate_Separ_map2. assumption. 
    apply IHceval_single3; try reflexivity; try assumption.
    apply IHc with [(sigma, rho)] F; try assumption.
    inversion_clear H1. econstructor; try assumption. apply H7.
    apply H8. apply H9. econstructor.
    apply IHceval_single1; try reflexivity. inversion_clear H1. assumption.
    assumption. apply H3. 
    apply dstate_Separ_map2. assumption. 
    inversion_clear H1. econstructor; try assumption. apply H9.
    apply H10. apply H11. econstructor.
    apply IHceval_single; try reflexivity. inversion_clear H1. assumption.
    assumption. apply H3.
-- { induction mu; intros mu' F Hs ; intros. inversion  H; subst. intuition.  
     destruct a.
    r3_solve_1 F; [try apply dstate_Separ_Qinit_r| try apply dstate_Separ_Qinit_l]; r3_solve_2.  }
-- { induction mu; intros mu' F Hs ; intros. inversion  H; subst. intuition.    
    destruct a. 
    r3_solve_1 F; [try apply dstate_Separ_QUnit_One_r| try apply dstate_Separ_QUnit_One_l]; r3_solve_2. } 
-- { induction mu; intros mu' F Hs ; intros. inversion  H; subst. intuition.
   destruct a. 
   r3_solve_1 F; [try apply dstate_Separ_QUnit_Ctrl_r| try apply dstate_Separ_QUnit_Ctrl_l]; r3_solve_2.  }
--{ induction mu; intros mu' F Hs ; intros. inversion  H; subst. intuition. 
   destruct a.  r3_solve_1 F;
   try match goal with 
   H: big_app' ?f ?n ?mu |- _ => apply (dstate_Separ_big_app'  f n); try lia;try assumption; intros end;
   [try apply dstate_Separ_QMeas_r| try apply dstate_Separ_QMeas_l];
   r3_solve_2.  }
Qed.


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
       exists x.  intuition. 
       apply Rle_trans with (Cmod (@trace (2^(e-s)) (@big_sum (Matrix (2^(e-s)) (2^(e-s))) _  f n))).
        repeat  rewrite big_sum_Cmod.
        apply big_sum_le. intros. 
        apply H in H5. destruct H5. 
        apply nz_mixed_state_Cmod_1_aux in H5. lra.
        rewrite H5. rewrite Zero_trace. rewrite Cmod_0.
        lra. lia. intros. apply H. assumption.
        intros. apply H. lia.   
        assumption. assumption.
Qed.


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
        rewrite <-Reduced_scale.
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
        unfold not. intros. apply nz_mixed_state_Cmod_1_aux in H.
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
        unfold not. intros. apply nz_mixed_state_Cmod_1_aux in H0.
        rewrite H4 in H0. lra. 
         rewrite H3. rewrite H4.
          rewrite Reduced_plus. 
          rewrite <-Reduced_scale. 
          rewrite Rdiv_unfold in *.
          destruct H1. destruct H5. destruct H6. destruct H2.
          destruct H8. destruct H9.
          split. intuition. split. intuition.
          split. intuition. split. intuition.
           destruct H7.
          rewrite H11.
          rewrite <-Reduced_scale. 
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
         apply nz_mixed_state_Cmod_1_aux. apply H.
         intuition.  apply nz_mixed_state_Cmod_1_aux. apply H0.
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
      -simpl in *. eapply IHF; try assumption.
      rewrite (state_eq_aexp _ (c,q)); try reflexivity; try assumption.
      rewrite (state_eq_aexp _ (c,q0)); try reflexivity; try assumption.
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
      rewrite Reduced_plus in H3.
      apply (@Mixed_pure (2^(e-s))
      (Reduced ((R1 / Cmod (trace (q1 .+ q2)))%R .* q1) s e) 
      (Reduced ((R1 / Cmod (trace (q1 .+ q2)))%R .* q2) s e) ) in H3.
      destruct H3. destruct H3.
      destruct H3. 
      repeat rewrite <-Reduced_scale in H5.
      rewrite Rdiv_unfold in H5.
      rewrite Rmult_1_l in H5. 
      destruct H5. 

       simpl. repeat rewrite Rdiv_unfold.
      repeat  rewrite Rmult_1_l. repeat rewrite <-Reduced_scale.
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
       rewrite H7. rewrite <-(Reduced_trace _ _ _ s e).
       apply (@normalize_eq (2^(e-s))).
       assumption. 
       exists (Cmod (@trace (2^(e0-s0)) (q1 .+ q2)) * x)%R.
       split. 
       apply RtoC_neq. apply Rmult_integral_contrapositive_currified.
       rewrite mixed_state_Cmod_plus; try assumption.
       apply Rgt_neq_0.
       apply Rplus_lt_0_compat; apply nz_mixed_state_Cmod_1; assumption.
       lra. rewrite <-RtoC_mult. rewrite<- Mscale_assoc.
       unfold outer_product.
       rewrite <-H5. rewrite Mscale_assoc.
       rewrite RtoC_mult. rewrite Rinv_r.
       rewrite Mscale_1_l. reflexivity.
       assert(Cmod (@trace (2^(e0-s0)) (q1 .+ q2)) >0)%R.
       apply nz_mixed_state_Cmod_1. assumption. lra.
       lia. apply WF_NZ_Mixed. assumption.
       assert(Cmod (@trace (2^(e0-s0)) (q1 )) >0)%R.
       apply nz_mixed_state_Cmod_1. assumption.
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
       rewrite H7. rewrite <-(Reduced_trace _ _ _ s e).
       apply (@normalize_eq (2^(e-s))).
       assumption. 
       exists (Cmod (@trace (2^(e0-s0)) (q1 .+ q2)) * x0)%R.
       split. apply RtoC_neq. apply Rmult_integral_contrapositive_currified.
       rewrite mixed_state_Cmod_plus; try assumption.
       apply Rgt_neq_0.
       apply Rplus_lt_0_compat; apply nz_mixed_state_Cmod_1; assumption.
       lra. rewrite <-RtoC_mult. rewrite<- Mscale_assoc.
       unfold outer_product.
       rewrite <-H6. rewrite Mscale_assoc.
       rewrite RtoC_mult. rewrite Rinv_r.
       rewrite Mscale_1_l. reflexivity.
       assert(Cmod (@trace (2^(e0-s0)) (q1 .+ q2)) >0)%R.
       apply nz_mixed_state_Cmod_1. assumption. lra.
       lia. apply WF_NZ_Mixed. assumption.
       assert(Cmod (@trace (2^(e0-s0)) (q2)) >0)%R.
       apply nz_mixed_state_Cmod_1. assumption. lra.
       apply WF_qstate_Reduced. lia.
       split. apply Mixed_State_aux_to_01'.
       apply Mixed_State_aux_to_Mix_State. assumption.
       rewrite Rdiv_unfold. rewrite Rmult_1_l.
       apply Rinv_0_lt_compat. apply nz_mixed_state_Cmod_1.
       assumption. 
       rewrite trace_mult_dist. rewrite Cmod_mult.
       rewrite Rdiv_unfold. rewrite Rmult_1_l.
       rewrite Cmod_R. rewrite Rabs_right.
       rewrite mixed_state_Cmod_plus; try assumption. 
       rewrite Rmult_comm. rewrite <-Rdiv_unfold.
       apply Rdiv_in01; apply nz_mixed_state_Cmod_1; assumption.
       assert((/ Cmod (@trace (2^(e0-s0)) (q1 .+ q2)) > 0)%R).
       apply Rinv_0_lt_compat. apply nz_mixed_state_Cmod_1.
       assumption. lra.   lia.   
       apply WF_qstate_Reduced. lia.
       split. apply Mixed_State_aux_to_01'.
       apply Mixed_State_aux_to_Mix_State.
       assumption. 
       rewrite Rdiv_unfold. rewrite Rmult_1_l.
       apply Rinv_0_lt_compat. apply nz_mixed_state_Cmod_1.
       assumption. 
       rewrite trace_mult_dist. rewrite Cmod_mult.
       rewrite Rdiv_unfold. rewrite Rmult_1_l.
       rewrite Cmod_R. rewrite Rabs_right.
       rewrite mixed_state_Cmod_plus; try assumption. 
       rewrite Rmult_comm. rewrite <-Rdiv_unfold.
       rewrite Rplus_comm.
       apply Rdiv_in01; apply nz_mixed_state_Cmod_1; assumption.
       assert((/ Cmod (@trace (2^(e0-s0)) (q1 .+ q2)) > 0)%R).
       apply Rinv_0_lt_compat. apply nz_mixed_state_Cmod_1.
       assumption. lra. 
       lia. 
       rewrite <-Reduced_plus.
       rewrite <-Mscale_plus_distr_r.
       rewrite Rdiv_unfold. rewrite Rmult_1_l.
       rewrite <-Reduced_scale. 
       rewrite <-(Reduced_trace _ _ _ s e).
       apply Mixed_State_aux_to01.
       apply Mixed_State_aux_to_Mix_State.
       apply WF_qstate_Reduced. lia.
       split. assumption. lia.  
       lia. apply WF_NZ_Mixed. assumption.
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

      simpl. split. eapply IHF; [ try apply Hq2| try apply Hq1| apply Hq'| | ].
      rewrite Mplus_comm. assumption.
      simpl in H0. 
      rewrite (state_eq_aexp _ (c, q')); try reflexivity; try assumption.
      simpl in H0.
      eapply IHF; [ try apply Hq1| try apply Hq2| apply Hq'| apply H | ].
      simpl in H0. 
      rewrite (state_eq_aexp _ (c, q')); try reflexivity; try assumption.
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
State_eval F (c, Reduced q s2 e2)->
State_eval F (c_update i j c, Reduced (QMeas_fun s0 e0 j q) s2 e2).
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
apply WF_qstate_Reduced. lia. 
apply WF_qstate_QMeas. intuition.
intuition. lia. assumption. assumption.
apply WF_qstate_kron; assumption.
assert(@State_eval s2 e F
(c, ((fun i : nat => 
@Reduced s e
(@kron (2 ^ (s2 - s)) (2 ^ (s2 - s)) (2 ^ (e - s2)) (2 ^ (e - s2)) 
(q0_i i)  (q1_i i)) s2 e) j0))).
eapply (@State_eval_sub_sum s2 e (S n) c 
((fun i : nat => 
@Reduced s e
(@kron (2 ^ (s2 - s)) (2 ^ (s2 - s)) (2 ^ (e - s2)) (2 ^ (e - s2)) 
(q0_i i)  (q1_i i)) s2 e))).
intros.
rewrite Reduced_R .
rewrite (Reduced_r _ (q0_i i0) (q1_i i0)).
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
apply WF_qstate_Reduced. lia. assumption.
lia.  assumption. lia. 
apply WF_qstate_Reduced. lia.
apply WF_qstate_kron; assumption.
simpl in *.
rewrite Reduced_R in *; try reflexivity; auto_wf.
rewrite (Reduced_r _ (q0_i j0 )  (q1_i j0)) in H7 ; try reflexivity; auto_wf.
rewrite QMeas_fun_kron_r; auto_wf.
rewrite (Reduced_r _ (QMeas_fun s0 e0 j (q0_i j0))  (q1_i j0)) ;try reflexivity; auto_wf.
apply s_seman_scale_c. 
assert (@Mixed_State (2^(s2-s)) (QMeas_fun s0 e0 j (q0_i j0))).
apply WF_qstate_QMeas. intuition. intuition.
lia.  
rewrite (@QMeas_fun_kron_r s s2 e) in H4.
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
apply (WF_qstate_Reduced ).
lia.
rewrite <-(@QMeas_fun_sum s  e).
apply WF_qstate_QMeas.
intuition. intuition. lia.
assumption. assumption. 
assumption. 
lia. lia. lia. 
Qed.




Lemma r10'{ s e:nat}: forall c (q: qstate s e) s0 e0 s1 e1 s2 e2 i j F,
s1 <= e1 /\ s2 <= s0 /\ s0 <= e0 /\ e0 <= e2 ->
j < (2^(e0-s0))->
QMeas_fun s0 e0 j (q) <> Zero ->
WF_qstate q->
dstate_Separ [(c, q)] s1 e1 s2 e2 ->
NSet.Subset (Qsys_to_Set s0 e0) (Qsys_to_Set s2 e2)->
NSet.Equal
(NSet.inter (fst (Free_state F))
(fst (MVar <{ i :=M [[s0 e0]] }>))) NSet.empty ->
State_eval F (c, Reduced q s1 e1)->
State_eval F (c_update i j c, Reduced (QMeas_fun s0 e0 j q) s1 e1).
Proof. intros c q s0 e0 s1 e1 s2 e2 i j F Hj Hq Hw. intros.  
simpl in *. 
inversion H0; subst.
clear H0. clear H17.
rewrite big_sum_par_trace in *; try lia. 
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
apply WF_qstate_Reduced. lia. 
apply WF_qstate_QMeas. intuition.
intuition. lia. assumption. assumption.
apply WF_qstate_kron; assumption.
assert(@State_eval s s2 F
(c, ((fun i : nat => 
@Reduced s e
(@kron (2 ^ (s2 - s)) (2 ^ (s2 - s)) (2 ^ (e - s2)) (2 ^ (e - s2)) 
(q0_i i)  (q1_i i)) s s2) j0))).
eapply (@State_eval_sub_sum s s2 (S n) c 
((fun i : nat => 
@Reduced s e
(@kron (2 ^ (s2 - s)) (2 ^ (s2 - s)) (2 ^ (e - s2)) (2 ^ (e - s2)) 
(q0_i i)  (q1_i i)) s s2))).
intros.
rewrite Reduced_L ; try lia. 
rewrite (Reduced_l _ (q0_i i0) (q1_i i0)); auto_wf.
pose (H10 i0). 
pose (H11 i0).
destruct o.  destruct o0.
left. econstructor.
 apply Mixed_State_scale_c.
 apply H8. apply mixed_state_trace_in01.
 apply H9. apply mixed_state_trace_real.
 apply H9. lia. 
right. rewrite H9. rewrite Zero_trace. rewrite Mscale_0_l.
reflexivity. rewrite H8.
right.  rewrite Mscale_0_r.
reflexivity. reflexivity.  auto_wf. 
rewrite <-(@big_sum_par_trace s e  _  _ s  s2).
apply WF_qstate_Reduced. lia. assumption.
lia.  assumption. lia. 
apply WF_qstate_Reduced. lia.
apply WF_qstate_kron; assumption.
simpl in *.
rewrite Reduced_L in *; try reflexivity; auto_wf; try lia. 
rewrite (Reduced_l _ (q0_i j0 )  (q1_i j0)) in H7 ; try reflexivity; auto_wf.
rewrite QMeas_fun_kron_l; auto_wf.
rewrite (Reduced_l _ (q0_i j0) (QMeas_fun s0 e0 j (q1_i j0))  ) ;try reflexivity; auto_wf.
apply s_seman_scale_c. 
assert (@Mixed_State (2^(e-s2)) (QMeas_fun s0 e0 j (q1_i j0))).
apply WF_qstate_QMeas. intuition. intuition.
lia.  
rewrite (@QMeas_fun_kron_l s s2 e) in H4.
intro. rewrite H8 in H4. rewrite kron_0_r in H4.
destruct H4. reflexivity. assumption. auto_wf.
lia. lia. assumption.
split.   
apply mixed_state_trace_in01. assumption. 
apply mixed_state_trace_real. assumption. 
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
apply mixed_state_trace_gt0. apply H6.
apply mixed_state_trace_real. apply H6.
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
rewrite <-(@big_sum_par_trace s e  _  _ s s2).
apply (@WF_qstate_not_Zero s s2).   
apply (WF_qstate_Reduced ).
lia.
rewrite <-(@QMeas_fun_sum s  e).
apply WF_qstate_QMeas.
intuition. intuition. lia.
assumption. assumption. 
assumption. 
lia. lia. 
Qed.

Lemma d_reduced_not_nil{s e:nat}: forall s' e' (mu: list (state s e)) (mu':list (state s' e')),
d_reduced mu s' e'= mu'->
mu <> [] -> mu'<>[].
Proof. induction mu; intros. destruct H0. reflexivity.
       inversion_clear H. destruct a.  simpl.
       discriminate. 
Qed.

Lemma rule_f_classic_assn{s e:nat}: forall sigma (rho:qstate s e) F (i:nat) a,  
NSet.Equal (NSet.inter (fst (Free_state F)) (NSet.add i (NSet.empty))) NSet.empty->
State_eval F (sigma, rho)->
State_eval F (c_update i a sigma, rho).
Proof. intros. 
       simpl in H.
       apply cstate_eq_F with sigma. 
       unfold cstate_eq.
       intros. rewrite c_update_find_not.
       reflexivity.
       unfold not.
       intros. rewrite<-H2 in *.
       apply (In_inter_empty _ _ i) in H. 
       destruct H. assumption. 
       apply NSet.add_1. reflexivity.
        assumption. 
Qed.


Ltac quan_solve c q:=
       try  match goal with 
       H:ceval_single ?x ?y ?z |-_ => inversion H; subst; clear H end;
       try  match goal with 
       H:ceval_single ?x [] ?z |-_ => inversion_clear H; try rewrite map2_nil_r  end;
       try  match goal with 
       H: existT ?a ?b ?c = existT ?x ?y ?z|-_ => apply inj_pair2_eq_dec in H end;
       try  match goal with 
       H: existT ?a ?b ?c = existT ?x ?y ?z|-_ => apply inj_pair2_eq_dec in H; destruct H end;
       try apply Nat.eq_dec;  try rewrite d_reduced_map2;
       try  match goal with 
       H:State_eval_dstate ?x ?z |-_ => inversion_clear H end;
       try match goal with 
       H2: NSet.Subset ?a ?b |- _ =>simpl in H2 end;
       try match goal with 
       H2: NSet.Subset (NSet.union ?a ?b) ?c |- _ => pose H2 as H2'; apply subset_union in H2';
       destruct H2' as [H2' H2'']; apply subset_Qsys in H2' end;
       try match goal with 
       H2'': NSet.Subset ?a ?b |- _ => pose H2'' as H2''';  apply subset_Qsys in H2''' end;  try lia;
       assert(WF_dstate_aux [(c,q)]); try apply WF_state_dstate_aux;
       try inversion_clear Hw; try assumption;
       try  match goal with 
       H:dstate_Separ ?x ?y ?z ?k ?j|-_ => inversion H; subst; clear H end.
       

Ltac d_seman_app_solve s e  i:=
try apply d_seman_app_aux; try  apply WF_d_reduced; try lia;
try eapply WF_ceval  with _ _ ;
try apply ceval_Qinit; try apply ceval_QUnit_One;
try apply ceval_QUnit_Ctrl ; try match goal with
H: big_app' ?f ?n ?mu'' |- _  => try apply (ceval_QMeas _ _ s e i mu''); try assumption end;
try  match goal with 
H:ceval_single ?x ?y ?z |-_ => try apply H end; try assumption.


Lemma r4_meas{s e:nat}:forall s0 e0 s2 c (q:qstate s e) mu i F, 
NSet.Equal (NSet.inter (fst (Free_state F)) (fst (MVar <{ i :=M [[s0 e0]] }>)))
  NSet.empty ->
s <= s0 /\ s0 <= e0 /\ e0 <= s2 <= e->
NSet.Subset (Qsys_to_Set s0 e0) (Qsys_to_Set s s2)->
WF_dstate_aux [(c,q)]->
big_app' (fun j : nat =>
         (c_update i j c,
          QMeas_fun s0 e0 j q))
        (2 ^ (e0 - s0)) mu->
dstate_Separ [(c, q)] s s2 s2 e->
State_eval F (c, Reduced q s2 e)->
State_eval_dstate F (d_reduced mu s2 e).
Proof. intros s0 e0 s2 c q mu i F H' H H0'. intros. 

pose H1 as H1'.
apply (d_reduced_app' _ s2 e) in H1'. destruct H1' . destruct H4 as [H1' H4].
rewrite H4.   
eapply (big_app_seman ((2 ^ (e0 - s0))) (fun j : nat =>
(c_update i j c,
 Reduced (QMeas_fun s0 e0 j _ ) s2 e))); try apply H1.
 intros. split.    
 assert([(c_update i j c,
 @Reduced s e (QMeas_fun s0 e0 j q ) s2 e)] 
 = @d_reduced s e [(c_update i j c, (QMeas_fun s0 e0 j q))] s2 e).
 reflexivity. rewrite H7.
 apply WF_d_reduced. lia.
 apply WF_state_dstate_aux.
 unfold WF_state. simpl. 
 apply WF_qstate_QMeas. intuition.
 intuition. lia. simpl in H6. intro.
 rewrite H8 in H6. rewrite Par_trace_Zero in H6.
 destruct H6. reflexivity. assumption.
 inversion_clear H0. assumption.
 simpl. econstructor.
 apply r10 with s s2; try lia. simpl in H6.    
 intro.
 rewrite H7 in H6. rewrite Par_trace_Zero in H6.
 destruct H6. reflexivity. 
  inversion_clear H0. intuition. 
   assumption. assumption.   assumption. assumption.  
  econstructor. assumption.  
  rewrite <-H4. apply WF_d_reduced. lia.
  eapply (WF_qstate_QMeas_app s0 e0 q c i (2 ^ (e0 - s0)) ). lia.  
 lia.    inversion_clear H0. assumption.  assumption.
   apply pow_gt_0. apply d_reduced_not_nil with mu.
   assumption. intro. assert(d_trace_aux mu =0%R).
   rewrite H5. reflexivity. 
   assert(d_trace_aux mu =  (s_trace (c,q))).
   apply QMeas_trace' with s0 e0 i. intuition.
   lia. apply WWF_qstate_to_WF_qstate.
   inversion_clear H0. apply H7. assumption.
   assert(s_trace (c,q)>0)%R. unfold  s_trace.
   simpl. apply nz_nz_mixed_state_Cmod_1. inversion_clear H0.
   apply H8. rewrite <- H7 in H8. rewrite H6 in H8.
   lra. lia. simpl. intros. apply mixed_super_ge_0; try lia.
   auto_wf. 
   apply Mixed_State_aux_to_Mix_State. inversion_clear H0.
   apply H5. 
       
Qed.

Lemma r4'_meas{s e:nat}:forall s0 e0 s2 c (q:qstate s e) mu i F, 
NSet.Equal (NSet.inter (fst (Free_state F)) (fst (MVar <{ i :=M [[s0 e0]] }>)))
  NSet.empty ->
s <= s2 /\ s2 <= s0 /\ s0 <= e0 <= e->
NSet.Subset (Qsys_to_Set s0 e0) (Qsys_to_Set s2 e)->
WF_dstate_aux [(c,q)]->
big_app' (fun j : nat =>
         (c_update i j c,
          QMeas_fun s0 e0 j q))
        (2 ^ (e0 - s0)) mu->
dstate_Separ [(c, q)] s s2 s2 e->
State_eval F (c, Reduced q s s2)->
State_eval_dstate F (d_reduced mu s s2).
Proof. intros s0 e0 s2 c q mu i F H' H H0'. intros. 

pose H1 as H1'.
apply (d_reduced_app' _ s s2) in H1'. destruct H1' . destruct H4 as [H1' H4].
rewrite H4.   
eapply (big_app_seman ((2 ^ (e0 - s0))) (fun j : nat =>
(c_update i j c,
 Reduced (QMeas_fun s0 e0 j _ ) s s2))); try apply H1.
 intros. split.    
 assert([(c_update i j c,
 @Reduced s e (QMeas_fun s0 e0 j q ) s s2)] 
 = @d_reduced s e [(c_update i j c, (QMeas_fun s0 e0 j q))] s s2).
 reflexivity. rewrite H7.
 apply WF_d_reduced. lia.
 apply WF_state_dstate_aux.
 unfold WF_state. simpl. 
 apply WF_qstate_QMeas. intuition.
 intuition. lia. simpl in H6. intro.
 rewrite H8 in H6. rewrite Par_trace_Zero in H6.
 destruct H6. reflexivity. assumption.
 inversion_clear H0. assumption.
 simpl. econstructor.
 apply r10' with  s2 e; try lia. simpl in H6.    
 intro.
 rewrite H7 in H6. rewrite Par_trace_Zero in H6.
 destruct H6. reflexivity. 
  inversion_clear H0. intuition. 
   assumption. assumption.   assumption. assumption.  
  econstructor. assumption.  
  rewrite <-H4. apply WF_d_reduced. lia.
  eapply (WF_qstate_QMeas_app s0 e0 q c i (2 ^ (e0 - s0)) ). lia.  
 lia.    inversion_clear H0. assumption.  assumption.
   apply pow_gt_0. apply d_reduced_not_nil with mu.
   assumption. intro. assert(d_trace_aux mu =0%R).
   rewrite H5. reflexivity. 
   assert(d_trace_aux mu =  (s_trace (c,q))).
   apply QMeas_trace' with s0 e0 i. intuition.
   lia. apply WWF_qstate_to_WF_qstate.
   inversion_clear H0. apply H7. assumption.
   assert(s_trace (c,q)>0)%R. unfold  s_trace.
   simpl. apply nz_mixed_state_Cmod_1. inversion_clear H0.
   apply H8. rewrite <- H7 in H8. rewrite H6 in H8.
   lra. lia. simpl. intros. apply mixed_super_ge_0; try lia.
   auto_wf. 
   apply Mixed_State_aux_to_Mix_State. inversion_clear H0.
   apply H5. 
       
Qed.


Lemma r4{s e:nat}: forall c s0 e0 s1 e1
(mu mu':list (cstate *qstate s e)) F ,
s <= s1 /\ s1 <= e1 <= e->
WF_dstate_aux mu ->
ceval_single c mu mu'-> 
dstate_Separ mu s0 e0 s1 e1->
NSet.Equal (NSet.inter (fst (Free_state F)) (fst (MVar c))) (NSet.empty)  ->
(NSet.Subset (snd (MVar c)) (Qsys_to_Set s0 e0)) ->
State_eval_dstate F (d_reduced mu s1 e1) ->
State_eval_dstate F (d_reduced mu' s1 e1).
Proof. induction c. 
-- {intros s0 e0 s1 e1 mu mu' F Hs Hw. intros. apply ceval_skip_1 in H. subst. intuition. }
-- induction mu; intros mu' F Hs Hw; intros. 
  {inversion  H; subst. intuition.  }
   {destruct a0.  
   
   inversion H; subst. clear H.
   rewrite d_reduced_map2.
   inversion_clear H3.
   destruct mu. inversion_clear H10.
   simpl. 
   econstructor.  
   apply (@rule_f_classic_assn s1 e1 c (Reduced q s1 e1)); try assumption.
   econstructor.
   apply d_seman_app_aux.
   apply WF_d_reduced. lia. 
    apply WF_state_dstate_aux.
   apply WF_state_eq with (c, q).
   reflexivity. inversion_clear Hw. assumption.
   apply WF_d_reduced. lia. 
    apply WF_ceval with <{ i := a }> (p :: mu).
   inversion_clear Hw. assumption.
   assumption. 
   simpl. econstructor. 
   apply (@rule_f_classic_assn s1 e1 c (Reduced q s1 e1)); try assumption.
   econstructor. 
apply IHmu. assumption. inversion_clear Hw. assumption.
assumption. 
inversion H0; subst.   intuition.
assumption. assumption.
destruct p. simpl. assumption. } 
--  induction mu; intros mu' F Hs Hw; intros. 
{inversion  H; subst. intuition.  }
 {destruct a0.  
 
 inversion H; subst. assumption.  }
--{ intros s0 e0 s1 e1 mu mu'  F Hs  Hw. intros. inversion H; subst. intuition.
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
   rewrite d_reduced_map2;
   inversion_clear H3.
   destruct mu. inversion H13;subst.
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
   apply WF_d_reduced.
   lia.  apply WF_ceval  with c1 [(c, q)].
   apply WF_state_dstate_aux.
   inversion_clear Hw. assumption.
   assumption.
   apply WF_d_reduced. lia.  
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

   destruct mu. inversion H13;subst.
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
   apply WF_d_reduced. lia. 
    apply WF_ceval  with c2 [(c, q)].
   apply WF_state_dstate_aux.
   inversion_clear Hw. assumption.
   assumption.
   apply WF_d_reduced. lia. 
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
{  intros. remember <{while b do c end}> as original_command eqn:Horig. 
   induction H1;  try inversion Horig; subst.
   simpl in H5. destruct H5. inversion_clear H0. clear H8. 
   assert( WF_dstate_aux [(sigma, rho)]). apply WF_state_dstate_aux. assumption.
   assert( dstate_Separ [(sigma, rho)] s0 e0 s1 e1). inversion_clear H2.
   econstructor; try assumption. apply H11. apply H12. apply H13. econstructor.
  assert( WF_dstate_aux mu1). 
  apply WF_ceval with c [(sigma, rho)]; try assumption. 
  assert(WF_dstate_aux mu' ).
  apply WF_ceval with <{ while b do c end }> mu1 ; try assumption.
  assert(WF_dstate_aux mu'' ). 
  apply WF_ceval with <{ while b do c end }> mu ; try assumption. simpl in H4.
  destruct mu.  inversion_clear H1_. rewrite map2_nil_r. 
  apply IHceval_single3; try assumption. 
  eapply r3; try lia.  apply H1_0. apply H8. apply H3. 
  left. assumption.  
  eapply (IHc s0 e0); try apply H1_0; try  lia; try assumption.
   rewrite d_reduced_map2. 
   apply d_seman_app_aux. 
   apply WF_d_reduced. lia. assumption.
   apply WF_d_reduced. lia. assumption.
   apply IHceval_single3; try reflexivity; try assumption.
   eapply r3; try lia; try apply H1_0; try assumption. 
   apply H3. left. assumption.   
   eapply (IHc s0 e0); try apply H1_0; try lia; try assumption.  
   inversion_clear H5.  
   simpl. econstructor. assumption. econstructor.
   apply IHceval_single1; try assumption. 
   inversion_clear H2. assumption. inversion_clear H5. destruct p. simpl.
   assumption.
   inversion_clear H0. clear H10. 
   assert( WF_dstate_aux [(sigma, rho)]). apply WF_state_dstate_aux. assumption.
   assert(WF_dstate_aux mu' ).
   apply WF_ceval with <{ while b do c end }> mu; try assumption.
   assert( dstate_Separ [(sigma, rho)] s0 e0 s1 e1). inversion_clear H2.
   econstructor; try assumption. apply H14. apply H15. apply H16. econstructor. 
   destruct mu.  inversion_clear H7. rewrite map2_nil_r. 
    inversion_clear H5.  
    simpl. econstructor. assumption. econstructor.
    rewrite d_reduced_map2. 
   apply d_seman_app_aux. 
   apply WF_d_reduced. lia. assumption.
   apply WF_d_reduced. lia. assumption.
   inversion_clear H5.  
   simpl. econstructor. assumption. econstructor.
   apply IHceval_single; try assumption. 
   inversion_clear H2. assumption. inversion_clear H5. destruct p. simpl.
   assumption.

  }
{induction mu; intros mu' F Hs Hw; intros.
{inversion  H; subst. intuition.  }
 {destruct a.  

 destruct mu; quan_solve c q;
 [try econstructor;try econstructor;
 try rewrite (Reduced_QInit_r c _ _ _  s s2); try assumption;
 try econstructor; try reflexivity; try assumption; try lia | d_seman_app_solve s e i]; 
 try econstructor;try econstructor;
 try rewrite (Reduced_QInit_r c _ _ _  s s2); try assumption;
 try econstructor; try reflexivity; try assumption; try lia; try econstructor;
 try  match goal with 
  IHmu: _ |-_ =>
  apply IHmu; destruct p; try assumption end.
   }  }

{induction mu; intros mu' F Hs Hw; intros.
{inversion  H; subst. intuition.  }
 {destruct a.
 
 destruct mu; quan_solve c q.
 try econstructor;try econstructor.
  try rewrite (Reduced_QUnit_one_r c _ _ _  _ s s2); try assumption;
 try econstructor; try reflexivity; try assumption; try lia.
 d_seman_app_solve s e i; 
 try econstructor;try econstructor;
 try rewrite (Reduced_QUnit_one_r c _ _ _  _ s s2); try assumption;
 try econstructor; try reflexivity; try assumption; try lia; try econstructor;
 try  match goal with 
  IHmu: _ |-_ =>
  apply IHmu; destruct p; try assumption end.
  }  }


{induction mu; intros mu' F Hs Hw; intros.
{inversion  H; subst. intuition.  }
 {destruct a. 
 
 destruct mu; quan_solve c q. 
 try econstructor;try econstructor;
  try rewrite (Reduced_QUnit_Ctrl_r c _ _ _ _ _  _ s s3); try assumption;
 try econstructor; try reflexivity; try assumption; try lia. 
 d_seman_app_solve s e i; 
 try econstructor;try econstructor;
 try rewrite (Reduced_QUnit_Ctrl_r c _ _ _  _ _ _ s s3); try assumption;
 try econstructor; try reflexivity; try assumption; try lia; try econstructor;
 try  match goal with 
  IHmu: _ |-_ =>
  apply IHmu; destruct p; try assumption end. 
  }  }

{induction mu; intros mu' F Hs Hw; intros.
{inversion  H; subst. intuition.  }
 {destruct a.
 
 destruct mu; quan_solve c q. 
 eapply (r4_meas s0 e0 _ c _ _ i); try apply H3; try assumption;  try lia;
 try econstructor; try reflexivity; try assumption; try lia; try econstructor.


 d_seman_app_solve s e i; try apply H3. eapply (ceval_QMeas  c  _ s0 e0 i); try apply H13; try lia.
 try econstructor;try econstructor;
 eapply (r4_meas s0 e0 _ c _ _ i); try apply H3; try assumption;  try lia;
 try econstructor; try reflexivity; try assumption; try lia; try econstructor.
 try  match goal with 
  IHmu: _ |-_ =>
  apply IHmu; destruct p; try assumption end. 
 }  }
Qed.






Lemma seman_eq_two'''{s e:nat}: forall F r c (q:qstate s e),
Considered_Formula (F) /\
(r <= e /\ snd (option_free (Free_State F)) <=r /\ fst (option_free (Free_State F)) < snd (option_free (Free_State F)))->
WF_qstate q->
State_eval F (c, q) -> 
exists 
(q1:qstate (fst (option_free (Free_State F))) (snd (option_free (Free_State F))))
(q2:qstate  (snd (option_free (Free_State F))) r), 
(q_combin' q1 q2 (@Reduced s e q  (fst (option_free (Free_State F))) r)).
Proof. intros F r c q H Hw. intros. 
       assert(s<=fst (option_free (Free_State F))). 
       pose (State_eval_dom F c q H0). destruct o.
       rewrite H1 in *. simpl in *. lia. 
        apply H1.  
        remember ((snd (option_free (Free_State F)))) as x.
        remember ((fst (option_free (Free_State F)))) as s'.
        simpl.  
        remember ((Reduced q s' r)).
       assert(exists (q1:qstate s' x) (q2: qstate x r), 
       and (WF_qstate q1 /\ WF_qstate q2)
       (q0 = @kron (2^(x-s')) (2^(x-s')) (2^(r-x))  (2^(r-x)) q1 q2)).
       apply Odot_Sepear''; try lia. 
       rewrite Heqq0. apply WF_qstate_Reduced; try lia. 
       assumption. 
       rewrite Heqq0. rewrite Reduced_assoc; try lia. 
       apply State_eval_pure  in H0. destruct H0.
       subst. rewrite H0 in *. simpl in *.  lia. rewrite Heqs'. rewrite Heqx. apply H0.
      apply H. assumption. 
       destruct H2. destruct H2.
       destruct H2. rewrite H3. 
       exists x0. exists x1.
       econstructor; try reflexivity; try apply H2.
Qed.


Lemma seman_eq_two''{s e:nat}: forall F l  c (q:qstate s e),
Considered_Formula (F) /\
(s <= l /\ l <= fst (option_free (Free_State F)) /\ fst (option_free (Free_State F)) < snd (option_free (Free_State F)))->
WF_qstate q->
State_eval F (c, q) -> 
exists 
(q1:qstate l (fst (option_free (Free_State F))))
(q2:qstate (fst (option_free (Free_State F))) (snd (option_free (Free_State F)))), 
(q_combin' q1 q2 (@Reduced s e q l (snd (option_free (Free_State F))))).
Proof. intros F l c q H Hw. intros. 
        assert(snd (option_free (Free_State F))<=e). 
        pose (State_eval_dom F c q H0). destruct o.
        rewrite H1 in *. simpl in *. 
        subst. lia. apply H1.  
        remember ((fst (option_free (Free_State F)))) as x.
        remember ((snd (option_free (Free_State F)))) as e'.
        simpl.  
        remember ((Reduced q l e')).
       assert(exists (q1:qstate l x) (q2: qstate x e'), 
       and (WF_qstate q1 /\ WF_qstate q2)
       (q0 = @kron (2^(x-l)) (2^(x-l)) (2^(e'-x))  (2^(e'-x)) q1 q2)).
       apply Odot_Sepear'''; try lia.  
       rewrite Heqq0. apply WF_qstate_Reduced; try lia; try assumption.
       rewrite Heqq0. rewrite Reduced_assoc; try lia. 
       apply State_eval_pure  in H0; try assumption; try apply H. 
       destruct H0. subst. rewrite H0 in *. simpl in *. lia. rewrite Heqx. rewrite Heqe'. apply H0.
       destruct H2. destruct H2.
       destruct H2. rewrite H3. 
       exists x0. exists x1.
       econstructor; try reflexivity; try apply H2.
Qed.


Lemma r1{s e:nat}: forall (mu : list (cstate *qstate s e)) F l,
Considered_Formula F /\
(s <= l /\ l <= fst (option_free (Free_State F)) /\ fst (option_free (Free_State F)) < snd (option_free (Free_State F)))->
State_eval_dstate F mu->
WF_dstate_aux mu ->
(dstate_Separ (d_reduced mu l (snd (option_free (Free_State F)))) 
l (fst (option_free (Free_State F))) (fst (option_free (Free_State F))) (snd (option_free (Free_State F)))).
Proof. induction mu; intros. 
      simpl. intuition.
      destruct mu. 
      destruct a. 
      simpl.

      assert(exists (q1:qstate l (fst (option_free (Free_State F)))) 
      (q2:qstate (fst (option_free (Free_State F))) (snd (option_free (Free_State F)))), 
      (q_combin' q1 q2 (@Reduced s e q l (snd (option_free (Free_State F)))))).
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
      assert(exists (q1:qstate l (fst (option_free (Free_State F))))
      (q2:qstate (fst (option_free (Free_State F))) (snd (option_free (Free_State F)))), 
      (q_combin' q1 q2 (@Reduced s e q l (snd (option_free (Free_State F)))))).
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
(r <= e /\ snd (option_free (Free_State F)) <=r /\ fst (option_free (Free_State F)) < snd (option_free (Free_State F)))->
State_eval_dstate F mu->
WF_dstate_aux mu ->
(dstate_Separ (d_reduced mu  (fst (option_free (Free_State F))) r) 
(fst (option_free (Free_State F))) (snd (option_free (Free_State F))) (snd (option_free (Free_State F))) r).
Proof. induction mu; intros. 
      simpl. intuition.
      destruct mu. 
      destruct a. 
      simpl.

      assert(exists 
      (q1:qstate (fst (option_free (Free_State F))) (snd (option_free (Free_State F))))
      (q2:qstate  (snd (option_free (Free_State F))) r), 
      (q_combin' q1 q2 (@Reduced s e q  (fst (option_free (Free_State F))) r))).
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
      (q1:qstate (fst (option_free (Free_State F))) (snd (option_free (Free_State F))))
      (q2:qstate  (snd (option_free (Free_State F))) r), 
      (q_combin' q1 q2 (@Reduced s e q  (fst (option_free (Free_State F))) r))).
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
s <= s0 /\ s0 <= e0 <= e->
WF_dstate_aux mu ->
ceval_single c mu mu'-> 
dstate_Separ mu s0 e0 s1 e1->
NSet.Equal (NSet.inter (fst (Free_state F)) (fst (MVar c))) (NSet.empty)  ->
(NSet.Subset (snd (MVar c)) (Qsys_to_Set s1 e1)) ->
State_eval_dstate F (d_reduced mu s0 e0) ->
State_eval_dstate F (d_reduced mu' s0 e0).
Proof. induction c. 
-- {intros s0 e0 s1 e1 mu mu' F Hs Hw. intros. apply ceval_skip_1 in H. subst. intuition. }
-- induction mu; intros mu' F Hs Hw; intros. 
  {inversion  H; subst. intuition.  }
   {destruct a0. inversion H; subst. clear H.
   rewrite d_reduced_map2.
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
   apply WF_d_reduced. lia. 
    apply WF_state_dstate_aux.
   apply WF_state_eq with (c, q).
   reflexivity. inversion_clear Hw. assumption.
   apply WF_d_reduced. lia. 
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
-- induction mu; intros mu' F Hs Hw; intros. 
{inversion  H; subst. intuition.  }
 {destruct a0. inversion H; subst. assumption. }
--{ intros s0 e0 s1 e1 mu mu'  F Hs  Hw. intros. inversion H; subst. intuition.
   apply IHc2 with s1 e1 mu1. assumption.
   apply WF_ceval with c1 ((sigma, rho) :: mu0).
   assumption. assumption. 
   assumption. 
   apply r3 with c1 ((sigma, rho) :: mu0)  F. inversion_clear H0.
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
   apply IHc1 with s1 e1  ((sigma, rho) :: mu0).
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
   rewrite d_reduced_map2;
   inversion_clear H3.
   destruct mu. inversion H13;subst.
   simpl. repeat rewrite map2_nil_r.
   apply IHc1 with s1 e1 [(c,q)].
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
   apply WF_d_reduced.
   lia.  apply WF_ceval  with c1 [(c, q)].
   apply WF_state_dstate_aux.
   inversion_clear Hw. assumption.
   assumption.
   apply WF_d_reduced. lia.  
   apply WF_ceval with <{ if b then c1 else c2 end }> (p :: mu).
   inversion_clear Hw.
   assumption. assumption.
   apply IHc1 with s1 e1 [(c,q)].
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

   destruct mu. inversion H13;subst.
   simpl. repeat rewrite map2_nil_r.
   apply IHc2 with s1 e1 [(c,q)].
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
   apply WF_d_reduced. lia. 
    apply WF_ceval  with c2 [(c, q)].
   apply WF_state_dstate_aux.
   inversion_clear Hw. assumption.
   assumption.
   apply WF_d_reduced. lia. 
   apply WF_ceval with <{ if b then c1 else c2 end }> (p :: mu).
   inversion_clear Hw.
   assumption. assumption.
   apply IHc2 with s1 e1 [(c,q)].
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
{ intros. remember <{while b do c end}> as original_command eqn:Horig. 
induction H1;  try inversion Horig; subst.
simpl in H5. destruct H5. inversion_clear H0. clear H8. 
assert( WF_dstate_aux [(sigma, rho)]). apply WF_state_dstate_aux. assumption.
assert( dstate_Separ [(sigma, rho)] s0 e0 s1 e1). inversion_clear H2.
econstructor; try assumption. apply H11. apply H12. apply H13. econstructor.
assert( WF_dstate_aux mu1). 
apply WF_ceval with c [(sigma, rho)]; try assumption. 
assert(WF_dstate_aux mu' ).
apply WF_ceval with <{ while b do c end }> mu1 ; try assumption.
assert(WF_dstate_aux mu'' ). 
apply WF_ceval with <{ while b do c end }> mu ; try assumption. simpl in H4.
destruct mu.  inversion_clear H1_. rewrite map2_nil_r. 
apply IHceval_single3; try assumption. 
eapply r3. inversion_clear H2. try lia.   apply H1_0. apply H8. apply H3. 
right. assumption.  
eapply (IHc _ _ s1 e1); try apply H1_0; try  lia; try assumption.
rewrite d_reduced_map2. 
apply d_seman_app_aux. 
apply WF_d_reduced. lia. assumption.
apply WF_d_reduced. lia. assumption.
apply IHceval_single3; try reflexivity; try assumption.
eapply r3.  inversion_clear H2. try lia.  try apply H1_0; try assumption. 
assumption. apply H3. right. assumption.   
eapply (IHc _ _ s1 e1); try apply H1_0; try lia; try assumption.  
inversion_clear H5.  
simpl. econstructor. assumption. econstructor.
apply IHceval_single1; try assumption. 
inversion_clear H2. assumption. inversion_clear H5. destruct p. simpl.
assumption.
inversion_clear H0. clear H10. 
assert( WF_dstate_aux [(sigma, rho)]). apply WF_state_dstate_aux. assumption.
assert(WF_dstate_aux mu' ).
apply WF_ceval with <{ while b do c end }> mu; try assumption.
assert( dstate_Separ [(sigma, rho)] s0 e0 s1 e1). inversion_clear H2.
econstructor; try assumption. apply H14. apply H15. apply H16. econstructor.
destruct mu.  inversion_clear H7. rewrite map2_nil_r. 
 inversion_clear H5.  
 simpl. econstructor. assumption. econstructor.
 rewrite d_reduced_map2. 
apply d_seman_app_aux. 
apply WF_d_reduced. lia. assumption.
apply WF_d_reduced. lia. assumption.
inversion_clear H5.  
simpl. econstructor. assumption. econstructor.
apply IHceval_single; try assumption. 
inversion_clear H2. assumption. inversion_clear H5. destruct p. simpl.
assumption. }
{induction mu; intros mu' F Hs Hw; intros.
{inversion  H; subst. intuition.  }
 {destruct a.  

 destruct mu; quan_solve c q;
 [try econstructor;try econstructor;
 try rewrite (Reduced_QInit_l c _ _ _ _ _ s2 e); try assumption;
 try econstructor; try reflexivity; try assumption; try lia | d_seman_app_solve s e i]; 
 try econstructor;try econstructor;
 try rewrite (Reduced_QInit_l c _ _ _ _ _ s2 e); try assumption;
 try econstructor; try reflexivity; try assumption; try lia; try econstructor;
 try  match goal with 
  IHmu: _ |-_ =>
  apply IHmu; destruct p; try assumption end.
   }  }

{induction mu; intros mu' F Hs Hw; intros.
{inversion  H; subst. intuition.  }
 {destruct a.
 
 destruct mu; quan_solve c q.
 try econstructor;try econstructor.
  try rewrite (Reduced_QUnit_one_l c _ _ _  _ _ _ s2 e); try assumption;
 try econstructor; try reflexivity; try assumption; try lia.
 d_seman_app_solve s e i; 
 try econstructor;try econstructor;
 try rewrite (Reduced_QUnit_one_l c _ _ _  _ _ _ s2 e); try assumption;
 try econstructor; try reflexivity; try assumption; try lia; try econstructor;
 try  match goal with 
  IHmu: _ |-_ =>
  apply IHmu; destruct p; try assumption end.
  }  }


{induction mu; intros mu' F Hs Hw; intros.
{inversion  H; subst. intuition.  }
 {destruct a. 
 
 destruct mu; quan_solve c q. 
 try econstructor;try econstructor;
  try rewrite (Reduced_QUnit_Ctrl_l c _ _ _ _ _  _ _ _  s3 e); try assumption;
 try econstructor; try reflexivity; try assumption; try lia.
 d_seman_app_solve s e i; 
 try econstructor;try econstructor;
 try rewrite (Reduced_QUnit_Ctrl_l c _ _ _ _ _  _ _ _ s3 e); try assumption;
 try econstructor; try reflexivity; try assumption; try lia; try econstructor;
 try  match goal with 
  IHmu: _ |-_ =>
  apply IHmu; destruct p; try assumption end. 

  }  }

{induction mu; intros mu' F Hs Hw; intros.
{inversion  H; subst. intuition.  }
 {destruct a.
 
 destruct mu; quan_solve c q. 
 eapply (r4'_meas s0 e0 _ c _ _ i); try apply H3; try assumption;  try lia;
 try econstructor; try reflexivity; try assumption; try lia; try econstructor.


 d_seman_app_solve s e i; try apply H3. eapply (ceval_QMeas  c  _ s0 e0 i); try apply H13; try lia.
 try econstructor;try econstructor;
 eapply (r4'_meas s0 e0 _ c _ _ i); try apply H3; try assumption;  try lia;
 try econstructor; try reflexivity; try assumption; try lia; try econstructor.
 try  match goal with 
  IHmu: _ |-_ =>
  apply IHmu; destruct p; try assumption end. 
 }  }
Qed.


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

Lemma subset_empty: forall a, NSet.Subset NSet.empty a.
Proof. intros.  pose (NSet.empty_1). unfold NSet.Empty in e.
       unfold NSet.Subset. intros. apply e in H. destruct H.
Qed.

Lemma Qsys_subset: 
forall r s e l  : nat,
s <=l /\ l <= r /\ r <= e
->NSet.Subset (Qsys_to_Set l r) (Qsys_to_Set s e).
Proof.
       unfold Qsys_to_Set. induction r; intros. 
       pose (NSet.empty_1). unfold NSet.Empty in e0.
      simpl. apply subset_empty.
      simpl. 
      destruct H. destruct H0.
      assert(l=S r \/ l<> S r).
      apply Classical_Prop.classic.
      destruct H2.
      rewrite H2. 
       assert(S r <? S r =false).
       apply ltb_ge. lia. 
       rewrite H3. apply subset_empty. 
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
       pose(NSet.empty_1). unfold NSet.Empty in e0.
       apply e0 in H4. destruct H4. 
        lia. 
       apply IHr with l.
       lia.
       apply NSet.add_3 in H4.
       assumption.
       lia.  
Qed.


Lemma option_not_None{ A:Type }: forall (s: option A), 
s<> None -> exists a, s= Some a. 
Proof. intros.  destruct s. exists a. reflexivity.
      destruct H. reflexivity.  
  
Qed.


Lemma min_empty : forall s, 
NSet.Empty s -> 
NSet.min_elt s = None .
Proof. intros. unfold NSet.Empty in H. 
       apply Classical_Prop.NNPP.
      intro. apply option_not_None in H0.
      destruct H0. pose (H  x).
      destruct n. apply NSet.min_elt_1. assumption.
Qed.

Lemma max_empty : forall s, 
NSet.Empty s -> 
NSet.max_elt s = None .
Proof. intros. unfold NSet.Empty in H. 
      apply Classical_Prop.NNPP.
      intro. apply option_not_None in H0.
      destruct H0. pose (H  x).
      destruct n. apply NSet.max_elt_1. assumption.
Qed.


Lemma min_not_empty : forall s, 
~NSet.Empty s -> 
(exists a, NSet.min_elt s = Some a) .
Proof. intros. apply option_not_None. 
       intro. apply NSet.min_elt_3 in H0. 
       destruct H. assumption.
Qed.

Lemma max_not_empty : forall s, 
~NSet.Empty s -> 
(exists a, NSet.max_elt s = Some a) .
Proof. intros. apply option_not_None. 
       intro. apply NSet.max_elt_3 in H0. 
       destruct H. assumption.
Qed.


Lemma Nexist: forall (A:Type)(P:A->Prop),
(~(exists x, (P x)))->(forall x, ~(P x) ).
Proof. intros. unfold not in H. unfold not.
       intros. assert((exists x : A, P x)).
       exists x. assumption.
       apply H in H1.
      assumption.
Qed. 


Lemma  not_empty_some:  forall s, 
~ NSet.Empty s -> (exists a, NSet.In a s).
Proof. intros. unfold NSet.Empty in *.
       apply Classical_Prop.NNPP.
       intro. destruct H.   apply (Nexist NSet.elt). 
       assumption.
Qed.



Lemma min_le_max: forall (s: NSet.t),
(option_nat (NSet.min_elt s)) <= option_nat (NSet.max_elt s).
Proof. intros. 
       assert(NSet.Empty s\/ ~(NSet.Empty s)).
       apply Classical_Prop.classic.
       destruct H. rewrite(min_empty s H).
       rewrite (max_empty s H). simpl. lia.
       pose H. pose H.  apply max_not_empty in n. 
       apply min_not_empty in n0.
       destruct n0. destruct n.
       apply not_empty_some in H. 
       destruct H. pose H.   
       apply (@NSet.min_elt_2 s x x1 ) in i; try assumption.
       apply (@NSet.max_elt_2 s x0 x1 ) in H; try assumption.
       rewrite H1. rewrite H0. simpl. lia.   
Qed. 

Lemma In_min_max: forall (s: NSet.t),
NSet.Subset s 
(Qsys_to_Set (option_nat (NSet.min_elt s)) (option_nat (NSet.max_elt s) + 1)).
Proof.  intros. unfold NSet.Subset. intros.
assert(NSet.Empty s\/ ~(NSet.Empty s)).
apply Classical_Prop.classic.
destruct H0. unfold NSet.Empty in H0. pose (H0 a).
 destruct n. assumption.
pose H0. pose H0.  apply max_not_empty in n. 
apply min_not_empty in n0.
destruct n0. destruct n.
pose H. 
apply (@NSet.min_elt_2 s x a ) in i; try assumption.
apply (@NSet.max_elt_2 s x0 a ) in H; try assumption.
rewrite H1. rewrite H2. simpl.
rewrite In_Qsys. lia. lia.    
Qed. 

Lemma  empty_Empty: forall s, 
NSet.Equal s NSet.empty <-> NSet.Empty s.
Proof. unfold NSet.Equal. unfold NSet.Empty.
       intros. split;intros.
       intro. apply H in H0. 
       pose (NSet.empty_1 ).
       unfold NSet.Empty in e.
       apply e in H0. 
      destruct H0.
      split; intros. apply H in H0.
      destruct H0. 
      pose (NSet.empty_1 ).
       unfold NSet.Empty in e.
       apply e in H0. 
      destruct H0.
 
  
Qed.

Lemma min_1: forall x s,
~NSet.Empty s -> NSet.In x s ->
(forall a, NSet.In a s-> x<=a)->
NSet.min_elt s = Some x.
Proof. intros. 
       apply min_not_empty in H. 
       destruct H.  
       pose H. pose H. 
       apply (@NSet.min_elt_2 _ _ x)in e.
       apply NSet.min_elt_1 in e0. 
       apply H1 in e0.
       assert( x= x0). lia.
       rewrite H2. assumption.
       assumption.  

       
Qed.

Lemma max_1: forall x s,
~NSet.Empty s -> NSet.In x s ->
(forall a, NSet.In a s-> x>=a)->
NSet.max_elt s = Some x.
Proof. intros. 
       apply max_not_empty in H. 
       destruct H.  
       pose H. pose H. 
       apply (@NSet.max_elt_2 _ _ x)in e.
       apply NSet.max_elt_1 in e0. 
       apply H1 in e0.
       assert( x= x0). lia.
       rewrite H2. assumption.
       assumption.  
Qed.



Lemma  min_eq: forall x y, 
NSet.Equal x y ->
NSet.min_elt x = NSet.min_elt y.
Proof. intros.
assert(NSet.Empty x\/ ~(NSet.Empty x)).
apply Classical_Prop.classic. destruct H0.
assert(NSet.Empty y).  
rewrite <-empty_Empty in *. rewrite <-H0. rewrite <-H. reflexivity.
 repeat rewrite min_empty; try assumption. reflexivity.
 assert(~ NSet.Empty y).
 rewrite <-empty_Empty in *. intro. destruct H0.
  rewrite H. assumption.
  pose H0. pose H1. 
  apply not_empty_some in n. 
  apply min_not_empty in H0. 
  apply min_not_empty in n0.
  destruct H0. destruct n0. destruct n.
  unfold NSet.Equal in H.
  rewrite H0. 
  symmetry. apply min_1. assumption.
  apply NSet.min_elt_1 in H0. apply H . assumption.
  intros. apply H in H4. 
  apply (@NSet.min_elt_2 _ _ a) in H0; try assumption.
  lia.
Qed. 

Lemma  max_eq: forall x y, 
NSet.Equal x y ->
NSet.max_elt x = NSet.max_elt y.
Proof. intros.
assert(NSet.Empty x\/ ~(NSet.Empty x)).
apply Classical_Prop.classic. destruct H0.
assert(NSet.Empty y).  
rewrite <-empty_Empty in *. rewrite <-H0. rewrite <-H. reflexivity.
 repeat rewrite max_empty; try assumption. reflexivity.
 assert(~ NSet.Empty y).
 rewrite <-empty_Empty in *. intro. destruct H0.
  rewrite H. assumption.
  pose H0. pose H1. 
  apply not_empty_some in n. 
  apply max_not_empty in H0. 
  apply max_not_empty in n0.
  destruct H0. destruct n0. destruct n.
  unfold NSet.Equal in H.
  rewrite H0. 
  symmetry. apply max_1. assumption.
  apply NSet.max_elt_1 in H0. apply H . assumption.
  intros. apply H in H4. 
  apply (@NSet.max_elt_2 _ _ a) in H0; try assumption.
  lia.
Qed. 

Lemma union_empty_r: forall x : NSet.t, 
NSet.Equal (NSet.union x NSet.empty ) x.
Proof. intros. unfold NSet.Equal. unfold NSet.union.
       intros. split. intros.
       apply NSet.union_1 in H. destruct H.
       assumption. apply In_empty in H. destruct H.
       intros. apply NSet.union_2. assumption.
       
Qed.


Lemma union_empty_refl_l:forall x y,
NSet.Equal x (NSet.empty)->
NSet.Equal (NSet.union x y) y.
Proof. unfold NSet.Equal. intros.
      split. intros. 
      apply NSet.union_1 in H0. destruct H0. apply H in H0.
      apply In_empty in H0. destruct H0. assumption.  intros.
      apply NSet.union_3. assumption.
Qed. 

Lemma union_empty_refl_r:forall x y,
NSet.Equal y (NSet.empty)->
NSet.Equal (NSet.union x y) x.
Proof. unfold NSet.Equal. intros.
      split. intros. 
      apply NSet.union_1 in H0. destruct H0. assumption. apply H in H0.
      apply In_empty in H0. destruct H0.  intros.
      apply NSet.union_2. assumption.
Qed.


Lemma min_union: forall x y, 
(NSet.Equal x NSet.empty -> 
option_nat (NSet.min_elt (NSet.union x y)) = (option_nat (NSet.min_elt y)) ) /\
(NSet.Equal y NSet.empty -> 
option_nat (NSet.min_elt (NSet.union x y)) = (option_nat (NSet.min_elt x)) ) /\
(~ NSet.Equal x NSet.empty ->  ~ NSet.Equal y NSet.empty -> 
option_nat (NSet.min_elt (NSet.union x y)) = min (option_nat (NSet.min_elt x))
 (option_nat (NSet.min_elt y))).
Proof. intros. split.  intros. 
      assert(NSet.Equal (NSet.union x y) y).
      rewrite H. rewrite union_empty_refl_l; try   reflexivity.
      rewrite (min_eq _ y). reflexivity. assumption.
      split. 
      intros. 
      assert(NSet.Equal (NSet.union x y) x).
      rewrite H. apply    union_empty_r. 
      rewrite (min_eq _ x). reflexivity. assumption.
      intros.
      assert (~NSet.Equal (NSet.union x y) NSet.empty).
      intro. apply union_empty in H1. destruct H1. 
      destruct H. assumption.
      rewrite empty_Empty in H.
      rewrite empty_Empty in H0.
      rewrite empty_Empty in H1.
      apply min_not_empty in H.
      apply min_not_empty in H0.
      destruct H. destruct H0.
      rewrite H. rewrite H0.
      simpl.   
      assert(x0<=x1\/ ~ (x0 <=x1)).
      apply Classical_Prop.classic.
      destruct H2.  rewrite min_l; try assumption.
      assert((NSet.min_elt (NSet.union x y))= Some x0).
      apply min_1. assumption. 
      apply NSet.union_2. 
      apply NSet.min_elt_1; try assumption. 
      intros. apply NSet.union_1 in H3.
      destruct H3. 
      apply (@NSet.min_elt_2 _ _ a) in H; try assumption. lia.
      apply (@NSet.min_elt_2 _ _ a) in H0; try assumption. lia.
      rewrite H3. reflexivity.
      rewrite min_r; try assumption.
      assert((NSet.min_elt (NSet.union x y))= Some x1).
      apply min_1. assumption.  
      apply NSet.union_3. 
      apply NSet.min_elt_1; try assumption. 
      intros. apply NSet.union_1 in H3.
      destruct H3. 
      apply (@NSet.min_elt_2 _ _ a) in H; try assumption. lia.
      apply (@NSet.min_elt_2 _ _ a) in H0; try assumption. lia.
      rewrite H3. reflexivity. lia. 

Qed.




Lemma max_union: forall x y, 
(NSet.Equal x NSet.empty -> 
option_nat (NSet.max_elt (NSet.union x y)) = (option_nat (NSet.max_elt y)) ) /\
(NSet.Equal y NSet.empty -> 
option_nat (NSet.max_elt (NSet.union x y)) = (option_nat (NSet.max_elt x)) ) /\
(~ NSet.Equal x NSet.empty ->  ~ NSet.Equal y NSet.empty -> 
option_nat (NSet.max_elt (NSet.union x y)) = max (option_nat (NSet.max_elt x))
 (option_nat (NSet.max_elt y))).
 Proof. intros. split.
 intros. 
 assert(NSet.Equal (NSet.union x y) y).
 rewrite H. rewrite union_empty_refl_l; try reflexivity.
 rewrite (max_eq _ y). reflexivity. assumption.
 split. 
 intros. 
 assert(NSet.Equal (NSet.union x y) x).
 rewrite H. apply    union_empty_r. 
 rewrite (max_eq _ x). reflexivity. assumption.
 intros.
 assert (~NSet.Equal (NSet.union x y) NSet.empty).
 intro. apply union_empty in H1. destruct H1. 
 destruct H. assumption.
 rewrite empty_Empty in H.
 rewrite empty_Empty in H0.
 rewrite empty_Empty in H1.
 apply max_not_empty in H.
 apply max_not_empty in H0.
 destruct H. destruct H0.
 rewrite H. rewrite H0.
 simpl.   
 assert(x0<=x1\/ ~ (x0 <=x1)).
 apply Classical_Prop.classic.
 destruct H2.  rewrite max_r; try assumption.
 assert((NSet.max_elt (NSet.union x y))= Some x1).
 apply max_1. assumption. 
 apply NSet.union_3. 
 apply NSet.max_elt_1; try assumption. 
 intros. apply NSet.union_1 in H3.
 destruct H3. 
 apply (@NSet.max_elt_2 _ _ a) in H; try assumption. lia.
 apply (@NSet.max_elt_2 _ _ a) in H0; try assumption. lia.
 rewrite H3. reflexivity.
 rewrite max_l; try assumption.
 assert((NSet.max_elt (NSet.union x y))= Some x0).
 apply max_1. assumption.  
 apply NSet.union_2. 
 apply NSet.max_elt_1; try assumption. 
 intros. apply NSet.union_1 in H3.
 destruct H3. 
 apply (@NSet.max_elt_2 _ _ a) in H; try assumption. lia.
 apply (@NSet.max_elt_2 _ _ a) in H0; try assumption. lia.
 rewrite H3. reflexivity. lia. Qed. 





Lemma Pure_eval''{s e:nat}:forall  (F: State_formula) c0 c1 (q q0: qstate s e),
(Free_State F = None)->
cstate_eq c0 c1 (fst (Free_state F))->
State_eval F (c0, q) -> 
State_eval F (c1, q0).
Proof. induction F;   intros.
        rewrite <- (cstate_eq_P P c0 c1). 
        apply state_eq_Pure with (c0,q).
        reflexivity. apply H1.  assumption.
       apply QExp_eval_dom in H1.
       simpl in H. discriminate H.

       apply cstate_eq_union in H0. destruct H0.
       simpl in *;
       split. intuition.
       destruct H1. destruct H3. 
    destruct (option_edc (Free_State F1) None). rewrite H5 in *. 
    simpl in *.
    split. apply IHF1 with c0 q; try assumption. reflexivity.
    apply IHF2 with c0 q; try assumption. 
    destruct (option_edc (Free_State F2) None). rewrite H6 in *.
    apply option_eqb_neq in H5. rewrite H5 in *. simpl in *.  
    split. apply IHF1 with c0 q; try assumption.
   apply IHF2 with c0 q; try assumption. reflexivity.
   apply option_eqb_neq in H5. rewrite H5 in *.
   apply option_eqb_neq in H6. rewrite H6 in *. simpl in *.
   discriminate H.  

  apply cstate_eq_union in H0. destruct H0.
  simpl in *.
  destruct H1. 
  destruct (option_edc (Free_State F1) None). rewrite H4 in *. 
    simpl in *.
  split. apply IHF1 with c0 q; try assumption. reflexivity.
 apply IHF2 with c0 q; try assumption. 

 destruct (option_edc (Free_State F2) None). rewrite H5 in *.
    apply option_eqb_neq in H4. rewrite H4 in *. simpl in *.  
 split. apply IHF1 with c0 q; try assumption.
 apply IHF2 with c0 q; try assumption. reflexivity.
 apply option_eqb_neq in H5. rewrite H5 in *.
   apply option_eqb_neq in H4. rewrite H4 in *. simpl in *.
 discriminate H.

 simpl in *. apply cstate_eq_union in H0.
 rewrite <-(cstate_eq_a c0 c1).
 rewrite (state_eq_aexp _ (c0,q)); try reflexivity.
 apply (IHF  (c_update i (aeval (c0, q) a) c0) _  q). apply H.
 unfold cstate_eq in *.
 intros. destruct (eq_dec j i).
  rewrite e0. 
 repeat rewrite c_update_find_eq. 
 reflexivity.
 apply H0 in H2.  
 repeat rewrite c_update_find_not; try lia.
assumption. 
unfold cstate_eq in *. intros.
 apply H0 in H2. rewrite H2. reflexivity.

Qed.


Lemma rule_f_classic_meas{s0 e0:nat}: forall s e sigma (rho:qstate s0 e0) mu F (i:nat) , 
s0 <= s /\ s < e <= e0->
WF_dstate_aux [(sigma, rho)]->
Free_State F = None-> 
NSet.Equal (NSet.inter (fst (Free_state F)) (fst (MVar <{ i :=M [[s e]] }>))) NSet.empty->
big_app' (fun j : nat => (c_update i j sigma, QMeas_fun s e j rho))
        (2 ^ (e - s)) mu->
State_eval F (sigma, rho)->
State_eval_dstate F mu.
Proof. intros. 
apply (big_app_seman ((2 ^ (e - s)))  (fun j : nat =>
(c_update i j sigma, QMeas_fun s e j rho))); try apply H1; try apply pow_gt_0; try assumption.
intros. split.
apply WF_state_dstate_aux.
unfold WF_state. simpl. 
apply WF_qstate_QMeas; try assumption; try lia.
inversion_clear H0. assumption.
simpl. econstructor.
apply Pure_eval'' with sigma rho; try assumption.
simpl in H2. 
unfold cstate_eq.
intros. rewrite c_update_find_not.
reflexivity. 
unfold not.
intros. rewrite<-H8 in *.
apply (In_inter_empty _ _ i) in H2.
destruct H2. assumption.
apply NSet.add_1. reflexivity. econstructor.
apply WF_qstate_QMeas_app with s e rho sigma i (2 ^ (e - s)); try lia; try assumption. 
inversion_clear H0.  assumption. 
  intro. assert(d_trace_aux mu=0%R).
  rewrite H5. reflexivity. 
  assert(d_trace_aux mu =  (s_trace (sigma,rho))).
  apply QMeas_trace' with s e i; try assumption; try lia. 
  apply WWF_qstate_to_WF_qstate. 
  inversion_clear H0.  assumption.  
  assert(s_trace (sigma,rho)>0)%R. unfold  s_trace.
  simpl. apply nz_mixed_state_Cmod_1. inversion_clear H0.
  apply H8. rewrite<- H7 in H8. rewrite H6 in H8.
  lra. 
Qed.

Ltac rule_f_classic_sovle s e c q i mu:=
       destruct mu; 
 try  match goal with 
 H:ceval_single ?x ?y ?z |-_ => inversion H; subst; clear H end;
 try  match goal with 
 H:ceval_single ?x [] ?z |-_ => inversion_clear H end;
 try  match goal with 
 H: existT ?a ?b ?c = existT ?x ?y ?z|-_ => apply inj_pair2_eq_dec in H end;
 try  match goal with 
 H: existT ?a ?b ?c = existT ?x ?y ?z|-_ => apply inj_pair2_eq_dec in H; destruct H end;
 try apply Nat.eq_dec;
 try  match goal with 
 H:State_eval_dstate ?x ?z |-_ => inversion_clear H; try rewrite map2_nil_r end; try econstructor;try econstructor;
 [try apply rule_f_classic_meas with s e c q i; try assumption | ];
  try apply (@Pure_free_eval' s e s e) with q; try assumption;
 assert(WF_dstate_aux [(c,q)]); try apply WF_state_dstate_aux;
 try inversion_clear Hw; try assumption;
 apply d_seman_app_aux; 
 try eapply WF_ceval  with _ _ ;
 try apply ceval_Qinit; try apply ceval_QUnit_One;
 try apply ceval_QUnit_Ctrl ; try match goal with
 H: big_app' ?f ?n ?mu'' |- _  => apply (ceval_QMeas c q s e i mu''); try assumption end;
 try  match goal with 
 H:ceval_single ?x ?y ?z |-_ => apply H end; try assumption; try econstructor;try econstructor;
 [try apply rule_f_classic_meas with s e c q i; try assumption; try econstructor | ]; 
 try apply (@Pure_free_eval' s e s e) with q; try assumption; try econstructor;
   match goal with 
   IHmu: _ |-_ =>
  apply IHmu; try left; try assumption end.


Lemma Qsys_to_Set_not_empty:forall s e,
s<e->
~ (NSet.Equal (Qsys_to_Set s e) NSet.empty).
Proof. intros. unfold NSet.Equal. intro. 
       pose (H0 s). pose (In_Qsys_l_r e s H). destruct a. 
       apply i in H1. apply In_empty in H1. destruct H1.  
       
Qed.


Lemma rule_f_classic: forall   c s e (mu mu':list (cstate * qstate s e )) F,
(Considered_Formula F )->
((Free_State F)= None \/ NSet.Equal (snd (MVar c)) NSet.empty) ->
WF_dstate_aux mu ->
State_eval_dstate F mu->
ceval_single c mu mu'-> 
NSet.Equal (NSet.inter (fst (Free_state F)) (fst (MVar c))) (NSet.empty) ->
State_eval_dstate F mu'.
Proof. induction c. 
-intros. apply ceval_skip_1 in H3. subst. assumption.
-induction mu; intros. destruct H2. 
 destruct mu; inversion H3; subst.
 inversion_clear H10. simpl. econstructor.
  inversion_clear H2.  apply rule_f_classic_assn; try assumption. econstructor.
   apply d_seman_app_aux. 
   apply WF_state_dstate_aux.
   apply WF_state_eq with (sigma, rho).
   reflexivity. inversion_clear H1. assumption.
   apply WF_ceval with <{ i := a }> (p :: mu).
   inversion_clear H1. assumption.
   assumption. 
   simpl. econstructor. inversion_clear H2. apply rule_f_classic_assn; try assumption.
   econstructor. 
   inversion_clear H1. inversion_clear H2.
   apply IHmu; try assumption. 
-induction mu; intros. destruct H2. destruct a0. inversion H3; subst. assumption.  
-intros. simpl in H0. rewrite union_empty in H0.
 simpl in H4. rewrite inter_union_dist in H4.
 apply union_empty in H4. 
 apply ceval_seq_1 in H3. destruct H3.
 apply IHc2 with x; try assumption; try apply H3; try apply H4.  destruct H0; [ left|right];  apply H0. 
 apply WF_ceval with c1 mu; try assumption; try apply H3. 
 apply IHc1 with mu; try assumption; try apply H3; try apply H4. destruct H0; [ left|right];  apply H0.
- induction mu; intros. destruct H2.
   inversion_clear H2. inversion_clear  H1.
   inversion H3; subst; destruct mu;
  [inversion_clear H16| | inversion_clear H16|]; try rewrite map2_nil_r.
  simpl in *;  rewrite inter_union_dist in H4;
  rewrite union_empty in H0; apply union_empty in H4;
  apply IHc1 with [(sigma, rho)]; 
  try apply WF_state_dstate_aux; try assumption; try apply H4. destruct H0; [ left|right];  apply H0.
  econstructor. assumption. econstructor.
  apply d_seman_app_aux. apply WF_ceval with c1 [(sigma, rho)];
  try assumption.
  apply WF_state_dstate_aux; try assumption. 
  apply WF_ceval with  <{ if b then c1 else c2 end }> (p :: mu);
  try apply WF_state_dstate_aux; try assumption.
  simpl in *.  rewrite inter_union_dist in H4.
  rewrite union_empty in H0. apply union_empty in H4.
  apply IHc1 with [(sigma, rho)]; 
  try apply WF_state_dstate_aux; try assumption; try apply H4. destruct H0; [ left|right];  apply H0.
  econstructor. assumption. econstructor.
  apply IHmu; try assumption; try apply H4.

  simpl in *;  rewrite inter_union_dist in H4;
  rewrite union_empty in H0; apply union_empty in H4;
  apply IHc2 with [(sigma, rho)]; 
  try apply WF_state_dstate_aux; try assumption; try apply H4. destruct H0; [ left|right];  apply H0.
  econstructor. assumption. econstructor.
  apply d_seman_app_aux. apply WF_ceval with c2 [(sigma, rho)];
  try assumption.
  apply WF_state_dstate_aux; try assumption. 
  apply WF_ceval with  <{ if b then c1 else c2 end }> (p :: mu);
  try apply WF_state_dstate_aux; try assumption.
  simpl in *.  rewrite inter_union_dist in H4.
  rewrite union_empty in H0. apply union_empty in H4.
  apply IHc2 with [(sigma, rho)]; 
  try apply WF_state_dstate_aux; try assumption; try apply H4. destruct H0; [ left|right];  apply H0.
  econstructor. assumption. econstructor.
  apply IHmu; try assumption; try apply H4.

-intros.  remember <{while b do c end}> as original_command eqn:Horig. 
induction H3;  try inversion Horig; subst.  destruct H2.
destruct mu. inversion_clear H3_. rewrite map2_nil_r.
apply IHceval_single3; try reflexivity; try assumption.
eapply WF_ceval; try apply H3_0. assumption.  
eapply IHc; try apply H3_0; try assumption.
assert( WF_dstate_aux [(sigma, rho)]).
apply WF_state_dstate_aux. inversion_clear H1. assumption.
assert( WF_dstate_aux mu1).
eapply WF_ceval; try apply H3_0; try assumption.
assert( WF_dstate_aux mu').
eapply WF_ceval; try apply H3_1; try assumption.
assert( WF_dstate_aux mu''). 
inversion_clear H1.
eapply WF_ceval; try apply H3_; try assumption.
apply d_seman_app_aux; try assumption. 
apply IHceval_single3; try reflexivity; try assumption. 
eapply IHc; try apply H3_0; try assumption.
inversion_clear H2. econstructor. assumption. econstructor.
inversion_clear H1. inversion_clear H2.
apply IHceval_single1; try reflexivity; try assumption.

destruct mu. inversion_clear H6. rewrite map2_nil_r. assumption.
assert( WF_dstate_aux [(sigma, rho)]).
apply WF_state_dstate_aux. inversion_clear H1. assumption.
assert( WF_dstate_aux mu'). inversion_clear H1.
eapply WF_ceval; try apply H6; try assumption.  
apply d_seman_app_aux; try assumption.  
inversion_clear H2. econstructor. assumption. econstructor.
inversion_clear H1. inversion_clear H2.
apply IHceval_single; try reflexivity; try assumption.

{  induction mu; intros mu2 F Hs Hm Hw; intros.
{inversion  H.  }
 {destruct Hm. destruct a.  rule_f_classic_sovle s0 e0 c q s mu. 
 simpl in H2. inversion_clear H0.
 apply Qsys_to_Set_not_empty in H2; try lia. 
}  }
-{  induction mu; intros mu2 F Hs Hm Hw; intros.
{inversion  H.  }
{destruct Hm. destruct a. rule_f_classic_sovle s0 e0 c q s mu.  
inversion_clear H0.
apply Qsys_to_Set_not_empty in H2; try lia. 
} }

  {  induction mu; intros mu2 F Hs Hm Hw; intros.
  {inversion  H.  }
  {destruct Hm. destruct a. 
  rule_f_classic_sovle s e c q s mu.
  inversion_clear H0. simpl in H2. rewrite union_empty in H2. 
  destruct H2.
  apply Qsys_to_Set_not_empty in H2; try lia. 
} }

{induction mu; intros mu2 F Hs Hm Hw; intros.
{inversion  H.  }
{destruct Hm. destruct a.    rule_f_classic_sovle s e c q i mu.
inversion_clear H0.
 apply Qsys_to_Set_not_empty in H2; try lia. 
 }}  
Qed.

Lemma State_eval_dstate_dom{s e:nat}: forall (mu:list (cstate * qstate s e)) F, 
State_eval_dstate F mu->
Free_State F = None \/
s <=fst (option_free (Free_State F)) /\ fst (option_free (Free_State F)) < snd (option_free (Free_State F)) <= e.
Proof. induction mu; intros. destruct H. 
       inversion_clear H. destruct a.  
        apply State_eval_dom in H0.    assumption. 
Qed.

Lemma min_add_empty: forall e, 
 (NSet.min_elt (NSet.add e NSet.empty)) = Some  e .
Proof. intros. apply min_1. intro. unfold NSet.Empty in H. 
        pose (H e). destruct n. apply NSet.add_1. reflexivity. 
        apply NSet.add_1. reflexivity. 
        intros. destruct(eq_dec a e). subst. lia.
        apply NSet.add_3 in H; try lia. apply In_empty in H. destruct H.
Qed.

Lemma max_add_empty: forall e, 
 (NSet.max_elt (NSet.add e NSet.empty)) = Some  e .
Proof. intros. apply max_1. intro. unfold NSet.Empty in H. 
        pose (H e). destruct n. apply NSet.add_1. reflexivity. 
        apply NSet.add_1. reflexivity. 
        intros. destruct(eq_dec a e). subst. lia.
        apply NSet.add_3 in H; try lia. apply In_empty in H. destruct H.
Qed.


Lemma min_add: forall e s, 
  ~NSet.Empty s ->
  option_nat (NSet.min_elt s) < e ->
 (NSet.min_elt (NSet.add e s)) = NSet.min_elt s .
Proof. intros. apply min_not_empty in H.  destruct H.  rewrite H. 
        apply min_1. intro. unfold NSet.Empty in H1. 
        pose (H1 e). destruct n. apply NSet.add_1. reflexivity.  
        apply NSet.add_2. apply NSet.min_elt_1. assumption. 
        intros. rewrite H in *. simpl in *.
         destruct(eq_dec a e). subst. lia.
        apply NSet.add_3 in H1; try lia. apply (@NSet.min_elt_2 _ x) in H1. lia.
        assumption. 
Qed.

Lemma max_add: forall e s, 
  ~NSet.Empty s ->
  option_nat (NSet.max_elt s) < e ->
 (NSet.max_elt (NSet.add e s)) = Some e.
Proof. intros. apply max_not_empty in H.  destruct H.  
        apply max_1. intro. unfold NSet.Empty in H1. 
        pose (H1 e). destruct n. apply NSet.add_1. reflexivity.  
        apply NSet.add_1. reflexivity.  
        intros. rewrite H in *. simpl in *.
         destruct(eq_dec a e). subst. lia.
        apply NSet.add_3 in H1; try lia. apply (@NSet.max_elt_2 _ x) in H1. lia.
        assumption. 
Qed.


Lemma Qsys_to_Set_min_max: forall s e,
s<e ->
option_nat (NSet.min_elt (Qsys_to_Set s e)) = s/\
option_nat (NSet.max_elt (Qsys_to_Set s e)) = e-1.
Proof. intros. induction e.  simpl. lia.  
   unfold Qsys_to_Set in *.
      simpl. rewrite Lt_n_i; try assumption.
      destruct (eq_dec s e). 
      rewrite e0. rewrite Qsys_to_Set_empty.
      rewrite Nat.sub_0_r.  
      split. rewrite min_add_empty. reflexivity.
      rewrite max_add_empty. reflexivity.
       assert(s<e). lia. destruct IHe. lia.
       split. rewrite min_add. apply H1. 
       intro. apply empty_Empty in H3. apply Qsys_to_Set_not_empty in H3.
       destruct H3. lia.    rewrite H1. lia. 
       rewrite max_add. simpl. rewrite sub_0_r. reflexivity.
       intro. apply empty_Empty in H3. apply Qsys_to_Set_not_empty in H3. 
       destruct H3. lia. rewrite H2. lia.  
Qed.


Lemma union_not_empty: forall x y, 
~ NSet.Equal (NSet.union x y) NSet.empty->
~ NSet.Equal x NSet.empty \/ ~ NSet.Equal y NSet.empty.
Proof. intros. assert(NSet.Equal x NSet.empty \/ ~NSet.Equal x NSet.empty).
  apply Classical_Prop.classic. destruct H0. right. 
  intro. destruct H. apply union_empty. auto. 
  left. assumption. 
Qed.




Lemma  subset_union': forall x y z, 
NSet.Subset x z /\ NSet.Subset y z ->NSet.Subset (NSet.union x y) z.
Proof. intros. unfold NSet.Subset in *. 
       destruct H.  intros. apply NSet.union_1 in H1.
       destruct H1.  
       apply H. 
       assumption.
       apply H0. 
       assumption.
       
Qed.

Lemma ceval_not_nil{ s e:nat}: forall c (mu mu': list (cstate * qstate s e)), 
WF_dstate_aux mu->
ceval_single c mu mu' ->
mu<>[]
->mu'<>[].
Proof.  intros. induction H0;
try match goal with 
H: [] <> []  |- _ => destruct H; try reflexivity end; try discriminate; 
try apply map2_app_not_nil; try left; try discriminate; try auto.
intro. assert(d_trace_aux mu'' =0%R). rewrite H4. reflexivity.
erewrite QMeas_trace' in H5; try apply H0; try apply H3; try assumption; try lia;
try apply WWF_qstate_to_WF_qstate; try inversion_clear H; try assumption.
apply WF_qstate_gt_0 in H6. unfold s_trace in *. simpl in *.
unfold q_trace in *.  rewrite H5 in H6. lra.
apply IHceval_single2. eapply WF_ceval. apply H. apply H0_.
apply  IHceval_single1. assumption. discriminate. 
eapply IHceval_single2. apply WF_state_dstate_aux. inversion_clear H.
assumption. discriminate.
eapply IHceval_single2. apply WF_state_dstate_aux. inversion_clear H.
assumption. discriminate.  inversion_clear H. 
assert(WF_dstate_aux [(sigma, rho)]). apply WF_state_dstate_aux. assumption.
apply IHceval_single3. eapply WF_ceval. apply H. apply H0_0.
 apply IHceval_single2. assumption. discriminate. 
Qed.


Lemma ceval_single_dom{ s e:nat}: forall c (mu mu': list (cstate * qstate s e)) , 
WF_dstate_aux mu->
ceval_single c mu mu' ->
mu <> [] ->
~NSet.Equal (snd (MVar c)) NSet.empty ->
NSet.Subset (snd (MVar c)) (Qsys_to_Set s e).
Proof. induction c. intros  mu mu' Hw H Hnil H0; intros.
simpl in *. try destruct H0; try reflexivity.
-intros. try destruct H2; try reflexivity.
-intros. try destruct H2; try reflexivity.
-intros  mu mu' Hw H Hnil H0; intros.
apply ceval_seq_1 in H; destruct H. 
simpl in *.   apply union_not_empty in H0.
assert(NSet.Equal (snd (MVar c1)) NSet.empty \/ ~NSet.Equal (snd (MVar c1)) NSet.empty ).
apply Classical_Prop.classic.  
destruct H1. destruct H0. destruct H0. assumption. 
rewrite union_empty_refl_l; try assumption.
assert(WF_dstate_aux x). eapply WF_ceval. apply Hw. apply H. 
eapply IHc2; try assumption.  apply H2.  apply H. 
eapply ceval_not_nil. apply Hw. apply H. assumption. 
assert(NSet.Equal (snd (MVar c2)) NSet.empty \/ ~NSet.Equal (snd (MVar c2)) NSet.empty ).
apply Classical_Prop.classic.  
destruct H2. 
rewrite union_empty_refl_r; try assumption.
eapply IHc1; try assumption. apply Hw. apply H. assumption. 
apply subset_union'. split.
eapply IHc1; try assumption. apply Hw. apply H. assumption.
assert(WF_dstate_aux x). eapply WF_ceval. apply Hw. apply H. 
eapply IHc2; try assumption. apply H3.   apply H. 
eapply ceval_not_nil. apply Hw. apply H. assumption. 

-induction mu; intros mu' Hw H Hnil H0; intros.
 inversion H; subst. destruct Hnil. reflexivity.
 inversion H; subst;
 simpl in *;    apply union_not_empty in H0;
 assert(NSet.Equal (snd (MVar c1)) NSet.empty \/ ~NSet.Equal (snd (MVar c1)) NSet.empty );
 try apply Classical_Prop.classic.  
 destruct H1. destruct H0. destruct H0. assumption.   
 rewrite union_empty_refl_l; try assumption. 
 assert(NSet.Equal (snd (MVar c2)) NSet.empty \/ ~NSet.Equal (snd (MVar c2)) NSet.empty ).
 apply Classical_Prop.classic.  
 destruct H2.  
 rewrite union_empty_refl_r; try assumption. 
 inversion_clear Hw. 
 assert(WF_dstate_aux [(sigma, rho)]). apply WF_state_dstate_aux. assumption.
 eapply IHc1; try assumption. apply H7. apply H10. discriminate.  
 apply subset_union'. split; try assumption.  
 inversion_clear Hw. 
 assert(WF_dstate_aux [(sigma, rho)]). apply WF_state_dstate_aux. assumption.
 eapply IHc1; try assumption. apply H7. apply H10. discriminate. 

destruct H1. destruct H0. destruct H0. assumption.   
 rewrite union_empty_refl_l; try assumption. 
 inversion_clear Hw. 
 assert(WF_dstate_aux [(sigma, rho)]). apply WF_state_dstate_aux. assumption.
 eapply IHc2; try assumption. apply H5. apply H10. discriminate.
 assert(NSet.Equal (snd (MVar c2)) NSet.empty \/ ~NSet.Equal (snd (MVar c2)) NSet.empty ).
 apply Classical_Prop.classic.  
 destruct H2.  
 rewrite union_empty_refl_r; try assumption. 
 apply subset_union'. split; try assumption.
 inversion_clear Hw. 
 assert(WF_dstate_aux [(sigma, rho)]). apply WF_state_dstate_aux. assumption.
 eapply IHc2; try assumption. apply H7. apply H10. discriminate.

-intros. remember <{while b do c end}> as original_command eqn:Horig. 
   induction H0;  try inversion Horig; subst. destruct H1. reflexivity.
   
   simpl in H2.  eapply IHc; try assumption; try apply H0_0.
   apply WF_state_dstate_aux. inversion_clear H. assumption. discriminate. 
   simpl. assumption. 

-intros  mu mu' Hw H Hnil H0; intros. inversion H; subst. destruct Hnil. reflexivity.
 simpl. apply Qsys_subset; try lia.  

-intros  mu mu' Hw H Hnil H0; intros. inversion H; subst. destruct Hnil. reflexivity.
simpl. apply Qsys_subset; try lia.  
intros  mu mu' Hw H Hnil H0; intros. inversion H; subst. destruct Hnil. reflexivity.
 simpl. apply subset_union'. split; apply Qsys_subset; try lia. 

-intros  mu mu' Hw H Hnil H0; intros. inversion H; subst. destruct Hnil. reflexivity.
simpl. apply Qsys_subset; try lia.  
Qed. 

Lemma Qsys_to_Set_empty':forall s e,
s>=e-> NSet.Empty (Qsys_to_Set s e) .
Proof. intros. unfold Qsys_to_Set. induction e. destruct s.  simpl. apply NSet.empty_1 .
       simpl. apply NSet.empty_1 . apply ltb_ge in H. simpl. rewrite H. apply NSet.empty_1.
       
Qed.



Lemma Subset_min_max_In: forall x s e, 
~NSet.Equal x NSet.empty ->
NSet.Subset x (Qsys_to_Set s e) ->
(s<=option_nat (NSet.min_elt x) /\ (option_nat (NSet.max_elt x))<e ).
Proof. intros. unfold NSet.Subset in H0. pose H. pose H.  rewrite empty_Empty in *.
        apply min_not_empty in n. apply max_not_empty in n0. 
        destruct n. destruct n0.
        rewrite H1 in *. rewrite H2 in *. simpl. 
        apply NSet.min_elt_1 in H1. 
        apply NSet.max_elt_1 in H2.  
        apply H0 in H1.  apply In_Qsys in H1; try lia. 
        apply H0 in H2.  apply In_Qsys in H2; try lia.  
        assert(~NSet.Empty(Qsys_to_Set s e)). 
        intro. unfold NSet.Empty in H4. apply H0 in H2. 
        destruct (H4  x1). assumption. 
        apply Classical_Prop.NNPP. intro.
        destruct H4. apply Qsys_to_Set_empty'. lia. 
Qed.


Lemma rule_f: forall  F c s e (mu mu':list (cstate * qstate s e )) ,
(Considered_Formula F /\ fst (option_free (Free_State F)) < snd (option_free (Free_State F)))->
WF_dstate_aux mu ->
State_eval_dstate F mu->
ceval_single c mu mu'-> 
~NSet.Equal (snd (MVar c)) NSet.empty ->
NSet.Equal (NSet.inter (fst (Free_state F)) (fst (MVar c))) (NSet.empty) ->
((option_nat (NSet.max_elt (snd (MVar c)))) <  (fst (option_free (Free_State F)))
\/((snd (option_free (Free_State F)))) <=  ((option_nat (NSet.min_elt (snd (MVar c)))))) ->
State_eval_dstate F mu'.
Proof. 
    intros. assert( mu<>[]). destruct mu. simpl in H1.
    destruct H1. discriminate.  apply (@ceval_single_dom s e c mu mu' H0 ) in H6; try assumption.
    apply Subset_min_max_In in H6; try lia; try assumption. 
    

    destruct H5. 
    assert(s <= option_nat (NSet.min_elt (snd (MVar c))) /\
    option_nat (NSet.min_elt (snd (MVar c))) <=
    fst (option_free (Free_State F)) /\
    fst (option_free (Free_State F)) < snd (option_free (Free_State F)) /\ snd (option_free (Free_State F)) <= e).
    split. lia. 
    split. apply le_trans with (option_nat  (NSet.max_elt (snd (MVar c)))).
    apply min_le_max. lia.  split. apply H.
    apply State_eval_dstate_dom in H1. destruct H1. rewrite H1 in *.
    simpl in *.  lia.
    apply H1.  
    rewrite (State_dstate_free_eval _ _ (fst (option_free (Free_State F)))
    (snd (option_free (Free_State F)))); try lia. 
    rewrite <-(d_reduced_assoc   mu' 
    (option_nat (NSet.min_elt (snd (MVar c))))
    (snd (option_free (Free_State F)))); try lia.   
    remember ((d_reduced mu'
    (option_nat (NSet.min_elt (snd (MVar c))))
    (snd (option_free (Free_State F))))).
    remember ((d_reduced mu
    (option_nat (NSet.min_elt (snd (MVar c))))
    (snd (option_free (Free_State F))))).
    apply r4 with c (option_nat (NSet.min_elt (snd (MVar c))))
    (fst (option_free (Free_State F))) l0; try assumption; try lia.
    rewrite Heql0. apply WF_d_reduced; try lia; try assumption.  
    rewrite Heql. rewrite Heql0. 
    apply Par_trace_ceval_swap; try lia; try assumption.
    apply subset_trans with ((Qsys_to_Set
    (option_nat (NSet.min_elt (snd (MVar c))))
       (option_nat (NSet.max_elt (snd (MVar c))) + 1))).
    apply In_min_max. apply Qsys_subset.
    split. lia. split. 
    

    apply le_trans with  (option_nat (NSet.max_elt (snd (MVar c)))).
    apply min_le_max. lia. lia. 
    rewrite Heql0. apply r1; try assumption; try split; [apply H |try lia].
    apply subset_trans with ((Qsys_to_Set
    (option_nat (NSet.min_elt (snd (MVar c))))
       (option_nat (NSet.max_elt (snd (MVar c))) + 1))).
    apply In_min_max. apply Qsys_subset.
    split. lia. split. 
    apply le_trans with  (option_nat (NSet.max_elt (snd (MVar c)))).
    apply min_le_max. lia. lia. 
    rewrite Heql0. rewrite d_reduced_assoc; try lia. 
    apply State_dstate_free_eval; try assumption; try lia. 
     apply WF_NZ_Mixed_dstate; assumption.
    apply WF_NZ_Mixed_dstate.
    apply WF_ceval with c mu. 
    assumption. assumption.

    assert(s <= fst (option_free (Free_State F)) /\
    fst (option_free (Free_State F)) <= fst (option_free (Free_State F)) /\
    fst (option_free (Free_State F)) <= snd (option_free (Free_State F)) /\
    snd (option_free (Free_State F)) <=
    option_nat (NSet.max_elt (snd (MVar c))) + 1 <= e).
    split. apply State_eval_dstate_dom in H1.
    destruct H1. rewrite H1 in *. simpl in *. lia. apply H1.
    split. lia. split. lia. split.
    apply le_trans with (option_nat (NSet.min_elt (snd (MVar c)))).
    assumption.
    apply le_trans with  (option_nat (NSet.max_elt (snd (MVar c)))).
    apply min_le_max. lia. lia. 
    rewrite (State_dstate_free_eval _ _ (fst (option_free (Free_State F)))
    (snd (option_free (Free_State F)))); try lia. 
    rewrite <-(d_reduced_assoc   mu' 
    (fst (option_free (Free_State F))) (option_nat (NSet.max_elt (snd (MVar c)))+ 1)); try lia.   
    remember ( (d_reduced mu' (fst (option_free (Free_State F)))
    (option_nat (NSet.max_elt (snd (MVar c)))+ 1))).
    remember ((d_reduced mu
    (fst (option_free (Free_State F)))
    (option_nat (NSet.max_elt (snd (MVar c))) + 1))).
    apply r4' with c (snd (option_free (Free_State F)))
    (option_nat (NSet.max_elt (snd (MVar c))) + 1) l0; try assumption; try lia. 
    rewrite Heql0. apply WF_d_reduced; try lia; try assumption.  
    rewrite Heql. rewrite Heql0. 
    apply Par_trace_ceval_swap; try lia; try assumption.
    apply subset_trans with ((Qsys_to_Set 
    (option_nat (NSet.min_elt (snd (MVar c))))
    (option_nat (NSet.max_elt (snd (MVar c))) + 1))).
    apply In_min_max. apply  Qsys_subset .  split.
    apply le_trans with (snd (option_free (Free_State F))).
    lia. assumption. split. 
    apply le_trans with  (option_nat (NSet.max_elt (snd (MVar c)))).
    apply min_le_max. lia. lia.   
    rewrite Heql0. apply r1'; try assumption; try split; [apply H |try lia].
    apply subset_trans with ((Qsys_to_Set
    (option_nat (NSet.min_elt (snd (MVar c))))
       ((option_nat (NSet.max_elt (snd (MVar c)))) + 1))).
    apply In_min_max. apply Qsys_subset.
    split. lia. split. 
    apply le_trans with  (option_nat (NSet.max_elt (snd (MVar c)))).
    apply min_le_max. lia. lia. 
    rewrite Heql0. rewrite d_reduced_assoc; try lia. 
    apply State_dstate_free_eval; try assumption; try lia. 
     apply WF_NZ_Mixed_dstate; assumption.
    apply WF_NZ_Mixed_dstate.
    apply WF_ceval with c mu. 
    assumption. assumption.
Qed.


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

Lemma subset_inter_empty: forall x y z,
NSet.Equal (NSet.inter x y) (NSet.empty)->
NSet.Subset z x->
NSet.Equal (NSet.inter z y) (NSet.empty).
Proof. unfold NSet.Equal in *. unfold NSet.Subset in *. intros. split; intros. 
       apply H. apply NSet.inter_3. apply H0. apply NSet.inter_1 with y. 
       assumption. apply NSet.inter_2 with z. assumption.
       apply In_empty in H1. 
      destruct H1.  
       
Qed.

Lemma Subset_min_max_In': forall a b, 
(forall i, option_nat (NSet.min_elt b)<= i /\ i <= option_nat (NSet.max_elt b) ->
NSet.In i b)->
option_nat (NSet.min_elt b) <= option_nat (NSet.min_elt a) ->
option_nat (NSet.max_elt a) <= option_nat (NSet.max_elt b)->
NSet.Subset a b.
Proof. unfold NSet.Subset. intros a b H' . intros. 
       assert((NSet.Empty a)\/ ~(NSet.Empty a)).
       apply Classical_Prop.classic. destruct H2.
       apply min_empty in H2.  pose H2.
       apply NSet.min_elt_3 in e. unfold NSet.Empty in e. 
       apply e in H1. destruct H1. 
       pose H2.
       apply  min_not_empty in n.
       destruct n. pose H3. 
       apply (@NSet.min_elt_2 _ _ a0) in e; try assumption.
       apply  max_not_empty in H2.
       destruct H2. pose H2. 
       apply (@NSet.max_elt_2 _ _ a0) in e0; try assumption.
       apply H'. split.  
       apply le_trans with (option_nat (NSet.min_elt a)).
       assumption. rewrite H3. simpl. lia. 
       apply le_trans with (option_nat (NSet.max_elt a)).
       rewrite H2. simpl. lia. assumption.    
Qed.


Lemma QExp_not_empty: forall qs,
Considered_QExp qs->
~ NSet.Equal (Free_Qexp qs) NSet.empty.
Proof. induction qs; intros; simpl in *. 
       apply Qsys_to_Set_not_empty; lia. 
       destruct H. intro.
       apply union_empty in H1. 
       destruct H1. destruct IHqs1; try assumption.       
Qed.

Lemma add_sub_eq_nz': forall m n p, 
m>=n->
m-n=p->p+n=m.
Proof. destruct p; intros. simpl. lia. apply add_sub_eq_nz in H0. lia. lia.     
Qed.


Lemma max_add_sub: forall a b,
max (a+1) (b+1) -1= max a b .
Proof. intros. assert(a<=b\/ ~(a<=b)). 
      apply Classical_Prop.classic. 
      destruct H. 
      rewrite max_r; try lia. 
      rewrite max_l; try lia. 
Qed.

Lemma Free_Qexp_snd_gt_0: forall qs,  
Considered_QExp qs->
(snd ( (Free_QExp' qs))) >= 1.
Proof. induction qs; intros; simpl in *. lia.
      destruct H. destruct H0. apply IHqs1 in H.
      apply IHqs2 in H0. lia.
Qed.  
          

Lemma Free_State_snd_gt_0: forall F,  
Considered_Formula F->(Free_State F)<> None->
 (snd (option_free (Free_State F))) >= 1.
Proof. induction F; intros; simpl in *. destruct H0. reflexivity.  
        apply Free_Qexp_snd_gt_0. assumption. 

        destruct (option_beq (Free_State F1) None) eqn:E.
        apply IHF2; try assumption. 
        destruct (option_beq (Free_State F2) None) eqn:E1.
        apply IHF1; try assumption.
        simpl in *.  
        destruct H. destruct H1.
        apply IHF1 in H. 
        apply IHF2 in H1. lia. 
        apply option_eqb_neq; try assumption.    
        apply option_eqb_neq; try assumption.
        
        destruct (option_beq (Free_State F1) None) eqn:E.
        apply IHF2; try assumption. 
        destruct (option_beq (Free_State F2) None) eqn:E1.
        apply IHF1; try assumption.
        simpl in *.  
        destruct H. destruct H1.
        apply IHF1 in H. 
        apply IHF2 in H1. lia. 
        apply option_eqb_neq; try assumption.    
        apply option_eqb_neq; try assumption.

        apply IHF; try assumption.
Qed.

Lemma  Considered_Qexp_max: forall qs ,
Considered_QExp qs ->
snd ( (Free_QExp' qs))-1=
option_nat (NSet.max_elt ( (Free_Qexp qs))).
Proof.
induction qs; intros. simpl.
simpl in H. 
apply Qsys_to_Set_min_max in H. destruct H.
rewrite H0. reflexivity.

simpl in H. destruct H. destruct H0.   
pose( IHqs1 H). 
pose(IHqs2 H0).
simpl in *. apply add_sub_eq_nz' in e.  
apply add_sub_eq_nz' in e0. rewrite <-e. rewrite<- e0.
rewrite max_add_sub. 
symmetry.
apply max_union. apply QExp_not_empty; try assumption.
apply QExp_not_empty; try assumption. 
apply Free_Qexp_snd_gt_0. assumption.
apply Free_Qexp_snd_gt_0. assumption.  
Qed. 


Lemma  Considered_Qexp_min: forall qs ,
Considered_QExp qs ->
fst ( (Free_QExp' qs)) =
option_nat (NSet.min_elt ( (Free_Qexp qs))).
Proof.
induction qs; intros. simpl.
simpl in H. 
apply Qsys_to_Set_min_max in H. destruct H.
rewrite H. reflexivity.

simpl in H. destruct H. destruct H0.   
pose( IHqs1 H). 
pose(IHqs2 H0).
simpl in *.  rewrite e. rewrite e0.
symmetry.
apply min_union. apply QExp_not_empty; try assumption.
apply QExp_not_empty; try assumption. 
Qed.



Lemma Free_State_None_empty: forall F,
option_beq (Free_State F) None = true ->
NSet.Equal (snd (Free_state F)) NSet.empty.
Proof. induction F;  intros; simpl in *. reflexivity. 
       induction qs; intros. simpl in *. intuition. 
       simpl in *. intuition. 

       destruct (option_beq (Free_State F1) None) eqn :E.
       destruct (option_beq (Free_State F2) None) eqn :E1.
    apply union_empty. split; auto. intuition.
    destruct (option_beq (Free_State F2) None) eqn :E1. rewrite H in E. 
    intuition.  simpl in *. intuition. 

    destruct (option_beq (Free_State F1) None) eqn :E.
       destruct (option_beq (Free_State F2) None) eqn :E1.
    apply union_empty. split; auto. intuition.
    destruct (option_beq (Free_State F2) None) eqn :E1. rewrite H in E. 
    intuition.  simpl in *. intuition. 

    apply IHF. assumption.
Qed.


Lemma Free_State_not_empty: forall F,
Considered_Formula F->
option_beq (Free_State F) None = false ->
~ NSet.Equal (snd (Free_state F)) NSet.empty.
Proof. induction F; intros; simpl in *. intuition.   
      apply QExp_not_empty. assumption.
      
      destruct (option_beq (Free_State F1) None) eqn :E.
      intro. apply union_empty in H1.  destruct H1.
      apply IHF2 in H0. destruct H0. assumption. assumption.
      
      destruct (option_beq (Free_State F2) None) eqn :E1.
      intro. apply union_empty in H1.  destruct H1.
      apply IHF1 in H1. destruct H1. assumption. reflexivity.

      intro. apply union_empty in H1.  destruct H1.
      apply IHF1 in H1. destruct H1. apply H. reflexivity.

      destruct (option_beq (Free_State F1) None) eqn :E.
      intro. apply union_empty in H1.  destruct H1.
      apply IHF2 in H0. destruct H0. assumption. assumption.
      
      destruct (option_beq (Free_State F2) None) eqn :E1.
      intro. apply union_empty in H1.  destruct H1.
      apply IHF1 in H1. destruct H1. assumption. reflexivity.

      intro. apply union_empty in H1.  destruct H1.
      apply IHF1 in H1. destruct H1. apply H. reflexivity.

  
   intuition.  Qed.

Lemma  Considered_Formula_min: forall F ,
Considered_Formula F ->
fst (option_free (Free_State F))=
option_nat (NSet.min_elt (snd (Free_state F))) .
Proof. induction F; intros.  simpl. reflexivity.
       apply Considered_Qexp_min. assumption. 
       
       simpl in *.
       destruct (option_beq (Free_State F1) None) eqn:E. 
       apply IHF2 in H. 
       rewrite H. symmetry.
       apply min_union. apply Free_State_None_empty. assumption. 

       destruct (option_beq (Free_State F2) None) eqn:E1. 
       apply IHF1 in H. 
       rewrite H. symmetry.
       apply min_union.  apply Free_State_None_empty. assumption. 

       destruct H. destruct H0. pose H. pose H0. 
       apply IHF1 in c. 
       apply IHF2 in c0.
       simpl in *. rewrite c. rewrite c0. 
       symmetry.
       apply min_union.  apply Free_State_not_empty; try  assumption. 
       apply Free_State_not_empty; try assumption. 

       simpl in *.
       destruct (option_beq (Free_State F1) None) eqn:E. pose H. 
       apply IHF2 in c. 
       rewrite c. symmetry.
       apply min_union.  apply Free_State_None_empty; try assumption. 

       simpl in *.
       destruct (option_beq (Free_State F2) None) eqn:E1. pose H. 
       apply IHF1 in c. 
       rewrite c. symmetry.
       apply min_union.  apply Free_State_None_empty; try assumption. 

       destruct H. destruct H0. pose H. pose H0. 
       apply IHF1 in c. 
       apply IHF2 in c0.
       simpl in *. rewrite c. rewrite c0. 
       symmetry.
       apply min_union.  apply Free_State_not_empty; try  assumption. 
       apply Free_State_not_empty; try assumption. 

       simpl in *. auto.  
Qed.




Lemma  Considered_Formula_max: forall F ,
Considered_Formula F ->
snd (option_free (Free_State F))-1=
option_nat (NSet.max_elt (snd (Free_state F))).
Proof. induction F; intros.  simpl. reflexivity. 
        
      apply Considered_Qexp_max. assumption.
       
       simpl in *.
       destruct (option_beq (Free_State F1) None) eqn:E. pose H.
       assert(Free_State F2=None\/ ~(Free_State F2=None)).
       apply Classical_Prop.classic. destruct H0. rewrite H0.
       assert(option_beq (Free_State F2) None = true).
       rewrite H0. reflexivity. 
       apply Free_State_None_empty in H1.  
       eapply (max_union  ((snd (Free_state F1)))) in H1.
       rewrite H1.   rewrite  max_empty. simpl. reflexivity. 
       rewrite <-empty_Empty. apply Free_State_None_empty. assumption. 
       apply IHF2 in c.  apply add_sub_eq_nz' in c.  
       rewrite <-c.  rewrite add_sub. symmetry.
       apply max_union. apply Free_State_None_empty. assumption.
       apply Free_State_snd_gt_0; try assumption. 
      
       destruct (option_beq (Free_State F2) None) eqn:E1. pose H. 
       apply IHF1 in c.  apply add_sub_eq_nz' in c.  
       rewrite <-c.  rewrite add_sub. symmetry.
       apply max_union. apply Free_State_None_empty. 
       assumption. apply Free_State_snd_gt_0. assumption.
       apply option_eqb_neq. assumption.
     

       destruct H. destruct H0.  
       pose (IHF1  H). 
       pose( IHF2  H0).
       simpl in *. 
       apply add_sub_eq_nz' in e.  
       apply add_sub_eq_nz' in e0. rewrite <-e. rewrite<- e0.
       rewrite max_add_sub.
       symmetry.
       apply max_union.
       apply Free_State_not_empty;try
       assumption.  apply Free_State_not_empty; try 
       assumption.
       apply Free_State_snd_gt_0. assumption.
       apply option_eqb_neq. assumption.
       apply Free_State_snd_gt_0. assumption.
       apply option_eqb_neq. assumption.

       simpl in *.
       destruct (option_beq (Free_State F1) None) eqn:E. pose H.
       assert(Free_State F2=None\/ ~(Free_State F2=None)).
       apply Classical_Prop.classic. destruct H0. rewrite H0.
       assert(option_beq (Free_State F2) None = true).
       rewrite H0. reflexivity. 
       apply Free_State_None_empty in H1.  
       eapply (max_union  ((snd (Free_state F1)))) in H1.
       rewrite H1.   rewrite  max_empty. simpl. reflexivity. 
       rewrite <-empty_Empty. apply Free_State_None_empty. assumption. 
       apply IHF2 in c.  apply add_sub_eq_nz' in c.  
       rewrite <-c.  rewrite add_sub. symmetry.
       apply max_union. apply Free_State_None_empty. assumption.
       apply Free_State_snd_gt_0; try assumption. 
      
       destruct (option_beq (Free_State F2) None) eqn:E1. pose H. 
       apply IHF1 in c.  apply add_sub_eq_nz' in c.  
       rewrite <-c.  rewrite add_sub. symmetry.
       apply max_union. apply Free_State_None_empty. 
       assumption. apply Free_State_snd_gt_0. assumption.
       apply option_eqb_neq. assumption.
     

       destruct H. destruct H0.  
       pose (IHF1  H). 
       pose( IHF2  H0).
       simpl in *. 
       apply add_sub_eq_nz' in e.  
       apply add_sub_eq_nz' in e0. rewrite <-e. rewrite<- e0.
       rewrite max_add_sub.
       symmetry.
       apply max_union.
       apply Free_State_not_empty; try
       assumption.
       apply Free_State_not_empty; try
       assumption.  
       apply Free_State_snd_gt_0. assumption.
       apply option_eqb_neq. assumption.
       apply Free_State_snd_gt_0. assumption.
       apply option_eqb_neq. assumption.

       simpl in *. auto.  
Qed.


Lemma Qsys_inter_empty: forall s e x, 
s<e->
(option_nat (NSet.max_elt x) <s) \/
(e<=option_nat (NSet.min_elt x)) ->
NSet.Equal (NSet.inter (Qsys_to_Set s e) x ) NSet.empty.
Proof. intros. assert(NSet.Empty x \/ ~(NSet.Empty x)).
       apply Classical_Prop.classic. 
       destruct H1. apply inter_empty. right. rewrite empty_Empty. assumption.
       unfold NSet.Equal in *. intros. split; intros.
       pose H1.  apply min_not_empty in n. 
       apply max_not_empty in H1. destruct n. destruct H1.
       rewrite H1 in *. rewrite H3 in *. simpl in *. 
       apply (@NSet.max_elt_2 _ _ a)in H1.
       apply (@NSet.min_elt_2 _ _ a)in H3.
       apply NSet.inter_1 in H2. 
       apply In_Qsys in H2; try lia.   
       apply NSet.inter_2 in H2. assumption. 
       apply NSet.inter_2 in H2. assumption.
       apply In_empty in H2. destruct H2. 
Qed.









Lemma Considered_Qexp_set: forall qs,
Considered_QExp qs->
(forall i, option_nat (NSet.min_elt ( (Free_Qexp qs)))<= i 
/\ i <= option_nat (NSet.max_elt ( (Free_Qexp qs))) ->
NSet.In i (( (Free_Qexp qs)))).
Proof.  induction qs; simpl in *; intros. 
      pose(Qsys_to_Set_min_max s e H). destruct a.
     rewrite H1 in H0. rewrite H2 in H0. 
      apply In_Qsys; try lia. 
      destruct H. destruct H1.
      pose (QExp_not_empty qs1 H).
      pose (QExp_not_empty qs2 H1).
      pose n0. pose n0.
      eapply (min_union) in n1; try apply n. 
      eapply (max_union) in n2; try apply n. 
      rewrite n1 in *. rewrite n2 in *. 
       rewrite Considered_Qexp_min in H2; try assumption.
       rewrite Considered_Qexp_min in H2; try assumption.
       pose( Considered_Qexp_max qs1 H).
      apply add_sub_eq_nz' in e. rewrite <-e in H2.  
      pose( Considered_Qexp_max qs2 H1).
      apply add_sub_eq_nz' in e0. rewrite <-e0 in H2. 
      destruct H2. 
      rewrite  <-H2 in H0. apply add_sub_eq_r in H2.
      rewrite <-H2 in H0 at 2. 
      rewrite min_l in H0.  rewrite max_r in H0. 
      assert((i<=option_nat (NSet.max_elt (Free_Qexp qs1)))\/
       ~((i<=option_nat (NSet.max_elt (Free_Qexp qs1))))).
       apply Classical_Prop.classic. 
       destruct H3. 
       apply NSet.union_2. apply IHqs1; try lia; try assumption.
       apply NSet.union_3. apply IHqs2; try lia; try assumption.
       pose (min_le_max (Free_Qexp qs2)). lia.
       pose (min_le_max (Free_Qexp qs1)). lia.  

       rewrite  <-H2 in H0. apply add_sub_eq_r in H2.
       rewrite <-H2 in H0 at 2. 
       rewrite min_r in H0.  rewrite max_l in H0. 
       assert((i<=option_nat (NSet.max_elt (Free_Qexp qs2)))\/
        ~((i<=option_nat (NSet.max_elt (Free_Qexp qs2))))).
        apply Classical_Prop.classic. 
        destruct H3. 
        apply NSet.union_3. apply IHqs2; try lia; try assumption.
        apply NSet.union_2. apply IHqs1; try lia; try assumption.
        pose (min_le_max (Free_Qexp qs1)). lia.
        pose (min_le_max (Free_Qexp qs2)). lia.
        apply Free_Qexp_snd_gt_0. assumption.
        apply Free_Qexp_snd_gt_0. assumption.
Qed.






Lemma Considered_Formula_set: forall F,
Considered_Formula F->(~ NSet.Empty (snd (Free_state F)))->
(forall i, option_nat (NSet.min_elt (snd (Free_state F)))<= i 
/\ i <= option_nat (NSet.max_elt (snd (Free_state F))) ->
NSet.In i ((snd (Free_state F)))). 
Proof. induction F; intros; simpl in *. destruct H0. apply NSet.empty_1.
      apply Considered_Qexp_set. assumption. assumption.
     
      destruct (option_beq (Free_State F1) None) eqn:E. 
      rewrite <-empty_Empty in H0. 
      apply union_not_empty in H0. 
      destruct H0. apply Free_State_None_empty in E. 
      destruct H0. assumption. 
      
    apply NSet.union_3. apply IHF2; try assumption. intro.
    rewrite empty_Empty in *. destruct H0. assumption.
    
    pose E. apply Free_State_None_empty in e. 
    eapply (min_union _ (snd (Free_state F2))) in e.
    apply Free_State_None_empty in E. 
    eapply (max_union _ (snd (Free_state F2))) in E. 
    rewrite e in *. rewrite E in *.  assumption. 

    destruct (option_beq (Free_State F2) None) eqn:E1. 
      rewrite <-empty_Empty in H0. 
      apply union_not_empty in H0. 
      destruct H0. apply Free_State_None_empty in E1. 
    
    apply NSet.union_2. apply IHF1; try assumption. intro.
    rewrite empty_Empty in *. destruct H0. assumption.
    
    pose E1. 
    eapply (min_union  (snd (Free_state F1))) in e.
    eapply (max_union  (snd (Free_state F1))) in E1. 
    rewrite e in *. rewrite E1 in *.  assumption. 
    apply Free_State_None_empty in E1. destruct H0. 
    assumption. 

    destruct H. destruct H2. 
      pose (Free_State_not_empty  F1 H E).
      pose (Free_State_not_empty F2 H2 E1).
      pose n0. pose n0.
      eapply (min_union) in n1; try apply n. 
      eapply (max_union) in n2; try apply n. 
      rewrite n1 in *. rewrite n2 in *. 
       rewrite Considered_Formula_min in H3; try assumption.
       rewrite Considered_Formula_min in H3; try assumption.
       pose( Considered_Formula_max F1 H).
      apply add_sub_eq_nz' in e. rewrite <-e in H3.  
      pose( Considered_Formula_max F2 H2).
      apply add_sub_eq_nz' in e0. rewrite <-e0 in H3. 
      destruct H3. 
      rewrite  <-H3 in H1. apply add_sub_eq_r in H3.
      rewrite <-H3 in H1 at 2. 
      rewrite min_l in H1.  rewrite max_r in H1. 
      assert((i<=option_nat (NSet.max_elt (snd (Free_state F1))))\/
       ~((i<=option_nat (NSet.max_elt (snd (Free_state F1)))))).
       apply Classical_Prop.classic. 
       destruct H4. 
       apply NSet.union_2. apply IHF1; try lia; try assumption. 
       intro. rewrite <-empty_Empty in H5. 
       destruct n. assumption.  
       apply NSet.union_3. apply IHF2; try lia; try assumption.
       intro. rewrite <-empty_Empty in H5. 
       destruct n0. assumption.  
       pose (min_le_max (snd (Free_state F2))). lia.
       pose (min_le_max (snd (Free_state F1))). lia.  

       rewrite  <-H3 in H1. apply add_sub_eq_r in H3.
      rewrite <-H3 in H1 at 2. 
      rewrite min_r in H1.  rewrite max_l in H1. 
      assert((i<=option_nat (NSet.max_elt (snd (Free_state F2))))\/
       ~((i<=option_nat (NSet.max_elt (snd (Free_state F2)))))).
       apply Classical_Prop.classic. 
       destruct H4.
       apply NSet.union_3. apply IHF2; try lia; try assumption.
       intro. rewrite <-empty_Empty in H5. 
       destruct n0. assumption.
       apply NSet.union_2. apply IHF1; try lia; try assumption. 
       intro. rewrite <-empty_Empty in H5. 
       destruct n. assumption.    
       pose (min_le_max (snd (Free_state F1))). lia.  
       pose (min_le_max (snd (Free_state F2))). lia.
       apply Free_State_snd_gt_0. assumption. 
       intro. destruct n0. 
       apply Free_State_None_empty. rewrite H4. reflexivity. 
       apply Free_State_snd_gt_0. assumption. 
       intro. destruct n. 
       apply Free_State_None_empty. rewrite H4. reflexivity. 


      destruct (option_beq (Free_State F1) None) eqn:E. 
      rewrite <-empty_Empty in H0. 
      apply union_not_empty in H0. 
      destruct H0. apply Free_State_None_empty in E. 
      destruct H0. assumption. 
      
    apply NSet.union_3. apply IHF2; try assumption. intro.
    rewrite empty_Empty in *. destruct H0. assumption.
    
    pose E. apply Free_State_None_empty in e. 
    eapply (min_union _ (snd (Free_state F2))) in e.
    apply Free_State_None_empty in E. 
    eapply (max_union _ (snd (Free_state F2))) in E. 
    rewrite e in *. rewrite E in *.  assumption. 

    destruct (option_beq (Free_State F2) None) eqn:E1. 
      rewrite <-empty_Empty in H0. 
      apply union_not_empty in H0. 
      destruct H0. apply Free_State_None_empty in E1. 
    
    apply NSet.union_2. apply IHF1; try assumption. intro.
    rewrite empty_Empty in *. destruct H0. assumption.
    
    pose E1. 
    eapply (min_union  (snd (Free_state F1))) in e.
    eapply (max_union  (snd (Free_state F1))) in E1. 
    rewrite e in *. rewrite E1 in *.  assumption. 
    apply Free_State_None_empty in E1. destruct H0. 
    assumption. 

    destruct H. destruct H2. 
      pose (Free_State_not_empty  F1 H E).
      pose (Free_State_not_empty F2 H2 E1).
      pose n0. pose n0.
      eapply (min_union) in n1; try apply n. 
      eapply (max_union) in n2; try apply n. 
      rewrite n1 in *. rewrite n2 in *. 
       rewrite Considered_Formula_min in H3; try assumption.
       rewrite Considered_Formula_min in H3; try assumption.
       pose( Considered_Formula_max F1 H).
      apply add_sub_eq_nz' in e. rewrite <-e in H3.  
      pose( Considered_Formula_max F2 H2).
      apply add_sub_eq_nz' in e0. rewrite <-e0 in H3.   
      destruct H3. destruct H3. 
      rewrite min_l in H1.  rewrite max_r in H1.     
      rewrite H3 in H1.  
      apply NSet.union_3. apply IHF2; try lia; try assumption. 
      intro. rewrite <-empty_Empty in H5.  
      destruct n0. assumption. 
      lia. lia.   

      destruct H3.
      rewrite  <-H3 in H1. apply add_sub_eq_r in H3.
      rewrite <-H3 in H1 at 2. 
      rewrite min_l in H1.  rewrite max_r in H1. 
      assert((i<=option_nat (NSet.max_elt (snd (Free_state F1))))\/
       ~((i<=option_nat (NSet.max_elt (snd (Free_state F1)))))).
       apply Classical_Prop.classic. 
       destruct H4. 
       apply NSet.union_2. apply IHF1; try lia; try assumption. 
       intro. rewrite <-empty_Empty in H5. 
       destruct n. assumption.  
       apply NSet.union_3. apply IHF2; try lia; try assumption.
       intro. rewrite <-empty_Empty in H5. 
       destruct n0. assumption.  
       pose (min_le_max (snd (Free_state F2))). lia.
       pose (min_le_max (snd (Free_state F1))). lia.  

       rewrite  <-H3 in H1. apply add_sub_eq_r in H3.
      rewrite <-H3 in H1 at 2. 
      rewrite min_r in H1.  rewrite max_l in H1. 
      assert((i<=option_nat (NSet.max_elt (snd (Free_state F2))))\/
       ~((i<=option_nat (NSet.max_elt (snd (Free_state F2)))))).
       apply Classical_Prop.classic. 
       destruct H4.
       apply NSet.union_3. apply IHF2; try lia; try assumption.
       intro. rewrite <-empty_Empty in H5. 
       destruct n0. assumption.
       apply NSet.union_2. apply IHF1; try lia; try assumption. 
       intro. rewrite <-empty_Empty in H5. 
       destruct n. assumption.    
       pose (min_le_max (snd (Free_state F1))). lia.  
       pose (min_le_max (snd (Free_state F2))). lia.
       apply Free_State_snd_gt_0. assumption. 
       intro. destruct n0. 
       apply Free_State_None_empty. rewrite H4. reflexivity. 
       apply Free_State_snd_gt_0. assumption. 
       intro. destruct n. 
       apply Free_State_None_empty. rewrite H4. reflexivity. 

      apply IHF; try assumption. 
Qed.


Lemma Considered_Formula_set_eq: forall F,
Considered_Formula F->(~ NSet.Empty (snd (Free_state F)))->
NSet.Equal (Qsys_to_Set (option_nat (NSet.min_elt (snd (Free_state F)))) 
(option_nat (NSet.max_elt (snd (Free_state F))) + 1))
(snd (Free_state F)). 
Proof. unfold NSet.Equal in *. intros. split; intros. 
        apply Considered_Formula_set; try assumption. 
        pose (In_Qsys 
        (option_nat (NSet.max_elt (snd (Free_state F))) + 1) 
        (option_nat (NSet.min_elt (snd (Free_state F)))) a).
        rewrite i in H1. lia. 
        pose (min_le_max (snd (Free_state F))). lia. 

        apply In_Qsys. 
        pose (min_le_max (snd (Free_state F))). lia. 
       
        pose H0.
        apply max_not_empty  in n. 
        apply min_not_empty  in H0.
        destruct n. destruct H0. rewrite H0. rewrite H2.
        simpl in *.    
        pose (@NSet.min_elt_2 (snd (Free_state F)) _ a H0 H1). 
        pose (@NSet.max_elt_2 (snd (Free_state F)) _ a H2 H1). 
        lia.
Qed.     

Lemma equal_trans: forall a b c, 
NSet.Equal a b ->
NSet.Equal b c ->
NSet.Equal a c.
Proof. unfold NSet.Equal in *. intros.  split; intros. 
apply H0. apply H. assumption.
apply H. apply H0. assumption.  
       
Qed.

Lemma inter_eq: forall a b c d,
NSet.Equal a b ->
NSet.Equal c d ->
NSet.Equal (NSet.inter a c ) (NSet.inter b d ).
Proof. unfold NSet.Equal. intros. split; intros.  
      apply NSet.inter_3. apply H. eapply NSet.inter_1.
      apply H1. apply H0.    eapply NSet.inter_2.
      apply H1. 
      apply NSet.inter_3. apply H. eapply NSet.inter_1.
      apply H1. apply H0.    eapply NSet.inter_2.
      apply H1.   
       
Qed. 


Lemma Qsys_inter_empty': forall s e l r, 
s<e->l<r->
NSet.Equal (NSet.inter (Qsys_to_Set s e) (Qsys_to_Set l r) ) NSet.empty->
(e<=l) \/ (r <=s) .
Proof.
       unfold NSet.Equal in *. intros.
       apply Classical_Prop.NNPP. intro. 
       apply Classical_Prop.not_or_and in H2. destruct H2.
       assert(l<=s\/~(l<=s)). apply Classical_Prop.classic.
       destruct H4.  destruct (In_empty s). apply H1. 
       apply NSet.inter_3. apply In_Qsys. lia. lia.  
       apply In_Qsys. lia. lia.  
       destruct (In_empty l). apply H1. 
       apply NSet.inter_3. apply In_Qsys. lia. lia.  
       apply In_Qsys. lia. lia.
Qed.  

    

Lemma Considered_Formula_not_empty_dom: forall F,
Considered_Formula F ->Free_State F <> None ->
fst (option_free (Free_State F)) < snd (option_free (Free_State F)).
Proof. induction F; intros.
       simpl in *. destruct H0. reflexivity. 
       apply Considered_QExp_dom in H. assumption.
       
        simpl in *.
       destruct (option_beq (Free_State F1) None) eqn :E.
       apply IHF2; try assumption. 
      
      destruct (option_beq (Free_State F2) None) eqn :E1.
      apply IHF1; try assumption.  
      
      simpl in *.  destruct H. destruct H1.
      apply IHF1 in H. apply IHF2  in H1.  
      destruct H2. rewrite min_l. rewrite max_r. lia. lia. lia. 
      rewrite min_r. rewrite max_l. lia. lia. lia. 
      rewrite option_eqb_neq. assumption.  
      rewrite option_eqb_neq. assumption. 
      
      simpl in *.
       destruct (option_beq (Free_State F1) None) eqn :E.
       apply IHF2; try assumption. 
      
      destruct (option_beq (Free_State F2) None) eqn :E1.
      apply IHF1; try assumption.  
      
      simpl in *.  destruct H. destruct H1.  
      apply IHF1 in H. apply IHF2  in H1.  
      destruct H2.
      rewrite min_l. rewrite max_r. lia. lia. lia.
      destruct H2.  
      rewrite min_l. rewrite max_r. lia. lia. lia.
      rewrite min_r. rewrite max_l. lia. lia. lia. 
      rewrite option_eqb_neq. assumption.  
      rewrite option_eqb_neq. assumption. 

simpl in *. apply IHF. assumption. assumption. 
Qed.

Lemma inter_empty_to_QSys: forall F1 F2,
Considered_Formula F1 ->
Considered_Formula F2 ->
~ NSet.Empty (snd (Free_state F1))->
~ NSet.Empty (snd (Free_state F2))->
NSet.Equal (NSet.inter (snd (Free_state F1)) (snd (Free_state F2))) NSet.empty->
snd (option_free (Free_State F1)) <= fst (option_free (Free_State F2))\/
snd (option_free (Free_State F2)) <= fst (option_free (Free_State F1)) .
Proof.  intros.     
       assert( NSet.Equal 
       (NSet.inter (Qsys_to_Set (option_nat (NSet.min_elt (snd (Free_state F1)))) 
       (option_nat (NSet.max_elt (snd (Free_state F1))) + 1))
       (Qsys_to_Set (option_nat (NSet.min_elt (snd (Free_state F2)))) 
(option_nat (NSet.max_elt (snd (Free_state F2))) + 1))) NSet.empty).
eapply equal_trans ; try apply H3. 
apply inter_eq;
apply Considered_Formula_set_eq; try assumption.
apply Qsys_inter_empty'. 
apply Considered_Formula_not_empty_dom; try assumption. 
intro. destruct H1. rewrite <-empty_Empty. apply Free_State_None_empty.
rewrite H5. reflexivity. 
apply Considered_Formula_not_empty_dom; try assumption. 
intro. destruct H2. rewrite <-empty_Empty. apply Free_State_None_empty.
rewrite H5. reflexivity. 
rewrite Considered_Formula_min; try assumption. 
rewrite Considered_Formula_min; try assumption. 
pose(Considered_Formula_max F1 H). 
pose(Considered_Formula_max F2 H0). 
rewrite <-e in H4. rewrite <-e0 in H4. 
rewrite sub_add in H4. rewrite sub_add in H4. 
assumption. 
apply Free_State_snd_gt_0; try assumption.
intro. destruct H2. rewrite <-empty_Empty. apply Free_State_None_empty.
rewrite H5. reflexivity. 
apply Free_State_snd_gt_0; try assumption.
intro. destruct H1. rewrite <-empty_Empty. apply Free_State_None_empty.
rewrite H5. reflexivity. 
Qed.



Lemma d_reduced_sort{s e:nat}:forall (mu: list (state s e)) l r,
Sorted (StateMap.Raw.PX.ltk (elt:=qstate s e)) mu->
Sorted (StateMap.Raw.PX.ltk (elt:=qstate s e)) (d_reduced mu l r).
Proof. induction mu; intros. simpl. econstructor.
inversion_clear H. 
destruct a. simpl. econstructor . 
apply IHmu. assumption.
destruct mu. simpl in *. econstructor.
destruct s0. 
simpl. econstructor.  inversion_clear H1.
unfold StateMap.Raw.PX.ltk in *. simpl in *.
assumption.
Qed.


Lemma Pure_free_dstate{s e s' e':nat}:forall  (F: State_formula)  (mu : list (state s e))  l r,
(Free_State F)= None-> 
State_eval_dstate F mu -> 
State_eval_dstate F (d_reduced mu l r).
Proof. induction mu; intros. simpl in *.  destruct H0.
       destruct a.   inversion_clear H0.  destruct mu.
       simpl in *. econstructor.  
       eapply Pure_free_eval'. assumption. apply H1.
       econstructor. destruct s0.   
       simpl. econstructor.   
       eapply Pure_free_eval'. assumption. apply H1.
       apply IHmu. assumption. assumption.
Qed. 






Definition Considered_Formula_F_c (F1 F2 F3:State_formula) c:=
(Free_State F1 = None \/ ((option_nat (NSet.max_elt (snd (MVar c)))) >= fst (option_free (Free_State F1)) /\
 snd (option_free (Free_State F1)) >= ((option_nat (NSet.min_elt (snd (MVar c)))))))
/\ Considered_Formula F1 /\ Considered_Formula F2 /\Considered_Formula F3.


Lemma inter_empty: forall a b,
NSet.Equal a (NSet.empty) \/
NSet.Equal b (NSet.empty) ->
NSet.Equal (NSet.inter a b) (NSet.empty).
Proof. unfold NSet.Equal. intros. split; intros. 
       destruct H. apply H. eapply NSet.inter_1. 
       apply H0. 
       apply H. eapply NSet.inter_2. 
       apply H0. 
       apply In_empty in H0. destruct H0.    
Qed.

Lemma subset_empty':forall a b,
NSet.Equal a NSet.empty->
NSet.Subset a b.
Proof. unfold NSet.Subset. unfold NSet.Equal; intros. 
       apply H in H0. 
       apply In_empty in H0. destruct H0.  
       
Qed.



Lemma add_sub_eq_r: forall m n p, 
m>=n->
m<p+n-> m-n<p.
Proof. destruct p; intros. simpl. lia. lia.     
Qed.

Lemma ceval_single_classic{s e:nat}:  forall c (mu mu':list (state s e)) l r , 
NSet.Equal (snd (MVar c)) NSet.empty->
ceval_single c mu mu'->
ceval_single c (d_reduced mu l r) (d_reduced mu' l r).
Proof. induction c. intros. apply ceval_skip_1 in H0. subst. 
      apply ceval_skip. 
      induction mu; intros; inversion_clear H0. econstructor.
      rewrite d_reduced_map2. simpl d_reduced .
      rewrite (state_eq_aexp _ (sigma, Reduced rho l r)); try reflexivity.
      econstructor. apply IHmu; try assumption. 

      induction mu; intros; inversion H0; subst. econstructor.  simpl. econstructor.
      assumption.
     
      intros. simpl in H. apply union_empty in H.
      destruct H.    apply ceval_seq_1 in H0. destruct H0. destruct H0.
      eapply ceval_seq with (d_reduced x l r). apply IHc1; try assumption.
      apply IHc2; try assumption.

      induction mu; intros; inversion_clear H0. econstructor.
      rewrite d_reduced_map2; simpl d_reduced .
      econstructor. 
      rewrite (state_eq_bexp _ (sigma, rho)); try reflexivity; try assumption.
      simpl in H. apply union_empty in H.  destruct H.   
      apply subset_empty'. assumption.
      apply IHmu; try assumption. 
      simpl in H. apply union_empty in H.  destruct H.   
      pose (IHc1 [(sigma, rho)] mu'0 ). simpl in c. apply c; try assumption.
      
      rewrite d_reduced_map2; simpl d_reduced .
      apply E_IF_false. 
      rewrite (state_eq_bexp _ (sigma, rho)); try reflexivity; try assumption.
      simpl in H. apply union_empty in H.  destruct H.   
      apply subset_empty'. assumption.
      apply IHmu; try assumption. 
      simpl in H. apply union_empty in H.  destruct H.   
      pose (IHc2 [(sigma, rho)] mu'0 ). simpl in c. apply c; try assumption.

      intros.  remember <{while b do c end}> as original_command eqn:Horig. 
    induction H0;  try inversion Horig; subst. 
    econstructor. rewrite d_reduced_map2; simpl d_reduced . 
    econstructor. 
    rewrite (state_eq_bexp _ (sigma, rho)); try reflexivity; try assumption.
    apply IHceval_single1; try reflexivity; try assumption.   
    pose (IHc [(sigma, rho)] mu1 ). simpl in c0. apply c0; try assumption.
    apply IHceval_single3; try reflexivity; try assumption.

     rewrite d_reduced_map2; simpl d_reduced . 
    apply E_While_false. 
    rewrite (state_eq_bexp _ (sigma, rho)); try reflexivity; try assumption. 
    apply subset_empty'. assumption.
    apply IHceval_single; try reflexivity; try assumption.   
   
    intros. simpl in *.  inversion_clear H0. econstructor.
     pose (Qsys_to_Set_not_empty s0 e0). destruct n. lia. assumption. 
     intros. simpl in *.  inversion_clear H0. econstructor.
     pose (Qsys_to_Set_not_empty s0 e0). destruct n. lia. assumption.
     intros. simpl in *.  inversion_clear H0. econstructor.
     pose (Qsys_to_Set_not_empty s0 e0). destruct n. lia. 
     apply union_empty in H. apply H.
     intros. simpl in *.  inversion_clear H0. econstructor.
     pose (Qsys_to_Set_not_empty s0 e0). destruct n. lia. assumption. 

       
Qed.

Lemma WF_lt: forall s e (mu:list (state s e)),
mu <> [] ->
WF_dstate_aux mu -> s<=e .
Proof. induction mu; intros. destruct H. reflexivity.  
      destruct a. inversion_clear H0. unfold WF_state in H1. 
      unfold WF_qstate in H1. lia.        
       
Qed.



Theorem rule_qframe: forall (F1 F2 F3: State_formula) c,
Considered_Formula_F_c F1 F2 F3 c-> 
({{F1}} c {{F2}}) 
/\ (NSet.Equal (NSet.inter (fst (Free_state F3)) (fst (MVar c))) (NSet.empty) )
/\ ((option_nat (NSet.max_elt (snd (MVar c)))) <  fst (option_free (Free_State F3)) \/
snd (option_free (Free_State F3)) <= ((option_nat (NSet.min_elt (snd (MVar c))))))
-> {{F1 ⊙ F3}} c {{F2 ⊙ F3}}. 
Proof.  unfold hoare_triple.  intros F1 F2 F3 c HF3. intros. destruct H. 
        unfold Considered_Formula_F_c in HF3.
        assert(StateMap.this mu<>[]) as H'. 
        eapply WF_sat_Assert. apply H1. 
        assert(sat_Assert mu F1 -> sat_Assert mu' F2).
        apply H. assumption. 
        destruct mu as [mu IHmu].
        destruct mu' as [mu' IHmu']. 
        
        inversion_clear H0. simpl in H5.
        repeat rewrite sat_Assert_to_State in *.
        inversion_clear H1.  simpl in *.
        econstructor. eapply WF_ceval. apply H4. apply H5. 
         simpl in *.
        pose H6.
        rewrite State_eval_odot in s0.
        rewrite State_eval_odot.
        destruct s0. destruct H7.
        split. 
        assert(sat_Assert (StateMap.Build_slist IHmu') F2).
        apply H with (StateMap.Build_slist IHmu).
        apply E_com. assumption. assumption.  rewrite sat_Assert_to_State.
        econstructor. assumption. assumption.
        rewrite sat_Assert_to_State in *.
        inversion_clear H9. assumption.
        split. 
        destruct (option_edc (Free_State F3) None).
        apply rule_f_classic with c mu; try left;
        try assumption.  apply HF3. apply H2.
        assert(NSet.Equal (snd (MVar c)) NSet.empty \/ ~NSet.Equal (snd (MVar c)) NSet.empty ).
apply Classical_Prop.classic.  
destruct H10. apply rule_f_classic with c mu; try right; try assumption. 
apply HF3. apply H2.
        apply rule_f  with  c mu; try assumption.
        split. apply HF3.
        apply State_eval_dstate_dom in H7. destruct H7. destruct H9.
assumption.
lia. apply H2. apply H2.


assert(forall (s e : nat) (mu mu' : list (state s e)),
WF_dstate_aux mu->
Sorted (StateMap.Raw.PX.ltk (elt:=qstate s e)) mu->
ceval_single c mu mu' -> State_eval_dstate F1 mu -> State_eval_dstate F2 mu').
intros.
assert(Sorted (StateMap.Raw.PX.ltk (elt:=qstate s0 e0)) mu'0).
apply ceval_sorted with c mu0; try assumption.
assert(ceval c (StateMap.Build_slist H10) (StateMap.Build_slist H13)).
econstructor. assumption.
simpl. assumption.   
assert(sat_Assert (StateMap.Build_slist H10) F1).
apply sat_Assert_to_State. econstructor.
assumption. assumption.
pose (H s0 e0 (StateMap.Build_slist H10) (StateMap.Build_slist H13) H14 H15).
rewrite sat_Assert_to_State in s1. 
inversion_clear s1. assumption. 


assert(Free_State F1 = None \/ ~(Free_State F1 = None )).
apply Classical_Prop.classic. destruct H10. 
pose (State_eval_dstate_dom mu F1 H1). 
destruct o. clear H11. 
assert(NSet.Equal (snd (MVar c)) NSet.empty \/ ~ NSet.Equal (snd (MVar c)) NSet.empty).
apply Classical_Prop.classic. 
destruct H11.
(* apply inter_empty. left. 
apply Free_State_None_empty. *)

pose H1. 
apply (@Pure_free_dstate s e) with (l:=s) (r:=s) in s0; try assumption.
pose H5. 
assert(ceval_single c (d_reduced mu s s)
(d_reduced mu' s s)) as c1.
apply ceval_single_classic; try assumption.

apply H9 in c1; try apply WF_d_reduced; try apply (@d_reduced_sort s e); try lia; try assumption .

apply subset_inter_empty with (Qsys_to_Set s s); try assumption.
apply inter_empty. left.  rewrite empty_Empty. apply Qsys_to_Set_empty'. lia.
apply State_eval_dstate_dom in c1.  destruct c1. 
apply subset_empty'. apply Free_State_None_empty. rewrite H12. reflexivity.
lia.   pose (WF_lt s e mu H' H0 ). lia.   

remember ( (option_nat (NSet.min_elt ((snd (MVar c)))) ) ) as l.
remember ( (option_nat (NSet.max_elt ((snd (MVar c)))) +1) ) as r.
assert(l<r). rewrite Heqr. rewrite Heql.  
pose (min_le_max (snd (MVar c))).   lia.    
pose (ceval_single_dom c mu mu' H0 H5 H' H11).
apply Subset_min_max_In in s0; try assumption.  
assert(s <= l /\ l <= r <= e). 
rewrite Heql. rewrite Heqr. lia.

assert (NSet.Empty (snd (Free_state F3)) \/ (~NSet.Empty (snd (Free_state F3)))).
apply Classical_Prop.classic. destruct H14.
apply inter_empty. right. rewrite empty_Empty. assumption.


pose H1.  
apply (@Pure_free_dstate s e) with (l:=l) (r:=r) in s1; try assumption.
pose H5.
apply Par_trace_ceval_swap with (l:=l) (r:=r) in c0; try assumption.
apply H9 in c0; try apply WF_d_reduced; try apply (@d_reduced_sort s e); try lia; try assumption .

apply subset_inter_empty with (Qsys_to_Set l r); try assumption.
apply Qsys_inter_empty; try lia.  
rewrite Heql. rewrite Heqr. 
destruct H2. destruct H15.
right.
rewrite <-Considered_Formula_min; try apply HF3. lia. 

left.   
rewrite <-Considered_Formula_max; try apply HF3.
apply add_sub_eq_r.  
apply Free_State_snd_gt_0; try apply HF3. 
intro. destruct H14. rewrite <-empty_Empty. 
apply Free_State_None_empty. rewrite H16. reflexivity. lia.  

apply State_eval_dstate_dom  in c0.
destruct c0.  apply subset_empty'.
apply Free_State_None_empty. rewrite H15. reflexivity. 
pose (Qsys_to_Set_min_max l r H12). destruct a. 
apply Subset_min_max_In'; 
intros; try rewrite H15 in *; try rewrite H16 in *.
apply In_Qsys; try lia.   
rewrite <-Considered_Formula_min; try apply HF3. lia. 
rewrite <-Considered_Formula_max; try apply HF3. lia.
 
pose (Qsys_to_Set_min_max l r H12). destruct a. 
apply Subset_min_max_In';
intros; try rewrite H14 in *; try rewrite H15 in *.
apply In_Qsys; try lia. lia. lia.  

rewrite H10 in *. simpl in *. lia.  
pose (State_eval_dstate_dom mu F1 H1). 
destruct o. destruct H10. assumption. 

(* Free_State F1 <> None*)
assert(NSet.Equal (snd (MVar c)) NSet.empty \/ ~ NSet.Equal (snd (MVar c)) NSet.empty).
apply Classical_Prop.classic. 
destruct H12. 
remember ( (fst (option_free (Free_State F1)))) as l.
remember ( (snd (option_free (Free_State F1)))) as r.
assert(l<r). rewrite Heqr. rewrite Heql.  lia.   
assert(s <= l /\ l <= r <= e). 
rewrite Heql. rewrite Heqr. lia.

pose H1.  
apply State_dstate_free_eval with (s':=l) (e':=r) in s0; try apply (@WF_NZ_Mixed_dstate s e); try assumption.
assert(ceval_single c (d_reduced mu l r)
(d_reduced mu' l r)) as c0.
apply ceval_single_classic; try assumption. 
apply H9 in c0; try apply WF_d_reduced; try apply (@d_reduced_sort s e); try lia; try assumption .

apply subset_inter_empty with (Qsys_to_Set l r); try assumption.  
rewrite Heql. rewrite Heqr.  
apply equal_trans with ( NSet.inter (snd (Free_state F1))(snd (Free_state F3))); try assumption.
apply inter_eq.  rewrite Considered_Formula_min; try apply HF3. 
destruct HF3. destruct H16. 
pose (Considered_Formula_max F1 H16).  
apply add_sub_eq_nz' in e0. rewrite <-e0. 
apply Considered_Formula_set_eq. assumption.
apply option_eqb_neq in H10. 
apply Free_State_not_empty in H10; try assumption. 
intro. destruct H10. rewrite empty_Empty. assumption.   
apply  Free_State_snd_gt_0; try apply H16; try assumption. 
reflexivity.


 

apply State_eval_dstate_dom  in c0.
destruct c0.    apply subset_empty'.
apply Free_State_None_empty. rewrite H15. reflexivity. 
pose (Qsys_to_Set_min_max l r H13). destruct a. 
apply Subset_min_max_In'; 
intros; try rewrite H15 in *; try rewrite H16 in *.
apply In_Qsys; try lia.   
rewrite <-Considered_Formula_min; try apply HF3. lia. 
rewrite <-Considered_Formula_max; try apply HF3. lia.
 
rewrite Heql.
rewrite Heqr. lia.  

remember (min (option_nat (NSet.min_elt ((snd (MVar c)))) ) (fst (option_free (Free_State F1)))) as l.
remember (max (option_nat (NSet.max_elt ((snd (MVar c)))) +1) (snd (option_free (Free_State F1)))) as r.


pose(State_eval_dstate_dom mu F1 H1). 
destruct o. destruct H10. assumption. 
assert(l<r). rewrite Heqr. rewrite Heql. lia.    
pose (ceval_single_dom c mu mu' H0 H5 H' H12).
apply Subset_min_max_In in s0; try assumption.  
assert(s <= l /\ l <= r <= e). 
rewrite Heql. rewrite Heqr. lia.

   
pose H1.
apply State_dstate_free_eval with (s':=l) (e':=r) in s1; try apply (@WF_NZ_Mixed_dstate s e); try assumption.
pose H5.
apply Par_trace_ceval_swap with (l:=l) (r:=r) in c0; try assumption.
apply H9 in c0; try apply WF_d_reduced; try apply (@d_reduced_sort s e); try lia; try assumption .



assert (NSet.Empty (snd (Free_state F3)) \/ (~NSet.Empty (snd (Free_state F3)))).
apply Classical_Prop.classic. destruct H16.
apply inter_empty. right. rewrite empty_Empty. assumption.
apply subset_inter_empty with (Qsys_to_Set l r); try assumption.
apply Qsys_inter_empty; try lia.  
rewrite Heql. rewrite Heqr.
destruct H2. destruct H17.
right.
rewrite <-Considered_Formula_min; try apply HF3.

apply max_lub_iff.
split. lia. 
apply inter_empty_to_QSys in H8; try apply HF3. 
destruct H8. lia. 
destruct HF3. destruct H19. destruct H20. 
pose (Considered_Formula_dom F3 H21) . 
destruct H18. destruct H10. assumption.   lia. 
rewrite <-empty_Empty.
apply Free_State_not_empty; try apply HF3. 
apply option_eqb_neq. assumption.
assumption.  

left.  
apply min_glb_lt_iff. 
rewrite <-Considered_Formula_max; try apply HF3.
split. apply add_sub_eq_r. 
apply Free_State_snd_gt_0; try apply HF3. 
intro. destruct H16. rewrite <-empty_Empty. apply Free_State_None_empty.
rewrite H18. reflexivity.        lia.   
apply inter_empty_to_QSys in H8; try apply HF3.
destruct H8.  destruct HF3.  destruct H18. destruct H10. 
assumption.   
assert(fst (option_free (Free_State F3))<snd (option_free (Free_State F3))).
apply Considered_Formula_not_empty_dom; try apply H19. 
intro. destruct H16. rewrite <-empty_Empty. apply Free_State_None_empty.
rewrite H20. reflexivity. 
lia. apply add_sub_eq_r.
apply Free_State_snd_gt_0; try apply HF3. 
intro. destruct H16. rewrite <-empty_Empty. apply Free_State_None_empty.
rewrite H18. reflexivity.   lia. 
rewrite <-empty_Empty.
apply Free_State_not_empty; try apply HF3. 
apply option_eqb_neq. assumption.
assumption.    
apply State_eval_dstate_dom  in c0.
destruct c0. apply subset_empty'.  
apply  Free_State_None_empty. rewrite H17. reflexivity.
pose (Qsys_to_Set_min_max l r H14). destruct a. 
apply Subset_min_max_In'; 
intros; try rewrite H18 in *; try rewrite H19 in *.
apply In_Qsys; try lia.   
rewrite <-Considered_Formula_min; try apply HF3. lia. 
rewrite <-Considered_Formula_max; try apply HF3. lia.
 
pose (Qsys_to_Set_min_max l r H14). destruct a. 
apply Subset_min_max_In';
intros; try rewrite H16 in *; try rewrite H17 in *.
apply In_Qsys; try lia. lia. lia.

rewrite Heql.
rewrite Heqr. 
split.  
apply  le_min_r. 
apply le_max_r. 
Qed.





Theorem rule_qframe': forall (F1 F2 F3: State_formula) c,
Considered_Formula_F_c F1 F2 F3 c ->
({{F1}} c {{F2}}) /\  (NSet.Equal (NSet.inter (fst (Free_state F3)) (fst (MVar c))) (NSet.empty) )
/\ ((option_nat (NSet.max_elt (snd (MVar c)))) <  fst (option_free (Free_State F3)) \/
snd (option_free (Free_State F3)) <= ((option_nat (NSet.min_elt (snd (MVar c))))))
->  {{F3 ⊙ F1}} c {{F3 ⊙ F2}}.
Proof. intros.
 eapply rule_conseq. apply rule_qframe.
 apply H. split. apply H0.   apply H0. 
 apply rule_OdotC.
 apply rule_OdotC.
Qed.


Theorem rule_qframe'': forall (P1 P2 P3: Pure_formula) c,
         ({{P1}} c {{P2}}) /\  (NSet.Equal (NSet.inter (fst (Free_state P3)) (fst (MVar c))) NSet.empty) 
         ->  {{P3 /\p P1}} c {{P3 /\p P2}}.
Proof. 
intros. eapply rule_conseq; try apply rule_OdotO.
eapply rule_qframe'. unfold Considered_Formula_F_c. simpl. auto.  
 split.   apply H. split. apply H.
simpl. right. lia. 
Qed.


