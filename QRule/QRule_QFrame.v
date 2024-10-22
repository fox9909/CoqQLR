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
From Quan Require Import QState.
From Quan Require Import QIMP_L.
From Quan Require Import QAssert.
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
         simpl in *. apply cstate_eq_union in H.  
         rewrite IHb1. rewrite IHb2.
         reflexivity. intuition. intuition.  
  Qed.
  
  
  Lemma cstate_eq_P{ s e:nat}: forall P c1 c2  (q: qstate s e),
  cstate_eq c1 c2 (Free_pure P)->
  State_eval P (c1, q)->
  State_eval P (c2, q).
  Proof. induction P; intros. 
         simpl. simpl in H0.
         rewrite<- (cstate_eq_b c1).
         assumption. assumption.
         simpl in *.  intros. apply IHP with (c_update i a c1).
         unfold cstate_eq in *. 
         intros. destruct (eq_dec j i).
         subst.  repeat rewrite c_update_find_eq. reflexivity.
         apply (@NSet.remove_2 _ i j) in H1; try lia. 
         apply H in H1. repeat rewrite c_update_find_not; try lia.
         apply H0.
         simpl in *. destruct H0. exists x.  apply IHP with (c_update i x c1).
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
((Free_State F = None) 
\/ @Par_Pure_State (2^((snd (option_free (Free_State F)))- ((fst (option_free (Free_State F))))))
(@PMpar_trace s e q ((fst (option_free (Free_State F)))) (((snd (option_free (Free_State F))))) )).
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
Qed. 

(*对于一个连续的而言*)  
Lemma State_free_eval{s e:nat}:forall (F: State_formula) (st: state s e) s' e',
s<=s'/\ s'<=e' /\ e'<=e ->
s'<=(fst (option_free (Free_State F))) /\ (snd (option_free (Free_State F)))<=e' ->
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
    apply (@Pure_free_eval' s' e') with (PMpar_trace (snd (c, q)) s' e'); try assumption.
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
    apply (@Pure_free_eval' s' e') with (PMpar_trace (snd (c, q)) s' e'); try assumption.
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
    apply (@Pure_free_eval' s' e') with (PMpar_trace (snd (c, q)) s' e'); try assumption.
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
    apply (@Pure_free_eval' s' e') with (PMpar_trace (snd (c, q)) s' e'); try assumption.
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
Qed.


Lemma State_dstate_free_eval{s e:nat}:forall  (mu: list (cstate * qstate s e)) (F: State_formula) s' e',
s<=s'/\ s'<=e' /\ e'<=e ->
s'<=(fst (option_free (Free_State F))) /\ (snd (option_free (Free_State F)))<=e' ->
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
      simpl. unfold q_trace.  rewrite  Ptrace_trace.
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

Import ParDensityO.
Local Open Scope nat_scope.
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
       exists x.  intuition. 
       apply Rle_trans with (Cmod (@trace (2^(e-s)) (@big_sum (Matrix (2^(e-s)) (2^(e-s))) _  f n))).
        repeat  rewrite big_sum_Cmod.
        apply big_sum_le. intros. 
        apply H in H5. destruct H5. 
        apply mixed_state_Cmod_1_aux in H5. lra.
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

Lemma d_par_trace_not_nil{s e:nat}: forall s' e' (mu: list (state s e)) (mu':list (state s' e')),
d_par_trace mu s' e'= mu'->
mu <> [] -> mu'<>[].
Proof. induction mu; intros. destruct H0. reflexivity.
       inversion_clear H. destruct a.  simpl.
       discriminate. 
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
   apply pow_gt_0. apply d_par_trace_not_nil with mu''.
   assumption. intro. assert(d_trace_aux mu'' =0%R).
   rewrite H6. reflexivity. 
   assert(d_trace_aux mu'' =  (s_trace (c,q))).
   apply QMeas_trace' with s0 e0 i. intuition.
   lia. apply WWF_qstate_to_WF_qstate.
   inversion_clear Hw. apply H8. assumption.
   assert(s_trace (c,q)>0)%R. unfold  s_trace.
   simpl. apply mixed_state_Cmod_1. inversion_clear Hw.
   apply H9. rewrite<- H8 in H9. rewrite H7 in H9.
   lra. lia. simpl. intros. apply mixed_super_ge_0; try lia.
   auto_wf. 
   apply Mixed_State_aux_to_Mix_State. inversion_clear Hw.
   apply H5. 
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
 apply pow_gt_0. apply d_par_trace_not_nil with mu''.
 assumption. intro. assert(d_trace_aux mu'' =0%R).
 rewrite H6. reflexivity. 
 assert(d_trace_aux mu'' =  (s_trace (c,q))).
 apply QMeas_trace' with s0 e0 i. intuition.
 lia. apply WWF_qstate_to_WF_qstate.
 inversion_clear Hw. apply H8. assumption.
 assert(s_trace (c,q)>0)%R. unfold  s_trace.
 simpl. apply mixed_state_Cmod_1. inversion_clear Hw.
 apply H9. rewrite<- H8 in H9. rewrite H7 in H9.
 lra. lia. simpl. intros.
  apply mixed_super_ge_0; try lia. auto_wf.  
   apply Mixed_State_aux_to_Mix_State. inversion_clear Hw.
   apply H5. 
apply IHmu. lia.  inversion_clear Hw. assumption.
assumption. 
inversion  H0; subst. intuition.
assumption. assumption.
destruct p. simpl. assumption.
 }  }
Admitted.


Lemma seman_eq_two'''{s e:nat}: forall F r c (q:qstate s e),
Considered_Formula (F) /\
(r <= e /\ snd (option_free (Free_State F)) <=r /\ fst (option_free (Free_State F)) < snd (option_free (Free_State F)))->
WF_qstate q->
State_eval F (c, q) -> 
exists 
(q1:qstate (fst (option_free (Free_State F))) (snd (option_free (Free_State F))))
(q2:qstate  (snd (option_free (Free_State F))) r), 
(q_combin' q1 q2 (@PMpar_trace s e q  (fst (option_free (Free_State F))) r)).
Proof. intros F r c q H Hw. intros. 
       assert(s<=fst (option_free (Free_State F))). 
       pose (State_eval_dom F c q H0). destruct o.
       rewrite H1 in *. simpl in *. lia. 
        apply H1.  
        remember ((snd (option_free (Free_State F)))) as x.
        remember ((fst (option_free (Free_State F)))) as s'.
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
(q_combin' q1 q2 (@PMpar_trace s e q l (snd (option_free (Free_State F))))).
Proof. intros F l c q H Hw. intros. 
        assert(snd (option_free (Free_State F))<=e). 
        pose (State_eval_dom F c q H0). destruct o.
        rewrite H1 in *. simpl in *. 
        subst. lia. apply H1.  
        remember ((fst (option_free (Free_State F)))) as x.
        remember ((snd (option_free (Free_State F)))) as e'.
        simpl.  
        remember ((PMpar_trace q l e')).
       assert(exists (q1:qstate l x) (q2: qstate x e'), 
       and (WF_qstate q1 /\ WF_qstate q2)
       (q0 = @kron (2^(x-l)) (2^(x-l)) (2^(e'-x))  (2^(e'-x)) q1 q2)).
       apply Odot_Sepear'''; try lia.  
       rewrite Heqq0. apply Mix_par_trace; try lia; try assumption.
       rewrite Heqq0. rewrite PMpar_trace_assoc; try lia. 
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
(dstate_Separ (d_par_trace mu l (snd (option_free (Free_State F)))) 
l (fst (option_free (Free_State F))) (fst (option_free (Free_State F))) (snd (option_free (Free_State F)))).
Proof. induction mu; intros. 
      simpl. intuition.
      destruct mu. 
      destruct a. 
      simpl.

      assert(exists (q1:qstate l (fst (option_free (Free_State F)))) 
      (q2:qstate (fst (option_free (Free_State F))) (snd (option_free (Free_State F)))), 
      (q_combin' q1 q2 (@PMpar_trace s e q l (snd (option_free (Free_State F)))))).
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
      (q_combin' q1 q2 (@PMpar_trace s e q l (snd (option_free (Free_State F)))))).
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
(dstate_Separ (d_par_trace mu  (fst (option_free (Free_State F))) r) 
(fst (option_free (Free_State F))) (snd (option_free (Free_State F))) (snd (option_free (Free_State F))) r).
Proof. induction mu; intros. 
      simpl. intuition.
      destruct mu. 
      destruct a. 
      simpl.

      assert(exists 
      (q1:qstate (fst (option_free (Free_State F))) (snd (option_free (Free_State F))))
      (q2:qstate  (snd (option_free (Free_State F))) r), 
      (q_combin' q1 q2 (@PMpar_trace s e q  (fst (option_free (Free_State F))) r))).
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
      (q_combin' q1 q2 (@PMpar_trace s e q  (fst (option_free (Free_State F))) r))).
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
      rewrite H. rewrite union_empty_refl. reflexivity.
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
 rewrite H. rewrite union_empty_refl. reflexivity.
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

Lemma rule_f_classic: forall   c s e (mu mu':list (cstate * qstate s e )) F,
(Considered_Formula F /\ fst (option_free (Free_State F)) < snd (option_free (Free_State F)))->
WF_dstate_aux mu ->
State_eval_dstate F mu->
ceval_single c mu mu'-> 
NSet.Equal (snd (MVar c)) NSet.empty ->
NSet.Equal (NSet.inter (fst (Free_state F)) (fst (MVar c))) (NSet.empty) ->
State_eval_dstate F mu'.
Proof. induction c. 
-intros. apply ceval_skip_1 in H2. subst. assumption.
-admit.
-induction mu; intros. destruct H1. destruct mu;inversion H2; subst.
 inversion_clear H10. simpl. econstructor.
 inversion_clear H1. 
 apply cstate_eq_F with sigma.
   simpl in H4. 
   unfold cstate_eq.
   intros. rewrite c_update_find_not.
   reflexivity.
   unfold not.
   intros. rewrite<-H7 in *.
   apply (In_inter_empty _ _ i) in H4.
   destruct H4. assumption. 
   apply NSet.add_1. reflexivity.
    assumption. 
   econstructor.
   apply d_seman_app_aux. 
    apply WF_state_dstate_aux.
   apply WF_state_eq with (sigma, rho).
   reflexivity. inversion_clear H0. assumption.
    apply WF_ceval with <{ i := a }> (p :: mu).
   inversion_clear H0. assumption.
   assumption. 
   simpl. econstructor.
   apply cstate_eq_F with sigma.
   simpl in H1. 
   unfold cstate_eq.
   intros. rewrite c_update_find_not.
   reflexivity. intro. rewrite H6 in *.
   apply (In_inter_empty _ _ j) in H4.
   destruct H4. assumption. 
   apply NSet.add_1. reflexivity. inversion_clear H1.
    assumption. econstructor.
apply IHmu. assumption. inversion_clear H0. assumption.
inversion_clear H1.
    assumption.
inversion H0; subst.   intuition.
assumption. assumption.
-admit.
-intros. simpl in H3. rewrite union_empty in H3.
 simpl in H4. rewrite inter_union_dist in H4.
 apply union_empty in H4. 
 apply ceval_seq_1 in H2. destruct H2.
 apply IHc2 with x; try assumption; try apply H2; try apply H3; try apply H4. 
 apply WF_ceval with c1 mu; try assumption; try apply H2. 
 apply IHc1 with mu; try assumption; try apply H2; try apply H3; try apply H4.
- induction mu; intros. destruct H1.
   inversion_clear H1. inversion_clear  H0.
   inversion H2; subst;
  destruct mu.
  simpl in *.  rewrite inter_union_dist in H4.
  apply union_empty in H3. apply union_empty in H4.
  inversion_clear H15; try rewrite map2_nil_r.
  apply IHc1 with [(sigma, rho)]; 
  try apply WF_state_dstate_aux; try assumption; try apply H3; try apply H4.
  econstructor. assumption. econstructor.
  apply d_seman_app_aux. apply WF_ceval with c1 [(sigma, rho)];
  try assumption.
  apply WF_state_dstate_aux; try assumption. 
  apply WF_ceval with  <{ if b then c1 else c2 end }> (p :: mu);
  try apply WF_state_dstate_aux; try assumption.
  simpl in *.  rewrite inter_union_dist in H4.
  apply union_empty in H3. apply union_empty in H4.
  apply IHc1 with [(sigma, rho)]; 
  try apply WF_state_dstate_aux; try assumption; try apply H3; try apply H4.
  econstructor. assumption. econstructor.
  apply IHmu; try assumption; try apply H3; try apply H4.

  simpl in *.  rewrite inter_union_dist in H4.
  apply union_empty in H3. apply union_empty in H4.
  inversion_clear H15; try rewrite map2_nil_r.
  apply IHc2 with [(sigma, rho)]; 
  try apply WF_state_dstate_aux; try assumption; try apply H3; try apply H4.
  econstructor. assumption. econstructor.
  apply d_seman_app_aux. apply WF_ceval with c2 [(sigma, rho)];
  try assumption.
  apply WF_state_dstate_aux; try assumption. 
  apply WF_ceval with  <{ if b then c1 else c2 end }> (p :: mu);
  try apply WF_state_dstate_aux; try assumption.
  simpl in *.  rewrite inter_union_dist in H4.
  apply union_empty in H3. apply union_empty in H4.
  apply IHc2 with [(sigma, rho)]; 
  try apply WF_state_dstate_aux; try assumption; try apply H3; try apply H4.
  econstructor. assumption. econstructor.
  apply IHmu; try assumption; try apply H3; try apply H4.

-admit.
-intros. simpl in H3.   
Admitted.

Lemma State_eval_dstate_dom{s e:nat}: forall (mu:list (cstate * qstate s e)) F, 
State_eval_dstate F mu->
Free_State F = None \/
s <=fst (option_free (Free_State F)) /\ fst (option_free (Free_State F)) < snd (option_free (Free_State F)) <= e.
Proof. induction mu; intros. destruct H. 
       inversion_clear H. destruct a.  
        apply State_eval_dom in H0.    assumption. 
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
       admit. 
       assert(s<e). lia.
Admitted.


Lemma ceval_single_dom{ s e:nat}: forall c (mu mu': list (cstate * qstate s e)) , 
ceval_single c mu mu' ->
mu <> [] ->
~NSet.Equal (snd (MVar c)) NSet.empty ->
s<=option_nat (NSet.min_elt (snd (MVar c)))
/\option_nat (NSet.max_elt (snd (MVar c))) < e .
Proof. induction c. intros  mu mu' H Hnil H0; intros.
simpl in *. try destruct H0; try reflexivity.
-admit.
-intros. try destruct H1; try reflexivity.
-intros. try destruct H1; try reflexivity.
-intros  mu mu' H Hnil H0; intros.
apply ceval_seq_1 in H; destruct H. 
simpl in H0. 
pose (min_union (snd (MVar c1)) (snd (MVar c2))).
destruct a.  destruct H2.
pose (max_union (snd (MVar c1)) (snd (MVar c2))).
destruct a. destruct H5. 
assert(NSet.Equal (snd (MVar c1)) NSet.empty \/ ~NSet.Equal (snd (MVar c1)) NSet.empty ).
apply Classical_Prop.classic. 
destruct H7. pose H7. apply H1 in e0.
apply H4 in H7. simpl. rewrite H7. rewrite e0.
apply IHc2 with x mu'. apply H. admit.
admit. 
assert(NSet.Equal (snd (MVar c2)) NSet.empty \/ ~NSet.Equal (snd (MVar c2)) NSet.empty ).
apply Classical_Prop.classic. destruct H8.
pose H8. apply H2 in e0. apply H5 in H8.
simpl. rewrite H8. rewrite e0. 
apply IHc1 with mu x. apply H. assumption.
assumption. 
assert( x <> []).  admit.  destruct H.
pose H7.
pose H7. apply H3 in n ; try assumption.  
apply H6 in n0; try assumption. simpl.
pose (IHc1 mu x H Hnil H7). pose (IHc2 x mu' H10 H9 H8).
rewrite n0.
rewrite n. 
split. apply min_glb. apply a. apply a0.
apply max_lub_lt. apply a. apply a0.

-induction mu; intros mu' H Hnil H0; intros.
 inversion H; subst. destruct Hnil. reflexivity.
 inversion H; subst.  
 simpl in *.  
 pose (min_union (snd (MVar c1)) (snd (MVar c2))).
destruct a.  destruct H2.
pose (max_union (snd (MVar c1)) (snd (MVar c2))).
destruct a. destruct H5. 
assert(NSet.Equal (snd (MVar c1)) NSet.empty \/ ~NSet.Equal (snd (MVar c1)) NSet.empty ).
apply Classical_Prop.classic. 
destruct H10. pose H10. apply H1 in e0.
apply H4 in H10. rewrite H10. rewrite e0.
admit. admit.
admit. admit.
-intros  mu mu' H Hnil H0; intros. inversion H; subst. destruct Hnil. reflexivity.
 simpl. pose  (Qsys_to_Set_min_max s0 e0).
 destruct a. lia. rewrite H1. rewrite H2.
 lia. 
-intros  mu mu' H Hnil H0; intros. inversion H; subst. destruct Hnil. reflexivity.
simpl. pose  (Qsys_to_Set_min_max s0 e0).
destruct a. lia. rewrite H1. rewrite H2.
lia.
intros  mu mu' H Hnil H0; intros. inversion H; subst. destruct Hnil. reflexivity.
 simpl. pose  (Qsys_to_Set_min_max s e).
 destruct a. lia. admit.
-intros  mu mu' H Hnil H0; intros. inversion H; subst. destruct Hnil. reflexivity.
simpl. pose  (Qsys_to_Set_min_max s0 e0).
destruct a. lia. rewrite H1. rewrite H2.
lia.
Admitted. 



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
    intros.  pose (@ceval_single_dom s e c mu mu').
    destruct a. assumption. destruct mu. destruct H1.
    discriminate. assumption.  
    destruct H5.  
    assert(s <= option_nat (NSet.min_elt (snd (MVar c))) /\
    option_nat (NSet.min_elt (snd (MVar c))) <=
    fst (option_free (Free_State F)) /\
    fst (option_free (Free_State F)) < snd (option_free (Free_State F)) /\ snd (option_free (Free_State F)) <= e).
    split. assumption. 
    split. apply le_trans with (option_nat  (NSet.max_elt (snd (MVar c)))).
    apply min_le_max. lia.  split. apply H.
    apply State_eval_dstate_dom in H1. destruct H1. rewrite H1 in *.
    simpl in *.  lia.
    apply H1.  
    rewrite (State_dstate_free_eval _ _ (fst (option_free (Free_State F)))
    (snd (option_free (Free_State F)))); try lia. 
    rewrite <-(d_par_trace_assoc   mu' 
    (option_nat (NSet.min_elt (snd (MVar c))))
    (snd (option_free (Free_State F)))); try lia.   
    remember ((d_par_trace mu'
    (option_nat (NSet.min_elt (snd (MVar c))))
    (snd (option_free (Free_State F))))).
    remember ((d_par_trace mu
    (option_nat (NSet.min_elt (snd (MVar c))))
    (snd (option_free (Free_State F))))).
    apply r4 with c (option_nat (NSet.min_elt (snd (MVar c))))
    (fst (option_free (Free_State F))) l0; try assumption; try lia. 
    rewrite Heql0. apply WF_d_par_trace; try lia; try assumption. 
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
    rewrite Heql0. rewrite d_par_trace_assoc; try lia. 
    apply State_dstate_free_eval; try assumption; try lia. 
     apply WF_Mixed_dstate; assumption.
    apply WF_Mixed_dstate.
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
    rewrite <-(d_par_trace_assoc   mu' 
    (fst (option_free (Free_State F))) (option_nat (NSet.max_elt (snd (MVar c)))+ 1)); try lia.   
    remember ( (d_par_trace mu' (fst (option_free (Free_State F)))
    (option_nat (NSet.max_elt (snd (MVar c)))+ 1))).
    remember ((d_par_trace mu
    (fst (option_free (Free_State F)))
    (option_nat (NSet.max_elt (snd (MVar c))) + 1))).
    apply r4' with c (snd (option_free (Free_State F)))
    (option_nat (NSet.max_elt (snd (MVar c))) + 1) l0; try assumption; try lia. 
    rewrite Heql0. apply WF_d_par_trace; try lia; try assumption.  
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
    rewrite Heql0. rewrite d_par_trace_assoc; try lia. 
    apply State_dstate_free_eval; try assumption; try lia. 
     apply WF_Mixed_dstate; assumption.
    apply WF_Mixed_dstate.
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




Lemma Pure_eval''{s e:nat}:forall  (F: State_formula) c0 c1 (q q0: qstate s e),
(Free_State F = None)->
cstate_eq c0 c1 (fst (Free_state F))->
State_eval F (c0, q) -> 
State_eval F (c1, q0).
Proof. induction F;   intros.
        eapply cstate_eq_P. apply H0.
        apply state_eq_Pure with (c0,q).
        reflexivity. apply H1.
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
Qed.
 


Lemma Pure_eval_preserve{s e:nat}:forall  c (mu1 mu2: list (cstate* qstate s e)) (F: State_formula) ,
( (Free_State F)= None)->
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
 inversion_clear H0.  assumption.  econstructor.
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
   apply pow_gt_0.  
   intro. assert(d_trace_aux mu'' =0%R).
   rewrite H. reflexivity. 
   assert(d_trace_aux mu'' =  (s_trace (c,q))).
   apply QMeas_trace' with s0 e0 i. intuition.
   lia. apply WWF_qstate_to_WF_qstate.
   inversion_clear Hw. apply H2. assumption.
   assert(s_trace (c,q)>0)%R. unfold  s_trace.
   simpl. apply mixed_state_Cmod_1. inversion_clear Hw.
   apply H3. rewrite<- H2 in H3. rewrite H1 in H3.
   lra. 
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
 apply pow_gt_0. 
 intro. assert(d_trace_aux mu'' =0%R).
   rewrite H. reflexivity. 
   assert(d_trace_aux mu'' =  (s_trace (c,q))).
   apply QMeas_trace' with s0 e0 i. intuition.
   lia. apply WWF_qstate_to_WF_qstate.
   inversion_clear Hw. apply H2. assumption.
   assert(s_trace (c,q)>0)%R. unfold  s_trace.
   simpl. apply mixed_state_Cmod_1. inversion_clear Hw.
   apply H3. rewrite<- H2 in H3. rewrite H1 in H3.
   lra. 
apply IHmu1. assumption.  inversion_clear Hw. assumption.
inversion_clear Hw. assumption.
assumption.
inversion_clear H0. assumption. 
 }  }
Admitted.


Theorem rule_qframe: forall (F1 F2 F3: State_formula) c,
Considered_Formula F3 -> 
({{F1}} c {{F2}}) 
/\ (NSet.Equal (NSet.inter (fst (Free_state F3)) (fst (MVar c))) (NSet.empty) )
/\ ((option_nat (NSet.max_elt (snd (MVar c)))) <  fst (option_free (Free_State F3)) \/
snd (option_free (Free_State F3)) <= ((option_nat (NSet.min_elt (snd (MVar c))))))
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
        destruct (option_edc (Free_State F3) None).
        apply Pure_eval_preserve with c mu;
        try assumption.  apply H2.
        assert(NSet.Equal (snd (MVar c)) NSet.empty \/ ~NSet.Equal (snd (MVar c)) NSet.empty ).
apply Classical_Prop.classic.  
destruct H11. apply rule_f_classic with c mu; try assumption.
split. assumption. 
apply State_eval_dstate_dom in H8. destruct H8. destruct H10.
assumption.
lia. apply H2.
        apply rule_f  with  c mu; try assumption.
        split. assumption. 
        apply State_eval_dstate_dom in H8. destruct H8. destruct H10.
assumption.
lia. apply H2. apply H2.  
         admit.
Admitted.


Theorem rule_qframe': forall (F1 F2 F3: State_formula) c,
Considered_Formula F3 ->
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