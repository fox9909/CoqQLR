Require Import Lists.List.
Require Import Reals.
Require Import Coquelicot.Complex.
Require Import Strings.String.

From Quan Require Import Matrix.
From Quan Require Import Quantum.
From Quan Require Import Basic.
From Quan Require Import ParDensityO.
From Quan Require Import QState.
From Quan Require Import Par_trace.
From Quan Require Import QIMP_L.
From Quan Require Import Ceval_Linear.
From Quan Require Import QAssert.
From Quan Require Import QRule_E_L.
From Quan Require Import QRule_Q_L.
From Quan Require Import QRule_I_L.
From Quan Require Import QSepar.
From Quan Require Import QRule_QFrame.
From Quan Require Import Forall_two.
From Quan Require Import add.
From Quan Require Import HHL.
From Quan Require Import OF.

Local Open Scope com_scope.
Local Open Scope assert_scope.
Local Open Scope nat_scope.
Local Open Scope matrix_scope.
Local Open Scope rule_scope.  


Module Shor (p:Param).

Module OF:=OF(p).

Definition x := p.x.
Definition N := p.N.
Definition z := p.z.
Definition r := p.r.

Parameter random: nat -> nat -> nat.
Hypothesis Hran: forall a b, (a <= random a b) /\ (random a b <= b).

Lemma bool_true: forall (a b:nat),
a=b-> (a=? b =true).
Proof. induction a; induction b; intros.
       simpl. intuition. intuition. intuition.
       simpl. injection H. intuition. 
Qed.

Theorem rule_Clet: forall (a b:nat),
{{BTrue}}
(Clet a b)
{{ BEq (ANum a) (ANum b) }} .
Proof. unfold hoare_triple. intros.
       destruct mu as [mu IHmu].
       destruct mu' as [mu' IHmu'].
       rewrite sat_Assert_to_State in *.
       inversion_clear H. simpl in *.
       inversion H3; subst.
       inversion_clear H0. simpl in H4. 
       destruct H4. unfold x0.
       rewrite seman_find. split.
       assumption. split. discriminate.
       intros. simpl.
       rewrite bool_true. intuition.
       reflexivity.
Qed.

Definition y:nat := 3.


Definition Shor :=
  let N2 := (N mod 2) in
  let b2 (x:nat) :=(BAnd (BEq (AMod z ' 2) 0 )  (BNeq (((AMod (APow x (ADiv z ' 2)) N))) 1)) in
  let b3 (x:nat) :=(BAnd (BNeq (AGcd  (AMinus (APow x (ADiv z ' 2)) 1) N) N)  
                          (BNeq (AGcd (AMinus (APow x (ADiv z ' 2)) 1) N) 1)  ) in
  <{  if  (BEq N2 0) then
           y:= 2
      else  
           (Clet x ((random 2 (N-1))));
           y:= (AGcd x N);
           while  (BEq y ' 1) do 
                   OF.OF ;
                  if (b2 x) then
                      if  (b3 x) then 
                          y:= (AGcd  (AMinus (APow x (ADiv z ' 2)) 1) N)
                      else 
                          y:= (AGcd (APlus (APow x (ADiv z ' 2)) 1) N )
                      end 
                  else 
                       (Clet x ((random 2 (N-1))));
                       y := (AGcd x N)
                  end 
            end 
      end 
  }>.

  Import Sorted.



Theorem rule_qframe'': forall (P1 P2 P3: Pure_formula) c,
         ({{P1}} c {{P2}}) /\  (NSet.Equal (NSet.inter (fst (Free_state P3)) (fst (MVar c))) NSet.empty) 
         ->  {{P3 /\p P1}} c {{P3 /\p P2}}.
Proof. 
intros. eapply rule_conseq; try apply rule_OdotO.
eapply rule_qframe'. simpl. auto. 
split. apply H. split. apply H.
simpl. right. lia. 
Qed.

Theorem rule_conseq_r' : forall (P Q Q' : Assertion) c,
{{P}} c {{Q'}} ->
(Q'->> Q) ->

{{P}} c {{Q}}.
Proof. intros. eapply rule_conseq. apply H. 
apply implies_refl. assumption. Qed.   


Definition Cop (N:nat) := exists a, 2<=a /\ a<=(N-1) /\ Nat.modulo N a =0.


Definition F_1(y x N:nat): Pure_formula := ((BEq y ' (((Nat.gcd (x ^ (r / 2) - 1) N)))) 
/\p (BNeq y ' 1) /\p (BNeq y ' N)).

Definition F_2(y x N:nat): Pure_formula :=  ((BEq y ' (((Nat.gcd (x ^ (r / 2) + 1) N)))) 
/\p (BNeq y ' 1) /\p (BNeq y ' N)).

Definition F_3(y x N:nat): Pure_formula := ((BEq y ' (Nat.gcd x N)) /\p (BNeq y ' N)) .


Definition Big_hypose (x z N:nat): Pure_formula:= 
  (BAnd (BNeq (AGcd  (AMinus (APow x (ADiv z ' 2)) 1) N) N)  
  (BNeq (AGcd (AMinus (APow x (ADiv z ' 2)) 1) N) 1)) \/p 
  (BAnd (BNeq (AGcd  (APlus (APow x (ADiv z ' 2)) 1) N) N)  
  (BNeq (AGcd (APlus (APow x (ADiv z ' 2)) 1) N) 1)).



Definition a :=4 .

Lemma rule_AndT: forall (F:State_formula),
F ->> F /\s BTrue .
Proof. rule_solve. 
  
Qed.

Lemma BAnd_split: forall (b1 b2:bool),
(if (b1&&b2) then True else False) ->
((if (b1) then True else False) /\
(if (b2) then True else False)).
Proof. intros. destruct (b1); destruct b2; simpl in *; try destruct H. intuition. 
Qed.


Ltac seman_sovle:=
  unfold assert_implies;
  intros; 
  rewrite sat_Assert_to_State in *;
   rewrite seman_find in *;
   try match goal with 
   H: WF_dstate ?mu /\ StateMap.this ?mu <> [] /\ 
        (forall x:cstate, d_find x ?mu <> Zero ->?Q)
   |-_ => destruct H as [H11 H12]; destruct H12 as [H21 H22];
   split; try assumption; split; try assumption; intros
   end;
   try  match goal with 
   H1:  forall x:cstate, d_find x ?mu <> Zero ->?Q,
   H2: d_find ?x ?mu <> Zero
   |- _ => apply H1 in H2; clear H1
   end;
   unfold State_eval in *;
   try repeat match goal with 
  H: Pure_eval (?P /\p ?Q) ?st |-_ => destruct H
  end;
  try repeat match goal with 
  H: _ |- Pure_eval (?P /\p ?Q) ?st => try split end;
  try assumption.

Ltac Pure_eval_solve:=
  try unfold F_1 in *; try unfold F_2 in * ; try unfold F_3 in *;
  try repeat match goal with 
  H: Pure_eval (?P \/p ?Q) ?st |-_ => destruct H
  end;
  try repeat match goal with 
  H: Pure_eval (?P /\p ?Q) ?st |-_ => destruct H
  end; try assumption;
  try repeat match goal with 
  H: _ |- Pure_eval (PAssn ?y ?x (?P /\p ?Q)) ?st => try split end;
  try assumption;
  try repeat match goal with 
  H: _ |- Pure_eval (?P /\p ?Q) ?st => try split end;
  try assumption.

Ltac classic_slove_aux:=
  unfold Pure_eval in *;
  unfold beval in *; try unfold s_update_cstate;unfold aeval in *;
  unfold fst in *; try rewrite c_update_find_eq;
  try match goal with 
  H1: if (¬ c_find ?y ?x0 =? ?x) then True else False,
  H: if (c_find ?y ?x0 =? ?x) then True else False 
  |- _ => bdestruct (c_find y x0 =? x);
  simpl in H1; destruct H1  end;
  try repeat match goal with 
  H : if (?y =? ?x) then True else False 
  |- _ => bdestruct (y =? x) end;
  try repeat match goal with 
  H: if (?b1 && ?b2) then True else False 
  |- _ => apply BAnd_split in H; destruct H; try assumption end;
  try repeat match goal with 
  H': c_find ?v2 ?x = ?y 
  |-_=> try rewrite H'
  end;
  try match goal with 
  H:_ |- if ?y =? ?y  then True else False => assert(y=y); try reflexivity
  end;
  try match goal with 
  H: ?y = ?y |- if ?y =? ?y  then True else False =>
  rewrite <-Nat.eqb_eq in H; rewrite H; simpl; auto end;
  try repeat match goal with 
H': c_find ?v2 ?x = ?y 
|-_=> try rewrite <-H'; rewrite<- Nat.eqb_eq  in H'
end;
try match goal with 
 H:_ |- if ?y =? ?y  then True else False => assert(y=y); try reflexivity
end;
try match goal with 
H: ?y = ?y |- if ?y =? ?y  then True else False =>
rewrite <-Nat.eqb_eq in H; rewrite H; simpl; auto end;
try match goal with 
H: False |-_ => destruct H end.

Ltac classic_slove_1:=
       seman_sovle; classic_slove_aux.

Ltac classic_slove_2:=
  seman_sovle; 
  Pure_eval_solve;
  classic_slove_aux.


Theorem Shor_correctness:
{{(Pre Cop N)}} Shor  {{  (BEq ((AMod N y ')) 0) /\p (BNeq y ' 1) /\p (BNeq y ' (N))}} .
Proof. unfold Shor. 
       eapply rule_cond_classic. split.
       {eapply rule_conseq_l with (((Pre Cop N) /\p (BEq ((N mod 2)) 0)) /\p (PAssn y 2 (BEq y ' 2))).
       implies_trans_solve 1 SAnd_PAnd_eq.
        apply rule_ConjE. split. apply rule_PT. apply Assn_true_P. simpl. unfold not. apply In_empty.

       eapply rule_conseq_r'.
       eapply rule_qframe''.
       split.  apply QRule_I_L.rule_assgn.
       
       simpl. apply inter_empty. left.
       apply union_empty; split; try reflexivity;
      apply union_empty; split; try reflexivity.
    
        }
       eapply rule_seq with ((Pre Cop N) /\p  (BNot (BEq (N mod 2) (0))) 
       /\p ((  (BLe (2) x) /\p (BLe (x) ((ANum (N-1))))))). 
          {eapply rule_conseq_l. apply rule_AndT.
          eapply rule_conseq_l. apply SAnd_PAnd_eq.
          eapply rule_conseq_r'.
          eapply rule_qframe''. 
          split.   eapply rule_Clet. 
          
          simpl. apply inter_empty. left.
          apply union_empty; split; try reflexivity;
         apply union_empty; split; try reflexivity.
         
          implies_trans_solve 0 SAnd_PAnd_eq. implies_trans_solve 1 SAnd_PAnd_eq. 
          apply rule_CconjCon. apply implies_refl.
        classic_slove_1;
        pose (Hran 2 (N-1)); try rewrite <-H0 in a0; destruct a0;
        rewrite <-Nat.leb_le in *; try rewrite H1; try rewrite H2; auto. 
        }
          eapply rule_seq with (((Pre Cop N) /\p  (BNot (BEq (N mod 2) 0)) /\p ( (BLe 2 x ) /\p (BLe x ((N-1)))))
          /\p ((F_1 y x N) \/p (F_2 y x N) \/p F_3 y x N)).
          {eapply rule_conseq_l with ((Pre Cop N) /\p  (BNot (BEq (N mod 2) 0)) /\p (( (BLe 2 x ) /\p (BLe x ((N-1))))) 
          /\p (PAssn y ((AGcd x N)) (BEq y ' ((AGcd x N))))).
          implies_trans_solve 1 SAnd_PAnd_eq.
          apply rule_ConjE. split. apply rule_PT. apply Assn_true_P.

          simpl;intro; try repeat match goal with 
          H:NSet.In ?b (NSet.union ?c1 ?c2)|-_ => apply NSet.union_1 in H;
          destruct H end;
          try match goal with 
          H:NSet.In ?b (NSet.add ?a (NSet.empty)) |-_ => apply NSet.add_3 in H;
          try discriminate end;
          try match goal with 
          H:NSet.In ?b NSet.empty |- _ => eapply In_empty; apply H end.
          eapply rule_conseq_r'.
          eapply rule_qframe''.
          split.  apply QRule_I_L.rule_assgn.
          
          simpl. apply inter_empty. left.
          apply union_empty; split; try reflexivity;
         try apply union_empty; try split; try reflexivity;
         try apply union_empty; try split; try reflexivity.
          }
          eapply rule_conseq_r'.
          apply rule_while_classic.
           eapply rule_seq with (((Pre Cop N)/\p  (BNot (BEq (N mod 2) 0)) /\p ( (BLe 2 x ) /\p (BLe x (N-1))))
           /\p (BEq z ' r)). 
           eapply rule_conseq_l with 
           ((((Pre Cop N) /\p  (BNot (BEq (N mod 2) 0)) /\p ( (BLe 2 x ) /\p (BLe x  (N-1))))
           /\p (BEq ((Nat.gcd x N)) 1))).
           classic_slove_2.


           
        
           apply rule_qframe''. 
           split.  
           apply OF.OF_correctness. 
           simpl. apply inter_empty. left.
          apply union_empty; split; try reflexivity;
         try apply union_empty; try split; try reflexivity;
         try apply union_empty; try split; try reflexivity.
           apply rule_cond_classic. split.
           eapply rule_conseq_l with ((((Pre Cop N) /\p (BNot (BEq (( (N mod 2))) 0)) /\p ((BLe 2 x ) /\p (BLe x ((N-1)))))
           /\p ( BEq z ' r) /\p (Big_hypose x z N))). 
           implies_trans_solve 1 SAnd_PAnd_eq.
           implies_trans_solve 0 SAnd_PAnd_eq.
           apply rule_CconjCon; try apply implies_refl.
           (*这是那个大假设*) 
            admit.
           apply rule_cond_classic. split.
           eapply rule_conseq_l with 
           ( (((Pre Cop N) /\p  (BNot (BEq ((ANum (N mod 2))) 0)) /\p ( (BLe 2 x ) /\p (BLe x ( (N-1))))) 
           )/\p (
           (PAssn y (AGcd (AMinus (APow x (ADiv z ' 2)) 1) N) ((F_1 y x N) /\p (BEq y ' ( (Nat.gcd ((x^ (r / 2)) -1) N))))))).
            { classic_slove_2.  

          
             } 
            eapply rule_conseq_r'.
           

          eapply rule_qframe''.
          split.  apply QRule_I_L.rule_assgn.
         
          
          simpl. apply inter_empty. left.
          apply union_empty; split; try reflexivity;
         try apply union_empty; try split; try reflexivity;
         try apply union_empty; try split; try reflexivity;
         try apply union_empty; try split; try reflexivity.
         try apply union_empty; try split; try reflexivity.
          
          intros. unfold assert_implies.
          intros.  rewrite sat_Assert_to_State in *.
          rewrite seman_find in *.
           split.  intuition.
           split. intuition. 
           intros. econstructor. apply H. assumption.
           try 
         left. left.
            apply H. assumption.

          eapply rule_conseq_l with 
          ( ((Pre Cop N) /\p  (BNot (BEq ((ANum (N mod 2))) 0)) /\p ( (BLe 2 x ) /\p (BLe x (ANum (N-1)))) ) 
          /\p (PAssn y (AGcd (APlus (APow x (ADiv z ' 2)) 1) N) ((F_2 y x N) /\p BEq y ' (ANum (Nat.gcd (x^ (r / 2) + 1) N))))).
          unfold Big_hypose.
          classic_slove_2;
          bdestruct ((Nat.gcd (x ^ (c_find z x0 / 2) - 1) N =? N) ); simpl in H1;
          destruct H1;
          bdestruct (Nat.gcd (x ^ (c_find z x0 / 2) - 1) N =? 1); simpl in H7;
          destruct H7; simpl in H0; destruct H0.

         eapply rule_conseq_r'.
         eapply rule_qframe''.
         split.  apply QRule_I_L.rule_assgn.
         

         simpl. apply inter_empty. left.
         apply union_empty; split; try reflexivity;
        try apply union_empty; try split; try reflexivity;
        try apply union_empty; try split; try reflexivity;
        try apply union_empty; try split; try reflexivity.


         intros. unfold assert_implies.
         intros.  rewrite sat_Assert_to_State in *.
         rewrite seman_find in *.
          split.  intuition.
          split. intuition. 
          intros. econstructor. apply H. assumption.
           unfold State_eval.  left. right.
           apply H. assumption.
         eapply rule_seq with (((Pre Cop N) /\p  (BNot (BEq ((ANum (N mod 2))) (0)))) 
       /\p (( (BLe (2) x) /\p (BLe (x) ((ANum (N-1))))))). 
          {eapply rule_conseq_l. apply rule_AndT.
          eapply rule_conseq_l. apply SAnd_PAnd_eq.
          eapply rule_conseq_r'.  
          eapply rule_qframe''. 
          split.   eapply rule_Clet. 
          
          simpl. apply inter_empty. right.
         reflexivity.
          classic_slove_1.
        }
        {eapply rule_conseq_l with ((((Pre Cop N) /\p  (BNot (BEq ((ANum ((N mod 2)))) 0)) /\p (( (BLe 2 x )/\p (BLe x (ANum (N-1))))))) 
        /\p PAssn y ((AGcd x N)) (BEq y ' ((AGcd x N)))).
        implies_trans_solve 1 SAnd_PAnd_eq.
        apply rule_ConjE; split. apply rule_PT. apply Assn_true_P.
       

        simpl;intro; try repeat match goal with 
H:NSet.In ?b (NSet.union ?c1 ?c2)|-_ => apply NSet.union_1 in H;
destruct H end;
try match goal with 
H:NSet.In ?b (NSet.add ?a (NSet.empty)) |-_ => apply NSet.add_3 in H;
try discriminate end;
try match goal with 
H:NSet.In ?b NSet.empty |- _ => eapply In_empty; apply H end.
          eapply rule_conseq_r'.
          eapply rule_qframe''.
          split.  apply QRule_I_L.rule_assgn. 

          simpl. apply inter_empty. left.
          apply union_empty; split; try reflexivity;
         try apply union_empty; try split; try reflexivity;
         try apply union_empty; try split; try reflexivity;
         try apply union_empty; try split; try reflexivity.


         seman_sovle. right. unfold F_3. split; try assumption.
         classic_slove_aux. apply Nat.eqb_eq in H4.
         rewrite H4. assert( Nat.gcd x N < N). 
          admit.
          }
          
       classic_slove_2; try rewrite Nat.eqb_eq in H7; try
       rewrite H7.
          admit. admit. try rewrite Nat.eqb_eq in H6. rewrite H6.
            admit.


Admitted.

End Shor.
