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
Hypothesis Hran: forall a b, (a <=? random a b) && (random a b <=? b)=true.

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


Theorem rule_while_classic: forall F (b:bexp) (c:com),
         {{F /\p b}} c {{ F}}
      -> {{F}}
         while b do c end
         {{ (F /\p (BNot b)) }}.
Proof. Admitted.

Theorem rule_cond_classic: forall (P1 P2: Pure_formula) (c1 c2:com) (b:bexp),
        ({{P1 /\p (b)}} c1 {{P2 }} /\ {{P1 /\p ((BNot b) )}} c2 {{P2 }})
     -> ({{P1 }}
        if b then c1 else c2 end
        {{P2}}).
Proof. Admitted.

Theorem rule_qframe'': forall (P1 P2 P3: Pure_formula) c,
         ({{P1}} c {{P2}}) /\  (NSet.inter (fst (Free_state P3)) (fst (MVar c)) =NSet.empty) 
         /\ (NSet.Equal (NSet.inter (snd (Free_state P3)) (snd (MVar c))) NSet.empty) 
         ->  {{P3 /\p P1}} c {{P3 /\p P2}}. Admitted.

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

Definition a :=4 .

Lemma rule_AndT: forall (F:State_formula),
F ->> F /\s BTrue .
Proof. rule_solve. 
  
Qed.


Ltac classic_slove_aux:=
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
   |- _ => apply H1 in H2
   end;
   unfold State_eval in *;
   unfold Pure_eval in *;
   unfold beval in *;
   try repeat match goal with 
   H :?P /\ ?Q |- _  => destruct H end;
   try repeat match goal with 
   H: _ |- ?P1 /\ ?P2 => try split end;
   try assumption;
   try repeat match goal with 
   H : if (aeval (?x, d_find ?x ?mu) ?v ' =? aeval (?x, d_find ?x ?mu) ?y)
       then True else False 
   |- _ => bdestruct (aeval (x, d_find x mu) v '=? aeval (x, d_find x mu) y) end;
   try unfold s_update_cstate; try unfold aeval in *;
   try unfold fst in *; try rewrite c_update_find_eq;  
   try repeat match goal with 
   H': c_find ?v2 ?x = ?y 
   |-_=> rewrite H'
   end; try match goal with 
   H: False |-_ => destruct H end.


Theorem Shor_correctness:
{{(Pre Cop N)}} Shor  {{  (BEq ((AMod N y ')) 0) /\p (BNeq y 
 1) /\p (BNeq y ' (N))}} .
Proof. unfold Shor. 
       eapply rule_cond_classic. split.
       {eapply rule_conseq_l with (((Pre Cop N) /\p (BEq ((N mod 2)) 0)) /\p (PAssn y 2 (BEq y ' 2))).
       implies_trans_solve 1 SAnd_PAnd_eq.
        apply rule_ConjE. split. apply rule_PT. apply Assn_true_P. simpl. unfold not. apply In_empty.

       eapply rule_conseq_r'.
       eapply rule_qframe''.
       split.  apply QRule_I_L.rule_assgn. simpl.  admit.
        }
       eapply rule_seq with ((Pre Cop N) /\p  (BNot (BEq (N mod 2) (0))) 
       /\p (( BAnd (BLe (2) x) (BLe (x) ((ANum (N-1))))))). 
          {eapply rule_conseq_l. apply rule_AndT.
          eapply rule_conseq_l. apply SAnd_PAnd_eq.
          eapply rule_conseq_r'.
          eapply rule_qframe''. 
          split.   eapply rule_Clet. admit.
          implies_trans_solve 0 SAnd_PAnd_eq. implies_trans_solve 1 SAnd_PAnd_eq. 
          apply rule_CconjCon. apply implies_refl.
         
          classic_slove_aux. 
        bdestruct (x =? random 2 (N - 1)).
        rewrite H0. 
        rewrite Hran. intuition. destruct H. 
        }
          eapply rule_seq with (((Pre Cop N) /\p  (BNot (BEq (N mod 2) 0)) /\p (BAnd (BLe 2 x ) (BLe x ((N-1)))))
          /\p ((F_1 y x N) \/p (F_2 y x N) \/p F_3 y x N)).
          {eapply rule_conseq_l with ((Pre Cop N) /\p  (BNot (BEq (N mod 2) 0)) /\p ((BAnd (BLe 2 x ) (BLe x ((N-1))))) 
          /\p (PAssn y ((AGcd x N)) (BEq y ' ((AGcd x N))))).
          implies_trans_solve 1 SAnd_PAnd_eq.
          apply rule_ConjE. split. apply rule_PT. apply Assn_true_P. simpl. unfold not. admit.
          eapply rule_conseq_r'.
          eapply rule_qframe''.
          split.  apply QRule_I_L.rule_assgn.  admit.
          }
          eapply rule_conseq_r'.
          apply rule_while_classic.
           eapply rule_seq with (((Pre Cop N)/\p  (BNot (BEq (N mod 2) 0)) /\p (BAnd (BLe 2 x ) (BLe x (N-1))))
           /\p (BEq z ' r)). 
           eapply rule_conseq_l with 
           ((((Pre Cop N) /\p  (BNot (BEq (N mod 2) 0)) /\p (BAnd (BLe 2 x ) (BLe x  (N-1))))
           /\p (BEq ((Nat.gcd x N)) 1))). 
           intros. unfold assert_implies.
          intros.  rewrite sat_Assert_to_State in *.
          rewrite seman_find in *.
          split.  intuition.
          split. intuition.
          intros. split.  
          split. apply H. assumption. 
         apply H. assumption. destruct H. destruct H1. 
         apply H2 in H0. destruct H0. destruct H0.
          admit.
           apply rule_qframe''. 
           split.  
           apply OF.OF_correctness.   admit.
           apply rule_cond_classic. split.
           eapply rule_conseq_l with ((((Pre Cop N) /\p (BNot (BEq (( (N mod 2))) 0)) /\p (BAnd (BLe 2 x ) (BLe x ((N-1)))))
           /\p ( BEq z ' r) /\p ( (F_1 y x N) \/p (F_2 y x N)))).
           (*这是那个大假设*) 
            admit.
           apply rule_cond_classic. split.
           eapply rule_conseq_l with 
           ( (((Pre Cop N) /\p  (BNot (BEq ((ANum (N mod 2))) 0)) /\p (BAnd (BLe 2 x ) (BLe x ( (N-1))))) 
           /\p ( (F_1 y x N) \/p (F_2 y x N))) /\p 
           (PAssn y (AGcd (AMinus (APow x (ADiv z ' 2)) 1) N) (BEq y ' ( (Nat.gcd ((x^ (r / 2)) -1) N))))).
            { classic_slove_aux.  
               admit. 
             } 
            eapply rule_conseq_r'.
          eapply rule_qframe''.
          split.  apply QRule_I_L.rule_assgn.
          admit. 
          intros. unfold assert_implies.
          intros.  rewrite sat_Assert_to_State in *.
          rewrite seman_find in *.
           split.  intuition.
           split. intuition. 
           intros. econstructor. apply H. assumption.
            unfold State_eval. unfold Pure_eval. left.
            apply H. assumption.

          eapply rule_conseq_l with 
          ( ((Pre Cop N) /\p  (BNot (BEq ((ANum (N mod 2))) 0)) /\p (BAnd (BLe 2 x ) (BLe x (ANum (N-1)))) /\p (F_1 y x N \/p F_2 y x N)) 
          /\p (PAssn y (AGcd (APlus (APow x (ADiv z ' 2)) 1) N) (BEq y ' (ANum (Nat.gcd (x^ (r / 2) + 1) N))))).
          classic_slove_aux.  
          admit. 
         eapply rule_conseq_r'.
         eapply rule_qframe''.
         split.  apply QRule_I_L.rule_assgn.
         admit.
         intros. unfold assert_implies.
         intros.  rewrite sat_Assert_to_State in *.
         rewrite seman_find in *.
          split.  intuition.
          split. intuition. 
          intros. econstructor. apply H. assumption.
           unfold State_eval.  left.
           apply H. assumption.
         eapply rule_seq with (((Pre Cop N) /\p  (BNot (BEq ((ANum (N mod 2))) (0)))) 
       /\p ((BAnd (BLe (2) x)  (BLe (x) ((ANum (N-1))))))). 
          {eapply rule_conseq_l. apply rule_AndT.
          eapply rule_conseq_l. apply SAnd_PAnd_eq.
          eapply rule_conseq_r'.  
          eapply rule_qframe''. 
          split.   eapply rule_Clet.  admit.
          classic_slove_aux.
        }
        {eapply rule_conseq_l with ((((Pre Cop N) /\p  (BNot (BEq ((ANum ((N mod 2)))) 0)) /\p ((BAnd (BLe 2 x ) (BLe x (ANum (N-1))))))) 
        /\p PAssn y ((AGcd x N)) (BEq y ' ((AGcd x N)))).
          intros. unfold assert_implies.
          intros.  rewrite sat_Assert_to_State in *.
          rewrite seman_find in *.
          split.  intuition.
          split. intuition.
          intros. split.  
          split. apply H. assumption.
         apply H. assumption.
          unfold State_eval. unfold Pure_eval.
          unfold s_update_cstate.  
          unfold beval. unfold aeval. unfold fst.
          rewrite c_update_find_eq.
          induction (Nat.gcd x N);
         simpl; intuition. 
          eapply rule_conseq_r'.
          eapply rule_qframe''.
          split.  apply QRule_I_L.rule_assgn. admit.
          intros. unfold assert_implies.
          intros.  rewrite sat_Assert_to_State in *.
          rewrite seman_find in *.
           split.  intuition.
           split. intuition. 
           intros. econstructor. apply H. assumption.
           right. unfold F_3. split. apply H. assumption.  
          admit.
          } 
          unfold assert_implies.
          intros.  rewrite sat_Assert_to_State in *.
          rewrite seman_find in *.
           split.  intuition.
           split. intuition. 
           intros. econstructor. split. 
          destruct H. destruct H1. 
          apply H2 in H0.  unfold State_eval in *.
          destruct H0. destruct H0. 
          unfold F_1 in *. unfold F_2 in *. unfold F_3 in *.
          destruct H4. destruct H4. 
          destruct H4. destruct H4.
          destruct H0. destruct H0. 
          unfold Pure_eval in *. 
          unfold beval in *. 
          unfold aeval in *.
       
           bdestruct (c_find y (fst (x0, d_find x0 mu)) =?
           Nat.gcd (x ^ (r / 2) - 1) N).
           rewrite H9. admit.
           destruct H4.
Admitted.

End Shor.
