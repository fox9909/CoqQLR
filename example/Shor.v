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
Clet a b
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
  let N2 :=ANum (N mod 2) in
  let b2 (x:nat) :=(BAnd (BEq (AMod z (ANum 2)) (ANum 0)) (BNeq (((AMod (APow (ANum x) (ADiv z (ANum 2))) (ANum N)))) (ANum 1))) in
  let b3 (x:nat) :=(BAnd (BNeq (AGcd  (AMinus (APow (ANum x) (ADiv z (ANum 2))) (ANum 1)) (ANum N)) (ANum N))  
                          (BNeq (AGcd (AMinus (APow (ANum x) (ADiv z (ANum 2))) (ANum 1)) (ANum N)) (ANum 1))  ) in
  <{  if BEq (N2) (ANum 0) then
           y:=ANum 2
      else  
           Clet x ((random 2 (N-1)));
           y:= AGcd (ANum x) (ANum N);
           while BEq y (ANum 1) do 
                   OF.OF ;
                  if b2 x then
                      if  b3 x then 
                          y:= AGcd  (AMinus (APow (ANum x) (ADiv z (ANum 2))) (ANum 1)) (ANum N)
                      else 
                          y:= AGcd (APlus (APow (ANum x) (ADiv z (ANum 2))) (ANum 1)) (ANum N)
                      end 
                  else 
                       Clet x ((random 2 (N-1)));
                       y := AGcd ((ANum x)) (ANum N)
                  end 
            end 
      end 
  }>.


Theorem rule_while_classic: forall F (b:bexp) (c:com),
         {{F /\ b}} c {{ F}}
      -> {{F}}
         while b do c end
         {{ (F /\ (BNot b)) }}.
Proof. Admitted.

Theorem rule_cond_classic: forall (F1 F2: State_formula) (c1 c2:com) (b:bexp),
        ({{F1 /\ (b)}} c1 {{F2 }} /\ {{F1 /\ ((BNot b) )}} c2 {{F2 }})
     -> ({{F1 }}
        if b then c1 else c2 end
        {{F2}}).
Proof. Admitted.

Theorem rule_qframe'': forall (F1 F2 F3: State_formula) c,
         ({{F1}} c {{F2}}) /\  (NSet.inter (fst (Free_state F3)) (fst (MVar c)) =NSet.empty) 
         /\ (NSet.inter (snd (Free_state F3)) (snd (MVar c)) =NSet.empty) 
         ->  {{F3 /\ F1}} c {{F3 /\ F2}}. Admitted.

Theorem rule_conseq_r' : forall (P Q Q' : Assertion) c,
{{P}} c {{Q'}} ->
(Q'->> Q) ->

{{P}} c {{Q}}.
Proof. intros. eapply rule_conseq. apply H. 
apply implies_refl. assumption. Qed.   


Definition Cop (a N:nat): Pure_formula := PExists  a 
((BAnd (BAnd (BLe (ANum 2) (ANum a))  (BLe (ANum a) (ANum (N-1))))
 (BEq (ANum (N mod a)) (ANum 0)))).

Definition F_1(y x N:nat): bexp := BAnd (BAnd (BEq y ((ANum (Nat.gcd (x ^ (r / 2) - 1) N)))) 
(BNeq y (ANum 1))) (BNeq y (ANum N)).

Definition F_2(y x N:nat): bexp := BAnd (BAnd (BEq y ((ANum (Nat.gcd (x ^ (r / 2) + 1) N)))) 
(BNeq y (ANum 1))) (BNeq y (ANum N)).

Definition F_3(y x N:nat): bexp := (BAnd (BEq y ((ANum (Nat.gcd x N)))) 
(BNeq y (ANum N))) .

Definition a :=4 .

Lemma rule_AndT: forall (P:State_formula),
P ->> P /\ BTrue .
Proof. rule_solve. 
  
Qed.

Theorem Shor_correctness:

{{Cop a N}} Shor  {{  (BEq ((AMod (ANum N) y)) (ANum 0)) /\ (BNeq y (ANum 1)) /\ (BNeq y ((ANum N)))}} .
Proof. unfold Shor. 
       eapply rule_cond_classic. split.
       {eapply rule_conseq_l with ((Cop a N /\ (BEq (ANum ((N mod 2))) (ANum 0))) /\ (Assn_sub_P y (ANum 2) (BEq y (ANum 2)))).
        apply rule_ConjE. split. apply rule_PT. apply Assn_true. simpl. unfold not. apply In_empty.
       eapply rule_conseq_r'.
       eapply rule_qframe''.
       split.  apply rule_assgn. simpl.  admit.
        }
       eapply rule_seq with ((Cop a N /\  (BNot (BEq ((ANum (N mod 2))) ((ANum 0))))) 
       /\ ((BAnd (BLe ((ANum 2)) (ANum x))  (BLe ((ANum x)) ((ANum (N-1))))))). 
          {eapply rule_conseq_l. apply rule_AndT.
          eapply rule_conseq_r'.
          eapply rule_qframe''. 
          split.   eapply rule_Clet. admit.
          apply rule_CconjCon. apply implies_refl. 
          intros. unfold assert_implies.
        intros.  rewrite sat_Assert_to_State in *.
        rewrite seman_find in *.
        split.  intuition.
        split. intuition.
        intros. 
        destruct H. destruct H1. apply H2 in H0.
        unfold State_eval in *. unfold Pure_eval in *.
        unfold beval in *. unfold aeval in *.
        bdestruct (x =? random 2 (N - 1)).
        rewrite H3.
        rewrite Hran. intuition. destruct H0. 
        }
          eapply rule_seq with ((Cop a N /\  (BNot (BEq ((ANum (N mod 2))) (ANum 0))) /\ (BAnd (BLe (ANum 2) (ANum x) ) (BLe (ANum x) (ANum (N-1)))))
          /\(BOr (F_1 y x N) (BOr (F_2 y x N) (F_3 y x N)))).
          {eapply rule_conseq_l with (((Cop a N /\  (BNot (BEq ((ANum ((N mod 2)))) (ANum 0))) /\ ((BAnd (BLe (ANum 2) (ANum x) ) (BLe (ANum x) (ANum (N-1))))))) 
          /\ Assn_sub_P y ((AGcd (ANum x) (ANum N))) (BEq y ((AGcd (ANum x) (ANum N))))).
          intros. unfold assert_implies.
          intros.  rewrite sat_Assert_to_State in *.
          rewrite seman_find in *.
          split.  intuition.
          split. intuition.
          intros. split.  
          split. apply H. assumption.
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
          split.  apply rule_assgn.  admit.
          }
          eapply rule_conseq_r'.
          apply rule_while_classic.
           eapply rule_seq with ((Cop a N/\  (BNot (BEq ((ANum (N mod 2))) (ANum 0))) /\ (BAnd (BLe (ANum 2) (ANum x) ) (BLe (ANum x) (ANum (N-1)))))
           /\(BEq z (ANum (ord x N)))). 
           eapply rule_conseq_l with 
           (((Cop a N /\  (BNot (BEq ((ANum (N mod 2))) (ANum 0))) /\ (BAnd (BLe (ANum 2) (ANum x) ) (BLe (ANum x) (ANum (N-1)))))
           /\(BEq (ANum (Nat.gcd x N)) (ANum 1)))).
           intros. unfold assert_implies.
          intros.  rewrite sat_Assert_to_State in *.
          rewrite seman_find in *.
          split.  intuition.
          split. intuition.
          intros. split.  
          split. apply H. assumption.
          split. apply H. assumption. 
         apply H. assumption. destruct H. destruct H1. 
         apply H2 in H0. destruct H0. destruct H0. 
         admit.
           apply rule_qframe''. 
           split. 
           apply OF.OF_correctness.   admit.
           apply rule_cond_classic. split.
           eapply rule_conseq_l with (((Cop a N /\  (BNot (BEq ((ANum (N mod 2))) (ANum 0))) /\ (BAnd (BLe (ANum 2) (ANum x) ) (BLe (ANum x) (ANum (N-1)))))
           /\( BEq z (ANum (ord x N))) /\ (BOr (F_1 y x N) (F_2 y x N)))). 
            admit.
           apply rule_cond_classic. split.
           eapply rule_conseq_l with 
           ( ((Cop a N /\  (BNot (BEq ((ANum (N mod 2))) (ANum 0))) /\ (BAnd (BLe (ANum 2) (ANum x) ) (BLe (ANum x) (ANum (N-1))))) /\(F_1 y x N)) /\ 
           (Assn_sub_P y (AGcd (AMinus (APow (ANum x) (ADiv z (ANum 2))) (ANum 1)) (ANum N)) (BEq y (ANum (Nat.gcd ((x^ (r / 2)) -1) N))))).
            {admit.
              (*intros. unfold assert_implies.
           intros.  rewrite sat_Assert_to_State in *.
           rewrite seman_find in *.
            split.  intuition.
            split. intuition. 
            intros. econstructor. apply H. assumption.
             unfold State_eval. unfold Pure_eval.
             unfold s_update_cstate. 
          unfold beval. unfold aeval. unfold fst.
          rewrite c_update_find_eq.
          rewrite c_update_find_not.
          induction (Nat.gcd (c_find x' x0) N);
         simpl; intuition. unfold y. unfold x'. lia. *)
             } 
            eapply rule_conseq_r'.
          eapply rule_qframe''.
          split.  apply rule_assgn.
          admit. admit.
          eapply rule_conseq_l with 
          ( (Cop a N /\  (BNot (BEq ((ANum (N mod 2))) (ANum 0))) /\ (BAnd (BLe (ANum 2) (ANum x) ) (BLe (ANum x) (ANum (N-1)))) /\(F_2 y x N)) 
          /\ (Assn_sub_P y (AGcd (APlus (APow (ANum x) (ADiv z (ANum 2))) (ANum 1)) (ANum N)) (BEq y (ANum (Nat.gcd (x^ ((ord x N) / 2) + 1) N))))).
          admit. 
         eapply rule_conseq_r'.
         eapply rule_qframe''.
         split.  apply rule_assgn.
         admit. admit.
         eapply rule_seq with ((Cop a N /\  (BNot (BEq ((ANum (N mod 2))) ((ANum 0))))) 
       /\ ((BAnd (BLe ((ANum 2)) (ANum x))  (BLe ((ANum x)) ((ANum (N-1))))))). 
          {eapply rule_conseq_l. apply rule_AndT.
          eapply rule_conseq_r'.
          eapply rule_qframe''. 
          split.   eapply rule_Clet.  admit.
          intros. unfold assert_implies.
        intros.  rewrite sat_Assert_to_State in *.
        rewrite seman_find in *.
        split.  intuition.
        split. intuition.
        intros. split. split.  apply H. assumption.
        apply H. assumption.
        destruct H. destruct H1. apply H2 in H0.
        destruct H0. unfold State_eval in *. unfold Pure_eval in *.
        unfold beval in *. unfold aeval in *.
        bdestruct (x =? random 2 (N - 1)).
        rewrite H4.
        rewrite Hran. intuition. destruct H3. 
        }
        {eapply rule_conseq_l with (((Cop a N /\  (BNot (BEq ((ANum ((N mod 2)))) (ANum 0))) /\ ((BAnd (BLe (ANum 2) (ANum x) ) (BLe (ANum x) (ANum (N-1))))))) /\ Assn_sub_P y ((AGcd (ANum x) (ANum N))) (BEq y ((AGcd (ANum x) (ANum N))))).
          intros. unfold assert_implies.
          intros.  rewrite sat_Assert_to_State in *.
          rewrite seman_find in *.
          split.  intuition.
          split. intuition.
          intros. split.  
          split. apply H. assumption.
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
          split.  apply rule_assgn. admit.
          admit.
          } admit. 
Admitted.

End Shor.
