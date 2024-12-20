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


Inductive Forall_two{A B:Type}: (A ->B-> Prop)-> (list A) -> (list B) -> Prop:=
|Forall_two_nil: forall P, Forall_two P [] []
|Forall_two_cons: forall (P:A-> B-> Prop) l1h l1t l2h l2t, 
                  P l1h l2h-> Forall_two P l1t l2t ->  Forall_two P (l1h::l1t) (l2h:: l2t).


Lemma Forall_two_length_eq{ A B:Type}: forall P (l1:list A) (l2:list B),
Forall_two P l1 l2 ->
length l1= length l2.
Proof. induction l1; destruct l2; intros; inversion_clear H; try reflexivity.
       simpl. auto.
Qed.


Lemma Forall_two_app{A B:Type}:forall (P:A-> B-> Prop)  (f1: list A) (g1: list B )  (f2: list A) 
  (g2: list B) ,
  (Forall_two P f1 g1)->
  (Forall_two P f2 g2)->
  (Forall_two P (f1++f2) (g1++g2)).
  Proof.  induction f1; destruct g1; simpl; intros; inversion_clear H.
          assumption. 
          econstructor. assumption.
          apply IHf1. intuition. intuition.
Qed.
                  

Lemma Forall_two_Conj{A B:Type }:forall (P Q: A ->B->Prop) (f :list A) (g:list B),
((Forall_two P f g) /\ (Forall_two Q f g))<->
(Forall_two (fun i j=> P i j /\ Q i j) f g).
Proof. induction f; intros; destruct g; split;intros;  try econstructor; inversion_clear H.
       econstructor. econstructor.  
       inversion_clear H0. inversion_clear H1.  
       inversion_clear H0. inversion_clear H1.  
       try split; try assumption. 
       inversion_clear H0. inversion_clear H1.
       apply IHf; split; try assumption. 
       econstructor. apply H0. apply IHf. assumption.
       econstructor. apply H0. apply IHf. assumption.
Qed.

