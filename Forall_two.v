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

                  


