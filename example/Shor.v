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


Require Import Coq.Arith.Arith.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.


Module Shor (p:Param).

Module OF:=OF(p).

Definition x := p.x.
Definition N := p.N.
Definition z := p.z.
Definition r := p.r.
Definition Hx:= p.H.
Definition Hr:= p.Hr.
Definition y:nat := 3.

Parameter random: nat -> nat -> nat.
Hypothesis Hran: forall a b, (a <= random a b) /\ (random a b <= b).

(*Shor程序*)
Definition Shor :=
  let N2 := (N mod 2) in
  let b2 (x:nat) :=(BAnd (BEq (AMod z ' 2) 0 )  (BNeq ((AMod (APlus (APow x (ADiv z ' 2)) 1) N)) 0)) in
  let b3 (x:nat) :=(BAnd (BNeq (AGcd  (AMinus (APow x (ADiv z ' 2)) 1) N) N)  
                         (BNeq (AGcd  (AMinus (APow x (ADiv z ' 2)) 1) N) 1) ) in
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

(*N是一个合数*)
Definition Cop (N:nat) := exists a, 2<=a /\ a<=(N-1) /\ Nat.modulo N a =0.

(*gcd (x^(z/2)-1)  N 是非平凡因子*)
Definition F_1(y x N:nat): Pure_formula := ((BEq y ' (((Nat.gcd (x ^ (r / 2) - 1) N)))) 
/\p (BNeq y ' 1) /\p (BNeq y ' N)).

(*gcd (x^(z/2)+1)  N 是非平凡因子*)
Definition F_2(y x N:nat): Pure_formula := ((BEq y ' (((Nat.gcd (x ^ (r / 2) + 1) N)))) 
/\p (BNeq y ' 1) /\p (BNeq y ' N)).

(*gcd x N 是非平凡因子*)
Definition F_3(y x N:nat): Pure_formula := ((BEq y ' (Nat.gcd x N)) /\p (BNeq y ' N)).

(*（gcd (x^(z/2)-1)  N） 或 （gcd (x^(z/2)+1)  N） 第一有一个是非平凡因子*)
Definition Big_hypose (x z N:nat): Pure_formula:= 
  (BAnd (BNeq (AGcd  (AMinus (APow x (ADiv z ' 2)) 1) N) N)  
  (BNeq (AGcd (AMinus (APow x (ADiv z ' 2)) 1) N) 1)) \/p 
  (BAnd (BNeq (AGcd  (APlus (APow x (ADiv z ' 2)) 1) N) N)  
  (BNeq (AGcd (APlus (APow x (ADiv z ' 2)) 1) N) 1)).

(*平方差公式*)
Lemma pow_sub: forall x y:nat, (y<=x) -> (x)^2 -(y^2)= (x+y)*(x-y).
Proof.  intros. rewrite Nat.mul_add_distr_r. repeat rewrite Nat.mul_sub_distr_l. 
       simpl. repeat rewrite Nat.mul_1_r. 
       rewrite Nat.add_sub_assoc.
       rewrite (Nat.mul_comm  x0 y0).
       rewrite Nat.sub_add. 
       reflexivity.
       apply Nat.mul_le_mono_r; lia. 
       apply Nat.mul_le_mono_l; lia. 
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

Lemma mod_eq_1: forall a b c ,
c<>0->
a>=b -> a mod c= b mod c ->
exists m:nat, a= m*c +b.
Proof. intros.  rewrite Nat.mod_eq in H1; try lia.
  rewrite Nat.mod_eq in H1; try lia. 
exists (a/c - b/c).
rewrite Nat.mul_sub_distr_r.
rewrite Nat.mul_comm.  
rewrite (Nat.mul_comm _ c).
apply repad_lemma2 in H1; try apply Nat.mul_div_le; try lia.  
rewrite H1 at 2. 
rewrite Nat.add_assoc.
rewrite Nat.add_sub_assoc; try try apply Nat.mul_div_le; try lia.  
Qed.



Lemma Big_hypose_sovle: 
    (BEq (z) '  r )  /\p
   (BAnd (BEq (AMod z ' 2) 0 )  
         (BNeq (( (AMod (APlus (APow x (ADiv z ' 2)) 1) N) )) 0))
    ->> Big_hypose x z N.
Proof. intros. seman_sovle. unfold Big_hypose. unfold Pure_eval in *.
       unfold beval in *. unfold aeval in *. simpl fst in *. 
       pose Hr. pose Hx. unfold r in *.     unfold x in *.  unfold N in *. 
       destruct a.  bdestruct (c_find z x0 =? p.r). 
       rewrite H3 in *. 
       bdestruct ((p.r mod 2 =? 0)). 
       assert(1= 1 mod p.N). rewrite Nat.mod_small. reflexivity. 
       lia. rewrite H5 in H1.
       assert(p.r = (p.r/2)*2).
       rewrite Nat.mul_comm. 
       rewrite <-Nat.divide_div_mul_exact; try lia.  
       rewrite <-(Nat.mul_1_r 2) at 2.
       rewrite Nat.div_mul_cancel_l; try lia.
       rewrite Nat.div_1_r. reflexivity. 
       rewrite <-Nat.mod_divide. assumption. lia.  
       rewrite H6 in H1.  rewrite Nat.pow_mul_r in H1.
       apply mod_eq_1 in H1.  destruct H1. 
       assert (((p.x ^ (p.r / 2)) ^ 2 - 1 ^ 2) mod p.N =0).
       rewrite H1. simpl. rewrite <-Nat.add_sub_assoc; try lia.
       rewrite Nat.sub_diag. rewrite Nat.add_0_r. 
       apply Nat.mod_mul. lia. 
       rewrite pow_sub in H7. rewrite Nat.mod_divide in H7; try lia. 
       apply Nat.divide_mul_split in H7.
       destruct H7. destruct H7.  destruct H7. 
       destruct H8.
       assert(exists c:nat, p.N=  x2 * c).
       exists x3. assumption.  
       assert(exists c:nat, p.N=  x3 * c).
       exists x2. rewrite Nat.mul_comm. assumption. 
       rewrite <-Nat.mod_divides in H10.
       rewrite <-Nat.mod_divides in H12.
       rewrite Nat.mod_divide in H10.
       rewrite Nat.mod_divide in H12.
       assert(Nat.divide x2 (Nat.gcd ((p.x ^ (p.r / 2) + 1)) (p.N))).
       apply Nat.gcd_divide_iff. split; try assumption.
       apply Nat.divide_pos_le in H13. 
       assert(Nat.divide x3 (Nat.gcd ((p.x ^ (p.r / 2) - 1)) (p.N))).
       apply Nat.gcd_divide_iff. split; try assumption.
       apply Nat.divide_pos_le in H14. 
       destruct ((¬ (p.x ^ (p.r / 2) + 1) mod p.N =? 0)) eqn:E.
       assert(Nat.gcd (p.x ^ (p.r / 2) + 1) p.N <> p.N).
       intro. rewrite Nat.gcd_comm in H15.
       apply Nat.divide_gcd_iff in H15; try lia.  
       rewrite <-Nat.mod_divide in H15; try lia. 
       rewrite H15 in E.   simpl in E.  auto. 
       apply Nat.eqb_neq in H15.  rewrite H15. 
       assert(1<x2 \/ ~(1<x2 )).
       apply Classical_Prop.classic. destruct H16. 
       assert(Nat.gcd (p.x ^ (p.r / 2) + 1) p.N <> 1).
       lia. apply Nat.eqb_neq in H17. rewrite H17. 
       right. simpl. auto.
       assert(x2<>0). intro. rewrite H17 in H7. simpl in H7. lia.   
       assert(x2=1). lia. rewrite H18 in *. rewrite Nat.mul_1_l in H7.
       rewrite<-H7 in H14.      
       assert(Nat.gcd (p.x ^ (p.r / 2) - 1) p.N <> p.N).
       intro. rewrite Nat.gcd_comm in H19.
       apply Nat.divide_gcd_iff in H19; try lia.  
       rewrite <-Nat.mod_divide in H19; try lia. 
       assert((p.x ^ (p.r / 2) ) mod p.N = 1).
       assert(0=0mod p.N). rewrite Nat.mod_small. reflexivity.
       lia. rewrite H20 in H19 at 3.
       apply mod_eq_1 in H19; try lia. destruct H19. 
       rewrite Nat.add_0_r in H19. symmetry in H19.
       apply repad_lemma2 in H19. 
       rewrite H19. rewrite Nat.mod_add; try lia.
       assert(p.x ^ (p.r / 2) <> 0). 
        apply Nat.pow_nonzero. lia. lia.   
       assert(p.r<=(p.r / 2)).  
       apply H2. assumption. 
       assert((p.r / 2)< p.r). apply Nat.div_lt; try lia. lia.
       apply Nat.eqb_neq in H19. rewrite H19. 
       assert(Nat.gcd (p.x ^ (p.r / 2) - 1) p.N <>1). lia.
       apply Nat.eqb_neq in H20. rewrite H20. 
       left. simpl. auto.
       simpl in H0. destruct H0.
       assert(Nat.gcd (p.x ^ (p.r / 2) - 1) p.N<>0).
       intro.  apply  Nat.gcd_eq_0 in H15. 
       destruct H15. lia. lia.   
       assert(Nat.gcd (p.x ^ (p.r / 2) + 1) p.N<>0).
       intro.  apply  Nat.gcd_eq_0 in H14. 
       destruct H14. lia. lia.
        intro. rewrite H13 in *.  rewrite Nat.mul_0_r in H7.
        lia.   
        intro. rewrite H13 in *.  rewrite Nat.mul_0_l in H7.
        lia.
        intro. rewrite H13 in *.  rewrite Nat.mul_0_r in H7.
        lia.
        intro. rewrite H13 in *.  rewrite Nat.mul_0_l in H7.
        lia.   
        lia. 
        assert(p.x ^ (p.r / 2) <> 0). 
        apply Nat.pow_nonzero. lia.  
        lia. lia.
        assert(1=1^2). simpl. reflexivity. rewrite H7 at 3.
        apply Nat.pow_le_mono_l. 
        assert(p.x ^ (p.r / 2) <> 0). 
        apply Nat.pow_nonzero. lia.  
        lia.
        simpl in H0. destruct H0. simpl in H0. destruct H. 
Qed.


(* Definition a :=4 . *)

Lemma BAnd_split: forall (b1 b2:bool),
(if (b1&&b2) then True else False) ->
((if (b1) then True else False) /\ (if (b2) then True else False)).
Proof. intros. destruct (b1); destruct b2; simpl in *; try destruct H. intuition. 
Qed.


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
{{(Pre Cop N)}} Shor  {{  (BEq ((AMod N y ')) 0) /\p (BNeq y ' 1) /\p (BNeq y ' (N)) }} .
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
       classic_slove_1;  rewrite Nat.eqb_eq in H2. rewrite H2. apply Nat.eqb_eq in H3. 
       rewrite H3. auto. rewrite H2. simpl. auto. rewrite H2.  pose Hx. unfold N. 
       bdestruct (2 =? p.N ). simpl. lia. auto.
    
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
        pose (Hran 2 (N-1)); try rewrite <-H0 in a; destruct a;
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
         classic_slove_2. right.  split. auto. rewrite Nat.eqb_eq in H4. rewrite H4. 
         bdestruct (Nat.gcd x N =? N). pose Hx. unfold N. unfold x. simpl. 
         rewrite Nat.gcd_comm in H5. apply Nat.divide_gcd_iff in H5; unfold N; try lia.
         apply Nat.divide_pos_le in H5; unfold x in *; unfold N in *; lia.   
         auto.
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
           eapply implies_trans with 
           ((((Pre Cop N) /\p (BNot (BEq (( (N mod 2))) 0)) /\p ((BLe 2 x ) /\p (BLe x ((N-1)))))
           /\p ( BEq z ' r) /\p (( BEq z ' r) /\p (<{ (z) ' % 2 = 0 && (APlus <{ x ^ (ADiv (z) ' 2) }> 1) % N <> 0 }>)))).
           classic_slove_1.
           implies_trans_solve 1 SAnd_PAnd_eq.
           implies_trans_solve 0 SAnd_PAnd_eq.  
           apply rule_CconjCon; try apply implies_refl.
           apply Big_hypose_sovle.
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
         rewrite H4. bdestruct (Nat.gcd x N =? N). pose Hx. unfold N. unfold x. simpl. 
         rewrite Nat.gcd_comm in H5. apply Nat.divide_gcd_iff in H5; unfold N; try lia.
         apply Nat.divide_pos_le in H5; unfold x in *; unfold N in *; lia.   
         auto.
          }
          
       classic_slove_2; try rewrite Nat.eqb_eq in H7; try
       rewrite H7. 
       assert(N mod Nat.gcd (x ^ (r / 2) - 1) N = 0).
       apply Nat.mod_divide. intro. apply Nat.gcd_eq_0 in H8. unfold N in *. pose Hx. lia.
       apply Nat.gcd_divide_r. apply Nat.eqb_eq in H8. rewrite H8. auto.
       assert(N mod Nat.gcd (x ^ (r / 2) + 1) N = 0).
       apply Nat.mod_divide. intro. apply Nat.gcd_eq_0 in H8. unfold N in *. pose Hx. lia.
       apply Nat.gcd_divide_r. apply Nat.eqb_eq in H8. rewrite H8. auto.
       rewrite Nat.eqb_eq in H6. rewrite H6. 
       assert(N mod Nat.gcd x N = 0).
       apply Nat.mod_divide. intro. apply Nat.gcd_eq_0 in H7. unfold N in *. pose Hx. lia.
       apply Nat.gcd_divide_r. apply Nat.eqb_eq in H7. rewrite H7. auto.
Qed.

End Shor.
