Require Import Lists.List.
Require Import Reals.
Require Import Coquelicot.Complex.
Require Import Strings.String.

From Quan Require Import Matrix.
From Quan Require Import Quantum.
From Quan Require Import Basic.
From Quan Require Import Mixed_State.
From Quan Require Import QState_L.
From Quan Require Import Reduced.
From Quan Require Import QIMP_L.
From Quan Require Import Ceval_Prop.
From Quan Require Import QAssert_L.
From Quan Require Import QSepar.
From Quan Require Import QRule_E_L.
From Quan Require Import QRule_Q_L.
From Quan Require Import QRule_I_L.
From Quan Require Import QSepar.
From Quan Require Import QFrame.
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
Hypothesis Hr : (r > 0) /\ x ^ r mod N =1 /\ (forall j, x ^ j mod N =1 -> r<=j).
Definition y:nat := 3.

Parameter random: nat -> nat -> nat.
Hypothesis Hran: forall a b, (a-1 < random a b) /\ (random a b < b+1).

(*Shor's Program*)
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

(*N is a composite number*)
Definition Cop (N:nat) := exists a, 2<=a /\ a<=(N-1) /\ Nat.modulo N a =0.

(*gcd (x^(z/2)-1)  N is a nontrivial factor of N*)
Definition F_1(y x N:nat): Pure_formula := ((BEq y ' (((Nat.gcd (x ^ (r / 2) - 1) N)))) 
/\p (BNeq y ' 1) /\p (BNeq y ' N)).

(*gcd (x^(z/2)+1)  N is a nontrivial factor of N*)
Definition F_2(y x N:nat): Pure_formula := ((BEq y ' (((Nat.gcd (x ^ (r / 2) + 1) N)))) 
/\p (BNeq y ' 1) /\p (BNeq y ' N)).

(*gcd x N is a nontrivial factor of N*)
Definition F_3(y x N:nat): Pure_formula := ((BEq y ' (Nat.gcd x N)) /\p (BNeq y ' N)).

(*either（gcd (x^(z/2)-1)  N） or （gcd (x^(z/2)+1)  N） is a nontrivial factor of N*)
Definition Big_hypose (x z N:nat): Pure_formula:= 
  (BAnd (BNeq (AGcd  (AMinus (APow x (ADiv z ' 2)) 1) N) N)  
  (BNeq (AGcd (AMinus (APow x (ADiv z ' 2)) 1) N) 1)) \/p 
  (BAnd (BNeq (AGcd  (APlus (APow x (ADiv z ' 2)) 1) N) N)  
  (BNeq (AGcd (APlus (APow x (ADiv z ' 2)) 1) N) 1)).

(*square variance*)
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
(<{ 1 < x }> /\p <{ x < N }>) /\p (BEq (z) '  r )  /\p
   (BAnd (BEq (AMod z ' 2) 0 )  
         (BNeq (( (AMod (APlus (APow x (ADiv z ' 2)) 1) N) )) 0))
    ->> Big_hypose x z N.
Proof. intros. seman_sovle. unfold Big_hypose. unfold Pure_eval in *.
       unfold beval in *. unfold aeval in *. simpl fst in *.  
       pose Hr.  bdestruct (1 <? x); try destruct H. 
       bdestruct (x <? N); try destruct H2.
       unfold r in *.     unfold x in *.  unfold N in *.
       destruct a as [a0 ]. destruct H2.   bdestruct (c_find z x0 =? p.r). 
       rewrite H5 in *. 
       bdestruct ((p.r mod 2 =? 0)). 
       assert(1= 1 mod p.N). rewrite Nat.mod_small. reflexivity. 
       lia. rewrite H7 in H2.
       assert(p.r = (p.r/2)*2).
       rewrite Nat.mul_comm. 
       rewrite <-Nat.divide_div_mul_exact; try lia.  
       rewrite <-(Nat.mul_1_r 2) at 2.
       rewrite Nat.div_mul_cancel_l; try lia.
       rewrite Nat.div_1_r. reflexivity. 
       rewrite <-Nat.mod_divide. assumption. lia.  
       rewrite H8 in H2.  rewrite Nat.pow_mul_r in H2.
       apply mod_eq_1 in H2.  destruct H2. 
       assert (((p.x ^ (p.r / 2)) ^ 2 - 1 ^ 2) mod p.N =0).
       rewrite H2. simpl. rewrite <-Nat.add_sub_assoc; try lia.
       rewrite Nat.sub_diag. rewrite Nat.add_0_r. 
       apply Nat.mod_mul. lia. 
       rewrite pow_sub in H9. rewrite Nat.mod_divide in H9; try lia. 
       apply Nat.divide_mul_split in H9.
       destruct H9. destruct H9.  destruct H9. 
       destruct H10.
       assert(exists c:nat, p.N=  x2 * c).
       exists x3. assumption.  
       assert(exists c:nat, p.N=  x3 * c).
       exists x2. rewrite Nat.mul_comm. assumption. 
       rewrite <-Nat.mod_divides in H13.
       rewrite <-Nat.mod_divides in H14.
       rewrite Nat.mod_divide in H13.
       rewrite Nat.mod_divide in H14.
       assert(Nat.divide x2 (Nat.gcd ((p.x ^ (p.r / 2) + 1)) (p.N))).
       apply Nat.gcd_divide_iff. split; try assumption.
       apply Nat.divide_pos_le in H15. 
       assert(Nat.divide x3 (Nat.gcd ((p.x ^ (p.r / 2) - 1)) (p.N))).
       apply Nat.gcd_divide_iff. split; try assumption.
       apply Nat.divide_pos_le in H16. 
       destruct ((¬ (p.x ^ (p.r / 2) + 1) mod p.N =? 0)) eqn:E.
       assert(Nat.gcd (p.x ^ (p.r / 2) + 1) p.N <> p.N).
       intro. rewrite Nat.gcd_comm in H17.
       apply Nat.divide_gcd_iff in H17; try lia.  
       rewrite <-Nat.mod_divide in H17; try lia. 
       rewrite H17 in E.   simpl in E.  auto. 
       apply Nat.eqb_neq in H17.  rewrite H17. 
       assert(1<x2 \/ ~(1<x2 )).
       apply Classical_Prop.classic. destruct H18. 
       assert(Nat.gcd (p.x ^ (p.r / 2) + 1) p.N <> 1).
       lia. apply Nat.eqb_neq in H19. rewrite H19. 
       right. simpl. auto.
       assert(x2<>0). intro. rewrite H19 in H9. simpl in H9. lia.   
       assert(x2=1). lia. rewrite H20 in *. rewrite Nat.mul_1_l in H9.
       rewrite<-H9 in H16.      
       assert(Nat.gcd (p.x ^ (p.r / 2) - 1) p.N <> p.N).
       intro. rewrite Nat.gcd_comm in H22.
       apply Nat.divide_gcd_iff in H22; try lia.  
       rewrite <-Nat.mod_divide in H22; try lia. 
       assert((p.x ^ (p.r / 2) ) mod p.N = 1).
       assert(0=0mod p.N). rewrite Nat.mod_small. reflexivity.
       lia. rewrite H23 in H22 at 3.
       apply mod_eq_1 in H22; try lia. destruct H22. 
       rewrite Nat.add_0_r in H22. symmetry in H22.
       apply repad_lemma2 in H22. 
       rewrite H22. rewrite Nat.mod_add; try lia.
       assert(p.x ^ (p.r / 2) <> 0). 
        apply Nat.pow_nonzero. lia. lia.   
       assert(p.r<=(p.r / 2)).  
       apply H4. assumption. 
       assert((p.r / 2)< p.r). apply Nat.div_lt; try lia.  lia.  
       apply Nat.eqb_neq in H22.  rewrite H22. 
       assert(Nat.gcd (p.x ^ (p.r / 2) - 1) p.N <>1). lia.
       apply Nat.eqb_neq in H23. rewrite H23. 
       left. simpl. auto.
       simpl in H0. destruct H0.
       assert(Nat.gcd (p.x ^ (p.r / 2) - 1) p.N<>0).
       intro.  apply  Nat.gcd_eq_0 in H17. 
       destruct H17. lia. lia.   
       assert(Nat.gcd (p.x ^ (p.r / 2) + 1) p.N<>0).
       intro.  apply  Nat.gcd_eq_0 in H16. 
       destruct H16. lia. lia.
        intro. rewrite H15 in *.  rewrite Nat.mul_0_r in H9.
        lia.   
        intro. rewrite H15 in *.  rewrite Nat.mul_0_l in H9.
        lia.
        intro. rewrite H15 in *.  rewrite Nat.mul_0_r in H9.
        lia.   
        intro. rewrite H15 in *.  rewrite Nat.mul_0_l in H9.
        lia.
        lia. 
        assert(p.x ^ (p.r / 2) <> 0). 
        apply Nat.pow_nonzero. lia.  
        lia. lia.
        assert(1=1^2). simpl. reflexivity. rewrite H9 at 3.
        apply Nat.pow_le_mono_l. 
        assert(p.x ^ (p.r / 2) <> 0). 
        apply Nat.pow_nonzero. lia.  
        lia.
        simpl in H0. destruct H0.  destruct H1.
Qed.


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
       eapply rule_qframe_P.
       split.  apply rule_PAssgn.
       
       simpl. apply inter_empty. left.
       apply union_empty; split; try reflexivity;
       apply union_empty; split; try reflexivity. 
       classic_slove_1;  rewrite Nat.eqb_eq in H2. rewrite H2. apply Nat.eqb_eq in H3. 
       rewrite H3. auto. rewrite H2. simpl. auto. rewrite H2. 
       unfold Cop in H.  destruct H. unfold N in *.  
       bdestruct (2 =? p.N ). simpl. lia. auto.
    
        }
       eapply rule_seq with (((  (BLt (1) x) /\p (BLt (x) ((ANum (N))))))). 
          {eapply rule_conseq_l. apply rule_AndT.
          eapply rule_conseq_l. apply SAnd_PAnd_eq.
          eapply rule_conseq_r'.
          eapply rule_qframe_P. 
          split.   eapply rule_Clet. 
          
          simpl. apply inter_empty. left.
          apply union_empty; split; try reflexivity;
         apply union_empty; split; try reflexivity. 
         
          implies_trans_solve 0 SAnd_PAnd_eq. implies_trans_solve 1 SAnd_PAnd_eq.
          implies_trans_solve 0 rule_Conj_split_r.  
        classic_slove_1;
        pose (Hran 2 (N-1)); try rewrite <-H0 in a; destruct a;
        rewrite <-Nat.ltb_lt in *; simpl in *; rewrite Nat.sub_add in *;  try rewrite H1; try rewrite H2; auto.
        pose p.H. unfold N. lia.  

        }
          eapply rule_seq with (( ( (BLt 1 x ) /\p (BLt x ((N)))))
          /\p ((F_1 y x N) \/p (F_2 y x N) \/p F_3 y x N)).
          {eapply rule_conseq_l with ( (( (BLt 1 x ) /\p (BLt x ((N))))) 
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
          eapply rule_qframe_P.
          split.  apply rule_PAssgn.
          
          simpl. apply inter_empty. left.
          apply union_empty; split; try reflexivity;
         try apply union_empty; try split; try reflexivity;
         try apply union_empty; try split; try reflexivity.
         classic_slove_2. right.  split. auto. rewrite Nat.eqb_eq in H2. rewrite H2.
         bdestruct (1 <? x). bdestruct (x <? N). 
         bdestruct (Nat.gcd x N =? N). 
         rewrite Nat.gcd_comm in H5. apply Nat.divide_gcd_iff in H5; unfold N; try lia.
         apply Nat.divide_pos_le in H5; unfold x in *; unfold N in *; lia.    
         auto. destruct H1. destruct H.
          }
          eapply rule_conseq_r'.
          apply rule_while_classic.
           eapply rule_seq with (( ( (BLt 1 x ) /\p (BLt x (N))))
           /\p (BEq z ' r)). 
           eapply rule_conseq_l with 
           ((( ( (BLt 1 x ) /\p (BLt x  (N))))
           /\p (BEq ((Nat.gcd x N)) 1))).
           classic_slove_2.

           apply rule_qframe_P. 
           split.  eapply rule_conseq_l; try
           apply OF.OF_correctness; try apply rule_PT. 
           simpl. apply inter_empty. left.
          apply union_empty; split; try reflexivity;
         try apply union_empty; try split; try reflexivity;
         try apply union_empty; try split; try reflexivity.
           apply rule_cond_classic. split.
           eapply rule_conseq_l with ((( ((BLt 1 x ) /\p (BLt x ((N)))))
           /\p ( BEq z ' r) /\p (Big_hypose x z N))).
           implies_trans_solve 1 SAnd_PAnd_eq.
           implies_trans_solve 0 SAnd_PAnd_eq.  
           apply rule_Conj_two. apply rule_Conj_split_l.
           implies_trans_solve 0 SAnd_PAnd_eq.  
           apply Big_hypose_sovle.
           apply rule_cond_classic. split.
           eapply rule_conseq_l with 
           ( (( ( (BLt 1 x ) /\p (BLt x ( (N))))) 
           )/\p (
           (PAssn y (AGcd (AMinus (APow x (ADiv z ' 2)) 1) N) ((F_1 y x N) /\p (BEq y ' ( (Nat.gcd ((x^ (r / 2)) -1) N))))))).
            { classic_slove_2.  
             } 
            eapply rule_conseq_r'.
           

          eapply rule_qframe_P.
          split.  apply rule_PAssgn.
         
          
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
          ( ( ( (BLt 1 x ) /\p (BLt x (ANum (N)))) ) 
          /\p (PAssn y (AGcd (APlus (APow x (ADiv z ' 2)) 1) N) ((F_2 y x N) /\p BEq y ' (ANum (Nat.gcd (x^ (r / 2) + 1) N))))).
          unfold Big_hypose.
          classic_slove_2;
          bdestruct ((Nat.gcd (x ^ (c_find z x0 / 2) - 1) N =? N) ); simpl in H1;
          destruct H1;
          bdestruct (Nat.gcd (x ^ (c_find z x0 / 2) - 1) N =? 1); simpl in H5;
          destruct H5; simpl in H0; destruct H0.

         eapply rule_conseq_r'.
         eapply rule_qframe_P.
         split.  apply rule_PAssgn.
         

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
         eapply rule_seq with ( (( (BLt (1) x) /\p (BLt (x) ((ANum (N))))))). 
          {eapply rule_conseq_l. apply rule_AndT.
          eapply rule_conseq_l. apply SAnd_PAnd_eq.
          eapply rule_conseq_r'.  
          eapply rule_qframe_P. 
          split.   eapply rule_Clet. 
          
          simpl. apply inter_empty. right.
         reflexivity.
          classic_slove_1.
        }
        {eapply rule_conseq_l with ((((( (BLt 1 x )/\p (BLt x (ANum (N))))))) 
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
          eapply rule_qframe_P.
          split.  apply rule_PAssgn. 

          simpl. apply inter_empty. left.
          apply union_empty; split; try reflexivity;
         try apply union_empty; try split; try reflexivity;
         try apply union_empty; try split; try reflexivity;
         try apply union_empty; try split; try reflexivity.


         seman_sovle. right. unfold F_3. split; try assumption.
         classic_slove_aux. apply Nat.eqb_eq in H2.
         rewrite H2.
         bdestruct (1 <? x). bdestruct (x <? N). 
         bdestruct (Nat.gcd x N =? N). 
         rewrite Nat.gcd_comm in H5. apply Nat.divide_gcd_iff in H5; unfold N; try lia.
         apply Nat.divide_pos_le in H5; unfold x in *; unfold N in *; lia.   
         auto. destruct H1. destruct H.
          }
          
       classic_slove_2; try rewrite Nat.eqb_eq in H7; try
       rewrite H7;
       bdestruct (1 <? x); bdestruct (x <? N); try destruct H2; try destruct H.
       assert(N mod Nat.gcd (x ^ (r / 2) - 1) N = 0).
       apply Nat.mod_divide. intro. apply Nat.gcd_eq_0 in H. unfold N in *. lia.
       apply Nat.gcd_divide_r. apply Nat.eqb_eq in H5. rewrite H5. rewrite H. auto.   
       assert(N mod Nat.gcd (x ^ (r / 2) + 1) N = 0).
       apply Nat.mod_divide. intro. apply Nat.gcd_eq_0 in H. unfold N in *.  lia.
       apply Nat.gcd_divide_r. apply Nat.eqb_eq in H5. rewrite H5. rewrite H. auto.
       rewrite Nat.eqb_eq in H4. rewrite H4. 
       assert(N mod Nat.gcd x N = 0).
       apply Nat.mod_divide. intro. apply Nat.gcd_eq_0 in H. unfold N in *.  lia.
       apply Nat.gcd_divide_r. apply Nat.eqb_eq in H. rewrite H. auto.
Qed.

End Shor.
