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
From Quan Require Import Basic.
From Quan Require Import Mixed_State.
From Quan Require Import QState_L.
From Quan Require Import QIMP_L.
From Quan Require Import QAssert_L.
From Quan Require Import Reduced.
From Quan Require Import QRule_Q_L.
From Quan Require Import QRule_E_L.
From Quan Require Import QRule_I_L.
From Quan Require Import Ceval_Prop.
From Quan Require Import QSepar.

Local Open Scope com_scope.
Local Open Scope nat_scope.
Local Open Scope rule_scope.


(*---------------------------------------------dstate_Separ preserve-----------------------------------------*)

Fixpoint dstate_qstate_eq {s e:nat} (mu1 mu2: list(cstate * qstate s e)):=
match mu1, mu2 with 
| nil , nil => True
|(c1,q1)::mu'1 , (c2,q2)::mu'2 => and (q1=q2) (dstate_qstate_eq mu'1 mu'2)
| _, _ => False 
end.

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



Ltac dstate_Separ_preserve_solve_1 F:=
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
       dom_solve.
       (* try match goal with 
       H2: NSet.Subset (NSet.union ?a ?b) ?c |- _ => apply subset_union in H2;
       destruct H2 as [H2 H2']; apply subset_Qsys in H2 end; 
       try match goal with 
       H2: NSet.Subset ?a ?b |- _ =>  apply subset_Qsys in H2 end;  try lia;
       try match goal with 
       H: WF_Unitary ?U |- _ => try apply H end;  
       try match goal with 
       H: forall i, WF_Unitary (?U i) |- _ => try apply H end. *)

Lemma dstate_Separ_preserve{s e:nat}: forall c s0 e0 s1 e1
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
    inversion_clear H1. econstructor; try assumption. apply H8.
    apply H9. apply H10. econstructor.
    apply IHceval_single; try reflexivity. inversion_clear H1. assumption.
    assumption. apply H3.
-- { induction mu; intros mu' F Hs ; intros. inversion  H; subst. intuition.  
     destruct a.
    dstate_Separ_preserve_solve_1 F; [try apply dstate_Separ_Qinit_r| try apply dstate_Separ_Qinit_l]; r3_solve_2.  }
-- { induction mu; intros mu' F Hs ; intros. inversion  H; subst. intuition.    
    destruct a. 
    dstate_Separ_preserve_solve_1 F; [try apply dstate_Separ_QUnit_One_r| try apply dstate_Separ_QUnit_One_l]; r3_solve_2. } 
-- { induction mu; intros mu' F Hs ; intros. inversion  H; subst. intuition.
   destruct a. 
   dstate_Separ_preserve_solve_1 F; [try apply dstate_Separ_QUnit_Ctrl_r| try apply dstate_Separ_QUnit_Ctrl_l]; r3_solve_2.  }
--{ induction mu; intros mu' F Hs ; intros. inversion  H; subst. intuition. 
   destruct a.  dstate_Separ_preserve_solve_1 F;
   try match goal with 
   H: big_app' ?f ?n ?mu |- _ => apply (dstate_Separ_big_app'  f n); try lia;try assumption; intros end;
   [try apply dstate_Separ_QMeas_r| try apply dstate_Separ_QMeas_l];
   r3_solve_2.  }
Qed.



(* mu is separable in S1 \cup S2 and  mv(C) \subseteq S2 => mu|_{S1} \modes F => [[c]]_{\mu}|_{S1} \models F *)

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
repeat rewrite (big_sum_Reduced); try lia. 
apply big_sum_eq_bounded.
intros.  destruct H0.
 destruct H1.
 destruct H2.
destruct H3. destruct H4.
destruct H5.
subst. 
rewrite (@QInit_fun_kron_l s s1 e); auto_wf; try lia. 

repeat rewrite Reduced_L; try reflexivity; auto_wf; try lia. 
rewrite (Reduced_tensor_l _  (q0_i x) ((QInit_fun s' e' (q1_i x)))); try reflexivity; auto_wf.
rewrite (Reduced_tensor_l _ (q0_i x) (q1_i x)); try reflexivity; auto_wf.
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
repeat rewrite (big_sum_Reduced); try lia.
apply big_sum_eq_bounded.
intros.  destruct H0.
destruct H2. destruct H3.
destruct H4. destruct H5.
destruct H6. 
subst. 
rewrite (@QUnit_One_fun_kron_r s s1 e); auto_wf; try lia.
repeat rewrite Reduced_R; try reflexivity; auto_wf.
rewrite (Reduced_tensor_r _ ((QUnit_One_fun s' e' U (q0_i x))) (q1_i x)); try reflexivity; auto_wf.
rewrite (Reduced_tensor_r _ (q0_i x) (q1_i x)); try reflexivity; auto_wf.
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
repeat rewrite (big_sum_Reduced); try lia.
apply big_sum_eq_bounded.
intros.  destruct H0.
destruct H2. destruct H3.
destruct H4. destruct H5.
destruct H6. 
subst. 
rewrite (@QUnit_One_fun_kron_l s s1 e); auto_wf; try lia; auto_wf.
repeat rewrite Reduced_L; try reflexivity; auto_wf; try lia. 
rewrite (Reduced_tensor_l _ (q0_i x) ((QUnit_One_fun s' e' U (q1_i x))) ); try reflexivity; auto_wf.
rewrite (Reduced_tensor_l _ (q0_i x) (q1_i x)); try reflexivity; auto_wf.
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
repeat rewrite (big_sum_Reduced); try lia.
apply big_sum_eq_bounded.
intros.  destruct H0.
destruct H2. destruct H3.
destruct H4. destruct H5.
destruct H6. destruct H7.
destruct H10. 
subst.    
rewrite (@QUnit_Ctrl_fun_kron_r s s1 e); auto_wf; try lia.
repeat rewrite Reduced_R; try reflexivity; auto_wf.
rewrite (Reduced_tensor_r _ ((QUnit_Ctrl_fun s0' e0' s1' e1' U (q0_i x))) (q1_i x)); try reflexivity; auto_wf.
rewrite (Reduced_tensor_r _ (q0_i x) (q1_i x)); try reflexivity; auto_wf.
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
repeat rewrite (big_sum_Reduced); try lia.
apply big_sum_eq_bounded.
intros.  destruct H0.
destruct H2. destruct H3.
destruct H4. destruct H5.
destruct H6. destruct H7.
destruct H10. 
subst.    
rewrite (@QUnit_Ctrl_fun_kron_l s s1 e); auto_wf; try lia.
repeat rewrite Reduced_L; try reflexivity; auto_wf; try lia.
rewrite (Reduced_tensor_l _  (q0_i x) ((QUnit_Ctrl_fun s0' e0' s1' e1' U (q1_i x)))); try reflexivity; auto_wf.
rewrite (Reduced_tensor_l _ (q0_i x) (q1_i x)); try reflexivity; auto_wf.
rewrite QUnit_Ctrl_trace; auto_wf; try lia. reflexivity. assumption. 

apply H1.    
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
       split.  apply nz_Mixed_State_aux_to_nz_Mix_State. apply H11.
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
       split.  apply nz_Mixed_State_aux_to_nz_Mix_State. apply H11.
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

Lemma In_inter_empty: forall x y a,
NSet.Equal (NSet.inter x y) (NSet.empty)->
NSet.In a  y ->
~(NSet.In a x) .
Proof. intros. intro.  
pose (NSet.inter_3 H1 H0) .
apply H in i. apply In_empty in i. destruct i.   
Qed.

Lemma State_eval_reduced_meas_l{ s e:nat}: forall c (q: qstate s e) s0 e0 s1 e1 s2 e2 i j F,
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
rewrite big_sum_Reduced in *.
rewrite (@QMeas_fun_sum s e).
rewrite big_sum_Reduced.
destruct n. simpl in H.
destruct H. 
apply NZ_Mixed_not_Zero in H.
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
apply Reduced_Zero. 
destruct o. destruct o0.  
left. split.
apply nz_Mixed_State_aux_to_nz_Mix_State.
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
rewrite (Reduced_tensor_r _ (q0_i i0) (q1_i i0)).
pose (H10 i0). 
pose (H11 i0).
destruct o.  destruct o0.
left. econstructor.
 apply nz_Mixed_State_scale_c.
 apply H9. apply nz_mixed_state_trace_in01.
 apply H8. apply nz_mixed_state_trace_real.
 apply H8. apply H9.
right. rewrite H9. rewrite Mscale_0_r.
reflexivity. rewrite H8.
right. rewrite Zero_trace. rewrite Mscale_0_l.
reflexivity.  auto_wf.  auto_wf. auto_wf. 
 reflexivity.
reflexivity. auto_wf.
rewrite <-(@big_sum_Reduced s e  _  _ s2 e).
apply WF_qstate_Reduced. lia. assumption.
lia.  assumption. lia. 
apply WF_qstate_Reduced. lia.
apply WF_qstate_kron; assumption.
simpl in *.
rewrite Reduced_R in *; try reflexivity; auto_wf.
rewrite (Reduced_tensor_r _ (q0_i j0 )  (q1_i j0)) in H7 ; try reflexivity; auto_wf.
rewrite QMeas_fun_kron_r; auto_wf.
rewrite (Reduced_tensor_r _ (QMeas_fun s0 e0 j (q0_i j0))  (q1_i j0)) ;try reflexivity; auto_wf.
apply s_seman_scale_c. 
assert (@NZ_Mixed_State (2^(s2-s)) (QMeas_fun s0 e0 j (q0_i j0))).
apply WF_qstate_QMeas. intuition. intuition.
lia.  
rewrite (@QMeas_fun_kron_r s s2 e) in H4.
intro. rewrite H8 in H4. rewrite kron_0_l in H4.
destruct H4. reflexivity. assumption. auto_wf.
lia. lia. assumption.
split.   
apply nz_mixed_state_trace_in01.
assumption.  
apply nz_mixed_state_trace_real.
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
apply nz_mixed_state_trace_gt0. apply H5.
apply nz_mixed_state_trace_real. apply H5.
unfold QMeas_fun. unfold q_update.
apply WF_super. auto_wf.  auto_wf.
unfold QMeas_fun. unfold q_update.
unfold super. auto_wf. lia. lia.  
unfold QMeas_fun. unfold q_update.
apply WF_super. auto_wf. auto_wf.
right. rewrite H6. rewrite kron_0_r.
rewrite QMeas_Zero. apply Reduced_Zero.
right. rewrite H5. rewrite kron_0_l.
rewrite QMeas_Zero. apply Reduced_Zero.
apply (@big_sum_not_0 (2^(e-s2))).
rewrite <-(@big_sum_Reduced s e  _  _ s2 e).
apply NZ_Mixed_not_Zero. 
apply (WF_qstate_Reduced ).
lia.
rewrite <-(@QMeas_fun_sum s  e).
apply WF_qstate_QMeas.
intuition. intuition. lia.
assumption. assumption. 
assumption. 
lia. lia. lia. 
Qed.


Lemma State_eval_reduced_meas_r{ s e:nat}: forall c (q: qstate s e) s0 e0 s1 e1 s2 e2 i j F,
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
rewrite big_sum_Reduced in *; try lia. 
rewrite (@QMeas_fun_sum s e).
rewrite big_sum_Reduced.
destruct n. simpl in H.
destruct H. 
apply NZ_Mixed_not_Zero in H.
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
apply Reduced_Zero. 
destruct o. destruct o0.  
left. split.
apply nz_Mixed_State_aux_to_nz_Mix_State.
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
rewrite (Reduced_tensor_l _ (q0_i i0) (q1_i i0)); auto_wf.
pose (H10 i0). 
pose (H11 i0).
destruct o.  destruct o0.
left. econstructor.
 apply nz_Mixed_State_scale_c.
 apply H8. apply nz_mixed_state_trace_in01.
 apply H9. apply nz_mixed_state_trace_real.
 apply H9. lia. 
right. rewrite H9. rewrite Zero_trace. rewrite Mscale_0_l.
reflexivity. rewrite H8.
right.  rewrite Mscale_0_r.
reflexivity. reflexivity.  auto_wf. 
rewrite <-(@big_sum_Reduced s e  _  _ s  s2).
apply WF_qstate_Reduced. lia. assumption.
lia.  assumption. lia. 
apply WF_qstate_Reduced. lia.
apply WF_qstate_kron; assumption.
simpl in *.
rewrite Reduced_L in *; try reflexivity; auto_wf; try lia. 
rewrite (Reduced_tensor_l _ (q0_i j0 )  (q1_i j0)) in H7 ; try reflexivity; auto_wf.
rewrite QMeas_fun_kron_l; auto_wf.
rewrite (Reduced_tensor_l _ (q0_i j0) (QMeas_fun s0 e0 j (q1_i j0))  ) ;try reflexivity; auto_wf.
apply s_seman_scale_c. 
assert (@NZ_Mixed_State (2^(e-s2)) (QMeas_fun s0 e0 j (q1_i j0))).
apply WF_qstate_QMeas. intuition. intuition.
lia.  
rewrite (@QMeas_fun_kron_l s s2 e) in H4.
intro. rewrite H8 in H4. rewrite kron_0_r in H4.
destruct H4. reflexivity. assumption. auto_wf.
lia. lia. assumption.
split.   
apply nz_mixed_state_trace_in01. assumption. 
apply nz_mixed_state_trace_real. assumption. 
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
apply nz_mixed_state_trace_gt0. apply H6.
apply nz_mixed_state_trace_real. apply H6.
unfold QMeas_fun. unfold q_update.
apply WF_super. auto_wf.  auto_wf.
unfold QMeas_fun. unfold q_update.
unfold super. auto_wf. lia. lia.  
unfold QMeas_fun. unfold q_update.
apply WF_super. auto_wf. auto_wf.
right. rewrite H6. rewrite kron_0_r.
rewrite QMeas_Zero. apply Reduced_Zero.
right. rewrite H5. rewrite kron_0_l.
rewrite QMeas_Zero. apply Reduced_Zero.
apply (@big_sum_not_0 (2^(e-s2))). 
rewrite <-(@big_sum_Reduced s e  _  _ s s2).
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


Lemma State_eval_dstate_reduced_meas_l{s e:nat}:forall s0 e0 s2 c (q:qstate s e) mu i F, 
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
 rewrite H8 in H6. rewrite Reduced_Zero in H6.
 destruct H6. reflexivity. assumption.
 inversion_clear H0. assumption.
 simpl. econstructor.
 apply State_eval_reduced_meas_l with s s2; try lia. simpl in H6.    
 intro.
 rewrite H7 in H6. rewrite Reduced_Zero in H6.
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
   apply QMeas_trace with s0 e0 i. intuition.
   lia. apply WWF_qstate_to_WF_qstate.
   inversion_clear H0. apply H7. assumption.
   assert(s_trace (c,q)>0)%R. unfold  s_trace.
   simpl. apply nz_mixed_state_Cmod_1. inversion_clear H0.
   apply H8. rewrite <- H7 in H8. rewrite H6 in H8.
   lra. lia. simpl. intros. apply mixed_super_ge_0; try lia.
   auto_wf. 
   apply nz_Mixed_State_aux_to_nz_Mix_State. inversion_clear H0.
   apply H5. 
       
Qed.

Lemma State_eval_dstate_reduced_meas_r{s e:nat}:forall s0 e0 s2 c (q:qstate s e) mu i F, 
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
rewrite H4.     simpl in H1'. 
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
 rewrite H8 in H6. rewrite Reduced_Zero in H6.
 destruct H6. reflexivity. assumption.
 inversion_clear H0. assumption.
 simpl. econstructor.
 apply State_eval_reduced_meas_r with  s2 e; try lia. simpl in H6.    
 intro.
 rewrite H7 in H6. rewrite Reduced_Zero in H6.
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
   apply QMeas_trace with s0 e0 i. intuition.
   lia. apply WWF_qstate_to_WF_qstate.
   inversion_clear H0. apply H7. assumption.
   assert(s_trace (c,q)>0)%R. unfold  s_trace.
   simpl. apply nz_mixed_state_Cmod_1. inversion_clear H0.
   apply H8. rewrite <- H7 in H8. rewrite H6 in H8.
   lra. lia. simpl. intros. apply mixed_super_ge_0; try lia.
   auto_wf. 
   apply nz_Mixed_State_aux_to_nz_Mix_State. inversion_clear H0.
   apply H5. 
       
Qed.


Ltac quan_solve c q:=
  try  match goal with 
  H:ceval_single ?x ?y ?z |-_ => inversion H; subst; clear H end;
  try  match goal with 
  H:ceval_single ?x [] ?z |-_ => inversion_clear H; try rewrite map2_nil_r  end;
  try  match goal with 
  H: existT ?a ?b ?c = existT ?x ?y ?z|-_ => apply inj_pair2_eq_dec in H end;
  try  match  goal with 
  H: existT ?a ?b ?c = existT ?x ?y ?z|-_ => apply inj_pair2_eq_dec in H; destruct H end;
  try apply Nat.eq_dec;  try rewrite d_reduced_map2;
  try  match goal with 
  H:State_eval_dstate ?x ?z |-_ => inversion_clear H end;
  assert(WF_dstate_aux [(c,q)]); try apply WF_state_dstate_aux;
  try inversion_clear Hw; try assumption;
  try  match goal with 
  H:dstate_Separ ?x ?y ?z ?k ?j|-_ => inversion H; subst; clear H end.
       

Ltac d_seman_app_solve s e  i :=
  try apply d_seman_app_aux; try  apply WF_d_reduced;
  try eapply WF_ceval  with _ _ ;
  try apply ceval_Qinit; try apply ceval_QUnit_One;
  try apply ceval_QUnit_Ctrl ; try match goal with
  H: big_app' ?f ?n ?mu'' |- _  => try apply (ceval_QMeas _ _ s e i mu''); try assumption end;
  try  match goal with 
  H:ceval_single ?x ?y ?z |-_ => try apply H end; try assumption;
  try apply WF_state_dstate_aux;
  try inversion_clear Hw; try assumption.


Lemma State_eval_dstate_reduced_l{s e:nat}: forall c s0 e0 s1 e1
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
   apply dstate_Separ_preserve with c1 ((sigma, rho) :: mu0)  F.
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
   simpl in *. assumption. inversion_clear H0. clear H8. 
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
  eapply dstate_Separ_preserve; try lia.  apply H1_0. apply H8. apply H3. 
  left. assumption.  
  eapply (IHc s0 e0); try apply H1_0; try  lia; try assumption.
   rewrite d_reduced_map2. 
   apply d_seman_app_aux. 
   apply WF_d_reduced. lia. assumption.
   apply WF_d_reduced. lia. assumption.
   apply IHceval_single3; try reflexivity; try assumption.
   eapply dstate_Separ_preserve; try lia; try apply H1_0; try assumption. 
   apply H3. left. assumption.   
   eapply (IHc s0 e0); try apply H1_0; try lia; try assumption.  
   inversion_clear H5.  
   simpl. econstructor. assumption. econstructor.
   apply IHceval_single1; try assumption. 
   inversion_clear H2. assumption. inversion_clear H5. destruct p. simpl.
   assumption.
   inversion_clear H0. clear H9. 
   assert( WF_dstate_aux [(sigma, rho)]). apply WF_state_dstate_aux. assumption.
   assert(WF_dstate_aux mu' ).
   apply WF_ceval with <{ while b do c end }> mu; try assumption.
   assert( dstate_Separ [(sigma, rho)] s0 e0 s1 e1). inversion_clear H2.
   econstructor; try assumption. apply H13. apply H14. apply H15. econstructor. 
   destruct mu.  inversion_clear H6. rewrite map2_nil_r. 
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
       

destruct mu.    quan_solve c q. 

try econstructor;try econstructor;
try rewrite (Reduced_QInit_r c _ _ _  s s2); try assumption;
try econstructor; try reflexivity; try assumption; try lia; try econstructor.

dom_solve. dom_solve.

quan_solve c q. 

d_seman_app_solve s e i.   

dom_solve.  

try econstructor;try econstructor;
try rewrite (Reduced_QInit_r c _ _ _  s s2); try assumption;
try econstructor; try reflexivity; try assumption; try lia; try econstructor.

dom_solve. dom_solve. 

try  match goal with 
  IHmu: _ |-_ =>
  apply IHmu; destruct p; try assumption end.  



 }  }

{induction mu; intros mu' F Hs Hw; intros.
{inversion  H; subst. intuition.  }
 {destruct a.
 
 destruct mu.    quan_solve c q. 

try econstructor;try econstructor;
try rewrite (Reduced_QUnit_one_r c _ _ _ _ s s2); try assumption;
try econstructor; try reflexivity; try assumption; try lia; try econstructor.

simpl in H4. apply subset_Qsys in H4; try lia.  
simpl in H. lia.  

simpl in *. apply subset_Qsys in H2; try lia. 
apply H. apply H.

quan_solve c q. 

d_seman_app_solve s e i. 

dom_solve. dom_solve. simpl.   

try econstructor;try econstructor;
try rewrite (Reduced_QUnit_one_r c _ _ _  _ s s2); try assumption;
try econstructor; try reflexivity; try assumption; try lia; try econstructor.

dom_solve. dom_solve. dom_solve. dom_solve.

try  match goal with 
  IHmu: _ |-_ =>
  apply IHmu; destruct p; try assumption end. 
  }  }


{induction mu; intros mu' F Hs Hw; intros.
{inversion  H; subst. intuition.  }
 {destruct a.
 
 destruct mu.    quan_solve c q. 

try econstructor;try econstructor;
try rewrite (Reduced_QUnit_Ctrl_r c _ _ _ _ _ _ s s3); try assumption;
try econstructor; try reflexivity; try assumption; try lia; try econstructor.

simpl in *. dom_solve.   
simpl in *. 
apply subset_union in H2.
apply subset_union in H4.
destruct H2. destruct H4.  
dom_solve. apply H. apply H.

quan_solve c q. 

d_seman_app_solve s e i. 

dom_solve. dom_solve. simpl.   

try econstructor;try econstructor;
try rewrite (Reduced_QUnit_Ctrl_r c _ _ _  _ _ _ s s3); try assumption;
try econstructor; try reflexivity; try assumption; try lia; try econstructor.

dom_solve. dom_solve. dom_solve. dom_solve.

try  match goal with 
  IHmu: _ |-_ =>
  apply IHmu; destruct p; try assumption end. 
  }  }

{induction mu; intros mu' F Hs Hw; intros.
{inversion  H; subst. intuition.  }
 {
  destruct a.
 
 destruct mu.    quan_solve c q. 

 eapply (State_eval_dstate_reduced_meas_l s0 e0 _ c _ _ i); try apply H3; try assumption;  try lia;
 try econstructor; try reflexivity; try assumption; try lia; try econstructor.
 dom_solve. dom_solve. dom_solve.

quan_solve c q. 


d_seman_app_solve s e i; try apply H5. eapply (ceval_QMeas  c  _ s0 e0 i); try apply H13; try lia.
dom_solve. apply H12. 
 eapply (State_eval_dstate_reduced_meas_l s0 e0 _ c _ _ i); try apply H3; try assumption;  try lia;
 try econstructor; try reflexivity; try assumption; try lia; try econstructor.
 dom_solve. dom_solve. dom_solve. 
 try  match goal with 
  IHmu: _ |-_ =>
  apply IHmu; destruct p; try assumption end. 
 }  }
Qed.





Lemma State_eval_dstate_reduced_r{s e:nat}: forall c s0 e0 s1 e1
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
   intros. rewrite<-H7 in *.
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
   apply dstate_Separ_preserve with c1 ((sigma, rho) :: mu0)  F. inversion_clear H0.
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
   destruct mu. inversion H12;subst.
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

   destruct mu. inversion H12;subst.
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
simpl in *. assumption.  inversion_clear H0. clear H8. 
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
eapply dstate_Separ_preserve. inversion_clear H2. try lia.   apply H1_0. apply H8. apply H3. 
right. assumption.  
eapply (IHc _ _ s1 e1); try apply H1_0; try  lia; try assumption.
rewrite d_reduced_map2. 
apply d_seman_app_aux. 
apply WF_d_reduced. lia. assumption.
apply WF_d_reduced. lia. assumption.
apply IHceval_single3; try reflexivity; try assumption.
eapply dstate_Separ_preserve.  inversion_clear H2. try lia.  try apply H1_0; try assumption. 
assumption. apply H3. right. assumption.   
eapply (IHc _ _ s1 e1); try apply H1_0; try lia; try assumption.  
inversion_clear H5.  
simpl. econstructor. assumption. econstructor.
apply IHceval_single1; try assumption. 
inversion_clear H2. assumption. inversion_clear H5. destruct p. simpl.
assumption.
inversion_clear H0. clear H9. 
assert( WF_dstate_aux [(sigma, rho)]). apply WF_state_dstate_aux. assumption.
assert(WF_dstate_aux mu' ).
apply WF_ceval with <{ while b do c end }> mu; try assumption.
assert( dstate_Separ [(sigma, rho)] s0 e0 s1 e1). inversion_clear H2.
econstructor; try assumption. apply H13. apply H14. apply H15. econstructor.
destruct mu.  inversion_clear H6. rewrite map2_nil_r. 
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
       

destruct mu.    quan_solve c q. 

try econstructor;try econstructor;
try rewrite (Reduced_QInit_l c _ _ _ _ _ s2 e); try assumption;
try econstructor; try reflexivity; try assumption; try lia; try econstructor.

dom_solve. dom_solve.

quan_solve c q. 

d_seman_app_solve s e i.   

dom_solve.  

try econstructor;try econstructor;
try rewrite (Reduced_QInit_l c _ _ _ _ _ s2 e); try assumption;
try econstructor; try reflexivity; try assumption; try lia; try econstructor.

dom_solve. dom_solve. 

try  match goal with 
  IHmu: _ |-_ =>
  apply IHmu; destruct p; try assumption end.  



 }  }

{induction mu; intros mu' F Hs Hw; intros.
{inversion  H; subst. intuition.  }
 {destruct a.
 
 destruct mu.    quan_solve c q. 

try econstructor;try econstructor;
try rewrite (Reduced_QUnit_one_l c _ _ _  _ _ _ s2 e); try assumption;
try econstructor; try reflexivity; try assumption; try lia; try econstructor.

simpl in H4. apply subset_Qsys in H4; try lia.  
simpl in H. lia.  

simpl in *. apply subset_Qsys in H2; try lia. 
apply H. apply H.

quan_solve c q. 

d_seman_app_solve s e i. 

dom_solve. dom_solve. simpl.   

try econstructor;try econstructor;
try rewrite (Reduced_QUnit_one_l c _ _ _  _ _ _ s2 e); try assumption;
try econstructor; try reflexivity; try assumption; try lia; try econstructor.

dom_solve. dom_solve. dom_solve. dom_solve.

try  match goal with 
  IHmu: _ |-_ =>
  apply IHmu; destruct p; try assumption end. 
  }  }


{induction mu; intros mu' F Hs Hw; intros.
{inversion  H; subst. intuition.  }
 {destruct a.
 
 destruct mu.    quan_solve c q. 

try econstructor;try econstructor;
try rewrite (Reduced_QUnit_Ctrl_l c _ _ _ _ _  _ _ _  s3 e); try assumption;
try econstructor; try reflexivity; try assumption; try lia; try econstructor.

simpl in *. dom_solve.   
simpl in *. 
apply subset_union in H2.
apply subset_union in H4.
destruct H2. destruct H4.  
dom_solve. apply H. apply H.

quan_solve c q. 

d_seman_app_solve s e i. 

dom_solve. dom_solve. simpl.   

try econstructor;try econstructor;
try rewrite (Reduced_QUnit_Ctrl_l c _ _ _ _ _  _ _ _  s3 e); try assumption;
try econstructor; try reflexivity; try assumption; try lia; try econstructor.

dom_solve. dom_solve. dom_solve. dom_solve.

try  match goal with 
  IHmu: _ |-_ =>
  apply IHmu; destruct p; try assumption end. 
  }  }

{induction mu; intros mu' F Hs Hw; intros.
{inversion  H; subst. intuition.  }
 {
  destruct a.
 
 destruct mu.    quan_solve c q. 

 eapply (State_eval_dstate_reduced_meas_r s0 e0 _ c _ _ i); try apply H3; try assumption;  try lia;
 try econstructor; try reflexivity; try assumption; try lia; try econstructor.
 dom_solve. dom_solve. 

quan_solve c q. 


d_seman_app_solve s e i; try apply H5. eapply (ceval_QMeas  c  _ s0 e0 i); try apply H13; try lia.
dom_solve. apply H12. 
 eapply (State_eval_dstate_reduced_meas_r s0 e0 _ c _ _ i); try apply H3; try assumption;  try lia;
 try econstructor; try reflexivity; try assumption; try lia; try econstructor.
 dom_solve. dom_solve. 
 try  match goal with 
  IHmu: _ |-_ =>
  apply IHmu; destruct p; try assumption end. 
 }  }
Qed.



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


(*-------------------------------------------rule_f--------------------------------------------------*)
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
  apply QMeas_trace with s e i; try assumption; try lia. 
  apply WWF_qstate_to_WF_qstate. 
  inversion_clear H0.  assumption.  
  assert(s_trace (sigma,rho)>0)%R. unfold  s_trace.
  simpl. apply nz_mixed_state_Cmod_1. inversion_clear H0.
  apply H8. rewrite<- H7 in H8. rewrite H6 in H8.
  lra. 
Qed.

Ltac rule_f_classic_sovle s0 e0 c q i mu:=
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
 [try apply rule_f_classic_meas with s0 e0 c q i; try assumption | ];
 try apply (@Pure_free_eval' s0 e0 s0 e0) with q; try assumption;
assert(WF_dstate_aux [(c,q)]); try apply WF_state_dstate_aux;
try inversion_clear Hw; try assumption;
 d_seman_app_solve s0 e0 i; try dom_solve;
[ try match goal with 
H : big_app' ?f ?n ?mu |-_ => 
apply rule_f_classic_meas with s0 e0 c q i
end ; try assumption; try econstructor  ];
try apply (@Pure_free_eval' s0 e0 s0 e0) with q; try assumption; try econstructor;
try match goal with 
  IHmu: _ |-_ =>
 apply IHmu; try left; try assumption end. 


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
-induction mu; intros. inversion_clear H3. assumption.
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
-induction mu; intros. inversion_clear H3. assumption.
  destruct a0. inversion H3; subst. assumption.  
-intros. simpl in H0. rewrite union_empty in H0.
 simpl in H4. rewrite inter_union_dist in H4.
 apply union_empty in H4. 
 apply ceval_seq_1 in H3. destruct H3.
 apply IHc2 with x; try assumption; try apply H3; try apply H4.  destruct H0; [ left|right];  apply H0. 
 apply WF_ceval with c1 mu; try assumption; try apply H3. 
 apply IHc1 with mu; try assumption; try apply H3; try apply H4. destruct H0; [ left|right];  apply H0.
- induction mu; intros. inversion_clear H3. assumption. 
   inversion_clear H2. inversion_clear  H1.
   inversion H3; subst; destruct mu;
  [inversion_clear H15| | inversion_clear H15|]; try rewrite map2_nil_r.
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
induction H3;  try inversion Horig; subst. assumption. 
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

destruct mu. inversion_clear H5. rewrite map2_nil_r. assumption.
assert( WF_dstate_aux [(sigma, rho)]).
apply WF_state_dstate_aux. inversion_clear H1. assumption.
assert( WF_dstate_aux mu'). inversion_clear H1.
eapply WF_ceval; try apply H5; try assumption.  
apply d_seman_app_aux; try assumption.  
inversion_clear H2. econstructor. assumption. econstructor.
inversion_clear H1. inversion_clear H2.
apply IHceval_single; try reflexivity; try assumption.

{  induction mu; intros mu2 F Hs Hm Hw; intros. 
{ inversion_clear H0. assumption. }
 {destruct Hm. destruct a.
 rule_f_classic_sovle s0 e0 c q s mu.
 simpl in H2. inversion_clear H0.
 apply Qsys_to_Set_not_empty in H2; try lia. 
 dom_solve. 
}  }
-{  induction mu; intros mu2 F Hs Hm Hw; intros.
{ inversion_clear H0. assumption.  }
{destruct Hm. destruct a.

 rule_f_classic_sovle s0 e0 c q s mu.  
inversion_clear H0.
apply Qsys_to_Set_not_empty in H2; try lia. dom_solve. 
} }

  {  induction mu; intros mu2 F Hs Hm Hw; intros.
  {  inversion_clear H0. assumption. }
  {destruct Hm. destruct a. 
  rule_f_classic_sovle s e c q s mu.
  inversion_clear H0. simpl in H2. rewrite union_empty in H2. 
  destruct H2.
  apply Qsys_to_Set_not_empty in H2; try lia. dom_solve. 
} }

{induction mu; intros mu2 F Hs Hm Hw; intros.
{  inversion_clear H0. assumption.  }
{destruct Hm. destruct a.

quan_solve c q.
apply d_seman_app_aux. 
eapply WF_ceval; try 
eapply (ceval_QMeas _ _ s e i mu''). 
apply H. dom_solve. apply H11. 
eapply WF_ceval; try apply H10. 
assumption. 

apply rule_f_classic_meas with s e c q i; try assumption.
dom_solve.

apply IHmu; try assumption. left. try assumption.

destruct mu. simpl. eapply State_eval_WF_formula.
apply H0. 
apply H3.

inversion_clear H0.
 apply Qsys_to_Set_not_empty in H2; try lia. 
 dom_solve. 
 }}  
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

Lemma subset_trans:
forall x y z,
 NSet.Subset x y ->
 NSet.Subset y z ->
 NSet.Subset x z.
Proof. intros. unfold NSet.Subset in *.
       intros. intuition.
       
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


Lemma rule_f: forall  F c s e (mu mu':list (cstate * qstate s e )) ,
(Considered_Formula F /\ ~NSet.Equal (snd (Free_state F)) (NSet.empty) )->
WF_dstate_aux mu ->
State_eval_dstate F mu->
ceval_single c mu mu'-> 
~NSet.Equal (snd (MVar c)) NSet.empty ->
NSet.Equal (NSet.inter (fst (Free_state F)) (fst (MVar c))) (NSet.empty) ->
(snd (option_free (Free_State F)) <= (option_nat (NSet.min_elt (snd (MVar c))))\/ 
(option_nat (NSet.max_elt (snd (MVar c)))) < fst (option_free (Free_State F))) ->
State_eval_dstate F mu'.
Proof. 
    intros F c s e mu mu'. intros.
    destruct mu.  inversion_clear H2. assumption. 
   pose H2 as H6.
    apply (@ceval_single_dom s e c  (p::mu) mu') in H6; try assumption.
    apply Subset_min_max_In in H6; try lia; try assumption.  
    assert((Free_State F) <> None). apply option_eqb_neq. apply Free_State_not_empty; apply H.
    destruct H.
    pose(Considered_Formula_not_empty_dom F H H7) as H''.    
  
    destruct H5. 
   
    assert(s <= fst (option_free (Free_State F)) /\
    fst (option_free (Free_State F)) <= fst (option_free (Free_State F)) /\
    fst (option_free (Free_State F)) <= snd (option_free (Free_State F)) /\
    snd (option_free (Free_State F)) <=
    option_nat (NSet.max_elt (snd (MVar c))) + 1 <= e).
    split. apply dstate_eval_dom in H1. 
    destruct H1. destruct H7. assumption.  apply H1. discriminate. 
    split. lia. split. lia.  split.
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
    remember ((d_reduced (p::mu)
    (fst (option_free (Free_State F)))
    (option_nat (NSet.max_elt (snd (MVar c))) + 1))).
    apply State_eval_dstate_reduced_r with c (snd (option_free (Free_State F)))
    (option_nat (NSet.max_elt (snd (MVar c))) + 1) l0; try assumption; try lia. 
    rewrite Heql0. apply WF_d_reduced; try lia; try assumption.  
    rewrite Heql. rewrite Heql0. 
    apply Reduced_ceval_swap; try lia; try assumption.
    apply subset_trans with ((Qsys_to_Set 
    (option_nat (NSet.min_elt (snd (MVar c))))
    (option_nat (NSet.max_elt (snd (MVar c))) + 1))).
    apply In_min_max. apply  Qsys_subset .  split.
    apply le_trans with (snd (option_free (Free_State F))).
    lia. assumption. split. 
    apply le_trans with  (option_nat (NSet.max_elt (snd (MVar c)))).
    apply min_le_max. lia. lia.   
    rewrite Heql0. apply State_eval_dstate_separ_r; try assumption; try split; [apply H |try lia]. 

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
    apply WF_ceval with c (p::mu). 
    assumption. assumption.

    assert(s <= option_nat (NSet.min_elt (snd (MVar c))) /\
    option_nat (NSet.min_elt (snd (MVar c))) <=
    fst (option_free (Free_State F)) /\
    fst (option_free (Free_State F)) < snd (option_free (Free_State F)) /\ snd (option_free (Free_State F)) <= e).
    split. lia. 
    split. apply le_trans with (option_nat  (NSet.max_elt (snd (MVar c)))).
    apply min_le_max. lia.  split. assumption. 
    apply dstate_eval_dom in H1. destruct H1. rewrite H1 in *.
    simpl in *.  lia. 
    apply H1. discriminate.  
    rewrite (State_dstate_free_eval _ _ (fst (option_free (Free_State F)))
    (snd (option_free (Free_State F)))); try lia. 
    rewrite <-(d_reduced_assoc   mu' 
    (option_nat (NSet.min_elt (snd (MVar c))))
    (snd (option_free (Free_State F)))); try lia.   
    remember ((d_reduced mu'
    (option_nat (NSet.min_elt (snd (MVar c))))
    (snd (option_free (Free_State F))))).
    remember ((d_reduced (p::mu)
    (option_nat (NSet.min_elt (snd (MVar c))))
    (snd (option_free (Free_State F))))).
    apply State_eval_dstate_reduced_l with c (option_nat (NSet.min_elt (snd (MVar c))))
    (fst (option_free (Free_State F))) l0; try assumption; try lia.
    rewrite Heql0. apply WF_d_reduced; try lia; try assumption.  
    rewrite Heql. rewrite Heql0. 
    apply Reduced_ceval_swap; try lia; try assumption.
    apply subset_trans with ((Qsys_to_Set
    (option_nat (NSet.min_elt (snd (MVar c))))
       (option_nat (NSet.max_elt (snd (MVar c))) + 1))).
    apply In_min_max. apply Qsys_subset.
    split. lia. split. 
    

    apply le_trans with  (option_nat (NSet.max_elt (snd (MVar c)))).
    apply min_le_max. lia. lia. 
    rewrite Heql0. apply State_eval_dstate_separ_l; try assumption; try split; [apply H |try lia]; try apply H8.
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
    apply WF_ceval with c (p::mu). 
    assumption. assumption.

Qed.


Import Sorted.
Theorem rule_qframe: forall (F1 F2 F3: State_formula) c,
NSet.Equal (NSet.inter (snd (Free_state F2)) (snd (Free_state F3))) NSet.empty ->
Considered_Formula F3->
({{F1}} c {{F2}}) 
/\ (NSet.Equal (NSet.inter (fst (Free_state F3)) (fst (MVar c))) (NSet.empty) )
/\ ((snd (option_free (Free_State F3)) <= (option_nat (NSet.min_elt (snd (MVar c))))\/ 
(option_nat (NSet.max_elt (snd (MVar c)))) < fst (option_free (Free_State F3))))
-> {{F1 ⊙ F3}} c {{F2 ⊙ F3}}. 
Proof.  unfold hoare_triple. intros F1 F2 F3 c HF3. intros. destruct H0. 
        
        assert(StateMap.this mu= [] \/ StateMap.this mu<>[] ) as H'.
        apply Classical_Prop.classic. destruct H' as[H'| H'].
        pose H2. apply sat_assert_odot in s0. destruct s0.
        eapply H0 in H4; try apply H1. 
        rewrite sat_Assert_to_State in *.
        apply sat_State_WF_formula in H2. 
        apply sat_State_WF_formula in H4.
        inversion_clear H1. rewrite H' in *. 
        inversion H7; subst. 
        rewrite <-sat_Assert_to_State. 
        apply sat_Assert_empty. simpl. split. econstructor.
        simpl in H2.
        simpl. split; try assumption. split; try apply  H2; try assumption.
        econstructor. discriminate. auto. 
       
        assert(sat_Assert mu F1 -> sat_Assert mu' F2).
        apply H0. assumption. 
        destruct mu as [mu IHmu].
        destruct mu' as [mu' IHmu']. 
        
        inversion_clear H1. simpl in *.
        repeat rewrite sat_Assert_to_State in *.
        inversion_clear H2.  simpl in *.

        econstructor. eapply WF_ceval. apply H1. apply H6. 
        simpl in *. 
        rewrite State_eval_odot in H7.
        rewrite State_eval_odot.
         destruct H7. destruct H7.
        split. 
        assert(sat_Assert (StateMap.Build_slist IHmu') F2).
        apply H0 with (StateMap.Build_slist IHmu).
        apply E_com. assumption. assumption.  rewrite sat_Assert_to_State.
        econstructor. assumption. assumption.
        rewrite sat_Assert_to_State in *.
        inversion_clear H9. assumption.
        split. 
      
        destruct (option_edc (Free_State F3) None).
        apply rule_f_classic with c mu; try left;
        try assumption; try apply H3. 

        assert(NSet.Equal (snd (MVar c)) NSet.empty \/ ~NSet.Equal (snd (MVar c)) NSet.empty ).
        apply Classical_Prop.classic.  
        destruct H10. apply rule_f_classic with c mu; try right; try assumption.
        try apply H3. 

        apply rule_f  with  c mu; try assumption.
        split. assumption.
        apply Free_State_not_empty. assumption.
        rewrite <-option_eqb_neq. intuition. apply H3.
        apply H3. assumption.
Qed.


Theorem rule_qframe': forall (F1 F2 F3: State_formula) c,
NSet.Equal (NSet.inter (snd (Free_state F2)) (snd (Free_state F3))) NSet.empty ->
Considered_Formula F3->
({{F1}} c {{F2}}) 
/\ (NSet.Equal (NSet.inter (fst (Free_state F3)) (fst (MVar c))) (NSet.empty) )
/\ ((snd (option_free (Free_State F3)) <= (option_nat (NSet.min_elt (snd (MVar c))))\/ 
(option_nat (NSet.max_elt (snd (MVar c)))) < fst (option_free (Free_State F3))))
->  {{F3 ⊙ F1}} c {{F3 ⊙ F2}}.
Proof. intros.
 eapply rule_conseq. apply rule_qframe.
 apply H. assumption. split. apply H1.   apply H1. 
 apply rule_OdotC.
 apply rule_OdotC.
Qed.


Theorem rule_qframe_P: forall (P1 P2 P3: Pure_formula) c,
({{P1}} c {{P2}}) /\ (NSet.Equal (NSet.inter (fst (Free_state P3)) (fst (MVar c))) NSet.empty) 
->  {{P3 /\p P1}} c {{P3 /\p P2}}.
Proof.
intros. eapply rule_conseq; try apply rule_OdotO. 
apply rule_qframe'. simpl. apply inter_empty. left. reflexivity.
simpl. auto. simpl. split. apply H. split. apply H. left. lia.
Qed. 