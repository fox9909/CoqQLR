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
From Quan Require Import QState_L.
From Quan Require Import QIMP_L.
From Quan Require Import QAssert_L.
From Quan Require Import Reduced.
From Quan Require Import QRule_E_L.
Require Import Basic.

Local Open Scope com_scope.

Definition hoare_triple
   (P:Assertion) (c : com) (Q : Assertion) : Prop :=
            forall (s e :nat)  (mu : dstate s e) (mu': dstate s e),
               ceval c mu mu' ->
               sat_Assert  mu P ->
               sat_Assert  mu' Q.
Declare Scope rule_scope.
Notation "{{ P }}  c  {{ Q }}" :=
(hoare_triple P c Q) (at level 90, c custom com at level 99)
               : rule_scope.
Local Open Scope rule_scope.


(*Skip*)
Theorem rule_skip : forall (D: Assertion), {{D}} skip {{D}}.
Proof. unfold hoare_triple. intros. 
       inversion_clear H. apply ceval_skip_1 in H2.
       apply sat_Assert_dstate_eq with mu.
       unfold dstate_eq. intuition.
       intuition. 
Qed.


(*Assgn*)
Theorem rule_PAssgn_aux :  forall (P:Pure_formula) (i:nat) ( a:aexp) 
(s e:nat) (mu : list (cstate * qstate s e)) (mu': list (cstate * qstate s e)),
WF_dstate_aux mu->
ceval_single (<{i := a}>) mu mu' ->
State_eval_dstate (PAssn i a P) mu->
State_eval_dstate P mu'.
Proof. intros P i a s e mu. induction mu; intros; inversion H; subst.
  --simpl in H0. inversion H0; subst. simpl in *. auto. 
  --  destruct mu. inversion H0; subst. inversion_clear H10; subst.
     simpl. econstructor.  simpl in H1. inversion_clear H1.
     assumption. apply Forall_nil.
     destruct a0. inversion_clear H0. 
     apply d_seman_app_aux.
     apply WF_state_dstate_aux.  
     apply WF_state_eq with (c,q). reflexivity.
     assumption. apply WF_ceval with (<{ i := a }>)
      ((p :: mu)). assumption. assumption.
    inversion_clear H1. simpl in H0. simpl.
    econstructor. assumption. apply Forall_nil.
     apply IHmu. intuition. assumption. 
     inversion_clear H1. apply State_eval_dstate_Forall.
     discriminate.  assumption.
Qed. 


Theorem rule_PAssgn: forall (P:Pure_formula) (i:nat) ( a:aexp),
             {{PAssn i a P}} i := a {{P}}.
Proof. unfold hoare_triple;
       intros F X a s e (mu,IHmu) (mu', IHmu').
       intros. 
       inversion_clear H; simpl in H2.
       rewrite sat_Assert_to_State in *.
       inversion_clear H0.
       apply sat_F. eapply WF_ceval. apply H1. apply H2. 
       apply rule_PAssgn_aux with X a mu.
       intuition. intuition. assumption. 
Qed. 



Theorem rule_SAssn_aux :  forall (F:State_formula) (i:nat) ( a:aexp) 
(s e:nat) (mu : list (cstate * qstate s e)) (mu': list (cstate * qstate s e)),
WF_dstate_aux mu->
ceval_single (<{i := a}>) mu mu' ->
State_eval_dstate (SAssn i a F) mu->
State_eval_dstate F mu'.
Proof. intros P i a s e mu. induction mu; intros; inversion H; subst.
  --simpl in H0. inversion H0; subst.  simpl. auto. 
  -- destruct mu. inversion H0; subst. inversion_clear H10; subst.
     simpl. econstructor.  simpl in H1. inversion_clear H1.
     assumption. apply Forall_nil.
     destruct a0. inversion_clear H0. 
     apply d_seman_app_aux.
     apply WF_state_dstate_aux.  
     apply WF_state_eq with (c,q). reflexivity.
     assumption. apply WF_ceval with (<{ i := a }>)
      ((p :: mu)). assumption. assumption.
    inversion_clear H1. simpl in H0. simpl.
    econstructor. assumption. apply Forall_nil.
     apply IHmu. intuition. assumption. 
     inversion_clear H1. apply State_eval_dstate_Forall.
     discriminate.  assumption.
Qed. 

Theorem rule_SAssgn: forall (F:State_formula) (i:nat) ( a:aexp),
             {{SAssn i a F}} i := a {{F}}.
Proof. unfold hoare_triple;
       intros F X a s e (mu,IHmu) (mu', IHmu').
       intros. 
       inversion_clear H; simpl in H2.
       rewrite sat_Assert_to_State in *.
       inversion_clear H0.
       apply sat_F. eapply WF_ceval. apply H1. apply H2. 
       apply rule_SAssn_aux with X a mu.
       intuition. intuition. assumption. 
Qed.

Lemma ceval_single_1{s e:nat}: forall (mu mu':list (state s e)) X a,
ceval_single <{ X := a }> mu mu'->
mu'= d_update_cstate_aux X a mu .
Proof. induction mu;  intros;
       inversion H; subst.
       simpl. reflexivity.
       unfold d_update_cstate_aux.
       f_equal. apply IHmu.
       assumption. 
Qed.


Theorem rule_assgn: forall (D:Assertion) (i:nat) ( a:aexp),
             {{Assn_sub i a D}} i := a {{D}}.
Proof. unfold hoare_triple;
       intros F X a s e (mu,IHmu) (mu', IHmu').
       intros. 
       inversion_clear H; simpl in H2.
       apply ceval_single_1 in H2.
       apply sat_Assert_dstate_eq with 
       ({|
        StateMap.this := d_update_cstate_aux X a mu;
        StateMap.sorted := d_update_cstate_sorted X a mu IHmu
      |}).
       unfold dstate_eq. simpl. intuition. 
       inversion_clear H0. unfold d_update_cstate in H.
       simpl in H. assumption.
Qed.


(*Clet*)
Lemma bool_true: forall (a b:nat),
a=b-> (a =? b =true).
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
       inversion H2; subst. 
       econstructor. econstructor.
        simpl in *. auto.
       unfold x0.
       rewrite seman_find. split.
       assumption. split. simpl. auto.
       intros. simpl.
       rewrite bool_true. intuition.
       reflexivity.
Qed.


(*Seq*)
Theorem rule_seq : forall (P Q R:Assertion) c1 c2,
              {{P}} c1 {{Q}} ->
              {{Q}} c2 {{R}} ->
              {{P}} c1; c2 {{R}}.
Proof.   unfold hoare_triple.  
         intros P Q R2 c1 c2 H1 H2 s e (mu,IHmu) (mu',IHmu').
         intros. inversion H;subst. 
         simpl in H4.
         inversion H4;subst. 
         apply H2 with ({| StateMap.this := []; StateMap.sorted := IHmu |}) .
         econstructor. econstructor. econstructor. 
         simpl in H5. apply H5. simpl in H6. 
         apply subset_union in H6. apply H6.
         apply H1 with ({| StateMap.this := []; StateMap.sorted := IHmu |}) .
         econstructor. econstructor. econstructor.
         simpl in H5. apply H5. simpl in H6. 
         apply subset_union in H6. apply H6.
         assumption.
         assert(WF_dstate_aux mu1). 
         unfold WF_dstate in H3. simpl in H3.
         apply (WF_ceval _ _ _ H3 H7).
         assert(Sorted.Sorted (StateMap.Raw.PX.ltk (elt:=qstate s e)) mu1).
         apply (ceval_sorted _ _ _ IHmu H7).
         apply H2 with (StateMap.Build_slist H6).
         apply E_com. intuition. intuition.
         simpl. intuition. intuition.
         apply H1 with (StateMap.Build_slist IHmu).
         apply E_com.  intuition. intuition. 
         simpl. intuition.  
Qed.

(*Conseq*)
Theorem rule_conseq : forall (P P' Q Q': Assertion) c,
           {{P'}} c {{Q'}} ->
           (P ->> P') -> (Q'->> Q) ->
           {{P}} c {{Q}}.
Proof.  unfold hoare_triple. intros. 
       unfold assert_implies in H1.
       unfold assert_implies in H0. 
       apply H1. apply H with mu.
       intuition. apply H0. intuition.
Qed.


Theorem rule_conseq_l : forall (P P' Q : Assertion) c,
           (P ->> P') ->
           {{P'}} c {{Q}} ->
           {{P}} c {{Q}}.
Proof. intros. eapply rule_conseq. apply H0. assumption.
apply implies_refl.
 Qed.


Theorem rule_conseq_r : forall (P Q Q' : Assertion) c,
(Q'->> Q) ->
{{P}} c {{Q'}} ->
{{P}} c {{Q}}.
Proof. intros. eapply rule_conseq. apply H0. 
apply implies_refl. assumption. Qed.

Theorem rule_conseq_l' : forall (P P' Q : Assertion) c,
{{P'}} c {{Q}} ->
(P ->> P') ->
{{P}} c {{Q}}.
Proof. intros. eapply rule_conseq. apply H. assumption.
apply implies_refl. Qed.

Theorem rule_conseq_r' : forall (P Q Q' : Assertion) c,
{{P}} c {{Q'}} ->
(Q'->> Q) ->
{{P}} c {{Q}}.
Proof. intros. eapply rule_conseq. apply H. 
apply implies_refl. assumption. Qed.   


(*Conj*)
Theorem rule_conj: forall (F1 F1' F2 F2': State_formula) c,
             {{F1}} c {{F1'}} 
             -> {{F2}} c {{F2'}}
             -> {{F1 /\s F2}} c {{F1' /\s F2'}}.
Proof. unfold hoare_triple. intros.
       apply sat_assert_conj.
       apply sat_assert_conj in H2.
       split.
       apply H with mu. intuition. intuition.
       apply H0 with mu. intuition. intuition.
Qed.

(*Absurd*)

Theorem rule_Absurd: forall D c, 
WF_assert D
-> {{BFalse}} c {{D}} .
Proof. intros. unfold hoare_triple. 
       intros . destruct mu as[mu IHmu].
       destruct mu' as[mu' IHmu'].
       inversion_clear H0. simpl in *.
       destruct mu. inversion H3; subst.
       apply sat_Assert_empty. assumption.
       reflexivity.
       rewrite sat_Assert_to_State in H1.
       inversion_clear H1.
       simpl in H4. inversion_clear H4. destruct H1.  
Qed.


(*Sum*)
Lemma big_add_ceval{s e:nat}: forall p_n (mu_n mu_n':list (dstate s e))
(nF1 nF2:npro_formula)  c (mu mu':dstate s e),
length mu_n =length nF1 -> length p_n= length nF1->
ceval c mu mu' ->
(Forall_two ( fun mu_i pF_i => 0 < fst pF_i -> sat_State mu_i (snd pF_i) /\ d_trace mu_i = d_trace mu) mu_n (npro_to_pro_formula nF1 p_n)) ->
(Forall_two ( fun i j =>ceval c i j) mu_n mu_n')->
(Forall_two ( fun (i j: State_formula) =>{{i}} c {{ j}}) nF1 nF2)->
(Forall_two ( fun mu_i pF_i=> 0 < fst pF_i -> sat_State mu_i (snd pF_i) /\ d_trace mu_i = d_trace mu') mu_n' (npro_to_pro_formula nF2 p_n)).
Proof. induction p_n; destruct mu_n; destruct mu_n'; destruct nF1; destruct nF2; intros;  try econstructor;
inversion_clear H2; inversion_clear H3; inversion_clear H4. 
 simpl in *.  
 unfold hoare_triple in *. 
 econstructor. intros. 
 rewrite <-sat_Assert_to_State in *.  eapply H3. apply H2. apply H5. assumption.
 apply ceval_trace_eq' in H1.   apply ceval_trace_eq' in H2. rewrite H2. rewrite H1.
 apply H5. assumption.   apply WWF_dstate_to_WF_dstate. eapply WF_sat_State. apply H5. assumption.
 apply WWF_dstate_to_WF_dstate. inversion_clear H1. assumption. 
 eapply IHp_n.  
 injection H.  intuition. apply H4. injection H0. intuition. apply H1. apply H6. 
 assumption. assumption. 
Qed.

Lemma Forall_ceval_trace{s e:nat}:forall c (mu_n mu_n':list (dstate s e)),
Forall (fun x  : dstate s e => WWF_dstate x) mu_n->
Forall_two (fun x y  => ceval c x y) mu_n mu_n'->
Forall_two (fun mu_i mu_j: dstate s e =>  d_trace mu_i = d_trace mu_j) mu_n mu_n'.
Proof. induction mu_n; intros; destruct mu_n'. econstructor. 
       inversion_clear H0. inversion_clear H0.
       inversion_clear H0.  inversion_clear H.
       econstructor.
       symmetry. 
       apply ceval_trace_eq' with c. assumption.
       assumption. apply IHmu_n; try assumption.
Qed.

Lemma Forall_two_Forall_impli{A :Type }:forall (P : A -> Prop) (Q:A-> A-> Prop) (f g:list A),
(forall i j, P i -> Q i j-> P j)->
(Forall_two Q f g)->
(Forall P f) -> (Forall P g).
Proof. induction f; intros; destruct g. econstructor. 
       inversion_clear H0. inversion_clear H0. 
       inversion_clear H0. inversion_clear H1.
      econstructor; try assumption.  apply H with a; try assumption.
       apply IHf. apply H. assumption. assumption.
Qed.

Import Ceval_Prop.
Theorem rule_sum: forall (nF1 nF2: npro_formula ) c  (p_n:list R),
            (Forall (fun x=> 0 < x %R) p_n)->
             length nF1 = length p_n -> 
             ( (Forall (fun x : State_formula => WF_formula x)) nF2)->
            ((Forall_two ( fun (i j: State_formula) => {{i}} c{{ j}} ) nF1 nF2))
         -> {{npro_to_pro_formula nF1 p_n}} c
            {{npro_to_pro_formula nF2 p_n}}.
Proof.  unfold hoare_triple. intros nF1 nF2 c p_n H'. intros.  
inversion_clear H3. inversion_clear H6.
 constructor.  inversion_clear H2. eapply WF_ceval. apply H6. apply H9. 
 econstructor;try rewrite (get_pro_formula_eq nF1);
 try rewrite <-(Forall_two_length_eq ( fun (i j: State_formula) => {{i}} c{{ j}} ) nF1 ); inversion_clear H5; 
 try assumption. rewrite pro_npro_inv. assumption.
 rewrite <-(Forall_two_length_eq (( fun (i j: State_formula)=>{{i}} c {{j}} )) nF1 _).
 assumption.
 assumption.

 rewrite get_pro_formula_p_n in *.

 assert(exists (mu_n': list (dstate s e)), 
 and (Forall_two ( fun i j=>ceval c i j ) mu_n mu_n')
 (dstate_eq mu' (big_dapp p_n mu_n'))).
 apply ceval_big_dapp with mu.
 assumption. inversion_clear H5.
  rewrite get_pro_formula_p_n in H9; try assumption.
  lra. assert( p_n = get_pro_formula (npro_to_pro_formula nF1 p_n)).
  rewrite get_pro_formula_p_n. reflexivity. assumption.
  rewrite H6. unfold get_pro_formula. 
  eapply Forall_two_map; try apply H8. simpl.  intros. apply WF_sat_State with (snd j).
  apply H9. assumption.  apply big_dapp'_length with mu'0.
  assumption. 
 apply dstate_eq_trans with mu'0. assumption.
 apply big_dapp_eq with p_n mu_n. assumption.
  apply big_dapp'_to_app. apply big_dapp'_length with mu'0.
  assumption.  assumption.
 assumption.
 destruct H6. destruct H6.
 econstructor.  rewrite get_pro_formula_p_n.
 assert(big_dapp' p_n x ((big_dapp p_n x))).
 apply big_dapp'_to_app. 
  rewrite <-(Forall_two_length_eq (( fun i j=>ceval c i j ))  mu_n).
  apply big_dapp'_length with mu'0. assumption. assumption.
  assumption.  apply H10.
 rewrite <-(Forall_two_length_eq (( fun (i j: State_formula)=>{{i}} c {{j}} )) nF1 _).
 assumption. assumption. assumption. 
 eapply big_add_ceval with mu_n nF1 c mu; try assumption. apply eq_trans with (length p_n).
 symmetry.
 apply big_dapp'_length with mu'0. assumption. symmetry.  assumption.
 symmetry. assumption. assumption.
Qed.

Local Open Scope R_scope.
(*Sum_pro*)
Definition pro_formula_scale (pF: pro_formula ) (p: R): pro_formula:= 
  map (fun i=> (p*(fst i), (snd i))) pF.

Fixpoint pro_formula_linear (pF:list pro_formula ) (p_n: list R): pro_formula:=
  match pF, p_n with 
  |[], [] =>[]
  |[], _ => []
  |_, [] => []
  |F :: pF', h::p' => (pro_formula_scale F h ) ++ (pro_formula_linear pF' p')
  end.


Lemma d_app_empty_r{s e:nat}: forall (mu:dstate s e), 
dstate_eq (d_app  mu (d_empty s e))  mu .
Proof. intros (mu , IHmu).
       unfold d_app. unfold d_empty.
       unfold StateMap.empty .
       unfold StateMap.Raw.empty.
       unfold StateMap.Raw.map2. unfold dstate_eq.
       simpl. apply map2_nil_r.
Qed.

Lemma get_pro_formula_scale: forall pF p,
get_pro_formula (pro_formula_scale pF p) =
map (fun x : R => (p * x)%R) (get_pro_formula pF).
Proof. induction pF;intros; try destruct a; simpl; try reflexivity.
 f_equal; auto. 
Qed.


Lemma get_pro_formula_app:forall pF1 pF2 p1 p2,
(get_pro_formula
  (pro_formula_scale pF1 p1 ++ pro_formula_scale pF2 p2))=
( map (fun x=> (p1* x)%R) (get_pro_formula pF1)) 
 ++(map (fun x=> (p2* x)%R) (get_pro_formula pF2)).
Proof. induction pF1. destruct pF2; intros; simpl.
  -reflexivity.
  -destruct p. simpl. 
   f_equal. apply get_pro_formula_scale.
  - intros. destruct a. simpl. f_equal.
    apply IHpF1.
Qed.

Lemma  big_dapp_app{ s e:nat}: forall (p1 p2: list R) (mu_n1 mu_n2: list (dstate s e)),
length p1= length mu_n1->
length p2= length mu_n2->
dstate_eq (big_dapp (p1 ++ p2) (mu_n1 ++ mu_n2))
(d_app (big_dapp p1 mu_n1) (big_dapp p2 mu_n2) ).
Proof. induction p1; intros. destruct mu_n1. simpl.
       apply dstate_eq_sym .
       apply d_app_empty_l.
       simpl in H.  lia.
       destruct mu_n1. simpl in H. lia.
       simpl. apply dstate_eq_trans with 
       ((d_app (d_scale_not_0 a d)
       (d_app (big_dapp p1 mu_n1) (big_dapp p2 mu_n2)) )) .
       apply d_app_eq. 
       apply dstate_eq_refl.
       apply IHp1. injection H. intuition.
       assumption.
       apply dstate_eq_sym.
       apply d_app_assoc'.
Qed.

Lemma  big_dapp_scale{ s e:nat}: forall  pF1 p1 (mu_n: list (dstate s e)),
length pF1= length mu_n->
dstate_eq (big_dapp (map (fun x : R => (p1 * x)%R) (get_pro_formula pF1)) mu_n)
(d_scale_not_0 p1 (big_dapp (get_pro_formula pF1) mu_n)).
Proof. induction pF1; intros; simpl. 
       destruct mu_n.
       apply dstate_eq_sym.
        apply d_scale_not_0_empty.
        simpl in H. lia.
        destruct mu_n. 
        simpl in H. lia.
        destruct a. simpl.   
        apply dstate_eq_trans with 
        ((d_app (d_scale_not_0 (p1 * r) d)
        (d_scale_not_0 p1 (big_dapp (get_pro_formula pF1) mu_n)))).
        apply d_app_eq.
        apply dstate_eq_refl.
        apply IHpF1. injection H. intuition.
        apply dstate_eq_trans with 
        ((d_app (d_scale_not_0 p1 (d_scale_not_0 r d))
        (d_scale_not_0 p1 (big_dapp (get_pro_formula pF1) mu_n)))).
        apply d_app_eq.
        apply dstate_eq_sym. 
        apply d_scale_not_0_assoc.
        apply dstate_eq_refl.
        apply d_scale_not_0_app_distr.
Qed.



Lemma pro_to_npro_formula_scale: forall pF p,
pro_to_npro_formula (pro_formula_scale pF p)=
pro_to_npro_formula pF.
Proof. induction pF; intros; 
try destruct a; simpl; try reflexivity.
f_equal. auto. 
Qed.

Lemma sum_over_list_map: forall (f:list R) p,
sum_over_list (map (fun x=> p*x) f) = 
p* (sum_over_list f) .
Proof. induction f; intros.  simpl. rewrite sum_over_list_nil. rewrite Rmult_0_r. reflexivity.
       simpl. repeat rewrite sum_over_list_cons. rewrite IHf. 
       rewrite Rmult_plus_distr_l. reflexivity. 
Qed.



Theorem rule_sum_pro: forall (F1 F2:State_formula ) (pF1 pF2: pro_formula) c (p1 p2: R),
Forall (fun x : R => 0< x) (get_pro_formula pF1) ->
Forall (fun x : R => 0< x) (get_pro_formula pF2) ->
Forall(fun x : State_formula => WF_formula x) (pro_to_npro_formula pF1) ->
Forall (fun x : State_formula => WF_formula x) (pro_to_npro_formula pF2) ->
              0< p1 /\ 0< p2->
              {{F1}} c {{pF1}}->
              {{F2}} c {{pF2}} ->
            {{APro [(p1,F1);(p2,F2)]}} c
            {{pro_formula_linear [pF1; pF2] [p1; p2]}}.
Proof.  unfold hoare_triple. intros F1 F2 pF1 pF2 c p1 p2 HF1 HF2 HNF1 HNF2.
intros.  inversion_clear H3. inversion_clear H6.
simpl in *.

 assert(exists (mu_n': list (dstate s e)), 
 and ((Forall_two (fun x y : dstate s e => ceval c x y) mu_n mu_n'))
 (dstate_eq mu' (big_dapp [p1;p2] mu_n'))).  
 apply ceval_big_dapp with mu. econstructor. apply H.
 econstructor. apply H. econstructor. inversion_clear H5. simpl in H9. 
 lra. assert([p1; p2]=get_pro_formula [(p1, F1); (p2, F2)] ). reflexivity.
 rewrite H6. unfold get_pro_formula. eapply Forall_two_map; try apply H8; simpl.
 intros. eapply WF_sat_State. apply H9. assumption.
 apply big_dapp'_length with mu'0. assumption. 
 apply dstate_eq_trans with mu'0. assumption.
 apply big_dapp_eq with [p1;p2] mu_n. assumption.
 apply big_dapp'_to_app. apply big_dapp'_length with mu'0.
 assumption. econstructor. lra. econstructor. lra.
 econstructor. assumption.
 destruct H6. destruct H6.

  rewrite app_nil_r.  destruct mu_n.
  inversion_clear H3. destruct mu_n. 
  inversion_clear H3. inversion_clear H11.
  destruct mu_n. destruct x. inversion_clear H6.
  destruct x. inversion_clear H6. inversion_clear H11.
  destruct x.  simpl in *. inversion H3; subst.
  inversion H16; subst. inversion H18; subst. clear H18. 
  clear H16. clear H3.
  inversion_clear H8. inversion_clear H10. clear H11.
  inversion_clear H6. inversion_clear H11. clear H12.

  pose H10. pose H6.
 apply H0 in c0. apply H1 in c1.
 inversion_clear c0. inversion_clear H13.
 inversion_clear c1. inversion_clear H20. 

econstructor. inversion_clear H2. eapply WF_ceval. apply H20. apply H24. 
econstructor. rewrite pro_to_npro_formula_app.
repeat rewrite pro_to_npro_formula_scale. 
apply Forall_app. split; try assumption. split.
rewrite get_pro_formula_app. simpl. 
rewrite Forall_app. split.
apply Forall_map. apply Forall_impl with  (fun x : R => 0 <= x).
intros. apply Rmult_le_pos. lra. assumption.
inversion_clear H12. destruct H24.  assumption. 
apply Forall_map. apply Forall_impl with  (fun x : R => 0 <= x).
intros. apply Rmult_le_pos. lra. assumption.
inversion_clear H19. destruct H24. assumption. 
rewrite get_pro_formula_app. simpl. 
rewrite sum_over_list_app. 
repeat rewrite sum_over_list_map. 
inversion_clear H12. destruct H24. rewrite H24. 
inversion_clear H19. destruct H26. rewrite H26. 
repeat rewrite Rmult_1_r. inversion_clear H5. 
simpl in H28. repeat rewrite sum_over_list_cons in H28. 
rewrite sum_over_list_nil in H28. rewrite Rplus_0_r in H28.
apply H28.
econstructor.
rewrite get_pro_formula_app. 
 assert (big_dapp'
 (map (fun x : R => (p1 * x)%R) (get_pro_formula pF1) ++
   map (fun x : R => (p2 * x)%R) (get_pro_formula pF2)) 
 (mu_n ++ mu_n0) (big_dapp (map (fun x : R => (p1 * x)%R) (get_pro_formula pF1) ++
 map (fun x : R => (p2 * x)%R) (get_pro_formula pF2)) (mu_n ++ mu_n0) ) ).
 apply big_dapp'_to_app.
 repeat rewrite app_length.
 repeat rewrite map_length. 
 f_equal; eapply big_dapp'_length; [apply H14| apply H21].
 apply Forall_app. 
 split; apply Forall_map.
 apply Forall_impl with  (fun x : R => 0 < x).
 intros. apply Rmult_gt_0_compat. lra. assumption. assumption.
 apply Forall_impl with  (fun x : R => 0 < x).
 intros. apply Rmult_gt_0_compat. lra. assumption. assumption.
  apply H20.
  apply dstate_eq_trans with 
  (d_app (big_dapp (map (fun x : R => (p1 * x)%R) (get_pro_formula pF1)
  ) mu_n )  (big_dapp (map (fun x : R => (p2 * x)%R) (get_pro_formula pF2))
  mu_n0)). 
  apply dstate_eq_trans with 
  ((d_app
  (d_scale_not_0 p1 (big_dapp (get_pro_formula pF1) mu_n))
  (d_scale_not_0 p2 (big_dapp (get_pro_formula pF2) mu_n0)))).
   apply dstate_eq_trans with 
   ((d_app (d_scale_not_0 p1  mu'0)
   (d_scale_not_0 p2 mu'1))).
   apply dstate_eq_trans with 
   ((d_app (d_scale_not_0 p1  d1)
   (d_scale_not_0 p2 d2))).
   apply dstate_eq_trans with 
   ((d_app (d_scale_not_0 p1 d1)
   (d_app (d_scale_not_0 p2 d2) (d_empty s e)))).
  assumption.
  apply d_app_eq. apply dstate_eq_refl.
  apply d_app_empty_r.
  apply d_app_eq;
  apply d_scale_not_0_eq;
  assumption.
  apply d_app_eq;
  apply d_scale_not_0_eq;
  eapply big_dapp_eq;
  [apply H14
  | apply big_dapp'_to_app; [eapply big_dapp'_length; apply H14 | assumption]|
  apply H21 | apply big_dapp'_to_app;
  [eapply big_dapp'_length; apply H21 | assumption] ].
  apply d_app_eq;
  apply dstate_eq_sym;
  apply big_dapp_scale;
  rewrite <-get_pro_formula_length;
  eapply big_dapp'_length; [apply H14| apply H21].
  apply dstate_eq_sym;
  apply big_dapp_app;
  rewrite map_length;
  eapply big_dapp'_length; [apply H14| apply H21].
  apply Forall_two_app; auto.
  assert(d_trace mu' = d_trace d1). 
  rewrite (ceval_trace_eq' c _ _ d d1); try assumption. destruct H3. simpl. lra.
  rewrite H20. 
  apply ceval_trace_eq' with c.
  apply WWF_dstate_aux_to_WF_dstate_aux.
  apply H4. assumption. 
  apply WWF_dstate_aux_to_WF_dstate_aux.
  inversion_clear H10. assumption. rewrite H20.
  unfold pro_formula_scale.
  eapply Forall_two_map; try apply H18; simpl.
  intros. apply H24. 
 apply Rmult_lt_reg_l with p1. lra. rewrite Rmult_0_r. 
  assumption. 
  assert(d_trace mu' = d_trace d2).
  rewrite (ceval_trace_eq' c _ _ d0 d2); try assumption. destruct H8. simpl. lra.
  rewrite H20. 
  apply ceval_trace_eq' with c.
  apply WWF_dstate_aux_to_WF_dstate_aux.
  apply H4. assumption. 
  apply WWF_dstate_aux_to_WF_dstate_aux.
  inversion_clear H6. assumption. rewrite H20.
  unfold pro_formula_scale.
  eapply Forall_two_map; try apply H23; simpl.
  intros. apply H24.  apply Rmult_lt_reg_l with p2. lra. rewrite Rmult_0_r. 
  assumption.  
  rewrite sat_Assert_to_State. apply H8. simpl. lra.
  rewrite sat_Assert_to_State. apply H3. simpl. lra. 
  inversion_clear H6. inversion_clear H11.
  inversion_clear H12.
  inversion_clear H3. inversion_clear H11.
  inversion_clear H12.
Qed.



(*Cond*)
Import Sorted.
Lemma rule_cond_aux: forall (F F':State_formula) (b:bexp) c1 c2,
{{F/\s b}} c1 {{F'}}->
{{F /\s b}} if b then c1 else c2 end {{F'}}.
Proof. unfold hoare_triple.  intros F F' b c1 c2. 
       intro.  intros s e (mu, IHmu); induction mu; 
       intros (mu' ,IHmu'); intros; 
       rewrite sat_Assert_to_State in *.

       (*mu=[]*)
      -inversion_clear H0. inversion H3;subst. simpl in *.
      rewrite <-sat_Assert_to_State. 
      apply H with ({| StateMap.this := []; StateMap.sorted := IHmu |}).
      econstructor. econstructor. simpl. rewrite <-H7. econstructor.
      apply H0.  simpl in H4. 
      apply subset_union in H4. apply H4.
      rewrite sat_Assert_to_State. assumption.
       
       (*mu<>[]*)
       -inversion_clear H0.
       simpl in *. inversion H3; subst.
       
       --(*b=true*)
       econstructor. eapply WF_ceval. apply  H2. apply H3.
       destruct mu. inversion H10; subst.
       simpl. 
       rewrite map2_nil_r. 
       assert(Sorted.Sorted
       (StateMap.Raw.PX.ltk (elt:=qstate s e))
       (mu'0)). apply ceval_sorted with c1 ([(sigma, rho)]).
       apply Sorted_cons. apply Sorted_nil.
       apply HdRel_nil. intuition.
       assert(Sorted.Sorted
       (StateMap.Raw.PX.ltk (elt:=qstate s e))
       ([(sigma, rho)])). 
       apply Sorted_cons. apply Sorted_nil.
       apply HdRel_nil.
        assert(WF_dstate_aux ([(sigma, rho)])). apply H2. 
       assert(sat_Assert (StateMap.Build_slist H5) F').
       apply H with (StateMap.Build_slist H6).
       apply E_com. intuition. 
       simpl. intuition. rewrite sat_Assert_to_State.
       inversion_clear H1. 
       constructor. intuition.
       simpl in *. 
       intuition. rewrite sat_Assert_to_State in H8.
       inversion_clear H8. assumption. 
       

      
       assert(WF_dstate_aux ([(sigma, rho)])).
        apply WF_state_dstate_aux. 
       inversion_clear H2. assumption. 
       apply d_seman_app_aux. 
       apply WF_ceval with c1 ([(sigma, rho)]).
       intuition.  intuition. 
       apply WF_ceval with (<{ if b then c1 else c2 end }>) ((p :: mu)).
       inversion_clear H2. assumption.  assumption.
       assert(Sorted.Sorted
       (StateMap.Raw.PX.ltk (elt:=qstate s e))
       (mu'0)). apply ceval_sorted with c1 ([(sigma, rho)]).
       apply Sorted_cons. apply Sorted_nil.
       apply HdRel_nil. intuition.
       assert(Sorted.Sorted
       (StateMap.Raw.PX.ltk (elt:=qstate s e))
       ([(sigma, rho)])). 
       apply Sorted_cons. apply Sorted_nil.
       apply HdRel_nil.
       
       assert(sat_Assert (StateMap.Build_slist H4) F').
       apply H with (StateMap.Build_slist H5).
       apply E_com. intuition. 
       simpl. intuition. rewrite sat_Assert_to_State.
       inversion_clear H1. 
       constructor. intuition.
       simpl in *. inversion_clear H7. 
       econstructor. assumption. apply Forall_nil.
       rewrite sat_Assert_to_State in H6. 
       inversion_clear H6. simpl in H9. assumption. 
      

       inversion_clear IHmu. 
       assert(Sorted (StateMap.Raw.PX.ltk (elt:=qstate s e))
       mu''). apply ceval_sorted with (<{ if b then c1 else c2 end }>)
       ((p::mu)). intuition. intuition.
       assert(WF_dstate_aux ((p:: mu))).
       inversion_clear H2.   intuition.
       assert(sat_Assert (StateMap.Build_slist H6) F').
       apply IHmu0 with H4. 
       apply E_com. unfold WF_dstate. simpl. intuition.  unfold WF_dstate.
       simpl. intuition.  rewrite sat_Assert_to_State.
       constructor.
       unfold WF_dstate. simpl. intuition.
       inversion_clear H1. destruct p. 
       inversion_clear H12. simpl. assumption.
       rewrite sat_Assert_to_State in *.  
       inversion_clear H8.    
       assumption.   
      

       inversion_clear H1.  simpl in *.
       inversion_clear H4.  
       rewrite H9 in H1. destruct H1. destruct H4.
Qed.

Local Open Scope assert_scope.
Local Open Scope com_scope.
Lemma rule_cond_aux_2: forall (F F':State_formula) (b:bexp) c1 c2,
{{F/\s (BNot b)}} c2 {{F'}}->
{{F /\s (BNot b)}} if b then c1 else c2 end {{F'}}.
       Proof. unfold hoare_triple.  intros F F' b c1 c2. 
       intro.  intros s e(mu, IHmu); induction mu; 
       intros (mu' ,IHmu'); intros; 
       rewrite sat_Assert_to_State in *.

       (*mu=[]*)
       -inversion_clear H0. inversion H3;subst. simpl in *.
       rewrite <-sat_Assert_to_State. 
       apply H with ({| StateMap.this := []; StateMap.sorted := IHmu |}).
       econstructor. econstructor. simpl. rewrite <-H7. econstructor.
    
      apply H0.  simpl in H4. 
      apply subset_union in H4. apply H4.
       rewrite sat_Assert_to_State. assumption.

       (*mu<>mu*)
       -inversion_clear H0.
       simpl in *. inversion H3; subst.

       --(*b=true*)  inversion_clear H1.  simpl in *.
       inversion_clear H4. 
       rewrite H9 in H1. destruct H1. destruct H4. intuition.
       --(*b=false*)
       econstructor. eapply WF_ceval. apply H2. apply H3.
       destruct mu. inversion H10; subst.
       simpl. 
       rewrite map2_nil_r. 
       assert(Sorted.Sorted
       (StateMap.Raw.PX.ltk (elt:=qstate s e))
       (mu'0)). apply ceval_sorted with c2 ([(sigma, rho)]).
       apply Sorted_cons. apply Sorted_nil.
       apply HdRel_nil. intuition.
       assert(Sorted.Sorted
       (StateMap.Raw.PX.ltk (elt:=qstate s e))
       ([(sigma, rho)])). 
       apply Sorted_cons. apply Sorted_nil.
       apply HdRel_nil.
       assert(WF_dstate_aux ([(sigma, rho)])).
       apply H2.
       assert(sat_Assert (StateMap.Build_slist H5) F').
       apply H with (StateMap.Build_slist H6).
       apply E_com. intuition.
       simpl. intuition. rewrite sat_Assert_to_State.
       inversion_clear H1. 
       constructor. intuition.
       simpl in *. 
       intuition. rewrite sat_Assert_to_State in H8.
       inversion_clear H8. assumption.
       
       
       assert(WF_dstate_aux ([(sigma, rho)])).
       apply WF_state_dstate_aux. 
       inversion_clear H2. assumption. 
       apply d_seman_app_aux.
       apply WF_ceval with c2 ([(sigma, rho)]).
       intuition.  intuition. 
       apply WF_ceval with (<{ if b then c1 else c2 end }>) ((p :: mu)).
       inversion_clear H2. assumption.  assumption.
       assert(Sorted.Sorted
       (StateMap.Raw.PX.ltk (elt:=qstate s e))
       (mu'0)). apply ceval_sorted with c2 ([(sigma, rho)]).
       apply Sorted_cons. apply Sorted_nil.
       apply HdRel_nil. intuition.
       assert(Sorted.Sorted
       (StateMap.Raw.PX.ltk (elt:=qstate s e))
       ([(sigma, rho)])). 
       apply Sorted_cons. apply Sorted_nil.
       apply HdRel_nil.
       assert(sat_Assert (StateMap.Build_slist H4) F').
       apply H with (StateMap.Build_slist H5).
       apply E_com. intuition.
       simpl. intuition. rewrite sat_Assert_to_State.
       inversion_clear H1. 
       constructor. intuition. 
       inversion_clear H7.  simpl. econstructor.
       assumption. apply Forall_nil. 
       rewrite sat_Assert_to_State in H6.
       inversion_clear H6. assumption. 

       inversion_clear IHmu. 
       assert(Sorted (StateMap.Raw.PX.ltk (elt:=qstate s e))
       mu''). apply ceval_sorted with (<{ if b then c1 else c2 end }>)
       ((p::mu)). intuition. intuition.
       assert(WF_dstate_aux ((p:: mu))).
       unfold WF_dstate in H2. simpl in H2.
       inversion_clear H2. 
       intuition.  
       assert(sat_Assert (StateMap.Build_slist H6) F').
       apply IHmu0 with H4. 
       apply E_com. unfold WF_dstate. simpl. intuition.  unfold WF_dstate.
       simpl. intuition.
       rewrite sat_Assert_to_State.
       constructor.
       unfold WF_dstate. simpl. intuition. 
       inversion_clear H1.  destruct p. simpl in *.
       inversion_clear H12. intuition.
       rewrite sat_Assert_to_State in *.
       inversion_clear H8. intuition.
Qed.

Local Open Scope R_scope.
Local Open Scope assert_scope.
Theorem rule_cond: forall (F1 F1' F2 F2': State_formula) (c1 c2:com) (b:bexp) (p:R),
        0<=p<=1-> Forall (fun x : State_formula => WF_formula x) [F1'; F2'] ->
        ({{F1 /\s (b)}} c1 {{F1'}} /\ {{F2 /\s ((BNot b) )}} c2 {{F2'}})
     -> ({{ APro [(p, (F1 /\s b)) ; ((1 - p), (F2 /\s (BNot b)))]}}
        if b then c1 else c2 end
        {{APro [(p, F1') ; ((1 - p), F2')]}}).
Proof. intros. 

       destruct (Req_dec p 0). subst. rewrite Rminus_0_r in *.
       eapply rule_conseq; try apply rule_cond_aux_2; try apply H1; try apply H1; try apply H2.
       unfold assert_implies; intros. pose H2. apply sat_Pro_State' in s0. apply s0. 
       unfold assert_implies; intros. apply sat_Pro_State'. split. apply H2.
       inversion_clear H0.  assumption.

     
       destruct (Req_dec p 1). subst. rewrite  Rcomplements.Rminus_eq_0 in *.
       eapply rule_conseq. apply rule_cond_aux. apply H1.
       unfold assert_implies; intros. apply (rule_POplusC _ 0 ) in H3. simpl in H3.
       apply sat_Pro_State' in H3. apply H3. 
       unfold assert_implies; intros. 
       assert(sat_Assert mu F1' /\ WF_formula F2').
       inversion_clear H0. inversion_clear H5. split; try assumption.
        rewrite <-sat_Pro_State' in H4.
       apply (rule_POplusC _ 0 ) in H4. simpl in H4. apply H4.

       assert ([(p, F1 /\s b); (1 - p, F2 /\s (BNot b))]=
       (npro_to_pro_formula ([(F1 /\s b); ( F2 /\s (BNot b))]) ([p; (1-p)]))).
       simpl. reflexivity. rewrite H4. 
       assert ([(p, F1'); (1 - p, F2')]=
       (npro_to_pro_formula ([(F1'); ( F2')]) ([p; (1-p)]))).
       reflexivity. rewrite H5.
       apply rule_sum. simpl. econstructor.
       lra. econstructor. lra. apply Forall_nil.
       reflexivity. assumption.
       econstructor.  apply rule_cond_aux. intuition. 
       econstructor. apply rule_cond_aux_2. intuition.
      econstructor.  
Qed.

Theorem rule_cond_classic: forall (P1 P2: Pure_formula) (c1 c2:com) (b:bexp),
        ({{P1 /\p (b)}} c1 {{P2 }} /\ {{P1 /\p ((BNot b) )}} c2 {{P2 }})
     -> ({{P1 }}
        if b then c1 else c2 end
        {{P2}}).
Proof. intros.  
assert(P1 ->> ANpro [P1 /\s b ; P1 /\s (BNot b)]). 
rule_solve. 
assert(StateMap.this mu=[] \/ StateMap.this mu <>[]).
apply Classical_Prop.classic. destruct H4.
apply sat_Assert_empty. simpl. split. econstructor;simpl. auto.
econstructor; simpl; auto; econstructor. discriminate. assumption.

apply sat_State_Npro; try  assumption. simpl. auto.

intros. apply H2 in H5. simpl in *. destruct (beval (x, d_find x mu) b); simpl;[left|right]; auto.
assert(({{P1 /\s b}} c1 {{P2}}) /\ ({{P1 /\s <{ ~ b }>}} c2 {{P2}})).
split; eapply rule_conseq_l; try apply SAnd_PAnd_eq; try apply H.
unfold hoare_triple. intros. apply H0 in H3. apply sat_Npro_Pro in H3. destruct H3.
pose (rule_cond P1 P2 P1 P2 c1 c2 b x). eapply h in H1. destruct H3. 
eapply H1 in H4; try apply H2. apply rule_Oplus in H4. simpl in *.
apply (@sat_NPro_State' s e) in H4; try assumption. lra.
econstructor; simpl. auto. econstructor. simpl. auto.
econstructor.
Qed.


(*While*)
Lemma while_seq: forall (b:bexp) c F0  F1, 
{{F0 /\s b}} c; while b do c end {{F1 /\s ((BNot b))}} ->
{{F0 /\s b}} while b do c end {{F1 /\s (BNot b)}} .
Proof. unfold hoare_triple. intros b c F0 F1 H.  
        intros s e(mu, IHmu); induction mu; intros;
        destruct mu' as  [mu' IHmu']; 
        inversion_clear H0; inversion H3; subst.
      apply H with ({| StateMap.this := []; StateMap.sorted := IHmu |}).
      econstructor. econstructor. simpl in *. rewrite <-H7. econstructor.
      simpl. split;
      apply H0.  simpl.
      apply subset_union'. split; apply H4.
      assumption.

      rewrite sat_Assert_to_State in *. simpl in *.

       econstructor. eapply WF_ceval. apply H2. apply H3.
       destruct mu. inversion H8; subst.
       simpl.
       rewrite map2_nil_r.
       assert(Sorted.Sorted
       (StateMap.Raw.PX.ltk (elt:=qstate s e))
       (mu'0)). apply ceval_sorted with <{ while b do c end }> mu1.
       apply ceval_sorted with c ([(sigma, rho)]).
       apply Sorted_cons. apply Sorted_nil.
       apply HdRel_nil. intuition. intuition. 
       assert(Sorted.Sorted
       (StateMap.Raw.PX.ltk (elt:=qstate s e))
       ([(sigma, rho)])). 
       apply Sorted_cons. apply Sorted_nil.
       apply HdRel_nil.
        assert(WF_dstate_aux ([(sigma, rho)])).
        apply H2.
       assert(sat_Assert (StateMap.Build_slist H5) (F1 /\s (BNot b))).
       apply H with (StateMap.Build_slist H6).
       apply E_com. intuition. 
       simpl. apply E_Seq with mu1.  intuition.
       assumption.
       rewrite sat_Assert_to_State.
       inversion_clear H1. 
       constructor. intuition.
       simpl in *. 
       intuition. rewrite sat_Assert_to_State in H12.
       inversion_clear H12. assumption. 

       rewrite <-H9.
       assert(WF_dstate_aux ([(sigma, rho)])).
       apply WF_state_dstate_aux. 
       inversion_clear H2. assumption. 
      
       apply d_seman_app_aux. 
       apply WF_ceval with (<{ while b do c end }>) (mu1).
       apply WF_ceval with c ([(sigma, rho)]).
       intuition.  intuition. assumption.  
       apply WF_ceval with (<{ while b do c end }>) ((p :: mu)).
       inversion_clear H2. assumption.  assumption.
       assert(Sorted.Sorted
       (StateMap.Raw.PX.ltk (elt:=qstate s e))
       (mu'0)).
       apply ceval_sorted with <{ while b do c end }> mu1.
       apply ceval_sorted with c ([(sigma, rho)]).
       apply Sorted_cons. apply Sorted_nil.
       apply HdRel_nil. intuition. intuition. 
       assert(Sorted.Sorted
       (StateMap.Raw.PX.ltk (elt:=qstate s e))
       ([(sigma, rho)])). 
       apply Sorted_cons. apply Sorted_nil.
       apply HdRel_nil.
       
       assert(sat_Assert (StateMap.Build_slist H4) ((F1 /\s (BNot b)))).
       apply H with (StateMap.Build_slist H5).
       apply E_com. intuition. simpl.
       apply E_Seq with mu1.  intuition.
       assumption. rewrite sat_Assert_to_State.
       inversion_clear H1. 
       constructor. intuition.
       simpl in *. inversion_clear H12. 
       econstructor. assumption. apply Forall_nil.
       rewrite sat_Assert_to_State in H6. 
       inversion_clear H6. simpl in H13. assumption. 
      

       inversion_clear IHmu. 
       assert(Sorted (StateMap.Raw.PX.ltk (elt:=qstate s e))
       mu''). apply ceval_sorted with (<{ while b do c end }>)
       ((p::mu)). intuition. intuition.
       assert(WF_dstate_aux ((p:: mu))).
       inversion_clear H2.   intuition.
       assert(sat_Assert (StateMap.Build_slist H6) (F1 /\s (BNot b))).
       apply IHmu0 with H4. 
       apply E_com. unfold WF_dstate. simpl. intuition. 
       simpl. intuition.  rewrite sat_Assert_to_State.
       constructor.
       unfold WF_dstate. simpl. intuition.
       inversion_clear H1. destruct p. 
       inversion_clear H14. simpl. assumption.
       rewrite sat_Assert_to_State in *.   
       inversion_clear H13.    
       assumption. 
       
       rewrite sat_Assert_to_State in *. simpl in *.
       inversion_clear H1. simpl in H4.
       inversion_clear H4. 
       rewrite H8 in H1. destruct H1. destruct H4.
Qed.



Lemma rule1: forall s e (mu:list (state s e)) (sigma:cstate) (rho:qstate s e) IHmu H
F0 F1 (b:bexp), 
sat_Assert {| StateMap.this := (sigma, rho) :: mu;
            StateMap.sorted := IHmu |} (ANpro ([F0 /\s b; F1 /\s (BNot b)])) ->
 beval (sigma, rho) b = true->
sat_Assert {| StateMap.this := [(sigma, rho)];
             StateMap.sorted := H |} (F0 /\s b)  .
Proof. intros. inversion_clear H0.   
  inversion_clear H3. destruct p_n. 
  inversion_clear H4. 
  simpl in *. rewrite sum_over_list_nil in H6.
  intuition.  destruct p_n. 
  simpl in H2. intuition. 
  destruct p_n.

 assert(r=0\/r<>0). apply Classical_Prop.classic.
 destruct H3. subst. inversion_clear H4.
 simpl in *.  
 repeat rewrite sum_over_list_cons in *. 
 rewrite sum_over_list_nil in *. simpl in H6.
 rewrite Rplus_0_l in H6. rewrite Rplus_0_r in H6. destruct H6. subst.
 apply sat_Pro_State in H5.  inversion_clear H5. inversion_clear H7. destruct H5. 
 simpl in H7.  rewrite H1 in H7. 
 simpl in H7. destruct H7. 
 assert(r0=0\/r0<>0). apply Classical_Prop.classic.
 destruct H6. subst. inversion_clear H4.
 simpl in *. 
 repeat rewrite sum_over_list_cons in *. 
 rewrite sum_over_list_nil in *. simpl in H6.
 rewrite Rplus_0_l in H7. rewrite Rplus_0_r in H7.
 simpl in H7. destruct H7. subst. 
 assert(sat_Assert
 {|
   StateMap.this := (sigma, rho) :: mu;
   StateMap.sorted := IHmu
 |} (APro ([(0, F1 /\s <{ ~ b }>); (1, F0 /\s b)]))).
 assert([(0, F1 /\s <{ ~ b }>); (1, F0 /\s b)]= swap_list 
 [(1, F0 /\s b); (0, F1 /\s <{ ~ b }>)] 0). reflexivity.
 rewrite H7. apply rule_POplusC.  econstructor.
 assumption. econstructor.  assumption.  
 simpl in *. 
 repeat rewrite sum_over_list_cons in *. 
 rewrite sum_over_list_nil in *.   rewrite Rplus_0_l. 
 rewrite Rplus_0_r; auto. 
 
 assumption. apply sat_Pro_State' in H7. 
 rewrite sat_Assert_to_State in *. destruct H7. 
 inversion_clear H7. inversion_clear H10. destruct H7. 
 econstructor.
 apply WF_state_dstate_aux.  inversion_clear H0. assumption.
 simpl. econstructor. rewrite H1.  intuition. apply Forall_nil.


 
 inversion_clear H4. simpl in *. destruct H8. 
 inversion_clear H4. inversion_clear H10. clear H11.
rewrite sat_Assert_to_State. 
inversion_clear H5. simpl in *. 
destruct mu_n. inversion_clear H12.
destruct mu_n.  inversion_clear H10.
inversion_clear H13. destruct mu_n. simpl in *.
inversion_clear H12. inversion_clear H13. clear H14.
destruct H5. simpl. lra. destruct H12. simpl. lra. simpl in *.
econstructor. inversion_clear H0.
apply WF_state_dstate_aux. assumption.
simpl in *.  
assert(dstate_eq mu' (big_dapp [r; r0] [d; d0] )).
apply big_dapp_eq with ([r; r0]) ([d; d0]).
assumption. apply big_dapp'_to_app.
reflexivity. econstructor. lra. econstructor. lra. econstructor.
assert(dstate_eq
{|
  StateMap.this := (sigma, rho) :: mu;
  StateMap.sorted := IHmu
|} (big_dapp [r; r0] [d; d0])).
apply dstate_eq_trans with mu'.
assumption. assumption. 
simpl in *.   
destruct d as [d Ihd]. 
destruct d0 as [d0 IHd0].
unfold d_app in *. unfold d_scale_not_0 in *.
 unfold StateMap.map2 in *. 
 unfold StateMap.map in *.  unfold dstate_eq in *.
 simpl in *.  destruct d. simpl in *.
 unfold d_trace in H13. simpl in H13.
 apply WF_dstate_gt0_le1 in H0. simpl in H0. lra.
 discriminate.
 destruct d0.
 unfold d_trace in H14. simpl in H14.
 apply WF_dstate_gt0_le1 in H0. simpl in H0. lra.
 discriminate.

 destruct p. destruct p0. 
simpl in *. 
destruct (Cstate_as_OT.compare c c0).
injection H16. intros. 
rewrite H18. rewrite H19.
 econstructor.  split.
 assert((@pair cstate (qstate s e) c (q_scale r q)) = s_scale r (c,q)).
 reflexivity. rewrite H20.
 apply s_seman_scale. lra.  inversion_clear H5. inversion_clear H22. destruct H5. assumption.
 rewrite (state_eq_bexp (c, q_scale r q) 
  (sigma ,rho) _).  rewrite H1. auto. simpl. rewrite H19. reflexivity. econstructor.

  injection H16. intros.
inversion_clear H12. inversion_clear H21.
  inversion_clear H12.  simpl in *.
  unfold Cstate_as_OT.eq in e0. 
  rewrite <-e0 in H23.  
  rewrite <-H19 in H23. 
  rewrite <-(state_eq_bexp (sigma, rho) 
  (sigma ,q0) _) in H23. 
  rewrite H1 in H23. destruct H23. intuition.

  injection H16. intros.
inversion_clear H12. inversion_clear H21.
  inversion_clear H12.  simpl in *.
  rewrite <-H19 in H23. 
  rewrite <-(state_eq_bexp (sigma, rho) 
  (sigma ,q0) _) in H23. 
  rewrite H1 in H23. destruct H23. intuition.
  
  inversion_clear H12. inversion_clear H13. inversion_clear H14.
  simpl in H2.  intuition.
Qed.



Lemma  ruleState: forall s e (mu:list (state s e)) (sigma:cstate) (rho:qstate s e) H1 H2 F,
sat_State {| StateMap.this := (sigma, rho) :: mu;StateMap.sorted := H1 |} F-> mu<>nil ->
sat_State {| StateMap.this := mu; StateMap.sorted := H2 |} F.
Proof. intros.  
simpl in *. econstructor. inversion_clear H. inversion_clear H3. 
assumption.  apply State_eval_dstate_Forall.
assumption. inversion_clear H. inversion_clear H4. assumption.
Qed.


Lemma Rdiv_in01': forall p1 p2,
0 < p1 ->
0 < p2 ->
0 < p1 / (p1 + p2) <=1.
Proof. split.  rewrite Rdiv_unfold. apply Rmult_gt_0_compat.
intuition. apply Rinv_0_lt_compat. apply Rplus_lt_0_compat.
intuition. intuition. apply (Rcomplements.Rdiv_le_1 p1 _).
apply Rplus_lt_0_compat.
intuition. intuition.  assert(p1=p1+0)%R. rewrite Rplus_0_r.
reflexivity. rewrite H1 at 1. apply Rplus_le_compat_l.
intuition. 
Qed.



Local Open Scope R_scope.
Lemma  rule2: forall s e (mu:list (state s e)) (sigma:cstate) (rho:qstate s e) H1 H2
F0 F1 ,
sat_Assert {| StateMap.this := (sigma, rho) :: mu; StateMap.sorted := H1 |} (ANpro ([F0; F1]))
-> mu<>nil ->
sat_Assert {| StateMap.this := mu; StateMap.sorted := H2 |} (ANpro ([F0; F1])).
Proof. 
intros. inversion_clear H. destruct p_n.
simpl in *. discriminate H3. destruct p_n. 
discriminate H3. destruct p_n. clear H3.
inversion_clear H4.

assert(r=0\/ r<>0). 
apply Classical_Prop.classic.
destruct H4.  subst. 
(*r=0*)
econstructor. assert(length [0; r0] = length [F0; F1]).
reflexivity.  apply H4. simpl. 

inversion_clear H3. simpl in *. repeat rewrite sum_over_list_cons in * .
simpl in *. rewrite sum_over_list_nil in *.
rewrite Rplus_0_l in *. rewrite Rplus_0_r in *. destruct H6. subst.
apply sat_Pro_State in H5. apply sat_Pro_State'.
apply (ruleState _ _ _ _ _ _ H2) in H5. rewrite sat_Assert_to_State.
split. 
assumption. inversion_clear H4. assumption. assumption.

assert(r0=0\/ r0<>0). 
apply Classical_Prop.classic.
destruct H6.  subst.

(*r0=0*)
econstructor. assert(length [r; 0] = length [F0; F1]).
reflexivity.  apply H6. simpl. 
econstructor.   inversion_clear H. assumption. assumption. 

assert(sat_Assert{| StateMap.this := (sigma, rho) :: mu;
  StateMap.sorted := H1 |} (APro ([(0, F1); (r, F0)]))).
assert([(0, F1); (r, F0)] = swap_list [(r, F0); (0, F1)] 0).
simpl. reflexivity. rewrite H6. clear H6. apply rule_POplusC.
econstructor. assumption. assumption. assumption. clear H5. 

inversion_clear H3. simpl in *. repeat rewrite sum_over_list_cons in * .
simpl in *. rewrite sum_over_list_nil in *.
rewrite Rplus_0_l in *. rewrite Rplus_0_r in *. 
destruct H7. subst. 
apply sat_Pro_State' in H6. destruct H6.   rewrite sat_Assert_to_State in H6.
apply (ruleState _ _ _ _ _ _ H2) in H6. 
assert(sat_Assert {| StateMap.this := mu; StateMap.sorted := H2 |} (APro [(1, F0); (0, F1)])).
assert([(1, F0); (0, F1)] = swap_list [(0, F1); (1, F0)] 0).
reflexivity. rewrite H8. apply rule_POplusC.
apply sat_Pro_State'. rewrite sat_Assert_to_State.
split. assumption. assumption.
inversion_clear H8. assumption. assumption. 

 (*r<>0/\r0<>0*)
inversion_clear H5.  
destruct mu_n. simpl in *. inversion_clear H7. 
destruct mu_n. simpl in *. inversion_clear H7.
inversion_clear H10. 
destruct mu_n. simpl in *. 

inversion H7; subst. inversion H15; subst.
inversion H17; subst. clear H17.
apply d_scale_to_not_0' in H14.
apply d_scale_to_not_0' in H16.
apply big_dapp'_to_app' in H7. 
simpl in H7. 
unfold dstate_eq in H8.
unfold d_app in H8. 
unfold StateMap.map2 in H8. 
simpl in H8. unfold StateMap.Raw.empty in H8.
rewrite map2_nil_r in H8. rewrite H14 in H8.
rewrite H16 in H8. clear H14. clear H16. 
clear H7. 
destruct d0 as [d0 IHd0]. destruct d as [d IHd].
destruct d0;  destruct d.
simpl in *. discriminate H8. inversion_clear H9. destruct H5. 
inversion_clear H3. destruct H9. inversion_clear H3. simpl. lra.  simpl in H5.  
inversion_clear H7. destruct H10. 
inversion_clear H3. destruct H10. inversion_clear H3. inversion_clear H13. simpl. lra.
unfold d_trace in H10.
simpl in H10.
apply WF_dstate_gt0_le1 in H. simpl in H. lra. discriminate.
inversion_clear H9. 
unfold d_trace in H5.
simpl in H5. destruct H5.
inversion_clear H3. destruct H9. inversion_clear H3. simpl. lra.
apply WF_dstate_gt0_le1 in H. simpl in H. lra. discriminate.
destruct p. destruct p0.
simpl in H8. 

inversion_clear H3 as [H'  H5]. 
destruct H5 as [H5 H7].  inversion_clear H5. inversion_clear H10.
simpl in *. clear H11. simpl in *. 
repeat rewrite sum_over_list_cons in *. rewrite sum_over_list_nil in *.
rewrite Rplus_0_r in *.  simpl in *.
inversion_clear H9. inversion_clear H11. simpl in *.
destruct H10. lra. destruct H9. lra. clear H12. 
assert( WF_dstate_aux d). inversion_clear H10. inversion_clear H12. assumption.
assert(WF_state (c, q)). inversion_clear H9. inversion_clear H14. assumption.
assert( WF_dstate_aux d0). inversion_clear H9. inversion_clear H16. assumption.
assert(WF_state (c0, q0)). inversion_clear H10. inversion_clear H17. assumption.
destruct (Cstate_as_OT.compare c0 c). 
injection H8. intros. 

  
econstructor.  assert(length ([((r/ d_trace_aux mu) * d_trace_aux d); ((r0/ d_trace_aux mu) * d_trace_aux ((c,q)::d0))]) = length [F0; F1]).
reflexivity. apply H21.  simpl.  
 assert(distribution_formula
[(r / d_trace_aux mu * d_trace_aux d, F0);
 (r0 / d_trace_aux mu *
  (s_trace (c, q) + d_trace_aux d0), F1)]). 
econstructor. simpl. assumption.
split.
econstructor. simpl. 
apply Rmult_le_pos. 
apply Rcomplements.Rdiv_le_0_compat. lra.
apply WF_dstate_gt0_le1. assumption.  inversion H. assumption.
apply WF_dstate_in01_aux. assumption.
 econstructor. simpl.
apply Rmult_le_pos. 
apply Rcomplements.Rdiv_le_0_compat. lra.
apply WF_dstate_gt0_le1. assumption.  inversion_clear H. assumption.
 assert(s_trace (c, q) + d_trace_aux d0=d_trace_aux ((c,q)::d0)).
 reflexivity. rewrite H21. 
 apply WF_dstate_in01_aux.  apply WF_sat_State in H9. 
 intuition. apply Forall_nil. simpl in *.
 repeat rewrite sum_over_list_cons. rewrite sum_over_list_nil.
 rewrite Rplus_0_r.  simpl. repeat rewrite Rdiv_unfold. 
 rewrite (Rmult_comm r).   rewrite (Rmult_comm r0).
 repeat rewrite Rmult_assoc. rewrite <-Rmult_plus_distr_l.
  assert(r * d_trace_aux d + r0 * (s_trace (c, q) + d_trace_aux d0)= d_trace_aux mu).
  rewrite H18. rewrite d_trace_app_aux. simpl. 
   repeat rewrite d_trace_map.
  unfold s_trace. simpl. 
  rewrite q_trace_scale. unfold q_trace. rewrite Rmult_plus_distr_l. reflexivity.
  lra. lra. lra. apply WWF_dstate_map. lra. 
 apply WWF_dstate_aux_to_WF_dstate_aux. assumption.
 econstructor.  apply WWF_qstate_scale. 
 split. lra.  apply WWF_qstate_to_WF_qstate. assumption.   
 apply WWF_dstate_map. lra.   apply WWF_dstate_aux_to_WF_dstate_aux.
 assumption. 
 rewrite <-H21. apply Rinv_l.  rewrite H21. 
 apply WWF_dstate_not_0. assumption.
 inversion_clear H. apply WWF_dstate_aux_to_WF_dstate_aux. 
 assumption. simpl. 
 econstructor. inversion_clear H. assumption. 
simpl. apply H21.

destruct d.  simpl in *. rewrite Rmult_0_r in *. 
inversion_clear H21. simpl in *. 
 repeat rewrite sum_over_list_cons in H23.
rewrite sum_over_list_nil in *. rewrite Rplus_0_r in *.
simpl in *. rewrite Rplus_0_l in *.
destruct H23. rewrite H23.


apply sat_Pro_State.  
econstructor. inversion_clear H. assumption.
simpl. rewrite H18. simpl. inversion_clear H9.
inversion_clear H25. econstructor. 
assert((@pair StateMap.Raw.key (qstate s e) c
(q_scale r0 q))= s_scale r0 (c,q)). reflexivity.
rewrite H25. apply s_seman_scale. lra.  
 assumption.
rewrite map2_r_refl. destruct d0. simpl. apply Forall_nil.
 apply State_eval_dstate_Forall. destruct p. simpl. discriminate.
apply d_seman_scale_aux. lra.  apply State_eval_dstate_Forall. discriminate.
apply H26. 


inversion_clear H1.  inversion_clear IHd.

econstructor. 
assert(big_dapp'
([r / d_trace_aux mu * d_trace_aux (((p::d)));
 r0 / d_trace_aux mu * (s_trace (c, q) + d_trace_aux d0)])

 ([d_scale_not_0 (d_trace_aux mu ) (d_scale_not_0 (R1/d_trace_aux (p::d)) (StateMap.Build_slist H24));
 d_scale_not_0 (d_trace_aux mu ) (d_scale_not_0 (R1/d_trace_aux (((c,q)::d0))) (StateMap.Build_slist IHd0))
 ])
 
 (d_app (d_scale_not_0 (r / d_trace_aux mu * d_trace_aux (((p::d)))) 
       (d_scale_not_0 (d_trace_aux mu ) (d_scale_not_0 (R1/d_trace_aux ((p::d))) (StateMap.Build_slist H24)))
 ) (d_app (d_scale_not_0 (r0 / d_trace_aux mu * (s_trace (c, q) + d_trace_aux d0)) (d_scale_not_0 (d_trace_aux mu ) (d_scale_not_0 (R1/d_trace_aux (((c,q)::d0))) (StateMap.Build_slist IHd0))) ) (d_empty s e)))).

 econstructor. 
 apply d_scalar_r.
 assert(
r / d_trace_aux mu * d_trace_aux (p :: d) > 0).
apply Rmult_gt_0_compat.
apply Rdiv_lt_0_compat.
lra. apply WF_dstate_gt0_le1.
assumption. inversion_clear H. assumption.
apply WF_dstate_gt0_le1. discriminate.
apply WF_sat_State in H10. assumption.
 lra.
 econstructor. 
 apply d_scalar_r.
 assert(r0 / d_trace_aux mu * (s_trace (c, q) + d_trace_aux d0) > 0).
 apply Rmult_gt_0_compat.
apply Rdiv_lt_0_compat.
lra. apply WF_dstate_gt0_le1.
assumption. inversion_clear H. assumption.
assert(s_trace (c, q) + d_trace_aux d0= d_trace_aux ((c,q)::d0)).
simpl. reflexivity. rewrite H26.
apply WF_dstate_gt0_le1. discriminate.
apply WF_sat_State in H9. intuition.
 lra.
 apply big_dapp_nil. simpl.
apply H26. 
apply dstate_eq_trans with (d_app (d_scale_not_0 r (StateMap.Build_slist H24))
(d_scale_not_0 r0 (StateMap.Build_slist (IHd0)))).
unfold dstate_eq. unfold d_app.
unfold StateMap.map2. unfold d_scale_not_0.
unfold StateMap.map. simpl. assumption.
apply d_app_eq. 
apply dstate_eq_sym. 
eapply dstate_eq_trans. 
apply d_scale_not_0_assoc. 
eapply dstate_eq_trans. 
apply d_scale_not_0_assoc.
unfold dstate_eq.
f_equal. f_equal. 
repeat rewrite Rdiv_unfold. rewrite Rmult_1_l.
 rewrite Rmult_assoc. rewrite Rmult_assoc.
 rewrite <-(Rmult_assoc (d_trace_aux ((p :: d)))) . 
 rewrite (Rmult_comm (d_trace_aux ((p :: d)) )).
repeat   rewrite Rmult_assoc . 
 rewrite Rinv_r. rewrite Rmult_1_r. 
 rewrite Rinv_l. rewrite Rmult_1_r. reflexivity.
 apply WWF_dstate_not_0. assumption.
 inversion_clear H. apply WWF_dstate_aux_to_WF_dstate_aux. 
 assumption. 
 apply WWF_dstate_not_0. discriminate.
apply WF_sat_State in H10. 
 apply WWF_dstate_aux_to_WF_dstate_aux. 
 assumption. 
 eapply dstate_eq_trans.
 apply dstate_eq_sym. 
 apply d_app_empty_l.
 eapply dstate_eq_trans.
 apply d_app_comm.
 apply d_app_eq.
 apply dstate_eq_sym. 
eapply dstate_eq_trans. 
apply d_scale_not_0_assoc. 
eapply dstate_eq_trans. 
apply d_scale_not_0_assoc.
unfold dstate_eq.
f_equal. f_equal.  
repeat rewrite Rdiv_unfold. rewrite Rmult_1_l.
 rewrite Rmult_assoc. rewrite Rmult_assoc.
 rewrite <-(Rmult_assoc (s_trace (c, q) + d_trace_aux d0)) . 
 rewrite (Rmult_comm (s_trace (c, q) + d_trace_aux d0)).
repeat   rewrite Rmult_assoc . 
 rewrite Rinv_r. rewrite Rmult_1_r. 
 rewrite Rinv_l. rewrite Rmult_1_r. reflexivity.
 apply WWF_dstate_not_0. assumption.
 inversion_clear H. apply WWF_dstate_aux_to_WF_dstate_aux. 
 assumption. 
 apply WWF_dstate_not_0. discriminate.
 apply WWF_dstate_aux_to_WF_dstate_aux.
 apply WF_sat_State in H9.  apply H9.  
  reflexivity.
 
simpl. econstructor. intros. split. apply d_seman_scale_not_0.
apply WF_dstate_gt0_le1. assumption.
inversion_clear H. 
assumption.
assert((R1 / (s_trace p + d_trace_aux d))=
/d_trace ({|
  StateMap.this := p :: d;
  StateMap.sorted := H24
|})).  rewrite Rdiv_unfold.
unfold d_trace. rewrite Rmult_1_l. simpl. reflexivity.
rewrite H27.
 apply d_seman_scale''. intuition.
 apply (ruleState _ _ _ c0 q0 IHd).
 assumption. discriminate. discriminate. 
 rewrite d_trace_scale_not_0.
rewrite d_trace_scale_not_0.
unfold d_trace.  simpl. 
rewrite Rdiv_unfold. rewrite Rmult_1_l.
rewrite Rinv_l. rewrite Rmult_1_r. reflexivity.
assert((s_trace p + d_trace_aux d = d_trace_aux (p::d))).
reflexivity. rewrite H27.
apply WWF_dstate_not_0.
discriminate. apply WWF_dstate_aux_to_WF_dstate_aux. 
apply WF_sat_State in H10.  assumption.
rewrite Rdiv_unfold.
rewrite Rmult_1_l.
apply Rinv_0_lt_compat.
assert((s_trace p + d_trace_aux d = d_trace_aux (p::d))).
reflexivity. rewrite H27.
apply WF_dstate_gt0_le1.
discriminate.  
apply WF_sat_State in H10.  assumption.
apply WF_dstate_gt0_le1. assumption.
inversion_clear H. assumption.
 econstructor. intros. split.
apply d_seman_scale_not_0.
apply WF_dstate_gt0_le1. assumption.
inversion_clear H.  assumption.
assert((R1 / (s_trace (c,q) + d_trace_aux d0))=
/d_trace ({|
  StateMap.this :=  (c, q) :: d0;
  StateMap.sorted := IHd0
|})).  rewrite Rdiv_unfold.
unfold d_trace. rewrite Rmult_1_l. simpl. reflexivity.
rewrite H27.
 apply d_seman_scale''. intuition.
 assumption. discriminate. 
 rewrite d_trace_scale_not_0.
rewrite d_trace_scale_not_0. 
unfold d_trace. simpl.
rewrite Rdiv_unfold. rewrite Rmult_1_l.
rewrite Rinv_l. rewrite Rmult_1_r. reflexivity.
assert((s_trace (c,q) + d_trace_aux d0 = d_trace_aux ((c,q)::d0))).
reflexivity. rewrite H27.
apply WWF_dstate_not_0.
discriminate. apply WWF_dstate_aux_to_WF_dstate_aux. 
apply WF_sat_State in H9. intuition.
assert((R1 / (s_trace (c,q) + d_trace_aux d0))=
/d_trace ({|
  StateMap.this :=  (c, q) :: d0;
  StateMap.sorted := IHd0
|})). rewrite Rdiv_unfold.
unfold d_trace.  rewrite Rmult_1_l. simpl. reflexivity.
rewrite H27.
apply Rinv_0_lt_compat.
apply WF_dstate_gt0_le1.
discriminate. 
apply WF_sat_State in H9. intuition. 
apply WF_dstate_gt0_le1. assumption.
 inversion_clear H. assumption. 
 econstructor.


- injection H8. intros.
econstructor. 
assert(length ([((r/ d_trace_aux mu) * d_trace_aux d); (r0/ d_trace_aux mu) * d_trace_aux (d0)]) = length [F0; F1]).
reflexivity. apply H21. simpl. 
 assert(distribution_formula
 [(r / d_trace_aux mu * d_trace_aux d, F0);
   (r0 / d_trace_aux mu * d_trace_aux d0, F1)]). 
simpl. econstructor. simpl. assumption.
econstructor.  simpl. econstructor. apply Rmult_le_pos. 
apply Rcomplements.Rdiv_le_0_compat. lra.
apply WF_dstate_gt0_le1. assumption.  inversion H. assumption.
apply WF_dstate_in01_aux. assumption. 
econstructor. simpl. apply Rmult_le_pos. 
apply Rcomplements.Rdiv_le_0_compat. lra.
apply WF_dstate_gt0_le1. assumption.  inversion_clear H. assumption.
 apply WF_dstate_in01_aux. assumption. 
 apply Forall_nil. simpl in *. 
repeat rewrite sum_over_list_cons.
rewrite sum_over_list_nil. 
rewrite Rplus_0_r.  simpl. 
repeat rewrite Rdiv_unfold. 
 rewrite Rmult_comm. rewrite <-Rmult_assoc.
 rewrite (Rmult_comm _ (d_trace_aux d0)). 
 rewrite <-Rmult_assoc.  rewrite <-Rmult_plus_distr_r.
 assert(r * d_trace_aux d + r0 * ( d_trace_aux d0)= d_trace_aux mu).
  rewrite H18. rewrite d_trace_app_aux. simpl.
   repeat rewrite d_trace_map.
 reflexivity.
  lra. lra. apply WWF_dstate_map. lra. 
 apply WWF_dstate_aux_to_WF_dstate_aux. assumption.
 apply WWF_dstate_map. lra.  apply WWF_dstate_aux_to_WF_dstate_aux.
 assumption. 
 rewrite <-H21. rewrite (Rmult_comm _ r).
 rewrite (Rmult_comm _ r0). apply Rinv_r.  rewrite H21. 
 apply WWF_dstate_not_0. assumption.
 inversion_clear H. apply WWF_dstate_aux_to_WF_dstate_aux. 
 assumption. 
econstructor. inversion_clear H. assumption.
apply H21. 


destruct d. destruct d0.
simpl in *. intuition.
simpl in *. rewrite Rmult_0_r in *.
inversion_clear H21. simpl in *.
repeat rewrite sum_over_list_cons in H23.
rewrite sum_over_list_nil in *. rewrite Rplus_0_r in *.
simpl in *. rewrite Rplus_0_l in *. 
destruct H23. rewrite H23.

apply sat_Pro_State. 
econstructor. inversion_clear H. assumption. destruct p. 
simpl. rewrite H18. simpl. inversion_clear H9.
inversion_clear H25. inversion_clear H26. econstructor. 
assert((@pair StateMap.Raw.key (qstate s e) c1
((q_scale r0 q1)))= s_scale r0 (c1,q1)). reflexivity.
rewrite H26. apply s_seman_scale. lra. 
 assumption. 
rewrite map2_r_refl. destruct d0. simpl. apply Forall_nil.
 apply State_eval_dstate_Forall. destruct p. simpl. discriminate.
apply d_seman_scale_aux. lra.  apply State_eval_dstate_Forall. discriminate.
apply H27.


destruct d0.
 simpl in *. rewrite Rmult_0_r in *.
inversion_clear H21. simpl in *.  
repeat rewrite sum_over_list_cons in H23.
rewrite sum_over_list_nil in *. rewrite Rplus_0_r in *.
simpl in *. rewrite Rplus_0_r in *.
destruct H23. rewrite H23.

assert(sat_Assert {| StateMap.this := mu; StateMap.sorted := H2 |} (APro [(1, F0); (0, F1)])).
assert(( [(1, F0); (0, F1)])= swap_list ( [(0, F1); (1, F0)]) 0).
reflexivity. rewrite H24. apply rule_POplusC. 
apply sat_Pro_State'. rewrite sat_Assert_to_State.
split. 
econstructor. inversion_clear H. assumption.  
rewrite H18. destruct p.  simpl.  inversion_clear H10.
inversion_clear H26. inversion_clear H27. econstructor. 
assert((@pair StateMap.Raw.key (qstate s e) c1
(q_scale r q1))= s_scale r (c1,q1)). reflexivity.
rewrite H27. apply s_seman_scale. lra.
inversion_clear H27.  assumption.
rewrite map2_l_refl. destruct d. apply Forall_nil.
apply State_eval_dstate_Forall. simpl. destruct p. discriminate.
apply d_seman_scale_aux. lra. 
 apply State_eval_dstate_Forall. discriminate. 
apply H28. inversion_clear H'. inversion_clear H26. assumption.
 inversion_clear H24. assumption. 


inversion_clear IHd.
inversion_clear IHd0. 

econstructor. 
assert(big_dapp'
([r / d_trace_aux mu * d_trace_aux ((p :: d));
 r0 / d_trace_aux mu * ( d_trace_aux ((p0 :: d0)))])

 ([d_scale_not_0 (d_trace_aux mu ) (d_scale_not_0 (R1/d_trace_aux ((p :: d))) (StateMap.Build_slist H22));
 d_scale_not_0 (d_trace_aux mu ) (d_scale_not_0 (R1/d_trace_aux ((p0 :: d0))) (StateMap.Build_slist H24))
 ])
 
 (d_app (d_scale_not_0 (r / d_trace_aux mu * d_trace_aux ((p :: d))) 
       (d_scale_not_0 (d_trace_aux mu ) (d_scale_not_0 (R1/d_trace_aux ((p :: d))) (StateMap.Build_slist H22)))
 ) (d_app (d_scale_not_0 (r0 / d_trace_aux mu * (d_trace_aux (p0 :: d0))) (d_scale_not_0 (d_trace_aux mu ) (d_scale_not_0 (R1/d_trace_aux (p0 :: d0)) (StateMap.Build_slist H24))) ) (d_empty s e)))).

 econstructor. apply d_scalar_r.
 assert(
  r / d_trace_aux mu * d_trace_aux (p :: d) > 0).
  apply Rmult_gt_0_compat.
  apply Rdiv_lt_0_compat.
  lra. apply WF_dstate_gt0_le1.
  assumption. inversion_clear H. assumption.
  apply WF_dstate_gt0_le1. discriminate. 
  apply WF_sat_State in H10. assumption.
   lra.
   econstructor. 
 
 apply d_scalar_r. 
 assert(
r0 / d_trace_aux mu * d_trace_aux (p0 :: d0) > 0).
apply Rmult_gt_0_compat.
apply Rdiv_lt_0_compat.
lra. apply WF_dstate_gt0_le1.
assumption. inversion_clear H. assumption.
apply WF_dstate_gt0_le1. discriminate. assumption.
 lra.
 apply big_dapp_nil.
apply H26. 
apply dstate_eq_trans with (d_app (d_scale_not_0 r (StateMap.Build_slist H22))
(d_scale_not_0 r0 (StateMap.Build_slist (H24)))).
unfold dstate_eq. unfold d_app.
unfold StateMap.map2. unfold d_scale_not_0.
unfold StateMap.map. simpl. assumption.
apply d_app_eq. 
apply dstate_eq_sym. 
eapply dstate_eq_trans. 
apply d_scale_not_0_assoc. 
eapply dstate_eq_trans. 
apply d_scale_not_0_assoc.
unfold dstate_eq.
f_equal. f_equal. 
repeat rewrite Rdiv_unfold. rewrite Rmult_1_l.
 rewrite Rmult_assoc. rewrite Rmult_assoc.
 rewrite <-(Rmult_assoc (d_trace_aux (p :: d))) . 
 rewrite (Rmult_comm (d_trace_aux (p :: d))).
repeat   rewrite Rmult_assoc . 
 rewrite Rinv_r. rewrite Rmult_1_r. 
 rewrite Rinv_l. rewrite Rmult_1_r. reflexivity.
 apply WWF_dstate_not_0. assumption.
 inversion_clear H. apply WWF_dstate_aux_to_WF_dstate_aux. assumption.
 apply WWF_dstate_not_0. discriminate.
 apply WWF_dstate_aux_to_WF_dstate_aux.
 inversion_clear H14. inversion_clear H21.
 assumption.
 
 eapply dstate_eq_trans.
 apply dstate_eq_sym. 
 apply d_app_empty_l.
 eapply dstate_eq_trans.
 apply d_app_comm.
 apply d_app_eq.
 apply dstate_eq_sym. 
eapply dstate_eq_trans. 
apply d_scale_not_0_assoc. 
eapply dstate_eq_trans. 
apply d_scale_not_0_assoc.
unfold dstate_eq.
f_equal. f_equal.  
repeat rewrite Rdiv_unfold. rewrite Rmult_1_l.
 rewrite Rmult_assoc. rewrite Rmult_assoc.
 rewrite <-(Rmult_assoc ( d_trace_aux ((p0 :: d0)))) . 
 rewrite (Rmult_comm ( d_trace_aux ((p0 :: d0)))).
repeat   rewrite Rmult_assoc . 
 rewrite Rinv_r. rewrite Rmult_1_r. 
 rewrite Rinv_l. rewrite Rmult_1_r. reflexivity.

 apply WWF_dstate_not_0. assumption.
 inversion_clear H. apply WWF_dstate_aux_to_WF_dstate_aux. assumption.
 apply WWF_dstate_not_0. discriminate.
 apply WWF_dstate_aux_to_WF_dstate_aux. assumption.
  reflexivity.
 
simpl. econstructor. intros. split.   apply d_seman_scale_not_0.
apply WF_dstate_gt0_le1. assumption.
inversion_clear H. 
assumption. 

assert((R1 / (s_trace p + d_trace_aux d))=
/d_trace ({|
  StateMap.this :=  p :: d;
  StateMap.sorted := H22
|})).  rewrite Rdiv_unfold.
unfold d_trace. rewrite Rmult_1_l. simpl. reflexivity.
rewrite H27.
 apply d_seman_scale''. intuition.
 apply (ruleState _ _ _ c0 q0 IHd).
 assumption. discriminate. discriminate. 
 rewrite d_trace_scale_not_0.
 rewrite d_trace_scale_not_0. 
 unfold d_trace. simpl.
 rewrite Rdiv_unfold. rewrite Rmult_1_l.
 rewrite Rinv_l. rewrite Rmult_1_r. reflexivity.
 assert((s_trace p + d_trace_aux d= d_trace_aux (p::d))).
 reflexivity. rewrite H27.
 apply WWF_dstate_not_0.
 discriminate. apply WWF_dstate_aux_to_WF_dstate_aux. assumption.
 assert((R1 / (s_trace p + d_trace_aux d))=
 /d_trace ({|
   StateMap.this :=  p :: d;
   StateMap.sorted := H22
 |})).  rewrite Rdiv_unfold.
 unfold d_trace. rewrite Rmult_1_l. simpl. reflexivity.
 rewrite H27. 
 apply Rinv_0_lt_compat.  
 apply WF_dstate_gt0_le1. discriminate. assumption.
   apply WF_dstate_gt0_le1. assumption.
  inversion_clear H. assumption.
 econstructor. intros. split.
apply d_seman_scale_not_0.
apply WF_dstate_gt0_le1. assumption.
inversion_clear H.  assumption.
assert((R1 / (s_trace p0 + d_trace_aux d0))=
/d_trace ({|
  StateMap.this :=  p0 :: d0;
  StateMap.sorted := H24
|})).  rewrite Rdiv_unfold.
unfold d_trace. rewrite Rmult_1_l. simpl. reflexivity.
rewrite H27.
 apply d_seman_scale''. intuition.
 apply (ruleState _ _ _ c q IHd0).
 assumption. discriminate. discriminate.
 rewrite d_trace_scale_not_0.
rewrite d_trace_scale_not_0. 
unfold d_trace. simpl.
rewrite Rdiv_unfold. rewrite Rmult_1_l.
rewrite Rinv_l. rewrite Rmult_1_r. reflexivity.
assert((s_trace p0 + d_trace_aux d0= d_trace_aux (p0::d0))).
reflexivity. rewrite H27.
apply WWF_dstate_not_0.
discriminate. apply WWF_dstate_aux_to_WF_dstate_aux. 
assumption.
 assert((R1 / (s_trace p0 + d_trace_aux d0))=
/d_trace ({|
  StateMap.this :=  p0 :: d0;
  StateMap.sorted := H24
|})).  rewrite Rdiv_unfold.
unfold d_trace. rewrite Rmult_1_l. simpl. reflexivity.
rewrite H27.  
apply Rinv_0_lt_compat. 
apply WF_dstate_gt0_le1. discriminate.
assumption.
apply WF_dstate_gt0_le1. assumption.
 inversion_clear H. assumption.
econstructor.


-injection H8. intros. 
econstructor.
assert(length ([((r/ d_trace_aux mu) * d_trace_aux ((c0,q0)::d)); (r0/ d_trace_aux mu) * d_trace_aux (d0)]) = length [F0; F1]).
reflexivity. apply H21. simpl.
assert(distribution_formula[(r / d_trace_aux mu *
(s_trace (c0, q0) + d_trace_aux d), F0);
(r0 / d_trace_aux mu * d_trace_aux d0, F1)]). 
simpl.  econstructor.  simpl. assumption.
split. econstructor.
  simpl. apply Rmult_le_pos. 
apply Rcomplements.Rdiv_le_0_compat. lra.
apply WF_dstate_gt0_le1. assumption.  inversion H. assumption.
assert(s_trace (c0, q0) + d_trace_aux d=d_trace_aux ((c0,q0)::d)).
 reflexivity. rewrite H21.
 apply WF_dstate_in01_aux. apply WF_sat_State in H10.
 intuition. 
 econstructor. simpl.
 apply Rmult_le_pos. 
apply Rcomplements.Rdiv_le_0_compat. lra.
apply WF_dstate_gt0_le1. assumption.  inversion H. assumption.
 apply WF_dstate_in01_aux. assumption.  
 
 apply Forall_nil. simpl in *.
repeat rewrite sum_over_list_cons.
rewrite sum_over_list_nil. 
rewrite Rplus_0_r.  simpl. 
repeat rewrite Rdiv_unfold. 
 rewrite (Rmult_comm r).   rewrite (Rmult_comm r0).
 repeat rewrite Rmult_assoc. rewrite <-Rmult_plus_distr_l.
  assert(r * ((s_trace (c0, q0) + d_trace_aux d)) + r0 * ( d_trace_aux d0)= d_trace_aux mu).
  rewrite H18. rewrite app_fix. rewrite d_trace_app_aux. simpl.
   repeat rewrite d_trace_map. unfold s_trace. simpl.
  rewrite q_trace_scale. rewrite Rmult_plus_distr_l. reflexivity.
  lra. lra. lra.  
 econstructor.  apply WWF_qstate_scale. 
 split. lra. apply WWF_qstate_to_WF_qstate. assumption.     
 apply WWF_dstate_map. lra.  apply WWF_dstate_aux_to_WF_dstate_aux.
 assumption. 
 apply WWF_dstate_map. lra. 
 apply WWF_dstate_aux_to_WF_dstate_aux. assumption. 
 rewrite <-H21. apply Rinv_l.  rewrite H21. 
 apply WWF_dstate_not_0. assumption.
 inversion_clear H. apply WWF_dstate_aux_to_WF_dstate_aux. 
 assumption. simpl. 
 econstructor. inversion_clear H. assumption. 
simpl. apply H21.


destruct d0.
 simpl in *. rewrite Rmult_0_r in *.
inversion_clear H21 as [H'' H22]. destruct H22 as [H22 H23].  simpl in *.
 repeat rewrite sum_over_list_cons in H23.
rewrite sum_over_list_nil in *. rewrite Rplus_0_r in *.
simpl in *. rewrite Rplus_0_r in *.  rewrite H23.

assert(sat_Assert {| StateMap.this := mu; StateMap.sorted := H2 |} (APro [(1, F0); (0, F1)])).
assert(( [(1, F0); (0, F1)])= swap_list ( [(0, F1); (1, F0)]) 0).
reflexivity. rewrite H21. apply rule_POplusC. 
apply sat_Pro_State'. rewrite sat_Assert_to_State.
split. 
econstructor.  inversion_clear H. assumption.
simpl.  
rewrite H18. simpl.  inversion_clear H10.
inversion_clear H25. econstructor. 
assert((@pair StateMap.Raw.key (qstate s e) c0
(q_scale r q0))= s_scale r (c0,q0)). reflexivity.
rewrite H25. apply s_seman_scale. lra.
 assumption.
rewrite map2_l_refl. destruct d. apply Forall_nil.
apply State_eval_dstate_Forall. destruct p. simpl.  discriminate.
apply d_seman_scale_aux. lra.  apply State_eval_dstate_Forall. discriminate.
apply H26. inversion_clear H'.  inversion_clear H25. assumption.  inversion_clear H21. assumption. 

inversion_clear IHd0.

econstructor. 
assert(big_dapp'
([r / d_trace_aux mu * d_trace_aux (((c0,q0)::d));
 r0 / d_trace_aux mu * ( d_trace_aux ((p :: d0)))])

 ([d_scale_not_0 (d_trace_aux mu ) (d_scale_not_0 (R1/d_trace_aux ((c0,q0)::d)) (StateMap.Build_slist IHd));
 d_scale_not_0 (d_trace_aux mu ) (d_scale_not_0 (R1/d_trace_aux ((p :: d0))) (StateMap.Build_slist H22))
 ])
 
 (d_app (d_scale_not_0 (r / d_trace_aux mu * d_trace_aux (((c0,q0)::d))) 
       (d_scale_not_0 (d_trace_aux mu ) (d_scale_not_0 (R1/d_trace_aux ((c0,q0)::d)) (StateMap.Build_slist IHd)))
 ) (d_app (d_scale_not_0 (r0 / d_trace_aux mu * (d_trace_aux ((p :: d0)))) (d_scale_not_0 (d_trace_aux mu ) (d_scale_not_0 (R1/d_trace_aux ((p :: d0))) (StateMap.Build_slist H22))) ) (d_empty s e)))).

 econstructor. apply d_scalar_r.
 assert(
r / d_trace_aux mu * d_trace_aux ((c0,q0) :: d) > 0).
apply Rmult_gt_0_compat.
apply Rdiv_lt_0_compat.
lra. apply WF_dstate_gt0_le1.
assumption. inversion_clear H. assumption.
apply WF_dstate_gt0_le1. discriminate.
apply WF_sat_State in H10. intuition.
 lra.
 econstructor.  
 apply d_scalar_r. 
 assert(
r0 / d_trace_aux mu * d_trace_aux (p :: d0) > 0).
apply Rmult_gt_0_compat.
apply Rdiv_lt_0_compat.
lra. apply WF_dstate_gt0_le1.
assumption. inversion_clear H. assumption.
apply WF_dstate_gt0_le1. discriminate. assumption.
 lra.
 apply big_dapp_nil.
apply H24. 
apply dstate_eq_trans with (d_app (d_scale_not_0 r (StateMap.Build_slist IHd))
(d_scale_not_0 r0 (StateMap.Build_slist (H22)))).
unfold dstate_eq. unfold d_app.
unfold StateMap.map2. unfold d_scale_not_0.
unfold StateMap.map. simpl. assumption.
apply d_app_eq. 
apply dstate_eq_sym. 
eapply dstate_eq_trans. 
apply d_scale_not_0_assoc. 
eapply dstate_eq_trans. 
apply d_scale_not_0_assoc.
unfold dstate_eq.
f_equal. f_equal. 
repeat rewrite Rdiv_unfold. rewrite Rmult_1_l.
 rewrite Rmult_assoc. rewrite Rmult_assoc.
 rewrite <-(Rmult_assoc (d_trace_aux (((c0, q0) :: d)))) . 
 rewrite (Rmult_comm (d_trace_aux ((c0, q0) :: d) )).
repeat   rewrite Rmult_assoc . 
 rewrite Rinv_r. rewrite Rmult_1_r. 
 rewrite Rinv_l. rewrite Rmult_1_r. reflexivity.
 apply WWF_dstate_not_0. assumption.
 inversion_clear H. apply WWF_dstate_aux_to_WF_dstate_aux. assumption.
 apply WWF_dstate_not_0. discriminate.
 apply WWF_dstate_aux_to_WF_dstate_aux. 
 inversion_clear H10. assumption.
 
 eapply dstate_eq_trans.
 apply dstate_eq_sym. 
 apply d_app_empty_l.
 eapply dstate_eq_trans.
 apply d_app_comm.
 apply d_app_eq.
 apply dstate_eq_sym. 
eapply dstate_eq_trans. 
apply d_scale_not_0_assoc. 
eapply dstate_eq_trans. 
apply d_scale_not_0_assoc.
unfold dstate_eq.
f_equal. f_equal.  
repeat rewrite Rdiv_unfold. rewrite Rmult_1_l.
 rewrite Rmult_assoc. rewrite Rmult_assoc.
 rewrite <-(Rmult_assoc ( d_trace_aux ((p :: d0)))) . 
 rewrite (Rmult_comm ( d_trace_aux ((p :: d0)))).
repeat   rewrite Rmult_assoc . 
 rewrite Rinv_r. rewrite Rmult_1_r. 
 rewrite Rinv_l. rewrite Rmult_1_r. reflexivity.
 apply WWF_dstate_not_0. assumption.
 inversion_clear H. apply WWF_dstate_aux_to_WF_dstate_aux. assumption.
 apply WWF_dstate_not_0. discriminate.
 apply WWF_dstate_aux_to_WF_dstate_aux. assumption.
 reflexivity.
 
 simpl. econstructor. intros; split. apply d_seman_scale_not_0.
 apply WF_dstate_gt0_le1. assumption.
 inversion_clear H. 
 assumption.


 assert((R1 / (s_trace (c0,q0) + d_trace_aux d))=
/d_trace ({|
  StateMap.this :=  (c0, q0) :: d;
  StateMap.sorted := IHd
|})).  rewrite Rdiv_unfold.
unfold d_trace. rewrite Rmult_1_l. simpl. reflexivity.
rewrite H25.
 apply d_seman_scale''. intuition. 
 assumption. discriminate.  
 rewrite d_trace_scale_not_0. 
 rewrite d_trace_scale_not_0. 
 unfold d_trace. simpl.
 rewrite Rdiv_unfold. rewrite Rmult_1_l.
 rewrite Rinv_l. rewrite Rmult_1_r. reflexivity.
 assert((s_trace (c0,q0) + d_trace_aux d= d_trace_aux ((c0,q0)::d))).
 reflexivity. rewrite H25.
 apply WWF_dstate_not_0.
 discriminate. apply WWF_dstate_aux_to_WF_dstate_aux. 
 apply WF_sat_State in H10.   
  intuition.  
 assert((R1 / (s_trace (c0,q0) + d_trace_aux d))=
 /d_trace ({|
   StateMap.this :=  (c0, q0) :: d;
   StateMap.sorted := IHd
 |})).  rewrite Rdiv_unfold.
 unfold d_trace. rewrite Rmult_1_l. simpl. reflexivity.
 rewrite H25.  apply Rinv_0_lt_compat.
 apply WF_dstate_gt0_le1. discriminate.
 apply WF_sat_State in H10. intuition. 
  apply WF_dstate_gt0_le1. assumption.
  inversion_clear H. assumption.

 econstructor. intros; split. 
 apply d_seman_scale_not_0.
 apply WF_dstate_gt0_le1. assumption.
 inversion_clear H.  assumption.


 assert((R1 / (s_trace p + d_trace_aux d0))=
/d_trace ({|
  StateMap.this :=  p :: d0;
  StateMap.sorted := H22
|})).  rewrite Rdiv_unfold.
unfold d_trace. rewrite Rmult_1_l. simpl. reflexivity.
rewrite H25.
 apply d_seman_scale''. intuition. 
 apply (ruleState _ _ _ c q IHd0).
 assumption. discriminate. discriminate. 
 rewrite d_trace_scale_not_0.
 rewrite d_trace_scale_not_0. 
 unfold d_trace. simpl.
 rewrite Rdiv_unfold. rewrite Rmult_1_l.
 rewrite Rinv_l. rewrite Rmult_1_r. reflexivity.
 assert((s_trace p + d_trace_aux d0= d_trace_aux (p::d0))).
 reflexivity. rewrite H25.
 apply WWF_dstate_not_0.
 discriminate. apply WWF_dstate_aux_to_WF_dstate_aux.
 assumption. 
 assert((R1 / (s_trace p + d_trace_aux d0))=
/d_trace ({|
  StateMap.this :=  p :: d0;
  StateMap.sorted := H22
|})).  rewrite Rdiv_unfold.
unfold d_trace. rewrite Rmult_1_l. simpl. reflexivity.
rewrite H25.
 apply Rinv_0_lt_compat. 
 apply WF_dstate_gt0_le1.
 discriminate. assumption. 
 apply WF_dstate_gt0_le1. assumption.
  inversion_clear H. assumption.
  econstructor.

reflexivity.
 inversion_clear H3. destruct H10.
simpl in H3. inversion_clear H3.
inversion_clear H12.
econstructor. lra. econstructor.    lra.
econstructor.
assumption. assumption.
inversion_clear H7.
inversion_clear H10.
inversion_clear H11.
discriminate H3.
Qed.


Lemma rule_false: forall s e (mu:list (state s e)) (sigma:cstate) (rho:qstate s e) IHmu H
F0 F1 (b:bexp), 
sat_Assert
       {|
         StateMap.this := (sigma, rho) :: mu;
         StateMap.sorted := IHmu
       |} (ANpro ([F0 /\s b; F1 /\s (BNot b)])) ->
       beval (sigma, rho) b = false->
       sat_Assert
       {|
         StateMap.this := [(sigma, rho)];
         StateMap.sorted := H
       |} (F1 /\s (BNot b))    
        .
Proof. intros. inversion_clear H0.   
  inversion_clear H3. destruct p_n. 
  inversion_clear H4.
  simpl in *. rewrite sum_over_list_nil in H6.
  intuition.  destruct p_n. 
  simpl in H2. intuition. 
  destruct p_n.

 assert(r=0\/r<>0). apply Classical_Prop.classic.
 destruct H3. subst. inversion_clear H4.
 simpl in *. 
 repeat rewrite sum_over_list_cons in *. 
 rewrite sum_over_list_nil in *. simpl in H6.
 rewrite Rplus_0_l in H6. rewrite Rplus_0_r in H6. destruct H6. subst.
 apply sat_Pro_State in H5. rewrite sat_Assert_to_State.
 inversion_clear H5.
 inversion_clear H7. destruct H5.   econstructor.
 apply WF_state_dstate_aux.  inversion_clear H0. assumption.
 simpl. econstructor. intuition. apply Forall_nil. 
 
 
 assert(r0=0\/r0<>0). apply Classical_Prop.classic.
 destruct H6. subst. inversion_clear H4.
 simpl in *.  
 repeat rewrite sum_over_list_cons in *. 
 rewrite sum_over_list_nil in *. simpl in *.
 rewrite Rplus_0_r in *. rewrite Rplus_0_r in *. destruct H7 as [H' H7]. subst.
 assert(sat_Assert
 {|
   StateMap.this := (sigma, rho) :: mu;
   StateMap.sorted := IHmu
 |} (APro ([(0, F1 /\s <{ ~ b }>); (1, F0 /\s b)]))).
 assert([(0, F1 /\s <{ ~ b }>); (1, F0 /\s b)]= swap_list 
 [(1, F0 /\s b); (0, F1 /\s <{ ~ b }>)] 0). reflexivity.
 rewrite H4. apply rule_POplusC.  econstructor.
 assumption. econstructor. assumption. 
  simpl in *.
 repeat rewrite sum_over_list_cons in *. 
 rewrite sum_over_list_nil in *.   rewrite Rplus_0_l.
 rewrite Rplus_0_r. auto. assumption.
 inversion_clear H4.  apply sat_Pro_State in H9. inversion_clear H9.
 inversion_clear H10.  
destruct H9. simpl in H10. rewrite H1 in H10.
 destruct H10.
 
 
inversion_clear H4 as [H' H7]. destruct H7 as [H7 H8].
 inversion_clear H7. inversion_clear H9. clear H10.
rewrite sat_Assert_to_State. 
inversion_clear H5. simpl in *.
destruct mu_n. inversion_clear H11. 
destruct mu_n. simpl in H3. inversion_clear H9.
inversion_clear H12. destruct mu_n. simpl in *.
econstructor. inversion_clear H0.
apply WF_state_dstate_aux. assumption.
simpl.  
assert(dstate_eq mu' (big_dapp [r; r0] [d; d0] )).
apply big_dapp_eq with ([r; r0]) ([d; d0]).
assumption. apply big_dapp'_to_app.
reflexivity. 
econstructor. lra. econstructor. lra.
econstructor. 
assert(dstate_eq
{|
  StateMap.this := (sigma, rho) :: mu;
  StateMap.sorted := IHmu
|} (big_dapp [r; r0] [d; d0])).
apply dstate_eq_trans with mu'.
assumption. assumption. 
simpl in *.   
destruct d as [d Ihd]. 
destruct d0 as [d0 IHd0].
unfold d_app in *. unfold d_scale_not_0 in *.
 unfold StateMap.map2 in *. 
 unfold StateMap.map in *.  unfold dstate_eq in *.
 simpl in *.
 inversion_clear H11. inversion_clear H14. 
 clear H15. destruct H13. simpl. lra. destruct H11. simpl. lra.  
 destruct d. simpl in *. 
 unfold d_trace in H14. simpl in H14.
 apply WF_dstate_gt0_le1 in H0. simpl in H0. lra.
 discriminate.
 destruct d0.
 unfold d_trace in H15. simpl in H15.
 apply WF_dstate_gt0_le1 in H0. simpl in H0. lra.
 discriminate.
 destruct p. destruct p0. 
simpl in *. 
destruct (Cstate_as_OT.compare c c0).
injection H12. intros.
rewrite H17. rewrite H18.
inversion_clear H13. inversion_clear H20.
 inversion_clear H13. simpl in *.  
 rewrite <-H18 in H22.
rewrite <- (state_eq_bexp (sigma, rho) 
  (sigma,q) _) in H22.
  rewrite H1 in H22. destruct H22. intuition.

  injection H12. intros.
  inversion_clear H13. inversion_clear H20.  simpl in *.
  destruct H13.
  rewrite <-H18 in H20.
  rewrite <-(state_eq_bexp (sigma, rho) 
  (sigma ,q) _) in H20.
  rewrite H1 in H20. destruct H20.
  intuition.

  injection H12. intros.
  rewrite H17. rewrite H18.
  inversion_clear H11. inversion_clear H20.
  destruct H11. simpl in *.
  econstructor.  split.
  assert((@pair cstate (qstate s e) c0 (q_scale r0 q0)) = s_scale r0 (c0,q0)).
  reflexivity. rewrite H22.
  apply s_seman_scale. lra.  assumption.
  rewrite (state_eq_bexp (c0, r0 .* q0) 
   (c0,q0) _). intuition. reflexivity.
   apply Forall_nil. 
  inversion_clear H11. inversion_clear H12.
  inversion_clear H13.
  simpl in H2. intuition. 
Qed.


Local Open Scope assert_scope.
Theorem rule_while: forall F0 F1 (b:bexp) (c:com),
         {{F0 /\s b}} c {{ ANpro [(F0 /\s b) ; (F1 /\s (BNot b))] }}
      -> {{ANpro[(F0 /\s b); (F1/\s (BNot b))]}}
         while b do c end
         {{ (F1 /\s (BNot b)) }}.
Proof.
       unfold hoare_triple.
        intros F0 F1 b c. intros H. 
      intros s e (mu,IHmu) (mu', IHmu'). intros.
      inversion_clear H0. simpl in *.
      
      remember <{while b do c end}> as original_command eqn:Horig. 
      induction H3;  try inversion Horig; subst.

     *rewrite sat_Assert_to_State. econstructor. 
      econstructor. simpl. split; auto. 
      inversion_clear H1. destruct p_n. simpl in H3. discriminate.
      destruct p_n. simpl in H3. discriminate.
      destruct p_n. inversion_clear H6. 
      inversion_clear H7. simpl in *. inversion_clear H6.
      inversion_clear H10. simpl in *. apply H6. simpl in *. discriminate.

      
      *
      assert(Sorted (StateMap.Raw.PX.ltk (elt:=qstate s e))
      [(sigma, rho)]).  apply Sorted_cons. apply Sorted_nil. apply HdRel_nil.
      assert(Sorted (StateMap.Raw.PX.ltk (elt:=qstate s e))
      mu1). apply ceval_sorted with (c) [(sigma, rho)] . 
      assumption.  assumption.
      assert(Sorted (StateMap.Raw.PX.ltk (elt:=qstate s e))
      mu'). apply ceval_sorted with (<{ while b do c end }>) mu1 .
      assumption. assumption. 
      assert(Sorted (StateMap.Raw.PX.ltk (elt:=qstate s e))
      mu''). apply ceval_sorted with (<{ while b do c end }>) mu. 
      inversion_clear IHmu. assumption. assumption. 
      assert(WF_dstate_aux [(sigma, rho)]).
      apply WF_state_dstate_aux. 
      inversion_clear H2. assumption.
      
      destruct mu. simpl in *. inversion H3_; subst.
      remember (StateMap.Raw.map2 option_app mu' []).
      rewrite map2_nil_r in Heqt0. subst.
      apply IHceval_single3 with H4. 
      apply H with (StateMap.Build_slist H3).
       econstructor. intuition.  assumption. 
       apply rule1 with [] IHmu F1. assumption.
       assumption.   
       apply WF_ceval with c [(sigma, rho)].
       assumption. intuition. 
       intuition.
      
     assert(sat_State (d_app (StateMap.Build_slist H5) (StateMap.Build_slist H6)) (F1 /\s (BNot b))).
     apply (d_seman_app' _ _ _ (StateMap.Build_slist H5) (StateMap.Build_slist H6)). 
     rewrite <-sat_Assert_to_State.
     apply IHceval_single3 with H4. 
     apply H with (StateMap.Build_slist H3).
      econstructor. intuition.  assumption. 
      apply rule1 with (p :: mu) IHmu F1. assumption.
      assumption.   
      apply WF_ceval with c [(sigma, rho)].
      assumption. intuition.  intuition.

      inversion_clear IHmu. 
      assert( (sat_Assert (StateMap.Build_slist H8) (ANpro [F0 /\s b; F1 /\s (BNot b)]))).
      apply rule2 with sigma rho IHmu. assumption. discriminate.
   
      rewrite<- sat_Assert_to_State.
      apply IHceval_single1 with (H8).
     assumption.  inversion_clear H2. assumption. reflexivity.
    
     apply WF_ceval with (<{ while b do c end }>) ((sigma, rho) :: (p :: mu)).
     intuition. simpl. apply E_While_true with mu1.
     assumption. assumption. assumption. assumption.
     unfold d_app in H8. unfold StateMap.map2 in H8. simpl in H8.
     inversion_clear H8. rewrite sat_Assert_to_State. 
     econstructor.   intuition.
      apply H10. 
     
     *assert(Sorted (StateMap.Raw.PX.ltk (elt:=qstate s e))
     [(sigma, rho)]).  apply Sorted_cons. apply Sorted_nil. apply HdRel_nil.
     assert(Sorted (StateMap.Raw.PX.ltk (elt:=qstate s e))
      mu'). apply ceval_sorted with (<{ while b do c end }>) mu. 
      inversion_clear IHmu. assumption. assumption.
      
      destruct mu. simpl in *. inversion H3; subst.
     apply rule_false with [] IHmu F0. assumption.
     assumption.

     rewrite sat_Assert_to_State. 
     assert(sat_State (d_app (StateMap.Build_slist H4) (StateMap.Build_slist H5)) (F1 /\s (BNot b))).
     apply (d_seman_app' _ _ _ (StateMap.Build_slist H4) (StateMap.Build_slist H5)).
     rewrite <-sat_Assert_to_State. 
     apply rule_false with (p::mu) IHmu F0. assumption.
     assumption.
    
     inversion_clear IHmu.
     assert((sat_Assert (StateMap.Build_slist H6) (ANpro [F0 /\s b; F1 /\s (BNot b)]))).
     apply rule2 with sigma rho IHmu. assumption. discriminate.
     rewrite <-sat_Assert_to_State. 
     apply IHceval_single with H6. 
     assumption. inversion_clear H2. intuition.  reflexivity.
     apply WF_ceval with (<{ while b do c end }>) ((sigma, rho) :: (p::mu)).
     intuition. apply E_While_false. assumption. intuition.
     inversion_clear H6. econstructor. intuition. intuition.
Qed.



Theorem rule_while': forall F0 F1 (b:bexp) (c:com),
         {{F0 /\s b}} c {{ ANpro [(F0 /\s b) ; (F1 /\s (BNot b))] }}
      -> {{(F0 /\s b)}}
         while b do c end
         {{ (F1 /\s (BNot b)) }}.
Proof. intros. apply while_seq. apply rule_seq with (ANpro[F0 /\s b; F1 /\s (BNot b)]).
          assumption. apply rule_while. assumption.
Qed.



Theorem rule_while_classic: forall F (b:bexp) (c:com),
         {{F /\p b}} c {{ F}}
      -> {{F}}
         while b do c end
         {{ (F /\p (BNot b)) }}.
Proof.  intros.  
assert(F ->> ANpro [F /\s b ; F /\s (BNot b)]).
rule_solve. 
assert(StateMap.this mu=[] \/ StateMap.this mu <>[]).
apply Classical_Prop.classic. destruct H3.
apply sat_Assert_empty. simpl.
split. econstructor;simpl. auto. 
econstructor; simpl; auto; econstructor. discriminate. assumption.
apply sat_State_Npro; try  assumption. simpl. auto. 
intros. apply H2 in H4. simpl in *. destruct (beval (x, d_find x mu) b); simpl;[left|right]; auto.
eapply rule_conseq. apply rule_while. 
eapply rule_conseq_r. apply H0. eapply rule_conseq_l. apply SAnd_PAnd_eq. assumption.
assumption.  apply SAnd_PAnd_eq.
Qed.



