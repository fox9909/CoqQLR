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
From Quan Require Import QState.
From Quan Require Import QIMP_L.
From Quan Require Import QAssert.
From Quan Require Import Par_trace.
From Quan Require Import QRule_Q_L.
From Quan Require Import QRule_E_L.
Require Import Forall_two.

Local Open Scope com_scope.


Open Scope rule_scope.
Theorem rule_skip : forall (D: Assertion), {{D}} skip {{D}}.
Proof. unfold hoare_triple. intros. 
       inversion_clear H. apply ceval_skip_1 in H2.
       apply sat_Assert_dstate_eq with mu.
       unfold dstate_eq. intuition.
       intuition. 
Qed.


Theorem rule_assgn: forall (P:Pure_formula) (i:nat) ( a:aexp),
             {{PAssn i a P}} i := a {{P}}.
Proof. unfold hoare_triple;
       intros F X a s e (mu,IHmu) (mu', IHmu').
       intros. 
       inversion_clear H; simpl in H2.
       rewrite sat_Assert_to_State in *.
       inversion_clear H0.
       apply sat_F. eapply WF_ceval. apply H1. apply H2. 
       apply rule_asgn_aux with X a mu.
       intuition. intuition. assumption. 
Qed. 


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
       inversion_clear H0. simpl in H3. 
       destruct H3. unfold x0.
       rewrite seman_find. split.
       assumption. split. discriminate.
       intros. simpl.
       rewrite bool_true. intuition.
       reflexivity.
Qed.


Theorem rule_seq : forall (P Q R:Assertion) c1 c2,
              {{P}} c1 {{Q}} ->
              {{Q}} c2 {{R}} ->
              {{P}} c1; c2 {{R}}.
Proof.   unfold hoare_triple.  
         intros P Q R2 c1 c2 H1 H2 s e (mu,IHmu) (mu',IHmu').
         intros. inversion H;subst. 
         simpl in H4.
         inversion H4;subst. apply WF_sat_Assert in H0.
         simpl in H0. destruct H0. destruct H0. reflexivity.
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

Lemma implies_refl: forall (D:Assertion), D->> D.
Proof. unfold assert_implies. intros. assumption. Qed.


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


Lemma seman_assert_False: forall s e (mu:dstate s e),
sat_Assert mu <{ false }>-> False .
Proof. intros s e(mu,IHmu).   induction mu; intros;
      rewrite sat_Assert_to_State in *; 
      inversion_clear H; 
    simpl in H1. destruct H1.   
    destruct a. destruct mu. inversion_clear H1.
    destruct H. inversion_clear H1. destruct H.
Qed.

Theorem rule_Absurd: forall D c,  {{BFalse}} c {{D}} .
Proof. intros. unfold hoare_triple. 
       intros. apply seman_assert_False in H0.
       destruct H0. 
Qed.


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

Import Ceval_Linear.
Theorem rule_sum: forall (nF1 nF2: npro_formula ) c  (p_n:list R),
            (Forall (fun x=> 0 < x %R) p_n)->
             length nF1 = length p_n -> 
            ((Forall_two ( fun (i j: State_formula) => {{i}} c{{ j}} ) nF1 nF2))
         -> {{npro_to_pro_formula nF1 p_n}} c
            {{npro_to_pro_formula nF2 p_n}}.
Proof.  unfold hoare_triple. intros nF1 nF2 c p_n H'. intros.  
inversion_clear H2. inversion_clear H5.
 constructor.  inversion_clear H1. eapply WF_ceval. apply H5. apply H8. 
 econstructor; rewrite (get_pro_formula_eq nF1);
 try rewrite <-(Forall_two_length_eq ( fun (i j: State_formula) => {{i}} c{{ j}} ) nF1 ); inversion_clear H4; 
 try assumption.

 rewrite get_pro_formula_p_n in *.

 assert(exists (mu_n': list (dstate s e)), 
 and (Forall_two ( fun i j=>ceval c i j ) mu_n mu_n')
 (dstate_eq mu' (big_dapp p_n mu_n'))).
 apply ceval_big_dapp with mu.
 assumption. inversion_clear H4.
  rewrite get_pro_formula_p_n in H8; try assumption.
  lra. assert( p_n = get_pro_formula (npro_to_pro_formula nF1 p_n)).
  rewrite get_pro_formula_p_n. reflexivity. assumption.
  rewrite H5. unfold get_pro_formula. 
  eapply Forall_two_map; try apply H7. simpl.  intros. apply WF_sat_State with (snd j).
  apply H8. assumption.  apply big_dapp'_length with mu'0.
  assumption. 
 apply dstate_eq_trans with mu'0. assumption.
 apply big_dapp_eq with p_n mu_n. assumption.
  apply big_dapp'_to_app. apply big_dapp'_length with mu'0.
  assumption.  assumption.
 assumption.
 destruct H5. destruct H5.
 econstructor.  rewrite get_pro_formula_p_n.
 assert(big_dapp' p_n x ((big_dapp p_n x))).
 apply big_dapp'_to_app. 
  rewrite <-(Forall_two_length_eq (( fun i j=>ceval c i j ))  mu_n).
  apply big_dapp'_length with mu'0. assumption. assumption.
  assumption.  apply H9.
 rewrite <-(Forall_two_length_eq (( fun (i j: State_formula)=>{{i}} c {{j}} )) nF1 _).
 assumption. assumption. assumption. 
 eapply big_add_ceval with mu_n nF1 c mu; try assumption. apply eq_trans with (length p_n).
 symmetry.
 apply big_dapp'_length with mu'0. assumption. symmetry.  assumption.
 symmetry. assumption. assumption.
Qed.



Import Sorted.
Lemma rule_cond_aux: forall (F F':State_formula) (b:bexp) c1 c2,
{{F/\s b}} c1 {{F'}}->
{{F /\s b}} if b then c1 else c2 end {{F'}}.
Proof. unfold hoare_triple.  intros F F' b c1 c2. 
       intro.  intros s e (mu, IHmu); induction mu; 
       intros (mu' ,IHmu'); intros; 
       rewrite sat_Assert_to_State in *.

       (*mu=[]*)
      - inversion_clear H1; apply State_eval_conj in H3;
       destruct H3. simpl in *. destruct H1.
       
       (*mu<>mu*)
       -inversion_clear H0.
       simpl in *. inversion H3; subst.
       
       --(*b=true*)
       econstructor. eapply WF_ceval. apply  H2. apply H3.
       destruct mu. inversion H11; subst.
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
       assert(sat_Assert (StateMap.Build_slist H0) F').
       apply H with (StateMap.Build_slist H4).
       apply E_com. intuition. 
       simpl. intuition. rewrite sat_Assert_to_State.
       inversion_clear H1. 
       constructor. intuition.
       simpl in *. 
       intuition. rewrite sat_Assert_to_State in H6.
       inversion_clear H6. assumption. 
       

      
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
       inversion_clear H13. simpl. assumption.
       rewrite sat_Assert_to_State in *.  
       inversion_clear H9.    
       assumption.   
      

       inversion_clear H1.  simpl in *.
       inversion_clear H4. 
       rewrite H8 in H1. destruct H1. destruct H4.
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
       - inversion_clear H1; apply State_eval_conj in H3;
       destruct H3. simpl in *. destruct H1.

       (*mu<>mu*)
       -inversion_clear H0.
       simpl in *. inversion H3; subst.

       --(*b=true*)  inversion_clear H1.  simpl in *.
       inversion_clear H4. 
       rewrite H8 in H1. destruct H1. destruct H4. intuition.
       --(*b=false*)
       econstructor. eapply WF_ceval. apply H2. apply H3.
       destruct mu. inversion H11; subst.
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
       assert(sat_Assert (StateMap.Build_slist H0) F').
       apply H with (StateMap.Build_slist H4).
       apply E_com. intuition.
       simpl. intuition. rewrite sat_Assert_to_State.
       inversion_clear H1. 
       constructor. intuition.
       simpl in *. 
       intuition. rewrite sat_Assert_to_State in H6.
       inversion_clear H6. assumption.
       
       
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
       inversion_clear H13. intuition.
       rewrite sat_Assert_to_State in *.
       inversion_clear H9. intuition.
Qed.

Check ([1;2]).

Local Open Scope R_scope.
Local Open Scope assert_scope.
Theorem rule_cond: forall (F1 F1' F2 F2': State_formula) (c1 c2:com) (b:bexp) (p:R),
        0<=p<=1->
        ({{F1 /\s (b)}} c1 {{F1'}} /\ {{F2 /\s ((BNot b) )}} c2 {{F2'}})
     -> ({{ APro [(p, (F1 /\s b)) ; ((1 - p), (F2 /\s (BNot b)))]}}
        if b then c1 else c2 end
        {{APro [(p, F1') ; ((1 - p), F2')]}}).
Proof. intros. 
       destruct (Req_dec p 0). subst. rewrite Rminus_0_r in *.
       eapply rule_conseq. apply rule_cond_aux_2. apply H0.
       unfold assert_implies; intros. apply sat_Pro_State' in H1. assumption.
       unfold assert_implies; intros. apply sat_Pro_State'. assumption.
     
       destruct (Req_dec p 1). subst. rewrite  Rcomplements.Rminus_eq_0 in *.
       eapply rule_conseq. apply rule_cond_aux. apply H0.
       unfold assert_implies; intros. apply (rule_POplusC _ 0 ) in H2. simpl in H2.
       apply sat_Pro_State' in H2. assumption.
       unfold assert_implies; intros. rewrite <-sat_Pro_State' in H2.
       apply (rule_POplusC _ 0 ) in H2. simpl in H2. apply H2.

       assert ([(p, F1 /\s b); (1 - p, F2 /\s (BNot b))]=
       (npro_to_pro_formula ([(F1 /\s b); ( F2 /\s (BNot b))]) ([p; (1-p)]))).
       simpl. reflexivity. rewrite H3. 
       assert ([(p, F1'); (1 - p, F2')]=
       (npro_to_pro_formula ([(F1'); ( F2')]) ([p; (1-p)]))).
       reflexivity. rewrite H4.
       apply rule_sum. simpl. econstructor.
       lra. econstructor. lra. apply Forall_nil.
       reflexivity.
       econstructor.  apply rule_cond_aux. intuition. 
       econstructor. apply rule_cond_aux_2. intuition.
      econstructor.  
Qed.

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
              0< p1 /\ 0< p2->
              {{F1}} c {{pF1}}->
              {{F2}} c {{pF2}} ->
            {{APro [(p1,F1);(p2,F2)]}} c
            {{pro_formula_linear [pF1; pF2] [p1; p2]}}.
Proof.  unfold hoare_triple. intros F1 F2 pF1 pF2 c p1 p2 HF1 HF2.
intros.  inversion_clear H3. inversion_clear H6.
simpl in *.

 assert(exists (mu_n': list (dstate s e)), 
 and ((Forall_two.Forall_two (fun x y : dstate s e => ceval c x y) mu_n mu_n'))
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
econstructor. rewrite get_pro_formula_app. simpl. 
rewrite Forall_app. split.
apply Forall_map. apply Forall_impl with  (fun x : R => 0 <= x).
intros. apply Rmult_le_pos. lra. assumption.
inversion_clear H12. assumption. 
apply Forall_map. apply Forall_impl with  (fun x : R => 0 <= x).
intros. apply Rmult_le_pos. lra. assumption.
inversion_clear H19. assumption. 
rewrite get_pro_formula_app. simpl. 
rewrite sum_over_list_app. 
repeat rewrite sum_over_list_map. 
inversion_clear H12. rewrite H24. 
inversion_clear H19. rewrite H25. 
repeat rewrite Rmult_1_r. inversion_clear H5. 
simpl in H26. repeat rewrite sum_over_list_cons in H26. 
rewrite sum_over_list_nil in H26. rewrite Rplus_0_r in H26.
assumption.
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


Lemma while_seq: forall (b:bexp) c F0  F1, 
{{F0 /\s b}} c; while b do c end {{F1 /\s ((BNot b))}} ->
{{F0 /\s b}} while b do c end {{F1 /\s (BNot b)}} .
Proof. unfold hoare_triple. intros b c F0 F1 H.  
        intros s e(mu, IHmu); induction mu; intros;
        destruct mu' as  [mu' IHmu']; 
        inversion_clear H0; inversion H3; subst;
        rewrite sat_Assert_to_State in *; simpl in *.
        apply WF_sat_State in H1.
        destruct H1. destruct H0. reflexivity.


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
       assert(sat_Assert (StateMap.Build_slist H0) (F1 /\s (BNot b))).
       apply H with (StateMap.Build_slist H4).
       apply E_com. intuition. 
       simpl. apply E_Seq with mu1.  intuition.
       assumption.
       rewrite sat_Assert_to_State.
       inversion_clear H1. 
       constructor. intuition.
       simpl in *. 
       intuition. rewrite sat_Assert_to_State in H6.
       inversion_clear H6. assumption. 

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
       
       
       inversion_clear H1. simpl in H4.
       inversion_clear H4. 
       rewrite H7 in H1. destruct H1. destruct H4.
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
 rewrite Rplus_0_l in H6. rewrite Rplus_0_r in H6. subst.
 apply sat_Pro_State in H5.  inversion_clear H5. inversion_clear H6. destruct H5. 
 simpl in H6.  rewrite H1 in H6. 
 simpl in H6. destruct H6. 
 assert(r0=0\/r0<>0). apply Classical_Prop.classic.
 destruct H6. subst. inversion_clear H4.
 simpl in *. 
 repeat rewrite sum_over_list_cons in *. 
 rewrite sum_over_list_nil in *. simpl in H6.
 rewrite Rplus_0_l in H7. rewrite Rplus_0_r in H7.
 simpl in H7. subst. 
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
 rewrite Rplus_0_r. auto. assumption. apply sat_Pro_State' in H4. 
 rewrite sat_Assert_to_State in *. 
 inversion_clear H4. inversion_clear H8. destruct H4. 
 econstructor.
 apply WF_state_dstate_aux.  inversion_clear H0. assumption.
 simpl. econstructor. rewrite H1.  intuition. apply Forall_nil.
 
 inversion_clear H4. simpl in *. inversion_clear H7. inversion_clear H9. clear H10.
rewrite sat_Assert_to_State. 
inversion_clear H5. simpl in *. 
destruct mu_n. inversion_clear H11.
destruct mu_n.  inversion_clear H9.
inversion_clear H12. destruct mu_n. simpl in *.
inversion_clear H11. inversion_clear H12. clear H13.
destruct H5. simpl. lra. destruct H11. simpl. lra. simpl in *.
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
  apply WF_sat_State in H5.
 simpl in *. intuition. 
 destruct d0. 
  apply WF_sat_State in H11.  
 simpl in *. intuition.
 destruct p. destruct p0. 
simpl in *. 
destruct (Cstate_as_OT.compare c c0).
injection H15. intros. 
rewrite H17. rewrite H18.
 econstructor.  split.
 assert((@pair cstate (qstate s e) c (q_scale r q)) = s_scale r (c,q)).
 reflexivity. rewrite H19.
 apply s_seman_scale. lra.  inversion_clear H5. inversion_clear H21. destruct H5. assumption.
 rewrite (state_eq_bexp (c, q_scale r q) 
  (sigma ,rho) _).  rewrite H1. auto. simpl. rewrite H18. reflexivity. econstructor.

  injection H15. intros.
inversion_clear H11. inversion_clear H20.
  inversion_clear H11.  simpl in *.
  unfold Cstate_as_OT.eq in e0. 
  rewrite <-e0 in H22.  
  rewrite <-H18 in H22. 
  rewrite <-(state_eq_bexp (sigma, rho) 
  (sigma ,q0) _) in H22. 
  rewrite H1 in H22. destruct H22. intuition.

  injection H15. intros.
inversion_clear H11. inversion_clear H20.
  inversion_clear H11.  simpl in *.
  rewrite <-H18 in H22. 
  rewrite <-(state_eq_bexp (sigma, rho) 
  (sigma ,q0) _) in H22. 
  rewrite H1 in H22. destruct H22. intuition.
  
  inversion_clear H11. inversion_clear H12. inversion_clear H13.
  simpl in H2.  intuition.
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
 rewrite Rplus_0_l in H6. rewrite Rplus_0_r in H6. subst.
 apply sat_Pro_State in H5. rewrite sat_Assert_to_State.
 inversion_clear H5.
 inversion_clear H6. destruct H5.   econstructor.
 apply WF_state_dstate_aux.  inversion_clear H0. assumption.
 simpl. econstructor. intuition. apply Forall_nil. 
 
 
 assert(r0=0\/r0<>0). apply Classical_Prop.classic.
 destruct H6. subst. inversion_clear H4.
 simpl in *.  
 repeat rewrite sum_over_list_cons in *. 
 rewrite sum_over_list_nil in *. simpl in *.
 rewrite Rplus_0_r in *. rewrite Rplus_0_r in *. subst.
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
 
 
inversion_clear H4. inversion_clear H7. inversion_clear H9. clear H10.
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
 apply WF_sat_State in H13.
 simpl in *. intuition. 
 destruct d0. 
  apply WF_sat_State in H11.
 simpl in *. intuition.
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

      *intros. apply WF_sat_Assert in H1. intuition.
      
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
      
      destruct mu. simpl in *. inversion H4; subst.
     apply rule_false with [] IHmu F0. assumption.
     assumption.

     rewrite sat_Assert_to_State. 
     assert(sat_State (d_app (StateMap.Build_slist H5) (StateMap.Build_slist H6)) (F1 /\s (BNot b))).
     apply (d_seman_app' _ _ _ (StateMap.Build_slist H5) (StateMap.Build_slist H6)).
     rewrite <-sat_Assert_to_State. 
     apply rule_false with (p::mu) IHmu F0. assumption.
     assumption.
    
     inversion_clear IHmu.
     assert((sat_Assert (StateMap.Build_slist H7) (ANpro [F0 /\s b; F1 /\s (BNot b)]))).
     apply rule2 with sigma rho IHmu. assumption. discriminate.
     rewrite <-sat_Assert_to_State. 
     apply IHceval_single with H7. 
     assumption. inversion_clear H2. intuition.  reflexivity.
     apply WF_ceval with (<{ while b do c end }>) ((sigma, rho) :: (p::mu)).
     intuition. apply E_While_false. assumption. intuition. assumption.
     inversion_clear H7. econstructor. intuition. intuition.
Qed.



Theorem rule_while': forall F0 F1 (b:bexp) (c:com),
         {{F0 /\s b}} c {{ ANpro [(F0 /\s b) ; (F1 /\s (BNot b))] }}
      -> {{(F0 /\s b)}}
         while b do c end
         {{ (F1 /\s (BNot b)) }}.
Proof. intros. apply while_seq. apply rule_seq with (ANpro[F0 /\s b; F1 /\s (BNot b)]).
          assumption. apply rule_while. assumption.
Qed.


Theorem rule_OplusC: forall F1 F2 ,
ANpro [F1; F2]->>
ANpro [F2; F1].
Proof.  intros.  unfold assert_implies. 
intros.
inversion_clear H. destruct p_n. discriminate H0. destruct p_n. 
discriminate H0. destruct p_n.  simpl in *. 
apply (rule_POplusC _ 0) in H1. simpl in *. 
econstructor. 
assert(length [r0;r] = length [F2; F1]). simpl. reflexivity.
apply H. simpl. apply H1. 
discriminate H0.
Qed.

Lemma Rmult_plus_gt_0:forall r1 r2 r3 r4,
0<r3/\ 0<r4 /\ 0<=r1 /\ 0<=r2->
~(r1 =0 /\ r2 =0) ->
0<r1*r3+r2*r4.
Proof. intros. apply Classical_Prop.not_and_or in H0. destruct H0. 
       apply Rplus_lt_le_0_compat. apply Rmult_lt_0_compat; try lra. 
       apply Rmult_le_pos; try lra. 
       apply Rplus_le_lt_0_compat. apply Rmult_le_pos; try lra. 
       apply Rmult_lt_0_compat; try lra.  
Qed.


From Quan Require Import Basic.
Local Open Scope  R_scope.
Lemma sat_dapp_npro{s e:nat}: forall (mu1 mu2: (dstate s e)) (F1 F2:State_formula),
sat_Assert (mu1) (ANpro [F1;F2]) ->
sat_Assert (mu2)  (ANpro [F1;F2]) ->
WF_dstate (d_app mu1 mu2)->
sat_Assert (d_app mu1 mu2)  (ANpro [F1;F2]).
Proof. intros. inversion_clear H. inversion_clear H0. 
       destruct p_n; destruct p_n0; try discriminate H2; try discriminate H.
       destruct p_n; destruct p_n0; try discriminate H2; try discriminate H.
       destruct p_n; destruct p_n0; try discriminate H2; try discriminate H.
       assert( (r=0/\r0=0) \/ ~(r=0/\r0=0))%R.
       apply Classical_Prop.classic. destruct H0. 
       destruct H0. rewrite H0 in *. rewrite H5 in *.
       simpl in *. inversion_clear H3. inversion_clear H4. 
       inversion_clear H7. inversion_clear H9.  simpl in *.
       repeat rewrite sum_over_list_cons in *. 
       rewrite sum_over_list_nil in *.  rewrite Rplus_0_l in *. 
       rewrite Rplus_0_r in *. subst. 
       rewrite sat_Pro_State in *. 
       apply rule_OplusC. apply sat_NPro_State. 
       rewrite sat_Assert_to_State.
       apply d_seman_app'; try assumption.

       assert( (r1=0/\r2=0) \/ ~(r1=0/\r2=0))%R.
       apply Classical_Prop.classic. destruct H5. 
       destruct H5. rewrite H5 in *. rewrite H6 in *.
       assert(r=1 /\ r0 =1).
       simpl in *. inversion_clear H3. inversion_clear H4. 
       inversion_clear H8. inversion_clear H10.  simpl in *.
       repeat rewrite sum_over_list_cons in *. 
       rewrite sum_over_list_nil in *.  rewrite Rplus_0_l in *. 
       rewrite Rplus_0_r in *. subst. auto. destruct H7. subst. 
       simpl in *. 
       apply (rule_POplusC _ 0) in H3.   apply (rule_POplusC _ 0) in H4.
       simpl in *. 
       rewrite sat_Pro_State' in *. 
        apply sat_NPro_State. 
       rewrite sat_Assert_to_State in *.
       apply d_seman_app'; try assumption.
       assert(0 < d_trace mu1<=1). 
       apply WF_dstate_gt0_le1; eapply WF_sat_Pro; apply H3.
       assert(0 < d_trace mu2<=1). 
       apply WF_dstate_gt0_le1; eapply WF_sat_Pro; apply H4.

       inversion_clear H3. inversion_clear H4.
       inversion_clear H9. inversion_clear H11. 
       inversion_clear H4. inversion_clear H15. clear H16.
       inversion_clear H9. inversion_clear H16. clear H17. simpl in *.
       repeat rewrite sum_over_list_cons in *. rewrite sum_over_list_nil in *.
       rewrite Rplus_0_r in *.
       assert(length [((r * (d_trace mu1) + r0 * (d_trace mu2)) 
       / ((d_trace mu1)+(d_trace mu2)))%R; ((r1 * (d_trace mu1) + r2 * (d_trace mu2)) 
       / ((d_trace mu1)+(d_trace mu2)))%R] = length [F1; F2])%nat. reflexivity.    
       econstructor. apply H16.

       
       econstructor. assumption.
       simpl. econstructor.  
       econstructor; [|econstructor; [|econstructor] ]; try apply Rcomplements.Rdiv_le_0_compat; try
       apply Rplus_le_le_0_compat; try apply Rmult_le_pos;
       try apply Rplus_lt_0_compat; try assumption; try lra.
       simpl. repeat rewrite sum_over_list_cons in *. rewrite sum_over_list_nil in *.
       rewrite Rplus_0_r in *.  repeat rewrite Rdiv_unfold.
       rewrite <-Rmult_plus_distr_r.   rewrite <-Rplus_assoc. 
       rewrite (Rplus_assoc _ (r0 * d_trace mu2) _). rewrite (Rplus_comm  (r0 * d_trace mu2) _).
        rewrite <-Rplus_assoc.  rewrite <-Rmult_plus_distr_r.
        rewrite Rplus_assoc. rewrite <-Rmult_plus_distr_r.
      rewrite H13. rewrite H14. repeat rewrite Rmult_1_l.  
       apply Rinv_r. apply Rgt_neq_0. apply Rplus_lt_0_compat; lra. 
      simpl. 
       inversion_clear H10. inversion_clear H12. simpl in *.
       destruct mu_n. inversion_clear H19. destruct mu_n. inversion_clear H19.
       inversion_clear H22. inversion_clear H19. inversion_clear H22. clear H23.
       destruct mu_n0. inversion_clear H21. destruct mu_n0. inversion_clear H21.
       inversion_clear H23. inversion_clear H21. inversion_clear H23. clear H24.
       inversion H17; subst. inversion H29; subst. inversion H31; subst.
       clear H31.  clear H17. clear H29.
       inversion H10; subst. inversion H29; subst. inversion H32; subst.
       clear H32.  clear H10. clear H29.
       
       pose(big_dapp'_to_app ([((r * (d_trace mu1) + r0 * (d_trace mu2)) 
       / ((d_trace mu1)+(d_trace mu2)))%R; ((r1 * (d_trace mu1) + r2 * (d_trace mu2)) 
       / ((d_trace mu1)+(d_trace mu2)))%R])
       [((d_scale_not_0 (((d_trace mu1)+(d_trace mu2)) /(r * (d_trace mu1) + r0 * (d_trace mu2))) 
       (d_app r3 r5 ))); ((d_scale_not_0 (((d_trace mu1)+(d_trace mu2)) /(r1 * (d_trace mu1) + r2 * (d_trace mu2))) 
       (d_app r4  r6 )))]  ).
       econstructor. apply b. reflexivity. clear b.
       econstructor. apply Rdiv_lt_0_compat.  
       apply Rmult_plus_gt_0; try lra.
        apply Rplus_lt_0_compat; try lra.
       econstructor. apply Rdiv_lt_0_compat. 
       apply Rmult_plus_gt_0; try lra.
       apply Rplus_lt_0_compat; try lra.
       econstructor. 
   
       simpl. clear b. 
       apply dstate_eq_trans with 
       (d_app
     (( (d_app r3 r5)))
     (( ( (d_app r4 r6)))
        )). 
        apply dstate_eq_trans with (d_app r3 (d_app r5 (d_app r4 r6))).
        apply dstate_eq_trans with (d_app r3 (d_app (d_app r5 r4) r6)).
        apply dstate_eq_trans with (d_app r3 (d_app (d_app r4 r5) r6)).
        apply dstate_eq_trans with (d_app r3 (d_app r4 (d_app r5 r6))).
        apply dstate_eq_trans with (d_app  (d_app r3 r4) (d_app r5 r6)).
        apply d_app_eq. 
        apply dstate_eq_trans with (d_app r3 (d_app r4 (d_empty s e))). assumption.
        apply d_app_eq. apply dstate_eq_refl. apply d_app_empty_r.
        apply dstate_eq_trans with  (d_app r5 (d_app r6 (d_empty s e))). assumption.
        apply d_app_eq. apply dstate_eq_refl. apply d_app_empty_r.
        apply d_app_assoc'. 
        apply d_app_eq. apply dstate_eq_refl. 
        apply dstate_eq_sym.
        apply d_app_assoc'. 
        apply d_app_eq. apply dstate_eq_refl. 
        apply d_app_eq. apply d_app_comm. apply dstate_eq_refl.
        apply d_app_eq. apply dstate_eq_refl.
        apply d_app_assoc'.
        apply dstate_eq_sym. apply d_app_assoc'.
       apply d_app_eq.  
       apply dstate_eq_trans with 
       ((d_scale_not_0 (((r * d_trace mu1 + r0 * d_trace mu2) / (d_trace mu1 + d_trace mu2)) * ((d_trace mu1 + d_trace mu2) / (r * d_trace mu1 + r0 * d_trace mu2))))
       (d_app r3 r5)).
       assert(((r * d_trace mu1 + r0 * d_trace mu2) / (d_trace mu1 + d_trace mu2) *
       ((d_trace mu1 + d_trace mu2) / (r * d_trace mu1 + r0 * d_trace mu2)))=1).
       repeat rewrite Rdiv_unfold.  
       rewrite Rmult_assoc. rewrite <-(Rmult_assoc  (/ (d_trace mu1 + d_trace mu2))).
       rewrite Rinv_l. rewrite Rmult_1_l.
       rewrite Rinv_r. reflexivity. apply Rgt_neq_0.
       apply Rmult_plus_gt_0; try lra. 
       apply Rgt_neq_0. apply Rplus_lt_0_compat; try lra. 
        rewrite H10. apply dstate_eq_sym.
       apply d_scale_not_0_1_l. 
       apply dstate_eq_sym. 
       apply d_scale_not_0_assoc.
       apply dstate_eq_trans with 
       ((d_scale_not_0 (((r1 * d_trace mu1 + r2 * d_trace mu2) / (d_trace mu1 + d_trace mu2)) * ((d_trace mu1 + d_trace mu2) / (r1 * d_trace mu1 + r2 * d_trace mu2))))
       (d_app r4 r6)).
       assert(((r1 * d_trace mu1 + r2 * d_trace mu2) / (d_trace mu1 + d_trace mu2) *
       ((d_trace mu1 + d_trace mu2) / (r1 * d_trace mu1 + r2 * d_trace mu2)))=1).
       repeat rewrite Rdiv_unfold. 
       rewrite Rmult_assoc. rewrite <-(Rmult_assoc  (/ (d_trace mu1 + d_trace mu2))).
       rewrite Rinv_l. rewrite Rmult_1_l.
       rewrite Rinv_r. reflexivity. apply Rgt_neq_0.
       apply Rmult_plus_gt_0; try lra. 
       apply Rgt_neq_0. apply Rplus_lt_0_compat; try lra.  
        rewrite H10. apply dstate_eq_sym.
       apply d_scale_not_0_1_l.
       apply dstate_eq_trans with ((d_scale_not_0
       ((r1 * d_trace mu1 + r2 * d_trace mu2) / (d_trace mu1 + d_trace mu2))
       (d_scale_not_0
          ((d_trace mu1 + d_trace mu2) /
           (r1 * d_trace mu1 + r2 * d_trace mu2)) 
          (d_app r4 r6)))).
          apply dstate_eq_sym. apply d_scale_not_0_assoc.
          apply dstate_eq_sym. apply d_app_empty_r.
        clear b.
       
       
       econstructor; simpl in *. split.
       apply sat_State_dstate_eq with (d_scale_not_0
       (d_trace mu1 + d_trace mu2)
       (d_scale_not_0 (/ (r * d_trace mu1 + r0 * d_trace mu2)) (d_app r3 r5))).
       rewrite Rdiv_unfold. apply d_scale_not_0_assoc.
       apply d_seman_scale'. lra. 
       rewrite d_trace_scale_not_0; try lra. 
       rewrite d_trace_scale_not_0.
       destruct (Req_dec r 0). subst. repeat rewrite Rmult_0_l.
       repeat rewrite Rplus_0_l.
       inversion_clear H28. 
       rewrite (d_trace_eq  (d_app (d_empty s e) r5) r5).
       inversion H27; subst. destruct H0. auto.
       rewrite d_trace_scale_not_0; try lra. 
       destruct H22. lra. rewrite H23.
       rewrite Rinv_l. rewrite Rmult_1_r. rewrite <-d_trace_app.
       apply WF_dstate_in01. assumption. 
       apply WWF_dstate_to_WF_dstate. assumption. 
       apply WWF_dstate_to_WF_dstate. assumption.
       apply Rmult_integral_contrapositive_currified.
       lra. lra. apply d_app_empty_l. lra. 
       destruct (Req_dec r0 0). subst. repeat rewrite Rmult_0_l.
       repeat rewrite Rplus_0_r.
       inversion_clear H27. 
       rewrite (d_trace_eq  (d_app  r3 (d_empty s e) ) r3).
       inversion H28; subst. lra. 
       rewrite d_trace_scale_not_0; try lra. 
       destruct H12. lra. rewrite H24.
       rewrite Rinv_l. rewrite Rmult_1_r. rewrite <-d_trace_app.
       apply WF_dstate_in01. assumption. 
       apply WWF_dstate_to_WF_dstate. assumption. 
       apply WWF_dstate_to_WF_dstate. assumption.
       apply Rmult_integral_contrapositive_currified.
       lra. lra. apply d_app_empty_r. lra.
       inversion H28; subst. lra. inversion H27; subst. lra. 
       rewrite d_trace_app. repeat rewrite d_trace_scale_not_0; try lra. 
       destruct H12. lra. destruct H22. lra. 
       rewrite H26. rewrite H29. rewrite Rinv_l.
       rewrite Rmult_1_r.  
       rewrite <-d_trace_app.
       apply WF_dstate_in01. assumption. 
       apply WWF_dstate_to_WF_dstate. assumption. 
       apply WWF_dstate_to_WF_dstate. assumption.
       apply Rgt_neq_0.
       apply Rmult_plus_gt_0; try lra.
       apply WWF_d_scale_not_0; try lra.
       apply WWF_dstate_to_WF_dstate.
       eapply WF_sat_State. apply H12. lra.
       apply WWF_d_scale_not_0; try lra.
       apply WWF_dstate_to_WF_dstate.
       eapply WF_sat_State. apply H22. lra.
       apply Rinv_0_lt_compat.
       apply Rmult_plus_gt_0; try lra.
       inversion H28; subst; inversion H27; subst.
       destruct H0. auto.
       rewrite Rmult_0_l. rewrite Rplus_0_l.
       apply sat_State_dstate_eq with ((d_scale_not_0 (/ (r0 * d_trace mu2))
       ( (d_scale_not_0 r0 d1)))).
       apply d_scale_not_0_eq. apply dstate_eq_sym.
       apply d_app_empty_l.  
       destruct H22. lra. rewrite<-H23. 
       rewrite<-d_trace_scale_not_0; try lra.
       apply d_seman_scale''. intuition.
       apply d_seman_scale. lra. apply H22.
       rewrite Rmult_0_l. rewrite Rplus_0_r.
       apply sat_State_dstate_eq with ((d_scale_not_0 (/ (r * d_trace mu1))
       ( (d_scale_not_0 r d)))).
       apply d_scale_not_0_eq. apply dstate_eq_sym.
       apply d_app_empty_r.  
       destruct H12. lra. rewrite<-H23. 
       rewrite<-d_trace_scale_not_0; try lra.
       apply d_seman_scale''. intuition.
       apply d_seman_scale. lra. apply H12.
       apply sat_State_dstate_eq with 
       (d_app (d_scale_not_0 (/ (r * d_trace mu1 + r0 * d_trace mu2))
       ((d_scale_not_0 r d))) (d_scale_not_0 (/ (r * d_trace mu1 + r0 * d_trace mu2))
       ((d_scale_not_0 r0 d1)))).
       apply d_scale_not_0_app_distr.
       apply d_seman_app'.
       apply d_seman_scale'. apply Rinv_0_lt_compat.
       apply Rplus_lt_0_compat; apply Rmult_gt_0_compat; try lra.
       rewrite d_trace_scale_not_0; try lra.
       rewrite d_trace_scale_not_0; try lra.
       destruct H12. lra. rewrite H24.  rewrite Rmult_comm. 
       rewrite <-Rdiv_unfold. 
       apply (Rcomplements.Rdiv_le_1 (r * d_trace mu1)). 
       apply Rmult_plus_gt_0; try lra. 
       rewrite <-Rplus_0_r at 1. 
       apply Rplus_le_compat_l. 
       apply Rmult_le_pos; try lra.
       apply Rinv_0_lt_compat.
       apply Rplus_lt_0_compat; apply Rmult_gt_0_compat; try lra.
       apply d_seman_scale; try lra. apply H12. lra.
       apply d_seman_scale'. apply Rinv_0_lt_compat.
       apply Rplus_lt_0_compat; apply Rmult_gt_0_compat; try lra.
       rewrite d_trace_scale_not_0; try lra.
       rewrite d_trace_scale_not_0; try lra.
       destruct H22. lra. rewrite H24. 
       rewrite Rmult_comm. 
       rewrite <-Rdiv_unfold. 
       apply (Rcomplements.Rdiv_le_1 (r0 * d_trace mu2)). 
       apply Rmult_plus_gt_0; try lra. 
       rewrite <-Rplus_0_l at 1. 
       apply Rplus_le_compat_r. 
       apply Rmult_le_pos; try lra.
       apply Rinv_0_lt_compat.
       apply Rplus_lt_0_compat; apply Rmult_gt_0_compat; try lra.
       apply d_seman_scale; try lra. apply H22. lra.
       apply WWF_dstate_to_WF_dstate.
       split. apply WWF_d_app. 
       apply WWF_d_scale_not_0. 
       apply Rinv_0_lt_compat.
       apply Rplus_lt_0_compat; apply Rmult_gt_0_compat; try lra.
       apply WWF_d_scale_not_0. lra.
       apply WWF_dstate_to_WF_dstate.
       eapply WF_sat_State. apply H12. lra.
       apply WWF_d_scale_not_0.  
       apply Rinv_0_lt_compat.
       apply Rplus_lt_0_compat; apply Rmult_gt_0_compat; try lra.
       apply WWF_d_scale_not_0. lra.
       apply WWF_dstate_to_WF_dstate.
       eapply WF_sat_State. apply H22. lra.
       rewrite d_trace_app; try repeat rewrite d_trace_scale_not_0.
       rewrite <-Rmult_plus_distr_l. 
       destruct H12. lra. destruct H22. lra. 
       rewrite H24. rewrite H25. 
       rewrite Rinv_l. lra. apply Rgt_neq_0.
       apply Rmult_plus_gt_0; try lra.
       lra. 
       apply Rinv_0_lt_compat.
       apply Rplus_lt_0_compat; apply Rmult_gt_0_compat; try lra.
       lra.
       apply Rinv_0_lt_compat.
       apply Rplus_lt_0_compat; apply Rmult_gt_0_compat; try lra.
       apply WWF_d_scale_not_0. 
       apply Rinv_0_lt_compat.
       apply Rplus_lt_0_compat; apply Rmult_gt_0_compat; try lra.
       apply WWF_d_scale_not_0. lra.
       apply WWF_dstate_to_WF_dstate.
       eapply WF_sat_State. apply H12. lra.
       apply WWF_d_scale_not_0.  
       apply Rinv_0_lt_compat.
       apply Rplus_lt_0_compat; apply Rmult_gt_0_compat; try lra.
       apply WWF_d_scale_not_0. lra.
       apply WWF_dstate_to_WF_dstate.
       eapply WF_sat_State. apply H22. lra.
       rewrite d_trace_scale_not_0. 
       inversion H28; subst; inversion H27; subst.
       destruct H0; try lra. 
       rewrite Rmult_0_l. rewrite Rplus_0_l.
       rewrite (d_trace_eq (d_app (d_empty s e) (d_scale_not_0 r0 d1)) ((d_scale_not_0 r0 d1))).
       rewrite d_trace_scale_not_0; try lra.
       rewrite Rdiv_unfold.
       rewrite Rmult_assoc. 
       destruct H22. lra. rewrite H23. rewrite Rinv_l.
       rewrite Rmult_1_r. rewrite d_trace_app. reflexivity.
       apply WWF_dstate_to_WF_dstate. assumption.
       apply WWF_dstate_to_WF_dstate. assumption.
       apply Rmult_integral_contrapositive_currified.
       lra. lra. 
       apply d_app_empty_l.
       rewrite Rmult_0_l. rewrite Rplus_0_r.
       rewrite (d_trace_eq (d_app  (d_scale_not_0 r d) (d_empty s e) ) ((d_scale_not_0 r d))).
       rewrite d_trace_scale_not_0; try lra.
       rewrite Rdiv_unfold.
       rewrite Rmult_assoc. 
       destruct H12. lra. rewrite H23. rewrite Rinv_l.
       rewrite Rmult_1_r. rewrite d_trace_app. reflexivity.
       apply WWF_dstate_to_WF_dstate. assumption.
       apply WWF_dstate_to_WF_dstate. assumption.
       apply Rmult_integral_contrapositive_currified.
       lra. lra. 
       apply d_app_empty_r.
       rewrite d_trace_app. repeat rewrite d_trace_scale_not_0; try lra.
       rewrite Rdiv_unfold.
       rewrite Rmult_assoc.
       destruct H12. lra. destruct H22. lra. 
       rewrite H24. rewrite H25.
       rewrite Rinv_l. rewrite Rmult_1_r.
       rewrite d_trace_app. reflexivity.
       apply WWF_dstate_to_WF_dstate. assumption.
       apply WWF_dstate_to_WF_dstate. assumption.
       apply Rgt_neq_0. apply Rmult_plus_gt_0; try lra.
       apply WWF_d_scale_not_0. lra.
       apply WWF_dstate_to_WF_dstate.
       eapply WF_sat_State. apply H12. lra.
       apply WWF_d_scale_not_0. lra.
       apply WWF_dstate_to_WF_dstate.
       eapply WF_sat_State. apply H22. lra.
       apply Rdiv_lt_0_compat.  apply Rplus_lt_0_compat; try lra.
       apply Rmult_plus_gt_0; try lra.
   
       

       econstructor; simpl in *. split.
       apply sat_State_dstate_eq with (d_scale_not_0
       (d_trace mu1 + d_trace mu2)
       (d_scale_not_0 (/ (r1 * d_trace mu1 + r2 * d_trace mu2)) (d_app r4 r6))).
       rewrite Rdiv_unfold. apply d_scale_not_0_assoc.
       apply d_seman_scale'. lra. 
       rewrite d_trace_scale_not_0; try lra. 
       rewrite d_trace_scale_not_0.
       destruct (Req_dec r1 0). subst. repeat rewrite Rmult_0_l.
       repeat rewrite Rplus_0_l.
       inversion_clear H30. 
       rewrite (d_trace_eq  (d_app (d_empty s e) r6) r6).
       inversion H31; subst. destruct H5. auto.
       rewrite d_trace_scale_not_0; try lra. 
       destruct H21. lra. rewrite H23.
       rewrite Rinv_l. rewrite Rmult_1_r. rewrite <-d_trace_app.
       apply WF_dstate_in01. assumption. 
       apply WWF_dstate_to_WF_dstate. assumption. 
       apply WWF_dstate_to_WF_dstate. assumption.
       apply Rmult_integral_contrapositive_currified.
       lra. lra. apply d_app_empty_l. lra. 
       destruct (Req_dec r2 0). subst. repeat rewrite Rmult_0_l.
       repeat rewrite Rplus_0_r.
       inversion_clear H31. 
       rewrite (d_trace_eq  (d_app  r4 (d_empty s e) ) r4).
       inversion H30; subst. lra. 
       rewrite d_trace_scale_not_0; try lra. 
       destruct H19. lra. rewrite H24.
       rewrite Rinv_l. rewrite Rmult_1_r. rewrite <-d_trace_app.
       apply WF_dstate_in01. assumption. 
       apply WWF_dstate_to_WF_dstate. assumption. 
       apply WWF_dstate_to_WF_dstate. assumption.
       apply Rmult_integral_contrapositive_currified.
       lra. lra. apply d_app_empty_r. lra.
       inversion H30; subst. lra. inversion H31; subst. lra. 
       rewrite d_trace_app. repeat rewrite d_trace_scale_not_0; try lra. 
       destruct H19. lra. destruct H21. lra. 
       rewrite H26. rewrite H29. rewrite Rinv_l.
       rewrite Rmult_1_r.  
       rewrite <-d_trace_app.
       apply WF_dstate_in01. assumption. 
       apply WWF_dstate_to_WF_dstate. assumption. 
       apply WWF_dstate_to_WF_dstate. assumption.
       apply Rgt_neq_0. apply Rmult_plus_gt_0; try lra.
       apply WWF_d_scale_not_0; try lra.
       apply WWF_dstate_to_WF_dstate.
       eapply WF_sat_State. apply H19. lra.
       apply WWF_d_scale_not_0; try lra.
       apply WWF_dstate_to_WF_dstate.
       eapply WF_sat_State. apply H21. lra.
       apply Rinv_0_lt_compat.
       apply Rmult_plus_gt_0; try lra.
       inversion H30; subst; inversion H31; subst.
       destruct H5. auto.
       rewrite Rmult_0_l. rewrite Rplus_0_l.
       apply sat_State_dstate_eq with ((d_scale_not_0 (/ (r2 * d_trace mu2))
       ( (d_scale_not_0 r2 d2)))).
       apply d_scale_not_0_eq. apply dstate_eq_sym.
       apply d_app_empty_l.  
       destruct H21. lra. rewrite<-H23. 
       rewrite<-d_trace_scale_not_0; try lra.
       apply d_seman_scale''. intuition.
       apply d_seman_scale. lra. apply H21.
       rewrite Rmult_0_l. rewrite Rplus_0_r.
       apply sat_State_dstate_eq with ((d_scale_not_0 (/ (r1 * d_trace mu1))
       ( (d_scale_not_0 r1 d0)))).
       apply d_scale_not_0_eq. apply dstate_eq_sym.
       apply d_app_empty_r.  
       destruct H19. lra. rewrite<-H23. 
       rewrite<-d_trace_scale_not_0; try lra.
       apply d_seman_scale''. intuition.
       apply d_seman_scale. lra. apply H19.
       apply sat_State_dstate_eq with 
       (d_app (d_scale_not_0 (/ (r1 * d_trace mu1 + r2 * d_trace mu2))
       ((d_scale_not_0 r1 d0))) (d_scale_not_0 (/ (r1 * d_trace mu1 + r2 * d_trace mu2))
       ((d_scale_not_0 r2 d2)))).
       apply d_scale_not_0_app_distr.
       apply d_seman_app'.
       apply d_seman_scale'. apply Rinv_0_lt_compat.
       apply Rplus_lt_0_compat; apply Rmult_gt_0_compat; try lra.
       rewrite d_trace_scale_not_0; try lra.
       rewrite d_trace_scale_not_0; try lra.
       destruct H19. lra. rewrite H24.
       rewrite Rmult_comm. 
       rewrite <-Rdiv_unfold. 
       apply (Rcomplements.Rdiv_le_1 (r1 * d_trace mu1)). 
       apply Rmult_plus_gt_0; try lra. 
       rewrite <-Rplus_0_r at 1. 
       apply Rplus_le_compat_l. 
       apply Rmult_le_pos; try lra.
       apply Rinv_0_lt_compat.
       apply Rplus_lt_0_compat; apply Rmult_gt_0_compat; try lra.
       apply d_seman_scale; try lra. apply H19. lra.
       apply d_seman_scale'. apply Rinv_0_lt_compat.
       apply Rplus_lt_0_compat; apply Rmult_gt_0_compat; try lra.
       rewrite d_trace_scale_not_0; try lra.
       rewrite d_trace_scale_not_0; try lra.
       destruct H21. lra. rewrite H24. 
       rewrite Rmult_comm. 
       rewrite <-Rdiv_unfold. 
       apply (Rcomplements.Rdiv_le_1 (r2 * d_trace mu2)). 
       apply Rmult_plus_gt_0; try lra. 
       rewrite <-Rplus_0_l at 1. 
       apply Rplus_le_compat_r. 
       apply Rmult_le_pos; try lra.
       apply Rinv_0_lt_compat.
       apply Rplus_lt_0_compat; apply Rmult_gt_0_compat; try lra.
       apply d_seman_scale; try lra. apply H21. lra.
       apply WWF_dstate_to_WF_dstate.
       split. apply WWF_d_app. 
       apply WWF_d_scale_not_0. 
       apply Rinv_0_lt_compat.
       apply Rplus_lt_0_compat; apply Rmult_gt_0_compat; try lra.
       apply WWF_d_scale_not_0. lra.
       apply WWF_dstate_to_WF_dstate.
       eapply WF_sat_State. apply H19. lra.
       apply WWF_d_scale_not_0.  
       apply Rinv_0_lt_compat.
       apply Rplus_lt_0_compat; apply Rmult_gt_0_compat; try lra.
       apply WWF_d_scale_not_0. lra.
       apply WWF_dstate_to_WF_dstate.
       eapply WF_sat_State. apply H21. lra.
       rewrite d_trace_app; try repeat rewrite d_trace_scale_not_0.
       rewrite <-Rmult_plus_distr_l. 
       destruct H19. lra. destruct H21. lra. 
       rewrite H24. rewrite H25. 
       rewrite Rinv_l. lra. 
       apply Rgt_neq_0. apply Rmult_plus_gt_0; try lra.  
       lra. 
       apply Rinv_0_lt_compat.
       apply Rplus_lt_0_compat; apply Rmult_gt_0_compat; try lra.
       lra.
       apply Rinv_0_lt_compat.
       apply Rplus_lt_0_compat; apply Rmult_gt_0_compat; try lra.
       apply WWF_d_scale_not_0. 
       apply Rinv_0_lt_compat.
       apply Rplus_lt_0_compat; apply Rmult_gt_0_compat; try lra.
       apply WWF_d_scale_not_0. lra.
       apply WWF_dstate_to_WF_dstate.
       eapply WF_sat_State. apply H19. lra.
       apply WWF_d_scale_not_0.  
       apply Rinv_0_lt_compat.
       apply Rplus_lt_0_compat; apply Rmult_gt_0_compat; try lra.
       apply WWF_d_scale_not_0. lra.
       apply WWF_dstate_to_WF_dstate.
       eapply WF_sat_State. apply H21. lra.
       rewrite d_trace_scale_not_0. 
       inversion H30; subst; inversion H31; subst.
       destruct H5; try lra. 
       rewrite Rmult_0_l. rewrite Rplus_0_l.
       rewrite (d_trace_eq (d_app (d_empty s e) (d_scale_not_0 r2 d2)) ((d_scale_not_0 r2 d2))).
       rewrite d_trace_scale_not_0; try lra.
       rewrite Rdiv_unfold.
       rewrite Rmult_assoc. 
       destruct H21. lra. rewrite H23. rewrite Rinv_l.
       rewrite Rmult_1_r. rewrite d_trace_app. reflexivity.
       apply WWF_dstate_to_WF_dstate. assumption.
       apply WWF_dstate_to_WF_dstate. assumption.
       apply Rmult_integral_contrapositive_currified.
       lra. lra. 
       apply d_app_empty_l.
       rewrite Rmult_0_l. rewrite Rplus_0_r.
       rewrite (d_trace_eq (d_app  (d_scale_not_0 r1 d0) (d_empty s e) ) ((d_scale_not_0 r1 d0))).
       rewrite d_trace_scale_not_0; try lra.
       rewrite Rdiv_unfold.
       rewrite Rmult_assoc. 
       destruct H19. lra. rewrite H23. rewrite Rinv_l.
       rewrite Rmult_1_r. rewrite d_trace_app. reflexivity.
       apply WWF_dstate_to_WF_dstate. assumption.
       apply WWF_dstate_to_WF_dstate. assumption.
       apply Rmult_integral_contrapositive_currified.
       lra. lra. 
       apply d_app_empty_r.
       rewrite d_trace_app. repeat rewrite d_trace_scale_not_0; try lra.
       rewrite Rdiv_unfold.
       rewrite Rmult_assoc.
       destruct H19. lra. destruct H21. lra. 
       rewrite H24. rewrite H25.
       rewrite Rinv_l. rewrite Rmult_1_r.
       rewrite d_trace_app. reflexivity.
       apply WWF_dstate_to_WF_dstate. assumption.
       apply WWF_dstate_to_WF_dstate. assumption.
       apply Rgt_neq_0. apply Rmult_plus_gt_0; try lra.
       apply WWF_d_scale_not_0. lra.
       apply WWF_dstate_to_WF_dstate.
       eapply WF_sat_State. apply H19. lra.
       apply WWF_d_scale_not_0. lra.
       apply WWF_dstate_to_WF_dstate.
       eapply WF_sat_State. apply H21. lra.
       apply Rdiv_lt_0_compat.  apply Rplus_lt_0_compat; try lra.
        apply Rmult_plus_gt_0; try lra.
       econstructor.
Qed.



Lemma sat_State_Npro{s e:nat}:forall (mu:dstate s e) F1 F2,
WF_dstate mu-> StateMap.this mu <> []->
(forall x,  (d_find x mu) <> Zero -> State_eval F1 (x, d_find x mu)
 \/ State_eval F2 (x, d_find x mu))->
sat_Assert mu (ANpro [F1;F2]).
Proof. intros (mu, IHmu); simpl in *; intros. 
       induction mu. destruct H0. reflexivity.
       destruct mu.
       destruct a.  
       pose(H1 c).  unfold d_find in *. unfold StateMap.find in *.
       destruct o.  simpl in *. MC.elim_comp.
       simpl. apply WF_qstate_not_Zero. 
       inversion_clear H. apply H3.
      simpl in *. 
      destruct (Cstate_as_OT.compare c c).
      apply Cstate_as_OT.lt_not_eq in l. intuition.
      apply sat_NPro_State.
      rewrite sat_Assert_to_State. 
      econstructor. inversion_clear H.
      unfold WF_dstate. apply WF_state_dstate_aux. assumption. 
      econstructor. apply H2. econstructor.
      apply Cstate_as_OT.lt_not_eq in l. intuition.
      simpl in H2.  
      destruct (Cstate_as_OT.compare c c).
      apply Cstate_as_OT.lt_not_eq in l. intuition.
      apply rule_OplusC. 
      apply sat_NPro_State.
      rewrite sat_Assert_to_State. 
      econstructor. inversion_clear H.
      unfold WF_dstate. apply WF_state_dstate_aux. assumption. 
      econstructor. apply H2. econstructor.
      apply Cstate_as_OT.lt_not_eq in l. intuition.  
      assert(Sorted.Sorted (StateMap.Raw.PX.ltk (elt:=qstate s e)) [a]).
      apply Sorted_cons. apply Sorted.Sorted_nil. 
      apply Sorted.HdRel_nil.  inversion_clear IHmu.
      assert( dstate_eq {| StateMap.this := a :: p :: mu; StateMap.sorted := IHmu |}
      (d_app (StateMap.Build_slist H2) (StateMap.Build_slist H3))).
       destruct a. 
       destruct p. unfold d_app. unfold StateMap.map2. unfold dstate_eq.
       simpl. destruct (Cstate_as_OT.compare c c0).
       rewrite map2_r_refl. reflexivity.
       unfold Cstate_as_OT.eq in *. rewrite e0 in H4.
       inversion_clear H4. apply Cstate_as_OT.lt_not_eq in H5.
       simpl in H5.  intuition. 
       inversion_clear H4. unfold StateMap.Raw.PX.ltk in H5.
       simpl in H5.  rewrite <-H5 in l.  apply Cstate_as_OT.lt_not_eq in l.
        intuition. 
        apply sat_Assert_dstate_eq with 
       (d_app (StateMap.Build_slist H2) (StateMap.Build_slist H3)).
       apply dstate_eq_sym.
       apply H5. 
       apply sat_dapp_npro. destruct a.  
       pose(H1 c).  unfold d_find in *. unfold StateMap.find in *.
       destruct o.  simpl in *. MC.elim_comp.
       simpl. 
       apply WF_qstate_not_Zero. 
       inversion_clear H. apply H7.
      simpl in *. 
      destruct (Cstate_as_OT.compare c c).
      apply Cstate_as_OT.lt_not_eq in l. intuition.
      apply sat_NPro_State.
      rewrite sat_Assert_to_State. 
      econstructor. inversion_clear H.
      unfold WF_dstate. apply WF_state_dstate_aux. assumption. 
      econstructor. apply H6. econstructor.
      apply Cstate_as_OT.lt_not_eq in l. intuition.
      simpl in H6.  
      destruct (Cstate_as_OT.compare c c).
      apply Cstate_as_OT.lt_not_eq in l. intuition.
      apply rule_OplusC. 
      apply sat_NPro_State.
      rewrite sat_Assert_to_State. 
      econstructor. inversion_clear H.
      unfold WF_dstate. apply WF_state_dstate_aux. assumption. 
      econstructor.  apply H6. econstructor.
      apply Cstate_as_OT.lt_not_eq in l. intuition.
      apply IHmu0. inversion_clear H. assumption.
      discriminate.
      intros. destruct p.  pose(H1 x). destruct a.
      pose H6. 
      apply dstate_1 with (t:=c0) (q:=q0) in n.
      assert(d_find x {| StateMap.this := (c0, q0) :: (c, q) :: mu; StateMap.sorted := IHmu |}=
      d_find x {| StateMap.this := (c, q) :: mu; StateMap.sorted := H3 |}).
       unfold d_find . 
      unfold StateMap.find. simpl in *. 
      MC.elim_comp. reflexivity. 
      rewrite H7 in *. apply o. assumption. 
      econstructor. assumption. assumption.    
      eapply WF_dstate_eq. apply H5.  assumption.  
Qed.

Lemma sat_Npro_Pro{s e:nat}:forall (mu:dstate s e) F1 F2, 
sat_Assert mu (ANpro [F1;F2])-> (exists p, 0<=p<=1 /\ sat_Assert mu (APro [(p, F1);(1-p, F2)])).
Proof. intros. inversion_clear H. destruct p_n. discriminate H0. destruct p_n.
      discriminate H0. destruct p_n. inversion_clear H1. 
      assert(r0=1-r). inversion_clear H2. simpl in *. repeat rewrite sum_over_list_cons in *.
      rewrite sum_over_list_nil in *. rewrite Rplus_0_r in *. lra. subst. 
      exists r. split. inversion_clear H2. simpl in *. inversion_clear H1.
      inversion_clear H5.  rewrite Rcomplements.Rle_minus_r in H1. rewrite Rplus_0_l in *.
      lra.  econstructor; try assumption. discriminate H0.
Qed.

Lemma sat_NPro_State'{s e:nat}:forall (mu:dstate s e) F, 
(ANpro [F;F])->> F.
Proof. unfold assert_implies. intros. rewrite sat_Assert_to_State.
      inversion_clear H. destruct p_n. discriminate H0. destruct p_n.
      discriminate H0. destruct p_n. inversion_clear H1.
      destruct (Req_dec r 0). subst. assert(r0=1). inversion_clear H2. simpl in H4.
      repeat rewrite sum_over_list_cons in *. rewrite sum_over_list_nil in *. rewrite Rplus_0_l in *.
      rewrite Rplus_0_r in *. assumption. subst.  
      apply sat_Pro_State in H3. assumption.
      
      destruct (Req_dec r0 0). subst. assert(r=1). inversion_clear H2. simpl in H5.
      repeat rewrite sum_over_list_cons in *. rewrite sum_over_list_nil in *. rewrite Rplus_0_l in *.
      rewrite Rplus_0_r in *. assumption. subst.  
      assert( sat_Assert mu0 (APro [(1, F); (0, F)])). econstructor; try assumption.
      apply (rule_POplusC _ 0) in H4. simpl in H4.
      apply sat_Pro_State' in H4. rewrite sat_Assert_to_State in *. assumption.
      
      inversion_clear H3. simpl in H5. 
      destruct mu_n. inversion_clear H5. destruct mu_n. inversion_clear H5. inversion_clear H8.
      destruct mu_n. inversion H5; subst. inversion H13; subst. inversion H15; subst. clear H15. 
    
      inversion_clear H7. inversion_clear H8. clear H9. simpl in *.
      inversion H12; subst. lra.  inversion H14; subst. lra.
      apply sat_State_dstate_eq with ((d_app (d_scale_not_0 r d) (d_scale_not_0 r0 d0))).
      apply dstate_eq_sym. eapply dstate_eq_trans. apply H6. apply d_app_eq; try apply dstate_eq_refl.
      apply d_app_empty_r.  
       inversion_clear H2. simpl in *. inversion_clear H10. 
      inversion_clear H15. repeat rewrite sum_over_list_cons in *. rewrite sum_over_list_nil in *.
      rewrite Rplus_0_r in *. 
      apply d_seman_app; try lra. apply H3; lra. apply H7; lra. 
      inversion_clear H5. inversion_clear H8. inversion_clear H9. discriminate H0.
Qed.



Lemma SAnd_PAnd_eq: forall (P1 P2:Pure_formula),
(P1 /\p P2) <<->> (P1 /\s P2).
Proof. rule_solve.
  
Qed.

Theorem rule_while_classic: forall F (b:bexp) (c:com),
         {{F /\p b}} c {{ F}}
      -> {{F}}
         while b do c end
         {{ (F /\p (BNot b)) }}.
Proof.  intros. 
assert(F ->> ANpro [F /\s b ; F /\s (BNot b)]).
rule_solve. apply sat_State_Npro; try  assumption. 
intros. apply H2 in H3. simpl in *. destruct (beval (x, d_find x mu) b); simpl;[left|right]; auto.
eapply rule_conseq. apply rule_while. 
eapply rule_conseq_r. apply H0. eapply rule_conseq_l. apply SAnd_PAnd_eq. assumption.
assumption.  apply SAnd_PAnd_eq.
Qed.



Theorem rule_cond_classic: forall (P1 P2: Pure_formula) (c1 c2:com) (b:bexp),
        ({{P1 /\p (b)}} c1 {{P2 }} /\ {{P1 /\p ((BNot b) )}} c2 {{P2 }})
     -> ({{P1 }}
        if b then c1 else c2 end
        {{P2}}).
Proof. intros.  
assert(P1 ->> ANpro [P1 /\s b ; P1 /\s (BNot b)]). 
rule_solve. apply sat_State_Npro; try  assumption. 
intros. apply H2 in H4. simpl in *. destruct (beval (x, d_find x mu) b); simpl;[left|right]; auto.
assert(({{P1 /\s b}} c1 {{P2}}) /\ ({{P1 /\s <{ ~ b }>}} c2 {{P2}})).
split; eapply rule_conseq_l; try apply SAnd_PAnd_eq; try apply H.
unfold hoare_triple. intros. apply H0 in H3. apply sat_Npro_Pro in H3. destruct H3.
pose (rule_cond P1 P2 P1 P2 c1 c2 b x). eapply h in H1. destruct H3. 
eapply H1 in H4; try apply H2. apply rule_Oplus in H4. simpl in *.
apply (@sat_NPro_State' s e) in H4; try assumption. lra.  
Qed.