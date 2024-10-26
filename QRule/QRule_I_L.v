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
       inversion_clear H. apply ceval_skip_1 in H3.
       apply sat_Assert_dstate_eq with mu.
       unfold dstate_eq. intuition.
       intuition. 
Qed.


Theorem rule_assgn: forall (P:Pure_formula) (i:nat) ( a:aexp),
             {{PAssn i a P}} i := a {{P}}.
Proof. unfold hoare_triple;
       intros F X a s e (mu,IHmu) (mu', IHmu').
       intros. 
       inversion_clear H; simpl in H3.
       rewrite sat_Assert_to_State in *.
       inversion_clear H0.
       apply sat_F. intuition.
       apply rule_asgn_aux with X a mu.
       intuition. intuition. assumption. 
Qed. 


Theorem rule_seq : forall (P Q R:Assertion) c1 c2,
              {{P}} c1 {{Q}} ->
              {{Q}} c2 {{R}} ->
              {{P}} c1; c2 {{R}}.
Proof.   unfold hoare_triple.  
         intros P Q R2 c1 c2 H1 H2 s e (mu,IHmu) (mu',IHmu').
         intros. inversion H;subst. 
         simpl in H5.
         inversion H5;subst. apply WF_sat_Assert in H0.
         simpl in H0. destruct H0. destruct H0. reflexivity.
         assert(WF_dstate_aux mu1). 
         unfold WF_dstate in H3. simpl in H3.
         apply (WF_ceval _ _ _ H3 H8).
         assert(Sorted.Sorted (StateMap.Raw.PX.ltk (elt:=qstate s e)) mu1).
         apply (ceval_sorted _ _ _ IHmu H8).
         apply H2 with (StateMap.Build_slist H7).
         apply E_com. intuition. intuition.
         simpl. intuition. intuition.
         apply H1 with (StateMap.Build_slist IHmu).
         apply E_com.  intuition. intuition. 
         simpl. intuition. intuition. 
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


Lemma big_add_ceval{s e:nat}: forall (mu_n mu_n':list (dstate s e))
(nF1 nF2:npro_formula)  c,
length mu_n =length nF1 ->
(Forall_two ( fun i j => sat_State i j) mu_n nF1) ->
(Forall_two ( fun i j =>ceval c i j) mu_n mu_n')->
(Forall_two ( fun (i j: State_formula) =>{{i}} c {{ j}}) nF1 nF2)->
(Forall_two ( fun i j => sat_State i j) mu_n' nF2).
Proof. induction mu_n; destruct mu_n';intros.
- destruct nF1; destruct nF2. assumption.
  inversion_clear H2. inversion_clear H2.
  inversion_clear H0.
-inversion_clear H1.
-inversion_clear H1. 
-destruct nF1; destruct nF2. discriminate H.
 inversion_clear H2. inversion_clear H2.
 simpl in *. inversion_clear H1; subst.
 inversion_clear H2. inversion_clear H0.
 unfold hoare_triple in *.
 econstructor. apply H1 in H3; rewrite sat_Assert_to_State in *.
 assumption. assumption.
 apply IHmu_n with nF1 c.
 injection H. intuition. 
 assumption. assumption. assumption.
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

Lemma Forall_two_impli{A B:Type }:forall (P Q : A -> B -> Prop) (f:list A) (g:list B),
(forall i j, P i j -> Q i j)-> 
(Forall_two P f g) ->(Forall_two Q f g).
Proof. induction f; intros; destruct g. econstructor. 
       inversion_clear H0. inversion_clear H0. 
       inversion_clear H0.
      econstructor; try assumption. apply H; try assumption.
       apply IHf. apply H. assumption.
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
 constructor. inversion_clear H1. intuition.  
 econstructor; rewrite (get_pro_formula_eq nF1);
 try rewrite <-(Forall_two_length_eq ( fun (i j: State_formula) => {{i}} c{{ j}} ) nF1 ); inversion_clear H4; 
 try assumption.

 rewrite get_pro_formula_p_n in *.
 rewrite pro_npro_inv in H7. 

 assert(exists (mu_n': list (dstate s e)), 
 and (Forall_two ( fun i j=>ceval c i j ) mu_n mu_n')
 (dstate_eq mu' (big_dapp p_n mu_n'))).
 apply ceval_big_dapp with mu.
 assumption. inversion_clear H4.
  rewrite get_pro_formula_p_n in H9; try assumption.
  lra. apply WF_big_and with nF1. assumption.
 apply big_dapp'_length with mu'0.
 assumption. apply dstate_eq_trans with mu'0. assumption.
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
  assumption.  apply H10.
 rewrite <-(Forall_two_length_eq (( fun (i j: State_formula)=>{{i}} c {{j}} )) nF1 _).
 assumption. assumption. assumption.
 rewrite pro_npro_inv. 
 apply big_add_ceval with mu_n nF1 c.
 rewrite H. symmetry.  apply big_dapp'_length with mu'0. 
 assumption. assumption.
 assumption. assumption. 
 rewrite <-(Forall_two_length_eq (( fun (i j: State_formula)=>{{i}} c {{j}} )) nF1 _).
 assumption. assumption.  
 rewrite (ceval_trace_eq' c _ _  mu mu').
 apply Forall_two_Forall_impli with (fun i j => d_trace i = d_trace j) mu_n.
 intros. rewrite <-H11. assumption.
 apply Forall_ceval_trace with c. apply Forall_WWF_WF.
  apply WF_big_and with nF1. assumption. 
  assumption. assumption.
 apply WWF_dstate_aux_to_WF_dstate_aux. assumption.
 assumption.

 assumption. assumption. 
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
       simpl in *. inversion H4; subst.
       
       --(*b=true*)
       econstructor. intuition.
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
        assert(WF_dstate_aux ([(sigma, rho)])).
       unfold WF_dstate in *. simpl in *.
       inversion_clear H2. apply WF_cons.
       apply H6. apply WF_nil. assumption.
       assert(sat_Assert (StateMap.Build_slist H0) F').
       apply H with (StateMap.Build_slist H5).
       apply E_com. intuition.
       apply WF_ceval with c1 ([(sigma, rho)]).
       intuition. simpl. intuition.
       simpl. intuition. rewrite sat_Assert_to_State.
       inversion_clear H1. 
       constructor. intuition.
       simpl in *. 
       intuition. rewrite sat_Assert_to_State in H7.
       inversion_clear H7. assumption. 
       

      
       assert(WF_dstate_aux ([(sigma, rho)])).
       unfold WF_dstate in *. simpl in *.
       inversion_clear H2. apply WF_cons.
       apply H0. apply WF_nil.
       apply WF_dstate_in01_aux in H5.
       simpl in *. rewrite Rplus_0_r. 
       apply Rplus_le_reg_pos_r  with ((s_trace p + d_trace_aux mu)%R) .
       intuition. intuition. 
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
       
       assert(sat_Assert (StateMap.Build_slist H5) F').
       apply H with (StateMap.Build_slist H6).
       apply E_com. intuition. 
       apply WF_ceval with c1 ([(sigma, rho)]).
       intuition. simpl. intuition.
       simpl. intuition. rewrite sat_Assert_to_State.
       inversion_clear H1. 
       constructor. intuition.
       simpl in *. inversion_clear H8. 
       econstructor. assumption. apply Forall_nil.
       rewrite sat_Assert_to_State in H7. 
       inversion_clear H7. simpl in H9. assumption. 
      

       inversion_clear IHmu. 
       assert(Sorted (StateMap.Raw.PX.ltk (elt:=qstate s e))
       mu''). apply ceval_sorted with (<{ if b then c1 else c2 end }>)
       ((p::mu)). intuition. intuition.
       assert(WF_dstate_aux ((p:: mu))).
       inversion_clear H2.   intuition.
       assert(sat_Assert (StateMap.Build_slist H7) F').
       apply IHmu0 with H5. 
       apply E_com. unfold WF_dstate. simpl. intuition.  unfold WF_dstate.
       apply WF_ceval with (<{ if b then c1 else c2 end }>)
       (p::mu). intuition. intuition. 
       simpl. intuition.  rewrite sat_Assert_to_State.
       constructor.
       unfold WF_dstate. simpl. intuition.
       inversion_clear H1. destruct p. 
       inversion_clear H13. simpl. assumption.
       rewrite sat_Assert_to_State in *.  
       inversion_clear H9.    
       assumption.   
      

       inversion_clear H1.  simpl in *.
       inversion_clear H5. 
       rewrite H10 in H1. destruct H1. destruct H5.
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
       simpl in *. inversion H4; subst.

       --(*b=true*)  inversion_clear H1.  simpl in *.
       inversion_clear H5. 
       rewrite H10 in H1. destruct H1. destruct H5. intuition.
       --(*b=false*)
       econstructor. intuition.
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
       unfold WF_dstate in *. simpl in *.
       inversion_clear H2. apply WF_cons.
       apply H6. apply WF_nil. assumption. 
       assert(sat_Assert (StateMap.Build_slist H0) F').
       apply H with (StateMap.Build_slist H5).
       apply E_com. intuition.
       apply WF_ceval with c2 ([(sigma, rho)]).
       intuition. simpl. intuition.
       simpl. intuition. rewrite sat_Assert_to_State.
       inversion_clear H1. 
       constructor. intuition.
       simpl in *. 
       intuition. rewrite sat_Assert_to_State in H7.
       inversion_clear H7. assumption.
       
       
       

       assert(WF_dstate_aux ([(sigma, rho)])).
       unfold WF_dstate in *. simpl in *.
       inversion_clear H2. apply WF_cons.
       apply H0. apply WF_nil. 
       apply WF_dstate_in01_aux in H5.
       simpl in *. rewrite Rplus_0_r. 
       apply Rplus_le_reg_pos_r  with ((s_trace p + d_trace_aux mu)%R) .
       intuition. intuition. 
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
       assert(sat_Assert (StateMap.Build_slist H5) F').
       apply H with (StateMap.Build_slist H6).
       apply E_com. intuition.
       apply WF_ceval with c2 ([(sigma, rho)]).
       intuition. simpl. intuition.
       simpl. intuition. rewrite sat_Assert_to_State.
       inversion_clear H1. 
       constructor. intuition. 
       inversion_clear H8.  simpl. econstructor.
       assumption. apply Forall_nil. 
       rewrite sat_Assert_to_State in H7.
       inversion_clear H7. assumption. 

       inversion_clear IHmu. 
       assert(Sorted (StateMap.Raw.PX.ltk (elt:=qstate s e))
       mu''). apply ceval_sorted with (<{ if b then c1 else c2 end }>)
       ((p::mu)). intuition. intuition.
       assert(WF_dstate_aux ((p:: mu))).
       unfold WF_dstate in H2. simpl in H2.
       inversion_clear H2. 
       intuition.  
       assert(sat_Assert (StateMap.Build_slist H7) F').
       apply IHmu0 with H5. 
       apply E_com. unfold WF_dstate. simpl. intuition.  unfold WF_dstate.
       simpl. intuition.
       apply WF_ceval with (<{ if b then c1 else c2 end }>)
       (p::mu). intuition. intuition. 
       simpl. intuition.  rewrite sat_Assert_to_State.
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
        0<p<1->
        ({{F1 /\s (b)}} c1 {{F1'}} /\ {{F2 /\s ((BNot b) )}} c2 {{F2'}})
     -> ({{ APro [(p, (F1 /\s b)) ; ((1 - p), (F2 /\s (BNot b)))]}}
        if b then c1 else c2 end
        {{APro [(p, F1') ; ((1 - p), F2')]}}).
Proof. intros. assert ([(p, F1 /\s b); (1 - p, F2 /\s (BNot b))]=
       (npro_to_pro_formula ([(F1 /\s b); ( F2 /\s (BNot b))]) ([p; (1-p)]))).
       simpl. reflexivity. rewrite H1. 
       assert ([(p, F1'); (1 - p, F2')]=
       (npro_to_pro_formula ([(F1'); ( F2')]) ([p; (1-p)]))).
       reflexivity. rewrite H2.
       apply rule_sum. simpl. econstructor.
       lra. econstructor. lra. apply Forall_nil.
       reflexivity.
       econstructor.  apply rule_cond_aux. intuition. 
       econstructor. apply rule_cond_aux_2. intuition.
      econstructor.  
Qed.


Fixpoint pro_formula_scale (pF: pro_formula ) (p: R): pro_formula:=
  match pF with 
  |[]=>[]
  |(h, F):: pF' => ((p*h)%R, F) :: (pro_formula_scale pF' p)
  end.

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
 econstructor. apply H. econstructor. inversion_clear H5. simpl in H10. 
 lra.  apply WF_big_and with [F1; F2]. assumption. 
 apply big_dapp'_length with mu'0. assumption. 
 apply dstate_eq_trans with mu'0. assumption.
 apply big_dapp_eq with [p1;p2] mu_n. assumption.
 apply big_dapp'_to_app. apply big_dapp'_length with mu'0.
 assumption. econstructor. lra. econstructor. lra.
 econstructor. assumption.
 destruct H6. destruct H6.

  rewrite app_nil_r.  destruct mu_n.
  inversion_clear H3. destruct mu_n. 
  inversion_clear H3. inversion_clear H12.
  destruct mu_n. destruct x. inversion_clear H6.
  destruct x. inversion_clear H6. inversion_clear H12.
  destruct x.  simpl in *. inversion H3; subst.
  inversion H17; subst. inversion H19; subst. clear H19. 
  clear H17. clear H3.
  inversion_clear H8. inversion_clear H11. clear H12.
  inversion_clear H6. inversion_clear H12. clear H13.

  pose H11. pose H6.
 apply H0 in c0. apply H1 in c1.
 inversion_clear c0. inversion_clear H14.
 inversion_clear c1. inversion_clear H22. 

econstructor. inversion_clear H2. assumption.
econstructor. rewrite get_pro_formula_app. simpl. 
rewrite Forall_app. split.
apply Forall_map. apply Forall_impl with  (fun x : R => 0 <= x).
intros. apply Rmult_le_pos. lra. assumption.
inversion_clear H13. assumption. 
apply Forall_map. apply Forall_impl with  (fun x : R => 0 <= x).
intros. apply Rmult_le_pos. lra. assumption.
inversion_clear H21. assumption. 
rewrite get_pro_formula_app. simpl. 
rewrite sum_over_list_app.
admit.
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
 f_equal; eapply big_dapp'_length; [apply H15| apply H23].
 apply Forall_app. 
 split; apply Forall_map.
 apply Forall_impl with  (fun x : R => 0 < x).
 intros. apply Rmult_gt_0_compat. lra. assumption. assumption.
 apply Forall_impl with  (fun x : R => 0 < x).
 intros. apply Rmult_gt_0_compat. lra. assumption. assumption.
  apply H22.
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
  [apply H15
  | apply big_dapp'_to_app; [eapply big_dapp'_length; apply H15 | assumption]|
  apply H23 | apply big_dapp'_to_app;
  [eapply big_dapp'_length; apply H23 | assumption] ].
  apply d_app_eq;
  apply dstate_eq_sym;
  apply big_dapp_scale;
  rewrite <-get_pro_formula_length;
  eapply big_dapp'_length; [apply H15| apply H23].
  apply dstate_eq_sym;
  apply big_dapp_app;
  rewrite map_length;
  eapply big_dapp'_length; [apply H15| apply H23].
  rewrite pro_to_npro_formula_app.
  repeat rewrite pro_to_npro_formula_scale.
  apply Forall_two_app; auto.
  apply Forall_app.
  split. 
  assert(d_trace mu' = d_trace d1).
  inversion_clear H9.
  rewrite (ceval_trace_eq' c _ _ d d1).
  rewrite H22. 
  apply ceval_trace_eq' with c.
  apply WWF_dstate_aux_to_WF_dstate_aux.
  apply H4. assumption.
  inversion_clear H3. 
  apply WWF_dstate_aux_to_WF_dstate_aux.
  assumption. assumption.
  rewrite H22. assumption.
  assert(d_trace mu' = d_trace d2).
  inversion_clear H9. inversion_clear H27.
  rewrite (ceval_trace_eq' c _ _ d0 d2).
  rewrite H9. 
  apply ceval_trace_eq' with c.
  apply WWF_dstate_aux_to_WF_dstate_aux.
  apply H4. assumption.
  inversion_clear H8. 
  apply WWF_dstate_aux_to_WF_dstate_aux.
  assumption. assumption.
  rewrite H22. assumption.
  rewrite sat_Assert_to_State.
  assumption. 
  rewrite sat_Assert_to_State.
  assumption.
  inversion_clear H6. inversion_clear H12.
  inversion_clear H13.
  inversion_clear H3. inversion_clear H12.
  inversion_clear H13.
 Admitted.


Lemma while_seq: forall (b:bexp) c F0  F1, 
{{F0 /\s b}} c; while b do c end {{F1 /\s ((BNot b))}} ->
{{F0 /\s b}} while b do c end {{F1 /\s (BNot b)}} .
Proof. unfold hoare_triple. intros b c F0 F1 H.  
        intros s e(mu, IHmu); induction mu; intros;
        destruct mu' as  [mu' IHmu']; 
        inversion_clear H0; inversion H4; subst;
        rewrite sat_Assert_to_State in *; simpl in *.
        apply WF_sat_State in H1.
        destruct H1. destruct H0. reflexivity.


       econstructor. intuition.
       destruct mu. inversion H9; subst.
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
       unfold WF_dstate in *. simpl in *.
       inversion_clear H2. apply WF_cons.
       apply H6. apply WF_nil. assumption.
       assert(sat_Assert (StateMap.Build_slist H0) (F1 /\s (BNot b))).
       apply H with (StateMap.Build_slist H5).
       apply E_com. intuition. 
       apply WF_ceval with <{ while b do c end }> mu1.
       apply WF_ceval with c ([(sigma, rho)]).
       intuition. simpl. intuition. assumption.
       simpl. apply E_Seq with mu1.  intuition.
       assumption.
       rewrite sat_Assert_to_State.
       inversion_clear H1. 
       constructor. intuition.
       simpl in *. 
       intuition. rewrite sat_Assert_to_State in H7.
       inversion_clear H7. assumption. 

        rewrite <-H10.
        assert(WF_dstate_aux ([(sigma, rho)])).
       unfold WF_dstate in *. simpl in *.
       inversion_clear H2. apply WF_cons.
       apply H0. apply WF_nil.
       apply WF_dstate_in01_aux in H5.
       simpl in *. rewrite Rplus_0_r. 
       apply Rplus_le_reg_pos_r  with (s_trace p + d_trace_aux mu) .
       intuition. intuition.  
      
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
       
       assert(sat_Assert (StateMap.Build_slist H5) ((F1 /\s (BNot b)))).
       apply H with (StateMap.Build_slist H6).
       apply E_com. intuition.
       apply WF_ceval with (<{ while b do c end }>) (mu1).
       apply WF_ceval with c ([(sigma, rho)]).
       intuition. simpl. intuition. 
       simpl. intuition. simpl.
       apply E_Seq with mu1.  intuition.
       assumption. rewrite sat_Assert_to_State.
       inversion_clear H1. 
       constructor. intuition.
       simpl in *. inversion_clear H13. 
       econstructor. assumption. apply Forall_nil.
       rewrite sat_Assert_to_State in H7. 
       inversion_clear H7. simpl in H14. assumption. 
      

       inversion_clear IHmu. 
       assert(Sorted (StateMap.Raw.PX.ltk (elt:=qstate s e))
       mu''). apply ceval_sorted with (<{ while b do c end }>)
       ((p::mu)). intuition. intuition.
       assert(WF_dstate_aux ((p:: mu))).
       inversion_clear H2.   intuition.
       assert(sat_Assert (StateMap.Build_slist H7) (F1 /\s (BNot b))).
       apply IHmu0 with H5. 
       apply E_com. unfold WF_dstate. simpl. intuition.  unfold WF_dstate.
       apply WF_ceval with (<{ while b do c end }>)
       (p::mu). intuition. intuition. 
       simpl. intuition.  rewrite sat_Assert_to_State.
       constructor.
       unfold WF_dstate. simpl. intuition.
       inversion_clear H1. destruct p. 
       inversion_clear H15. simpl. assumption.
       rewrite sat_Assert_to_State in *.   
       inversion_clear H14.    
       assumption. 
       
       
       inversion_clear H1. simpl in H5.
       inversion_clear H5. 
       rewrite H9 in H1. destruct H1. destruct H5.
Qed.



Lemma rule1: forall s e (mu:list (state s e)) (sigma:cstate) (rho:qstate s e) IHmu H
F0 F1 (b:bexp), 
sat_Assert
       {|
         StateMap.this := (sigma, rho) :: mu;
         StateMap.sorted := IHmu
       |} (ANpro ([F0 /\s b; F1 /\s (BNot b)])) ->
       beval (sigma, rho) b = true->
       sat_Assert
       {|
         StateMap.this := [(sigma, rho)];
         StateMap.sorted := H
       |} (F0 /\s b)    
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
 apply sat_Pro_State in H5. destruct H5. 
 inversion_clear H4. simpl in H7. 
 inversion_clear H7. destruct H4. rewrite H1 in H7.
 simpl in H7. destruct H7. 
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
 rewrite Rplus_0_r. auto. assumption.
 inversion_clear H4.  apply sat_Pro_State in H9. 
 destruct H9. inversion_clear H4. 
 simpl in H11. inversion_clear H11. 
 rewrite sat_Assert_to_State. econstructor.
 apply WF_state_dstate_aux.  inversion_clear H0. assumption.
 simpl. econstructor. intuition. apply Forall_nil. 

rewrite sat_Assert_to_State. 
inversion_clear H5. simpl in *. 
destruct mu_n. inversion_clear H9.
destruct mu_n. simpl in H3. inversion_clear H7.
inversion_clear H11. destruct mu_n. simpl in *.
econstructor. inversion_clear H0.
apply WF_state_dstate_aux. assumption.
simpl in *.  
assert(dstate_eq mu' (big_dapp [r; r0] [d; d0] )).
apply big_dapp_eq with ([r; r0]) ([d; d0]).
assumption. apply big_dapp'_to_app.
reflexivity.
inversion_clear H4. simpl in *.
inversion_clear H5. inversion_clear H12.
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
 simpl in *.  destruct d. simpl in *.
 inversion_clear H9. apply WF_sat_State in H12.
 simpl in *. intuition. 
 destruct d0. inversion_clear H9. inversion_clear H13.
  simpl in *.
  apply WF_sat_State in H9.
 simpl in *. intuition.
 destruct p. destruct p0. 
simpl in *. 
destruct (Cstate_as_OT.compare c c0).
injection H11. intros.
rewrite H13. rewrite H14.
inversion_clear H9. inversion_clear H16.
 econstructor.  split.
 assert((@pair cstate (qstate s e) c (q_scale r q)) = s_scale r (c,q)).
 reflexivity. rewrite H16.
 apply s_seman_scale.  inversion_clear H4.
 simpl in *. repeat rewrite sum_over_list_cons in H19.
 rewrite sum_over_list_nil in H19. simpl in H19.
 rewrite Rplus_0_r in H19. inversion_clear H18. 
 inversion_clear H20. simpl in *.  lra.
 inversion_clear H15. simpl in *. inversion_clear H19.
 intuition.  subst. rewrite H1. intuition. 
  apply Forall_nil.

  injection H11. intros.
inversion_clear H9. inversion_clear H16.
  inversion_clear H9.  simpl in *.
  inversion_clear H18. destruct H9.
  unfold Cstate_as_OT.eq in e0. 
  rewrite <-e0 in H18. 
  rewrite <-H14 in H18. 
  rewrite <-(state_eq_bexp (sigma, rho) 
  (sigma ,q0) _) in H18. 
  rewrite H1 in H18. destruct H18. intuition.

  injection H11. intros.
  inversion_clear H9. inversion_clear H16.
  inversion_clear H9.  simpl in *.
  inversion_clear H18. destruct H9.
  rewrite <-H14 in H18. 
  rewrite <-(state_eq_bexp (sigma, rho) 
  (sigma ,q0) _) in H18. 
  rewrite H1 in H18. destruct H18.
   intuition.
  inversion_clear H9. inversion_clear H11.
  inversion_clear H12.
  
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
 apply sat_Pro_State in H5. destruct H5. 
 inversion_clear H4. 
 simpl in H7. inversion_clear H7. 
 rewrite sat_Assert_to_State. econstructor.
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
 inversion_clear H4.  apply sat_Pro_State in H9. 
destruct H9.
 inversion_clear H4. simpl in H11. 
 inversion_clear H11. destruct H4. rewrite H1 in H11.
 destruct H11. 

rewrite sat_Assert_to_State. 
inversion_clear H5. simpl in *.
destruct mu_n. inversion_clear H9. 
destruct mu_n. simpl in H3. inversion_clear H7.
inversion_clear H11. destruct mu_n. simpl in *.
econstructor. inversion_clear H0.
apply WF_state_dstate_aux. assumption.
simpl.  
assert(dstate_eq mu' (big_dapp [r; r0] [d; d0] )).
apply big_dapp_eq with ([r; r0]) ([d; d0]).
assumption. apply big_dapp'_to_app.
reflexivity.
inversion_clear H4. inversion_clear H5. 
inversion_clear H12.
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
 simpl in *.  destruct d. simpl in *.
 inversion_clear H9. apply WF_sat_State in H12.
 simpl in *. intuition. 
 destruct d0. inversion_clear H9.
  inversion_clear H13.
  simpl in *.
  apply WF_sat_State in H9.
 simpl in *. intuition.
 destruct p. destruct p0. 
simpl in *. 
destruct (Cstate_as_OT.compare c c0).
injection H11. intros.
rewrite H13. rewrite H14.
inversion_clear H9. inversion_clear H15.
 inversion_clear H17.
destruct H15. rewrite <-H14 in H17.
simpl in H17.
rewrite <- (state_eq_bexp (sigma, rho) 
  (sigma,q) _) in H17.
  rewrite H1 in H17. destruct H17. intuition.

  injection H11. intros.
  inversion_clear H9. inversion_clear H15.
  inversion_clear H17.  simpl in *.
  destruct H15.
  unfold Cstate_as_OT.eq in e. 
  rewrite <-H14 in H17.
  rewrite <-(state_eq_bexp (sigma, rho) 
  (sigma ,q) _) in H17.
  rewrite H1 in H17. destruct H17.
  intuition.

  injection H11. intros.
  rewrite H13. rewrite H14.
  inversion_clear H9. inversion_clear H16.
  inversion_clear H9.  simpl in *.
  inversion_clear H18. destruct H9.
  econstructor.  split.
  assert((@pair cstate (qstate s e) c0 (q_scale r0 q0)) = s_scale r0 (c0,q0)).
  reflexivity. rewrite H20.
  apply s_seman_scale.  inversion_clear H4.
  simpl in *. repeat rewrite sum_over_list_cons in *.
  rewrite sum_over_list_nil in *. simpl in *.
  rewrite Rplus_0_r in *. inversion_clear H21. 
  inversion_clear H23. simpl in *.  lra.
  inversion_clear H15. assumption.
  intuition. rewrite (state_eq_bexp (c0, r0 .* q0) 
   (c0,q0) _). intuition. reflexivity.
   apply Forall_nil. 
  inversion_clear H9. inversion_clear H11.
  inversion_clear H12.
  simpl in H2. intuition. 
Qed.



(* Inductive d_scalar'{n:nat}: R-> (dstate n)-> Prop :=
|d_scalar_0 mu : d_scalar' 0  mu
|d_scalar_r r mu: r>0 -> d_scalar' r mu . *)

(* Definition d_scalar'' {n:nat} (r:R) (mu:dstate n) : dstate n :=

   match d with 
   |d_scalar_0 mu => d_empty n
   |d_scalar_r r mu H=> d_scalar r mu
   end.
     *)


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
      induction H4;  try inversion Horig; subst.

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
      inversion_clear H2. apply WF_cons. assumption.
      apply WF_nil.  apply WF_dstate_in01_aux in H9.
      simpl in *. rewrite Rplus_0_r. 
      apply Rplus_le_reg_pos_r  with ( d_trace_aux mu)%R .
      intuition. intuition. 
      
      destruct mu. simpl in *. inversion H4_; subst.
      remember (StateMap.Raw.map2 option_app mu' []).
      rewrite map2_nil_r in Heqt0. subst.
      apply IHceval_single3 with H5. 
      apply H with (StateMap.Build_slist H4).
       econstructor. intuition. apply WF_ceval with c [(sigma, rho)].
       assumption. intuition. assumption. 
       apply rule1 with [] IHmu F1. assumption.
       assumption.   
       apply WF_ceval with c [(sigma, rho)].
       assumption. intuition. 
       apply WF_ceval with (<{ while b do c end }>) mu1.
       apply WF_ceval with c [(sigma, rho)].
       assumption. intuition.  assumption.  intuition.
      
     assert(sat_State (d_app (StateMap.Build_slist H6) (StateMap.Build_slist H7)) (F1 /\s (BNot b))).
     apply (d_seman_app' _ _ _ (StateMap.Build_slist H6) (StateMap.Build_slist H7)). 
     rewrite <-sat_Assert_to_State.
     apply IHceval_single3 with H5. 
     apply H with (StateMap.Build_slist H4).
      econstructor. intuition. apply WF_ceval with c [(sigma, rho)].
      assumption. intuition. assumption. 
      apply rule1 with (p :: mu) IHmu F1. assumption.
      assumption.   
      apply WF_ceval with c [(sigma, rho)].
      assumption. intuition. 
      apply WF_ceval with (<{ while b do c end }>) mu1.
      apply WF_ceval with c [(sigma, rho)].
      assumption. intuition.  assumption.  intuition.


  

      inversion_clear IHmu. 
      assert( (sat_Assert (StateMap.Build_slist H9) (ANpro [F0 /\s b; F1 /\s (BNot b)]))).
      apply rule2 with sigma rho IHmu. assumption. discriminate.
   
      rewrite<- sat_Assert_to_State.
      apply IHceval_single1 with (H9).
     assumption.  inversion_clear H2. assumption.
     apply WF_ceval with (<{ while b do c end }>) (p :: mu).
     inversion_clear H2. assumption. assumption. reflexivity.
    
     apply WF_ceval with (<{ while b do c end }>) ((sigma, rho) :: (p :: mu)).
     intuition. simpl. apply E_While_true with mu1.
     assumption. assumption. assumption. assumption.
     unfold d_app in H9. unfold StateMap.map2 in H9. simpl in H9.
     inversion_clear H9. rewrite sat_Assert_to_State. 
     econstructor.   intuition.
      apply H11. 
     
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
     assumption. inversion_clear H2. intuition. 
     apply WF_ceval with (<{ while b do c end }>) (p::mu).
     inversion_clear H2. assumption. intuition. reflexivity.
     apply WF_ceval with (<{ while b do c end }>) ((sigma, rho) :: (p::mu)).
     intuition. apply E_While_false. assumption. intuition.
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


