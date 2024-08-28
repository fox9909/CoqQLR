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
From Quan Require Import QState_L.
From Quan Require Import QIMP_L.
From Quan Require Import QAssert_L.
From Quan Require Import Basic_Supplement.
From Quan Require Import QRule_Q_L.
From Quan Require Import QRule_E_L.

Local Open Scope com_scope.


Open Scope rule_scope.
Theorem rule_skip : forall (D: Assertion), {{D}} skip {{D}}.
Proof. unfold hoare_triple. intros. 
       inversion_clear H. apply ceval_skip_1 in H3.
       apply sat_Assert_dstate_eq with mu.
       unfold dstate_eq. intuition.
       intuition. 
Qed.

(* Lemma d_seman_app: forall n (F:State_formula)  (mu mu':list (cstate * qstate n)),
State_eval_dstate F mu-> State_eval_dstate  F (mu')
-> State_eval_dstate  F (StateMap.Raw.map2 option_app mu mu').
Proof. Admitted. *)
Require Import ParDensityO.
Lemma WF_state_dstate_aux{s e:nat}: forall (st:state s e), 
WF_state st <-> WF_dstate_aux [st] .
Proof. split; unfold WF_dstate;
       destruct st; simpl; intros. 
    
       apply WF_cons. intuition. apply WF_nil. 
       unfold WF_state in H.  unfold WF_qstate in H. simpl in H.
       unfold d_trace_aux. unfold s_trace. simpl. rewrite Rplus_0_r.
       apply mixed_state_Cmod_1. intuition.

       inversion_clear H. intuition. 
Qed.


Open Scope assert_scope.
Theorem rule_asgn_aux :  forall (P:Pure_formula) (i:nat) ( a:aexp) 
(s e:nat) (mu : list (cstate * qstate s e)) (mu': list (cstate * qstate s e)),
WF_dstate_aux mu->
ceval_single (<{i := a}>) mu mu' ->
State_eval_dstate (Assn_sub_P i a P) mu->
State_eval_dstate P mu'.
Proof. intros P i a s e mu. induction mu; intros; inversion H; subst.
  --simpl in H0. inversion H0; subst. simpl in H1. destruct H1.
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

Theorem rule_assgn: forall (P:Pure_formula) (i:nat) ( a:aexp),
             {{Assn_sub_P i a P}} i := a {{P}}.
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




 

Fixpoint fun_to_list{G:Type} (g: nat-> G) (n_0 : nat) : list (G) := 
  match n_0 with
  | 0 => []
  | S n' => (fun_to_list g n') ++ [g n']
  end. 

  Lemma fun_to_list_length{G:Type}: forall (g: nat-> G) (n_0 : nat),
  length (fun_to_list g n_0) = n_0.
  Proof. induction n_0. simpl. reflexivity.
         simpl. rewrite app_length. rewrite IHn_0. 
         simpl. intuition.
   
  Qed.


  Lemma big_pOplus_length: forall  (f : nat -> R) (g : nat -> State_formula) (n_0 : nat),
  length (big_pOplus f g n_0) = n_0.
  Proof. induction n_0. simpl. reflexivity.
         simpl. rewrite app_length. rewrite IHn_0. 
         simpl. intuition.
   
  Qed.
  
Lemma  get_pro_app: forall (pF1 pF2:pro_formula),
get_pro_formula (pF1 ++pF2)= get_pro_formula pF1 ++ get_pro_formula pF2.
Proof. induction pF1. simpl. intuition.
destruct a.
     simpl. intros. f_equal. intuition. 
   
Qed.


  Lemma big_pOplus_get_pro: forall  (f : nat -> R) (g : nat -> State_formula) (n_0 : nat),
  get_pro_formula (big_pOplus f g n_0) = fun_to_list f n_0.
  Proof. induction n_0. simpl. reflexivity.
         simpl. rewrite get_pro_app.  rewrite IHn_0. 
         simpl. intuition.
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

Theorem rule_conj: forall (F1 F1' F2 F2': State_formula) c,
             {{F1}} c {{F1'}} 
             -> {{F2}} c {{F2'}}
             -> {{F1 /\ F2}} c {{F1' /\ F2'}}.
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



Fixpoint big_hoare (g: npro_formula ) (f:npro_formula) c : Prop := 
           match g ,f with 
           |[],[] =>True
           |[], _ => False
           | _ ,[]=> False
           | hg::tg, hf:: tf =>  and ({{hg}} c {{hf}})  (big_hoare tg tf c) 
            end.


Lemma big_hoare_length:forall nF1 nF2 c,
big_hoare nF1 nF2 c-> length nF1 =length nF2 .
Proof. induction nF1; induction nF2.
       simpl. intuition.
       simpl. intuition.
       simpl. intuition.
       simpl. intros. f_equal.
       destruct H. apply IHnF1 in H0. intuition.
Qed.


Inductive big_ceval{s e:nat}: list (dstate s e) -> com -> list (dstate s e)-> Prop := 
|big_ceval_nil: forall c:com, big_ceval nil c nil
|big_ceval_cons: forall (h h': dstate s e) (t t':list (dstate s e)) (c:com),
                ceval c h h'->
                big_ceval t c t'->
                big_ceval (h::t) c (h'::t').
             
Lemma  get_pro_formula_p_n: forall nF p_n,
length nF =length p_n ->
(get_pro_formula (npro_to_pro_formula nF p_n))=
p_n. 
Proof. induction nF; destruct p_n; simpl; intros; try reflexivity.
    discriminate H. f_equal. apply IHnF. injection H. intuition.
Qed.



Local Close Scope assert_scope.
Lemma ceval_app{s e:nat}:  forall c  (x y mu mu': dstate s e) ,
dstate_eq mu (d_app x y)->
ceval c mu mu' ->
exists mu1 mu2 , ( (ceval c x mu1) /\
ceval c y mu2 
/\ dstate_eq mu' (d_app mu1 mu2)).
Proof. unfold dstate_eq.
 intros c (x, IHx) (y,IHy) (mu,IHmu) (mu', IHmu');
 simpl in *. intros.
 inversion_clear H0.  simpl in *. 
 rewrite H in H3. 
 assert( exists mu1 mu2 , (ceval_single c x mu1
 /\ceval_single c y mu2 
 /\mu'=StateMap.Raw.map2 option_app mu1 mu2)).
 apply ceval_app_aux. assumption.
 destruct H0. destruct H0. 
 destruct H0. destruct H4.
  assert(Sorted.Sorted (StateMap.Raw.PX.ltk (elt:=qstate s e)) x0).
  apply ceval_sorted with c x.
  assumption. assumption.
  assert(Sorted.Sorted (StateMap.Raw.PX.ltk (elt:=qstate s e)) x1).
  apply ceval_sorted with c y.
  assumption. assumption.
  exists (StateMap.Build_slist H6).
  exists (StateMap.Build_slist H7).
   simpl. split. econstructor.
  admit. apply WF_ceval with c x. 
  admit. simpl. assumption.
  simpl. assumption.
  split. econstructor.
  admit. apply WF_ceval with c y. 
  admit. simpl. assumption.
  simpl. assumption.
  assumption.
Admitted.
      

Lemma ceval_scalar{s e:nat}:  forall c  (x mu mu': dstate s e) (p:R),
dstate_eq mu (d_scale_not_0 p x)->
ceval c mu mu' ->
exists y, (and (ceval c x y)
(dstate_eq mu' (d_scale_not_0 p y))).
Proof. unfold dstate_eq.
intros c (x, IHx) (mu,IHmu) (mu', IHmu'); simpl.
intros. inversion_clear H0. simpl in *.
rewrite H in H3.
assert(exists y, (and (ceval_single c x y)
(mu'=StateMap.Raw.map (fun x: qstate s e => p .* x) y))).
apply ceval_dscale_aux. 
assumption. destruct H0. destruct H0.
assert(Sorted.Sorted (StateMap.Raw.PX.ltk (elt:=qstate s e)) x0).
apply ceval_sorted with c x.
assumption. assumption. 
exists (StateMap.Build_slist H5).
split. econstructor. admit.
apply WF_ceval with c x. admit.
simpl. assumption.
simpl. assumption.
simpl. assumption. 


Admitted.



(* Lemma ceval_scalar'{n:nat}:  forall c  (x mu mu' mu1: dstate n) (p:R),
d_scalar' p x  mu1 ->
dstate_eq mu mu1->
ceval c mu mu' ->
exists y1 y,  (and (ceval c x y) 
((d_scalar' p y y1) /\
(dstate_eq mu' y1))).
Proof. unfold dstate_eq. intros.
 assert(p=0%R\/p<>0%R). 
apply Classical_Prop.classic. destruct H2.
subst. inversion H ; subst.  
exists (d_empty n).  



inversion_clear H0. simpl in *.
rewrite H in H3.
assert(exists y, (and (ceval_single c x y)
(mu'=StateMap.Raw.map (fun x: qstate n => p .* x) y))).
apply ceval_6. 
assumption. destruct H0. destruct H0.
assert(Sorted.Sorted (StateMap.Raw.PX.ltk (elt:=qstate n)) x0).
apply ceval_sorted with c x.
assumption. assumption. 
exists (StateMap.Build_slist H5).
split. econstructor. admit.
apply WF_ceval with c x. admit.
simpl. assumption.
simpl. assumption.
simpl. assumption. 


Admitted. *)

Lemma ceval_big_dapp{s e:nat}: forall (p_n :list R) (mu_n:list (dstate s e)) (mu mu':dstate s e)   c,
length p_n =length mu_n->
dstate_eq mu (big_dapp p_n mu_n)->
ceval c mu mu' ->
exists (mu_n': list (dstate s e)), 
 and (big_ceval mu_n c mu_n') 
 (dstate_eq mu' (big_dapp p_n mu_n')).
Proof. induction  p_n; intros; destruct mu_n. 
       simpl in *; exists ([]);
       split; try apply big_ceval_nil.
       inversion H1; subst. unfold dstate_eq in *.
       simpl in *.    unfold StateMap.Raw.empty in *.
       rewrite H0 in H4. inversion_clear H4. reflexivity.
       discriminate H. discriminate H. 
       simpl. 
       assert(exists mu1 mu2 ,  (ceval c (d_scale_not_0 a d) mu1)/\
       (ceval c (big_dapp p_n mu_n) mu2) 
       /\ dstate_eq mu' (d_app mu1 mu2)).
       apply (ceval_app c (d_scale_not_0 a d) (big_dapp p_n mu_n ) mu mu').
       assumption. assumption.
       destruct H2. destruct H2.
       destruct H2.
       assert(exists y, (and (ceval c d y)
       (dstate_eq x (d_scale_not_0 a y)))).
       apply ceval_scalar with ((d_scale_not_0 a d)).
       unfold dstate_eq. reflexivity.
       assumption. destruct H4. 
       assert( exists mu_n' : list (dstate s e),
       big_ceval mu_n c mu_n' /\
       dstate_eq x0 (big_dapp p_n mu_n' )).
       apply IHp_n with ((big_dapp p_n mu_n)).
       unfold dstate_eq . injection H; intuition.
       reflexivity.
       intuition. destruct H5.
       exists (x1::x2). 
       split. apply big_ceval_cons. intuition.
       intuition. apply dstate_eq_trans with ((d_app x x0)).
       intuition. 
       apply d_app_eq. intuition.
       intuition.
Qed. 


 (* Lemma ceval_big_dapp'{n:nat}: forall (p_n :list R) (mu_n:list (dstate n)) (mu mu' mu1:dstate n)   c,
big_dapp' p_n mu_n mu1 ->
dstate_eq mu mu1->
ceval c mu mu' ->
exists (mu_n': list (dstate n)) (mu2:dstate n), 
big_dapp' p_n mu_n' mu2-> 
 and (big_ceval mu_n c mu_n') 
 (dstate_eq mu' mu2).
Proof. induction  p_n; intros; destruct mu_n.
       inversion H; subst.   
       simpl in *; exists ([]). exists (d_empty n).
       intros.  
       split; try apply big_ceval_nil.
       inversion H1; subst. unfold dstate_eq in *.
       simpl in *.    unfold StateMap.Raw.empty in *.
       rewrite H0 in H5. inversion_clear H5. reflexivity.
       inversion_clear H. inversion_clear H. 
       simpl.  inversion H; subst.
       assert(exists mu1 mu2, 
       ((ceval c r mu1)/\
       (ceval c d0 mu2) 
       /\ dstate_eq mu' (d_app mu1 mu2))).
       apply (ceval_app c r d0 mu mu').
       assumption. assumption.
       destruct H2. destruct H2.
       destruct H2. 
       assert(exists y, (and (ceval c d y)
       (dstate_eq x (d_scalar a y)))).
       apply ceval_scalar with ((d_scalar a d)).
       unfold dstate_eq. reflexivity.
       assumption. destruct H4. 
       assert( exists mu_n' : list (dstate n),
       big_ceval mu_n c mu_n' /\
       dstate_eq x0 (big_dapp p_n mu_n' )).
       apply IHp_n with ((big_dapp p_n mu_n)).
       unfold dstate_eq . injection H; intuition.
       reflexivity.
       intuition. destruct H5.
       exists (x1::x2). 
       split. apply big_ceval_cons. intuition.
       intuition. apply dstate_eq_trans with ((d_app x x0)).
       intuition. 
       apply d_app_eq. intuition.
       intuition.
Qed. *)
       

Lemma big_ceval_length{s e:nat}: forall (mu_n mu_n':list (dstate s e)) c,
big_ceval mu_n c mu_n'-> length mu_n' =length mu_n.
Proof. induction mu_n; intros; inversion_clear H.
     reflexivity.
     simpl. f_equal. apply IHmu_n with c.
     assumption.
       
Qed.

Lemma big_add_ceval{s e:nat}: forall (mu_n mu_n':list (dstate s e))
(nF1 nF2:npro_formula)  c,
length mu_n =length nF1 ->
big_and mu_n nF1 ->
big_ceval mu_n c mu_n'->
big_hoare nF1 nF2 c->
big_and mu_n' nF2.
Proof. induction mu_n; destruct mu_n';intros.
- destruct nF1; destruct nF2. assumption. 
  simpl in H2. destruct H2.
  simpl in H2. destruct H2.
 discriminate H.
- inversion H1.
-inversion H1.
-destruct nF1; destruct nF2. discriminate H.
 simpl in H2. destruct H2.
 simpl in H2. destruct H2.
 simpl in *. inversion_clear H1; subst.
 destruct H2. destruct H0. unfold hoare_triple in *.
 split. apply H1 in H3; rewrite sat_Assert_to_State in *.
 assumption. apply H0.
 apply IHmu_n with nF1 c.
 injection H. intuition. 
 assumption. assumption. assumption.
     
Qed.

Lemma big_dapp'_length{s e:nat}: forall p_n (mu_n:list (dstate s e)) (mu:dstate s e),
big_dapp' p_n mu_n mu -> length p_n = length mu_n.
Proof. induction p_n; intros; destruct mu_n. reflexivity.
      inversion_clear H. inversion_clear H.
      inversion H; subst.
      simpl. f_equal. apply IHp_n with d0 .
      assumption.

   
Qed.

Lemma ceval_trace_eq': forall c s e  (mu mu':dstate s e),
WWF_dstate mu->
ceval c mu mu'-> ((d_trace mu' = d_trace mu)%R).
Proof. intros  c s e(mu,IHmu) (mu', IHmu').
 unfold WWF_dstate.  simpl. intros. inversion_clear H0. 
 unfold d_trace. 
   simpl in *.  apply ceval_trace_eq with c. assumption.
   assumption.
Qed.




Theorem rule_sum: forall (nF1 nF2: npro_formula ) c  (p_n:list R),
            (Forall (fun x=> x<>0%R) p_n)->
             length nF1 = length p_n -> 
            (big_hoare nF1 nF2 c)
         -> {{npro_to_pro_formula nF1 p_n}} c
            {{npro_to_pro_formula nF2 p_n}}.
Proof.  unfold hoare_triple. intros nF1 nF2 c p_n H'. intros.  
inversion_clear H2. inversion_clear H5.
 constructor. inversion_clear H1. intuition.  
 apply distribution_formula_npro_to_pro with nF1.
 assumption. rewrite <-(big_hoare_length nF1 _  c).
 assumption. assumption.
 assumption.  rewrite get_pro_formula_p_n in *.
 rewrite pro_npro_inv in H7. 

 assert(exists (mu_n': list (dstate s e)), 
 and (big_ceval mu_n c mu_n') 
 (dstate_eq mu' (big_dapp p_n mu_n'))).
 apply ceval_big_dapp with mu. apply big_dapp'_length with mu'0.
 assumption. apply dstate_eq_trans with mu'0. assumption.
 apply big_dapp_eq with p_n mu_n. assumption.
  apply big_dapp'_to_app. apply big_dapp'_length with mu'0.
  assumption. assumption. assumption.
 destruct H5. destruct H5.
 econstructor.  rewrite get_pro_formula_p_n.
 assert(big_dapp' p_n x ((big_dapp p_n x))).
 apply big_dapp'_to_app.  rewrite (big_ceval_length mu_n _ c).
  apply big_dapp'_length with mu'0. assumption. assumption.
  assumption. apply H10.
 rewrite <-(big_hoare_length nF1 _  c).
 assumption. assumption. assumption.
 rewrite pro_npro_inv. 
 apply big_add_ceval with mu_n nF1 c.
 rewrite H. symmetry.  apply big_dapp'_length with mu'0. 
 assumption. assumption.
 assumption. assumption. 
 rewrite <-(big_hoare_length nF1 _  c).
 assumption. assumption.  
 rewrite (ceval_trace_eq' c _ _  mu mu').
 admit. apply WWF_dstate_aux_to_WF_dstate_aux. assumption.
 assumption.

 assumption. assumption. 

 Admitted.



Import Sorted.
Lemma rule_cond_aux: forall (F F':State_formula) (b:bexp) c1 c2,
{{F/\ b}} c1 {{F'}}->
{{F /\ b}} if b then c1 else c2 end {{F'}}.
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
{{F/\ (BNot b)}} c2 {{F'}}->
{{F /\ (BNot b)}} if b then c1 else c2 end {{F'}}.
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
        ({{F1 /\ (b)}} c1 {{F1'}} /\ {{F2 /\ ((BNot b) )}} c2 {{F2'}})
     -> ({{ APro [(p, (F1 /\ b)) ; ((1 - p), (F2 /\ (BNot b)))]}}
        if b then c1 else c2 end
        {{APro [(p, F1') ; ((1 - p), F2')]}}).
Proof. intros. assert ([(p, F1 /\ b); (1 - p, F2 /\ (BNot b))]=
       (npro_to_pro_formula ([(F1 /\ b); ( F2 /\ (BNot b))]) ([p; (1-p)]))).
       simpl. reflexivity. rewrite H1. 
       assert ([(p, F1'); (1 - p, F2')]=
       (npro_to_pro_formula ([(F1'); ( F2')]) ([p; (1-p)]))).
       reflexivity. rewrite H2.
       apply rule_sum. simpl. econstructor.
       lra. econstructor. lra. apply Forall_nil.
       reflexivity.
       simpl. 
       split. apply rule_cond_aux. intuition. 
       split. apply rule_cond_aux_2. intuition.
       intuition.   
Qed.


(* Theorem rule_sum_npro: forall (nF1 nF2: npro_formula ) c ,
            (big_hoare nF1 nF2 c)
         -> {{ nF1 }} c
            {{ nF2 }}.
Proof. intros. unfold hoare_triple. intros.
       inversion_clear H1.  inversion_clear H3.
       econstructor. admit.
       econstructor. inversion_clear H0. intuition.
       admit. 
      assert({{npro_to_pro_formula nF1 p_n}} c {{npro_to_pro_formula nF2 p_n}}).
      apply rule_sum. admit. assumption.
      unfold hoare_triple in *.
      assert(sat_Assert mu' (npro_to_pro_formula nF2 p_n)).
      apply H3 with mu.  assumption.
      econstructor. intuition. assumption. assumption.
      inversion_clear H6. apply H9.
Admitted. *)


(* Theorem rule_while_aux :  forall (P : State_formula) (b : bexp) (c : com),
(forall (n : nat) (mu mu' : list (cstate *qstate n )),
 ceval_single c mu mu' ->
 State_eval_dstate  (P /\ b) mu -> State_eval_dstate  P mu') ->
forall (n : nat) (mu mu' :list (cstate *qstate n )),
ceval_single <{ while b do c end }> mu mu' ->
State_eval_dstate P mu -> State_eval_dstate (P /\ ~ b) mu'.
Proof. intros. 
    remember <{while b do c end}> as original_command eqn:Horig.
    induction H0; try inversion Horig. simpl in H1. intuition.

apply d_seman_app.  apply IHceval_single2.
reflexivity. *)


      

(* Theorem hoare_while : forall P (b:bexp) c,
  {{P /\ b}} c {{P}} ->
  {{P}} while b do c end {{P /\ ~ b}}.
Proof. unfold hoare_triple.
  intros P b c Hhoare st st' Heval HP.  
  (* We proceed by induction on [Heval], because, in the "keep looping" case,
     its hypotheses talk about the whole loop instead of just [c]. The
     [remember] is used to keep the original command in the hypotheses;
     otherwise, it would be lost in the [induction]. By using [inversion]
     we clear away all the cases except those involving [while]. *)
  remember <{while b do c end}> as original_command eqn:Horig. 
  induction Heval;
    try (inversion Horig; subst; clear Horig);
    eauto.  simpl.
Qed. *)

Local Open Scope R_scope. 
Lemma d_seman_app'': forall s e (F:State_formula)  (mu mu':dstate s e),
sat_State mu F  -> sat_State  (mu') F ->
(WF_dstate (d_app mu mu'))
-> sat_State (d_app mu mu') F.
Proof. intros s e F (mu,IHmu) (mu',IHmu'). unfold WF_dstate.
        unfold d_app. unfold StateMap.map2 . simpl. 
        intros. inversion_clear H. 
        inversion_clear H0. 
        econstructor. assumption.
        apply d_seman_app_aux. 
        assumption. assumption. 
        assumption. assumption.
Qed.


Lemma while_seq: forall (b:bexp) c F0  F1, 
{{F0 /\ b}} c; while b do c end {{F1 /\ ((BNot b))}} ->
{{F0 /\ b}} while b do c end {{F1 /\ (BNot b)}} .
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
       assert(sat_Assert (StateMap.Build_slist H0) (F1 /\ (BNot b))).
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
       
       assert(sat_Assert (StateMap.Build_slist H5) ((F1 /\ (BNot b)))).
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
       assert(sat_Assert (StateMap.Build_slist H7) (F1 /\ (BNot b))).
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

(* Lemma rule_OMerg_npro:forall F1 b,
(ANpro [F1 /\ (BNot b); F1 /\ (BNot b)]) ->>(F1 /\ (BNot b)) .
Proof.

unfold assert_implies. intros.
inversion_clear H.  inversion_clear H1.
destruct p_n. inversion_clear H2. 
rewrite sum_over_list_nil_formula in H4. intuition.
destruct p_n.  
econstructor. discriminate.
econstructor. assumption.
assert(distribution_formula
(npro_to_pro_formula (F1 /\ (BNot b)) [r])).
apply H2. apply H1.  simpl npro_to_pro_formula.
apply H3. 

assert( APro([(r, F1 /\ (BNot b)); (r0, F1 /\ (BNot b))]) ->> APro [(r + r0, F1 /\ (BNot b))]).
apply rule_OMerg. admit. unfold assert_implies in H1. 
econstructor.  discriminate. 
assert(sat_Assert mu
(npro_to_pro_formula (F1 /\ ~ b) [r+r0])).
simpl npro_to_pro_formula. 
apply H1. econstructor; assumption. 
apply H4.  
Admitted. *)

Lemma rule1: forall s e (mu:list (state s e)) (sigma:cstate) (rho:qstate s e) IHmu H
F0 F1 (b:bexp), 
sat_Assert
       {|
         StateMap.this := (sigma, rho) :: mu;
         StateMap.sorted := IHmu
       |} (ANpro ([F0 /\ b; F1 /\ (BNot b)])) ->
       beval (sigma, rho) b = true->
       sat_Assert
       {|
         StateMap.this := [(sigma, rho)];
         StateMap.sorted := H
       |} (F0 /\ b)    
        .
Proof. intros. inversion_clear H0.   
  inversion_clear H3. destruct p_n. 
  inversion_clear H4. rewrite sum_over_list_nil_formula in H6.
  intuition.  destruct p_n. 
  simpl in H2. intuition. 
  destruct p_n.

 assert(r=0\/r<>0). apply Classical_Prop.classic.
 destruct H3. subst. inversion_clear H4. 
 repeat rewrite sum_over_list_cons_formula in *. 
 rewrite sum_over_list_nil_formula in *. simpl in H6.
 rewrite Rplus_0_l in H6. rewrite Rplus_0_r in H6. subst.
 apply sat_Pro_State in H5. destruct H5. 
 inversion_clear H4. simpl in H7. 
 inversion_clear H7. destruct H4. rewrite H1 in H7.
 simpl in H7. destruct H7. 
 assert(r0=0\/r0<>0). apply Classical_Prop.classic.
 destruct H6. subst. inversion_clear H4. 
 repeat rewrite sum_over_list_cons_formula in *. 
 rewrite sum_over_list_nil_formula in *. simpl in H6.
 rewrite Rplus_0_l in H7. rewrite Rplus_0_r in H7.
 simpl in H7. subst.
 assert(sat_Assert
 {|
   StateMap.this := (sigma, rho) :: mu;
   StateMap.sorted := IHmu
 |} (APro ([(0, F1 /\ <{ ~ b }>); (1, F0 /\ b)]))).
 assert([(0, F1 /\ <{ ~ b }>); (1, F0 /\ b)]= swap_list 
 [(1, F0 /\ b); (0, F1 /\ <{ ~ b }>)] 0). reflexivity.
 rewrite H4. apply rule_POplusC.  econstructor.
 assumption. econstructor. assumption. 
 repeat rewrite sum_over_list_cons_formula in *. 
 rewrite sum_over_list_nil_formula in *.   rewrite Rplus_0_l.
 rewrite Rplus_0_r. auto. assumption.
 inversion_clear H4.  apply sat_Pro_State in H9. 
 destruct H9. inversion_clear H4. 
 simpl in H11. inversion_clear H11. 
 rewrite sat_Assert_to_State. econstructor.
 apply WF_state_dstate_aux.  inversion_clear H0. assumption.
 simpl. econstructor. intuition. apply Forall_nil. 

rewrite sat_Assert_to_State. 
inversion_clear H5. simpl in *.
destruct mu_n. intuition.
destruct mu_n. simpl in H3. inversion_clear H7.
inversion_clear H11. destruct mu_n. simpl in *.
econstructor. inversion_clear H0.
apply WF_state_dstate_aux. assumption.
simpl in *.  
assert(dstate_eq mu' (big_dapp [r; r0] [d; d0] )).
apply big_dapp_eq with ([r; r0]) ([d; d0]).
assumption. apply big_dapp'_to_app.
reflexivity. econstructor. assumption. econstructor. assumption.
apply Forall_nil. 
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
 destruct H9. apply WF_sat_State in H9.
 simpl in *. intuition. 
 destruct d0. destruct H9. destruct H12.
  simpl in *.
  apply WF_sat_State in H12.
 simpl in *. intuition.
 destruct p. destruct p0. 
simpl in *. 
destruct (Cstate_as_OT.compare c c0).
injection H11. intros.
rewrite H13. rewrite H14.
destruct H9. inversion_clear H9.
simpl in H17. inversion_clear H17.
 econstructor.  split.
 assert((@pair cstate (qstate s e) c (r .* q)) = s_scale r (c,q)).
 reflexivity. rewrite H17.
 apply s_seman_scale.  inversion_clear H4. repeat rewrite sum_over_list_cons_formula in H20.
 rewrite sum_over_list_nil_formula in H20. simpl in H20.
 rewrite Rplus_0_r in H20. inversion_clear H19. 
 inversion_clear H21. simpl in *.  lra.
 intuition. rewrite (state_eq_bexp (c, r .* q) 
  (c,q) _). intuition. reflexivity.
  apply Forall_nil.

  injection H11. intros.
  destruct H9. inversion_clear H15.
  inversion_clear H16.  simpl in *.
  inversion_clear H18. destruct H16.
  unfold Cstate_as_OT.eq in e0. 
  rewrite <-e0 in H18. 
  rewrite <-H14 in H18. 
  rewrite <-(state_eq_bexp (sigma, rho) 
  (sigma ,q0) _) in H18. 
  rewrite H1 in H18. destruct H18. intuition.

  injection H11. intros.
  destruct H9. inversion_clear H15.
  inversion_clear H16.  simpl in *.
  inversion_clear H18. destruct H16.
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
       |} (ANpro ([F0 /\ b; F1 /\ (BNot b)])) ->
       beval (sigma, rho) b = false->
       sat_Assert
       {|
         StateMap.this := [(sigma, rho)];
         StateMap.sorted := H
       |} (F1 /\ (BNot b))    
        .
Proof. intros. inversion_clear H0.   
  inversion_clear H3. destruct p_n. 
  inversion_clear H4. rewrite sum_over_list_nil_formula in H6.
  intuition.  destruct p_n. 
  simpl in H2. intuition. 
  destruct p_n.

 assert(r=0\/r<>0). apply Classical_Prop.classic.
 destruct H3. subst. inversion_clear H4. 
 repeat rewrite sum_over_list_cons_formula in *. 
 rewrite sum_over_list_nil_formula in *. simpl in H6.
 rewrite Rplus_0_l in H6. rewrite Rplus_0_r in H6. subst.
 apply sat_Pro_State in H5. destruct H5. 
 inversion_clear H4. 
 simpl in H7. inversion_clear H7. 
 rewrite sat_Assert_to_State. econstructor.
 apply WF_state_dstate_aux.  inversion_clear H0. assumption.
 simpl. econstructor. intuition. apply Forall_nil. 
 
 
 assert(r0=0\/r0<>0). apply Classical_Prop.classic.
 destruct H6. subst. inversion_clear H4. 
 repeat rewrite sum_over_list_cons_formula in *. 
 rewrite sum_over_list_nil_formula in *. simpl in *.
 rewrite Rplus_0_r in *. rewrite Rplus_0_r in *. subst.
 assert(sat_Assert
 {|
   StateMap.this := (sigma, rho) :: mu;
   StateMap.sorted := IHmu
 |} (APro ([(0, F1 /\ <{ ~ b }>); (1, F0 /\ b)]))).
 assert([(0, F1 /\ <{ ~ b }>); (1, F0 /\ b)]= swap_list 
 [(1, F0 /\ b); (0, F1 /\ <{ ~ b }>)] 0). reflexivity.
 rewrite H4. apply rule_POplusC.  econstructor.
 assumption. econstructor. assumption. 
 repeat rewrite sum_over_list_cons_formula in *. 
 rewrite sum_over_list_nil_formula in *.   rewrite Rplus_0_l.
 rewrite Rplus_0_r. auto. assumption.
 inversion_clear H4.  apply sat_Pro_State in H9. 
destruct H9.
 inversion_clear H4. simpl in H11. 
 inversion_clear H11. destruct H4. rewrite H1 in H11.
 destruct H11. 

rewrite sat_Assert_to_State. 
inversion_clear H5. simpl in *.
destruct mu_n. intuition.
destruct mu_n. simpl in H3. inversion_clear H7.
inversion_clear H11. destruct mu_n. simpl in *.
econstructor. inversion_clear H0.
apply WF_state_dstate_aux. assumption.
simpl.  
assert(dstate_eq mu' (big_dapp [r; r0] [d; d0] )).
apply big_dapp_eq with ([r; r0]) ([d; d0]).
assumption. apply big_dapp'_to_app.
reflexivity. econstructor. assumption. econstructor. assumption.
apply Forall_nil. 
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
 destruct H9. apply WF_sat_State in H9.
 simpl in *. intuition. 
 destruct d0. destruct H9. destruct H12.
  simpl in *.
  apply WF_sat_State in H12.
 simpl in *. intuition.
 destruct p. destruct p0. 
simpl in *. 
destruct (Cstate_as_OT.compare c c0).
injection H11. intros.
rewrite H13. rewrite H14.
destruct H9. inversion_clear H9.
simpl in H17. inversion_clear H17.
destruct H9. rewrite <-H14 in H17.
rewrite <-(state_eq_bexp (sigma, rho) 
  (sigma ,q) _) in H17.
  rewrite H1 in H17. destruct H17. intuition.

  injection H11. intros.
  destruct H9. inversion_clear H9.
  inversion_clear H17.  simpl in *.
  destruct H9.
  unfold Cstate_as_OT.eq in e. 
  rewrite <-H14 in H17.
  rewrite <-(state_eq_bexp (sigma, rho) 
  (sigma ,q) _) in H17.
  rewrite H1 in H17. destruct H17.
  intuition.

  injection H11. intros.
  rewrite H13. rewrite H14.
  destruct H9. inversion_clear H15.
  inversion_clear H16.  simpl in *.
  inversion_clear H18. destruct H16.
  econstructor.  split.
  assert((@pair cstate (qstate s e) c0 (r0 .* q0)) = s_scale r0 (c0,q0)).
  reflexivity. rewrite H20.
  apply s_seman_scale.  inversion_clear H4. repeat rewrite sum_over_list_cons_formula in *.
  rewrite sum_over_list_nil_formula in *. simpl in *.
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
         {{F0 /\ b}} c {{ ANpro [(F0 /\ b) ; (F1 /\ (BNot b))] }}
      -> {{ANpro[(F0 /\ b); (F1/\ (BNot b))]}}
         while b do c end
         {{ (F1 /\ (BNot b)) }}.
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
      
     assert(sat_State (d_app (StateMap.Build_slist H6) (StateMap.Build_slist H7)) (F1 /\ (BNot b))).
     apply (d_seman_app'' _ _ _ (StateMap.Build_slist H6) (StateMap.Build_slist H7)). 
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
      assert( (sat_Assert (StateMap.Build_slist H9) (ANpro [F0 /\ b; F1 /\ (BNot b)]))).
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
     assert(sat_State (d_app (StateMap.Build_slist H5) (StateMap.Build_slist H6)) (F1 /\ (BNot b))).
     apply (d_seman_app'' _ _ _ (StateMap.Build_slist H5) (StateMap.Build_slist H6)).
     rewrite <-sat_Assert_to_State. 
     apply rule_false with (p::mu) IHmu F0. assumption.
     assumption.
    
     inversion_clear IHmu.
     assert((sat_Assert (StateMap.Build_slist H7) (ANpro [F0 /\ b; F1 /\ (BNot b)]))).
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
         {{F0 /\ b}} c {{ ANpro [(F0 /\ b) ; (F1 /\ (BNot b))] }}
      -> {{(F0 /\ b)}}
         while b do c end
         {{ (F1 /\ (BNot b)) }}.
Proof. intros. apply while_seq. apply rule_seq with (ANpro[F0 /\ b; F1 /\ (BNot b)]).
          assumption. apply rule_while. assumption.
Qed.


