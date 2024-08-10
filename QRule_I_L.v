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


(* Lemma rule_f: forall  F1 F2 c n (mu mu':list (cstate * qstate n )) ,
State_eval_dstate (F1 ⊙ F2) mu->
ceval_single c mu mu'-> 
NSet.Subset (fst (MVar c)) (fst (Free_state F1))->
NSet.Subset (snd (MVar c)) (snd (Free_state F1))->
State_eval_dstate F2 mu'.
Proof. induction c. intros. 
-(*skip*) apply ceval_skip_1 in H0. rewrite <-H0.
  rewrite State_eval_odot in H.  intuition.
-admit.
-intros. inversion H0; subst.  assumption. *)
Lemma rule_f': forall a s e sigma (rho:qstate s e) i a',
NSet.Equal (NSet.inter (NSet.add i NSet.empty)
       ((Free_aexp a))) (NSet.empty) ->
 aeval 
  (c_update i (aeval (sigma, rho) a') sigma, rho) a =
  aeval 
  (sigma, rho) a .
Proof. induction a; intros.
       simpl. reflexivity.   
       simpl in *. 
       assert(i0<>i). admit.
       rewrite c_update_find_not.
       reflexivity. assumption.
       simpl in *. rewrite IHa1.
       rewrite IHa2. reflexivity.
       admit. admit.
       simpl in *. rewrite IHa1.
       rewrite IHa2. reflexivity.
       admit. admit.
       simpl in *. rewrite IHa1.
       rewrite IHa2. reflexivity.
       admit. admit.
       simpl in *. rewrite IHa1.
       rewrite IHa2. reflexivity.
       admit. admit.
       simpl in *. rewrite IHa1.
       rewrite IHa2. reflexivity.
       admit. admit.
       simpl in *. rewrite IHa1.
       rewrite IHa2. reflexivity.
       admit. admit.
       simpl in *. rewrite IHa1.
       rewrite IHa2. reflexivity.
       admit. admit.
Admitted.

Lemma rule_f_b: forall b s e sigma (rho:qstate s e) i a,
NSet.Equal (NSet.inter (NSet.add i NSet.empty)
       ((Free_bexp b))) (NSet.empty) ->
beval 
  (c_update i (aeval (sigma, rho) a) sigma, rho) b=
beval 
  (sigma, rho) b .
Proof. induction b; intros.
       simpl. reflexivity.
       simpl. reflexivity.   
       simpl in *. repeat rewrite rule_f'.
       reflexivity. admit. admit.
       simpl in *. repeat rewrite rule_f'.
       reflexivity. admit. admit.
       simpl in *. repeat rewrite rule_f'.
       reflexivity. admit. admit.
       simpl in *. repeat rewrite rule_f'.
       reflexivity. admit. admit.
       simpl in *.  rewrite IHb.
       reflexivity. assumption.
       simpl in *. rewrite IHb1. rewrite IHb2.
       reflexivity. admit. admit.
       simpl in *. rewrite IHb1. rewrite IHb2.
       reflexivity. admit. admit.
Admitted.

(* Lemma Free_map: forall (P:nat->Pure_formula) (x y:nat) ,
(Free_pure (P x))= (Free_pure (P y)).
Proof. induction P. simpl. intros. induction (P x); induction (P y).
       destruct b; destruct b0. reflexivity.

  
Qed. *)


Lemma rule_f'_p: forall  P s e sigma (rho:qstate s e) i a,
NSet.Equal (NSet.inter (NSet.add i NSet.empty)
       ((Free_pure P))) (NSet.empty) ->
Pure_eval P
  (c_update i (aeval (sigma, rho) a) sigma, rho)<->
Pure_eval P
  (sigma, rho) .
Proof. induction P; intros.
       simpl. rewrite rule_f_b. reflexivity.    
       assumption. admit. admit.
       split. 
       simpl in *. intros.
       remember (c_update i (aeval (sigma, rho) a) sigma).
       apply (IHP _ _ c rho i0 a0).
       assumption.
       rewrite Heqc. admit.
       intros.
       simpl in *.
       remember (c_update i (aeval (sigma, rho) a) sigma).
       apply (IHP _ _ c rho i0 a0) in H0.
Admitted.

Lemma rule_f_assn: forall  F s e sigma (rho:qstate s e) i a,
NSet.Equal (NSet.inter (fst (MVar <{ i := a }>)) (fst (Free_state F))) NSet.empty ->
State_eval F (c_update i (aeval (sigma, rho) a) sigma, rho) <-> State_eval F (sigma, rho) .
Proof. induction F; intros; simpl in *. 
       apply rule_f'_p. assumption. 
       admit.
Admitted.

(* Fixpoint QExp_dom (qs:QExp) :=
  match qs with 
  | QExp_s s e v => (s, e) 
  | QExp_t qs1 qs2 =>  (QExp_dom qs1) .+ (QExp_dom qs2)
  end .

Fixpoint QExp_vec (qs: QExp) (s e:nat) :=
  match qs with 
  | QExp_s s e v => v 
  | QExp_t qs1 qs2 =>  (QExp_vec qs1) .+ (QExp_vec qs2)
  end . *)

(* Lemma QExp_pure: forall (qs: QExp) s e c (q : qstate s e) ,
State_eval qs (c, q)->
exists (q': Density (2^(e-s))) (p:R), and (Pure_State q')
(q=p .* q').
Proof. induction qs. intros. 
       simpl in H. 
  
Qed.


Lemma QExp_eval_sub: forall (qs: QExp) s e c (q q': qstate s e) ,
q_subseq q q'->
State_eval qs (c, q')->
State_eval qs (c, q).
Proof. induction qs; intros.
      inversion_clear H. subst. intuition.
      admit.
      inversion_clear H. subst. intuition.
      destruct H1. subst.
      simpl in H0.
      destruct H0. destruct H.
      destruct H. destruct H.
      destruct H. destruct H.
      destruct H. 
      inversion H; subst.
      simpl.
Admitted.



Lemma QExp_eval_sub': forall F s e c (q q': qstate s e) ,
q_subseq q q'->
State_eval F (c, q')->
State_eval F (c, q).
Proof. induction F; intros.
       apply state_eq_Pure with (c,q').
       reflexivity. intuition.
       inversion_clear H.
       subst. intuition.
       destruct H1.  subst.
       induction qs.
       simpl in H0. 
       simpl.  
       split. intuition.
       split. intuition.
       split. intuition.
       rewrite <-PMtrace_scale in *.
       rewrite PMtrace_plus in *.
       rewrite Mscale_plus_distr_r in *.
       destruct H0. destruct H0.
       destruct H1. 
       admit. lia. lia.
       admit.

       

      



Lemma State_eval_sub: forall s e (mu mu': list (state s e)) F,
d_subseq mu mu'->
State_eval_dstate F mu'->
State_eval_dstate F mu.
Proof. induction mu.  intros. destruct mu'.
       simpl in H0. destruct H0.
       simpl in H. destruct H.
       intros. destruct mu'.
       destruct a.
       simpl in H. destruct H.
       destruct mu; destruct mu';
       destruct a; destruct s0.
       simpl in H. 
       simpl. econstructor.
       inversion_clear H0.
       admit. 
       
       econstructor.

       simpl in H. intuition.
       destruct s1.
       simpl in H. intuition.
       simpl. econstructor.
       admit.
       apply IHmu with (s2 :: mu').
       destruct s1. destruct s2.
       simpl in H. econstructor. intuition.
       split. intuition. intuition.
       inversion_clear H0. intuition.   
 Admitted. *)



(* Lemma rule_f_qinit_qs: forall  F1 F2 s' e' (st st': (cstate * qstate s' e' )) s e,
State_eval (F1 ⊙ F2) st->
ceval_single (QInit s e) [st] [st']-> 
NSet.Subset (snd (MVar (QInit s e))) (snd (Free_state F1))->
State_eval F1 st'.
Proof. induction qs. intros. 
       inversion H0; subst. inversion H8; subst.
       inversion_clear H8. injection H7.
       intros. rewrite <-H2.  clear H7. clear H2.


       assert(e < s0 \/ s> e0)%nat. admit.
       destruct H2.
       simpl in *. split. intuition.
       split. intuition.  
        admit.
        intros.
        simpl in *.
        split.  intuition.
        split. apply (IHqs1 F1  n st st' s e).
        split. admit. intuition.
        assumption. assumption.
        apply (IHqs2 F1  n st st' s e).
        split. admit. intuition.
        assumption. assumption.
Admitted. *)




(* Lemma rule_f_qinit: forall  F1 F2 F3 s' e' (st st': (cstate * qstate s' e' )) s e,
(forall (s0 e0: nat) (st st':(cstate * qstate s' e' )), 
State_eval F1 st -> 
ceval_single (QInit s e) [st] [st']-> 
State_eval F2 st') -> 
State_eval (F1 ⊙ F3) st->
ceval_single (QInit s e) [st] [st']-> 
NSet.Subset (snd (MVar (QInit s e))) (snd (Free_state F1))->
State_eval (F2 ⊙ F3) st'.
Proof. intros. inversion H0; subst. destruct st.
       destruct st'.  destruct H3.
       destruct H3. destruct H3. destruct H3.
       destruct H3. destruct H3. 
       inversion H3; subst. simpl in H10. 
       rewrite <-H10 in H1. simpl in H2.
       inversion H1; subst. inversion H13; subst.
       clear H13. injection H12. intros; subst.
       clear H12. simpl in H4. 
Admitted. *)

(* Inductive d_combin {s0 e0 s1 e1 s2 e2:nat}: (list (cstate * qstate s0 e0))-> (list (cstate * qstate s1 e1))-> (list (cstate * qstate s2 e2))-> Prop:=
|combin_nil: d_combin nil nil nil 
|combin_cons: forall sigma rho0  rho1  rho' mu0 mu1 mu',
              q_combin rho0 rho1 rho'->
              d_combin mu0 mu1 mu'->
               d_combin ((sigma, rho0)::mu0) ((sigma, rho1)::mu1) ((sigma, rho')::mu'). *)

Inductive q_combin{s0 e0 s1 e1 s2 e2}: (qstate s0 e0) -> (qstate s1 e1)-> (qstate s2 e2)->Prop:=
|combin_l: forall q0 q1, e0 = s1-> s0 = s2 -> e1 = e2 ->
            q_combin q0 q1 (@kron (2^(e0-s0)) (2^(e0-s0)) (2^(e1-s1))  
            (2^(e1-s1)) q0 q1)
|combin_r: forall q0 q1, e1 = s0-> s1= s2 -> e0 =e2 ->
            q_combin q0 q1 (@kron  (2^(e1-s1))  
            (2^(e1-s1)) (2^(e0-s0)) (2^(e0-s0)) q1 q0).

Inductive d_combin {s0 e0 s1 e1 s2 e2:nat}: (list (cstate * qstate s0 e0))-> (list (cstate * qstate s1 e1))-> (list (cstate * qstate s2 e2))-> Prop:=
|combin_nil: d_combin nil nil nil 
|combin_cons: forall sigma rho0  rho1  rho' mu0 mu1 mu',
      q_combin rho0 rho1 rho'->
      d_combin mu0 mu1 mu'->
        d_combin ((sigma, rho0)::mu0) ((sigma, rho1)::mu1) ((sigma, rho')::mu').

Fixpoint d_subseq{s e: nat} (mu0 mu1: list (cstate *qstate s e)): Prop:=
match mu0, mu1 with 
|nil , nil=> True
|(c0,q0)::mu0', (c1,q1)::(mu1')=>c0=c1 /\ q_subseq q0 q1 /\ d_subseq mu0' mu1'
|_, _=> False
end.

(* Lemma State_eval_combin: forall s e (mu:list(cstate * qstate s e)) (F1 F2:State_formula),
State_eval_dstate (F1 ⊙ F2) mu <->
(exists s0 e0 s1 e1 (mu0:list(cstate * qstate s0 e0)) (mu1:list(cstate * qstate s1 e1)), 
and (d_combin mu0 mu1 mu ) 
((State_eval_dstate F1 mu0 /\ State_eval_dstate F2 mu1)))
.
Proof. 
Admitted. *)


Lemma rule_6: forall c s e s0 e0 s1 e1
(q:qstate s0 e0) (q0:qstate s1 e1) (rho': qstate s e)
(x:list(cstate * qstate s0 e0))(x0:list(cstate * qstate s1 e1))
(x1:list(cstate * qstate s e)),
q_combin q q0 rho'->
d_combin x x0 x1 ->
exists (mu:list (cstate * qstate s e)),
d_combin (StateMap.Raw.map2 option_app [(c, q)] x)
    (StateMap.Raw.map2 option_app [(c, q0)] x0) mu.
Proof. 
induction x; intros. inversion_clear H0.
simpl. exists [(c, rho')].
econstructor. assumption. econstructor.
destruct a. 
inversion_clear H0.
simpl. destruct (Cstate_as_OT.compare c c0).
exists ((c,rho')::(c0,rho'0)::mu').
econstructor. assumption.
econstructor. assumption.
repeat rewrite map2_r_refl.
assumption.
inversion H; subst.
exists ((c,@kron (2^(s1-s)) (2^(s1-s))
(2^(e-s1)) (2^(e-s1)) (q .+ q1) (q0 .+ rho1))::mu').
apply (@combin_cons s s1 s1 e s e).
econstructor; try reflexivity.
repeat rewrite map2_r_refl.
assumption.
exists ((c,@kron  (2^(s0-s)) (2^(s0-s)) (2^(e-s0)) (2^(e-s0))
 (q0 .+ rho1) (q .+ q1))::mu').
apply (@combin_cons s0 e s s0 s e).
econstructor; try reflexivity.
repeat rewrite map2_r_refl.
assumption.
apply IHx in H2.
destruct H2.
exists ((c0,rho'0)::x2).
econstructor. 
assumption.
apply H0.
assumption.
Qed.

Lemma rule_7: forall s e s0 e0 s1 e1
(x mu1:list(cstate * qstate s0 e0))(x0 mu2:list(cstate * qstate s1 e1))
(x1 mu3:list(cstate * qstate s e)),
d_combin mu1 mu2 mu3->
d_combin x x0 x1 ->
exists (mu:list (cstate * qstate s e)),
d_combin (StateMap.Raw.map2 option_app mu1 x)
    (StateMap.Raw.map2 option_app mu2 x0) mu.
Proof. 
induction x; induction mu1; intros.
{ inversion_clear H0. inversion_clear H.
simpl. exists nil.
econstructor. }
{ destruct a. 
inversion_clear H0. inversion_clear H.
simpl. repeat rewrite map2_l_refl.
exists ((c,rho')::mu').
econstructor. assumption. assumption. }
{destruct a. 
inversion_clear H0. inversion_clear H.
simpl. repeat rewrite map2_r_refl.
exists ((c,rho')::mu').
econstructor. assumption. assumption. }
{destruct a0. destruct a.
inversion_clear H. inversion_clear H0. 
simpl. destruct (Cstate_as_OT.compare c c0).
assert (exists mu : list (cstate * qstate s e),
d_combin (StateMap.Raw.map2 option_app mu1 ((c0, q0) :: x))
(StateMap.Raw.map2 option_app mu4 ((c0, rho2) :: mu5)) mu ).
apply IHmu1 with ((c0, rho'0)::mu'0) mu'.
assumption. econstructor. assumption.
assumption. destruct H0.
exists ((c,rho')::x2).
econstructor. assumption.
assumption.

assert(exists mu'1 : list (cstate * qstate s e),
d_combin (StateMap.Raw.map2 option_app mu1 x)
(StateMap.Raw.map2 option_app mu4 mu5) mu'1).
apply IHx with mu'0 mu'.
assumption. assumption.
destruct H0.
inversion H1; subst.
exists ((c,@kron (2^(s1-s)) (2^(s1-s))
(2^(e-s1)) (2^(e-s1)) (q .+ q0) (rho1 .+ rho2))::x2).
apply (@combin_cons s s1 s1 e s e).
econstructor; try reflexivity.
assumption.
exists ((c,@kron  (2^(s0-s)) (2^(s0-s)) (2^(e-s0)) (2^(e-s0))
(rho1 .+ rho2)(q .+ q0) )::x2).
apply (@combin_cons s0 e s s0 s e).
econstructor; try reflexivity.
assumption.

assert (exists mu : list (cstate * qstate s e),
d_combin (StateMap.Raw.map2 option_app ((c, q)::mu1) x)
    (StateMap.Raw.map2 option_app ((c, rho1)::mu4) mu5) mu).
apply IHx with  mu'0 ((c, rho') ::mu').
econstructor. assumption.
assumption. assumption.
destruct H0. 
exists ((c0,rho'0)::x2).
econstructor.
assumption.
assumption. }
Qed.

Lemma q_combin_eq:forall s e s0 e0 s1 e1
(q:qstate s0 e0) (q0:qstate s1 e1) (rho rho': qstate s e),
q_combin q q0 rho->
q_combin q q0 rho'->
rho=rho'.
Proof. intros. inversion H; subst. 
       inversion H0; subst. reflexivity.
       assert(1=2^(s-s))%nat. rewrite Nat.sub_diag.
       rewrite pow_0_r. lia. unfold qstate. destruct H1.
       admit. 
       inversion H0; subst.
       admit.
       reflexivity.
Admitted.

Lemma d_combin_eq:forall s e s0 e0 s1 e1
(mu:list (state s0 e0)) (mu0: list (state s1 e1)) (mu1 mu2: list (state s e)),
d_combin mu mu0 mu1->
d_combin mu mu0 mu2->
mu1=mu2.
Proof. induction mu; intros. inversion H; subst. 
       inversion H0; subst. reflexivity.
       inversion H; subst.
       inversion H0; subst. f_equal.
       f_equal. apply q_combin_eq with 
       s0 e0 s1 e1 rho0 rho1; assumption.
       apply IHmu with mu4; assumption.
Qed.

Lemma q_subseq_eq:forall s e  (q q':qstate s e),
q=q'-> q_subseq q q'.
Proof. intros. subst. unfold q_subseq.
       left. reflexivity. 
Qed.

Lemma d_subseq_eq:forall s e (mu mu':list (state s e)),
mu=mu'-> d_subseq mu mu'.
Proof. induction mu; destruct mu'; intros.
      econstructor. destruct H. econstructor.
      destruct H. 
      destruct a. econstructor. reflexivity.
      split.
      apply q_subseq_eq. reflexivity.
      apply IHmu. reflexivity.
      injection H; intros; subst.
      destruct s0. 
      econstructor. reflexivity.
      split.  
      apply q_subseq_eq. reflexivity.
      apply IHmu. reflexivity.

Qed.

Lemma rule_three:  forall s e s0 e0 s1 e1
(x:list(cstate * qstate s0 e0))(x0:list(cstate * qstate s1 e1))
(q:qstate s0 e0) (q0:qstate s1 e1) (rho': qstate s e)
(mu'1 mu:list(cstate * qstate s e)) c ,
q_combin q q0 rho'->
d_combin x x0 mu'1->
(d_combin
  (StateMap.Raw.map2 option_app
     [(c,q)] x)
  (StateMap.Raw.map2 option_app
     [(c, q0)] x0) mu)
  -> d_subseq (StateMap.Raw.map2 option_app
  [(c,
    rho')] mu'1) mu.
Proof. induction x; intros.
--inversion H0; subst.  clear H0. simpl in H1. 
  simpl StateMap.Raw.map2. inversion_clear H1.
  inversion_clear H2. econstructor. reflexivity.
  split. 
  apply q_subseq_eq. apply q_combin_eq with s0
  e0 s1 e1 q q0. assumption. assumption. econstructor.
--destruct a. inversion H0; subst. clear H0.
  simpl in H1.  
  destruct (Cstate_as_OT.compare c c0);
  repeat rewrite map2_r_refl in H1.
  inversion_clear H1; inversion_clear H2;
  simpl; MC.elim_comp;
  econstructor. reflexivity.  split. apply q_subseq_eq.
  apply q_combin_eq with s0
  e0 s1 e1 q q0. assumption. assumption.
  econstructor. reflexivity.  split. 
  apply q_subseq_eq.
  apply q_combin_eq with s0
  e0 s1 e1 q1 rho1. assumption. assumption.
  rewrite map2_r_refl.
  apply d_subseq_eq.
  apply d_combin_eq with s0 e0 s1 e1 x mu1; assumption.

  inversion_clear H1. simpl. MC.elim_comp. 
  econstructor. reflexivity.  split. 
  inversion H0; subst. inversion H; subst.
  inversion H7; subst.
  repeat rewrite kron_plus_distr_l.
  repeat rewrite kron_plus_distr_r. unfold q_subseq.
  right.  
   admit. admit. admit. admit.
   rewrite map2_r_refl. 
   apply d_subseq_eq.
   apply d_combin_eq with s0 e0 s1 e1 x mu1; assumption.

  inversion_clear H1. simpl. MC.elim_comp.
  econstructor. reflexivity.  split.  apply q_subseq_eq.
  apply q_combin_eq with s0
  e0 s1 e1 q1 rho1. assumption. assumption.
  apply IHx with mu1 q q0. 
  assumption. assumption.
  apply H2.
Admitted.


Lemma rule_for:  forall s e s0 e0 s1 e1
(x mu1:list(cstate * qstate s0 e0))(x0 mu2:list(cstate * qstate s1 e1))
(mu3 mu'1 mu:list(cstate * qstate s e)),
d_combin mu1 mu2 mu3->
d_combin x x0 mu'1->
(d_combin (StateMap.Raw.map2 option_app
     mu1 x)
(StateMap.Raw.map2 option_app
   mu2 x0)mu)
-> d_subseq (StateMap.Raw.map2 option_app
  mu3 mu'1) mu.
Proof. induction x; induction mu1; intros.
--inversion H0; subst.  clear H0.
  inversion H; subst. clear H.
  simpl in H1. 
  simpl StateMap.Raw.map2. inversion_clear H1.
   econstructor. 
 { inversion H0; subst.  clear H0.
 inversion H; subst. clear H.
  simpl in H1. repeat rewrite map2_l_refl in H1.
  inversion H1; subst. clear H1.
  simpl. rewrite map2_l_refl. intuition. apply q_subseq_eq.
  apply q_combin_eq with s0 e0 s1 e1 rho0 rho1.
  intuition. intuition. apply d_subseq_eq.
  apply d_combin_eq with s0 e0 s1 e1 mu1 mu4.
  assumption. assumption. }
  { inversion H0; subst.  clear H0.
  inversion H; subst. clear H.
   simpl in H1. repeat rewrite map2_r_refl in H1.
   inversion H1; subst. clear H1.
   simpl. rewrite map2_r_refl. intuition. apply q_subseq_eq.
   apply q_combin_eq with s0 e0 s1 e1 rho0 rho1.
   intuition. intuition. apply d_subseq_eq.
   apply d_combin_eq with s0 e0 s1 e1 x mu1.
   assumption. assumption. }
   {destruct a0; destruct a. inversion H0; subst. clear H0.
   inversion H; subst. clear H.  simpl in H1.
  destruct (Cstate_as_OT.compare c c0);
  repeat rewrite map2_r_refl in H1;
  inversion_clear H1;
  simpl; MC.elim_comp;
  econstructor; try reflexivity. 
  split. apply q_subseq_eq.
  apply q_combin_eq with s0
  e0 s1 e1 q rho2. assumption. assumption.
  apply IHmu1 with ((c0, rho1) :: mu4) mu5.
  assumption.  econstructor.
  assumption. assumption.
  assumption.


  
  split.  inversion H7; subst.
  inversion H6; subst. inversion H; subst.
  repeat rewrite kron_plus_distr_l.
  repeat rewrite kron_plus_distr_r.
  unfold q_subseq.
   admit. admit. admit. admit.
   apply IHx with mu1 mu4 mu5.
   assumption. assumption.
   assumption.

   split. apply q_subseq_eq.
  apply q_combin_eq with s0
  e0 s1 e1 q0 rho1. assumption. assumption.
  repeat rewrite app_fix in *.
  apply IHx with  ((c,q)::mu1) mu4 ((c,rho2)::mu5) .
  econstructor. assumption.
  assumption. 
  assumption. assumption. }
Admitted.


Lemma q_subseq_trans:forall s e  (q0 q1 q2: qstate s e),
 q_subseq q0 q1->
 q_subseq q1 q2->
 q_subseq q0 q2. 
Proof. intros. unfold q_subseq in *.
       destruct H; destruct H0. 
       left. subst. reflexivity.
       destruct H0. 
       right. exists x. subst. reflexivity.
       destruct H.
       right. exists x. subst. reflexivity.
       destruct H. destruct H0.
       right.
       exists (x .+ x0).
       subst. rewrite Mplus_assoc.
       reflexivity.
Qed.

Lemma d_subseq_trans:forall s e (mu0 mu1 mu2:list (state s e)),
 d_subseq mu0 mu1->
 d_subseq mu1 mu2->
 d_subseq mu0 mu2. 
Proof.  induction mu0;destruct mu1; destruct mu2;
       intros.
      {assumption. }
      {destruct s0; intuition. }
      {destruct s0; intuition. }
      {destruct s0; intuition. }
      {destruct a; intuition. }
      {destruct s0; intuition. }
      {destruct s0; intuition. }
      {destruct a. destruct s0. destruct s1. simpl in *.
       split. destruct H. rewrite H. intuition.
       split. apply q_subseq_trans with  q0.
       intuition. intuition.
       apply IHmu0 with mu1; intuition.
        }
Qed.


Lemma d_subseq_map2: forall s e
(mu1 mu2 mu1' mu2':list (cstate *qstate s e)),
d_subseq mu1 mu1'-> 
d_subseq mu2 mu2'->
d_subseq (StateMap.Raw.map2 option_app mu1 mu2)
  (StateMap.Raw.map2 option_app mu1' mu2').
Proof. induction mu1; induction mu2; intros;
       destruct mu1'; destruct mu2';
       try destruct p; try destruct a; 
       try destruct a0; try intuition.
       simpl in *.
       repeat rewrite map2_r_refl.
       intuition.
       simpl in *. 
       repeat rewrite map2_l_refl.
       intuition.
       destruct p0. 
       simpl in *. destruct H. destruct H0.
       subst. 
       destruct (Cstate_as_OT.compare c c2).
       simpl. split. intuition.
       split. intuition.
      apply IHmu1. intuition. 
      simpl. intuition. 
      
     
      econstructor. reflexivity.
      split.  admit. 
      apply IHmu1. intuition.
      intuition. 
     
      simpl. 
      repeat rewrite app_fix.
      split. reflexivity.
      split. intuition.
      apply IHmu2.
      split. reflexivity.
      intuition. intuition.
Admitted.




(* Lemma d_q_eq_map2: forall s e
(mu1 mu2 mu1' mu2':list (cstate *qstate s e)),
dstate_qstate_eq mu1 mu1'->
dstate_qstate_eq mu2 mu2'->
dstate_qstate_eq (StateMap.Raw.map2 option_app mu1 mu2)
  (StateMap.Raw.map2 option_app mu1' mu2').
Proof.   induction mu1; induction mu2; intros;
destruct mu1'; destruct mu2';
try destruct p; try destruct a; 
try destruct a0; try intuition.
simpl in *.
repeat rewrite map2_r_refl.
intuition.
simpl in *. 
repeat rewrite map2_l_refl.
intuition.
destruct p0. 
simpl in *. destruct H. destruct H0.
subst. 
destruct (Cstate_as_OT.compare c c2).
simpl. split. intuition.
apply IHmu1. intuition.
simpl. intuition.

simpl. split. intuition.
apply IHmu1. intuition. intuition.

split. reflexivity.
repeat rewrite app_fix in *.
apply IHmu2.
split. reflexivity.
intuition. intuition.
Qed.  *)
Local Open Scope nat_scope.
Lemma QInit_fun_sub{s' e':nat}: forall s e (q q': qstate s' e'), 
s'<=s/\s<=e/\e<=e'->
q_subseq q q'->
@q_subseq s' e' (QInit_fun s e q) (QInit_fun s e q').
Proof. intros. inversion_clear H0. subst.  
       apply q_subseq_eq. reflexivity.
      destruct H1. subst.
      rewrite <-QInit_fun_plus.
      unfold q_subseq. right.
      exists (QInit_fun s e x).
      reflexivity. intuition.
Qed.


Lemma QUnit_Ctrl_fun_sub{s' e':nat}: forall s0 e0 s1 e1 (q q0: qstate s' e') (U: nat-> Square (2^(e1-s1))), 
s'<=s0/\s0<=e0 /\ e0<=s1/\s1<=e1/\e1<=e'->
q_subseq q0 q->
q_subseq (QUnit_Ctrl_fun s0 e0 s1 e1 U q0) 
(QUnit_Ctrl_fun s0  e0 s1 e1 U q).
Proof. intros. inversion_clear H0. subst. 
apply q_subseq_eq. reflexivity.
destruct H1. subst.
rewrite <-QUnit_Ctrl_fun_plus.
unfold q_subseq. right.
exists (QUnit_Ctrl_fun s0 e0 s1 e1 U x).
reflexivity. intuition.
Qed.


Lemma QUnit_One_fun_sub{s' e':nat}: forall s e U (q q': qstate s' e'), 
s'<=s/\s<=e/\e<=e'->
q_subseq q q'->
@q_subseq s' e' (QUnit_One_fun s e U q) (QUnit_One_fun s e U q').
Proof. intros. inversion_clear H0. subst. 
       apply q_subseq_eq. reflexivity.
      destruct H1. subst.
      rewrite <-QUnit_One_fun_plus.
      unfold q_subseq. right.
      exists (QUnit_One_fun s e U x).
      reflexivity. intuition.
Qed.

Lemma QMeas_fun_sub{s' e':nat}: forall s e i (q q': qstate s' e'), 
s'<=s/\s<=e/\e<=e'->
q_subseq q q'->
@q_subseq s' e' (QMeas_fun s e i q) (QMeas_fun s e i q').
Proof. intros. inversion_clear H0. subst. 
       apply q_subseq_eq. reflexivity.
      destruct H1. subst.
      rewrite <-QMeas_fun_plus.
      unfold q_subseq. right.
      exists (QMeas_fun s e i x).
      reflexivity. intuition.
Qed.

Lemma rule_two: forall c s0 e0 s1 e1 
(mu1:list (cstate *qstate s0 e0))
(mu2:list (cstate *qstate s1 e1))
s e
(mu0 mu mu':list (cstate *qstate s e)) F ,
ceval_single c mu mu'-> 
d_combin mu1 mu2 mu0  ->
d_subseq mu mu0 ->
NSet.inter (fst (Free_state F)) (fst (MVar c)) = NSet.empty ->
NSet.Subset (snd (MVar c)) (Qsys_to_Set s0 e0) ->
State_eval_dstate F mu2 ->
(exists (mu1' :list (cstate *qstate s0 e0))
( mu2': list (cstate *qstate s1 e1))
( mu'': list (cstate *qstate s e)), and 
(ceval_single c mu1 mu1')
(State_eval_dstate F mu2' /\
d_combin mu1' mu2' mu''  /\
 d_subseq mu' mu'')).
Proof. induction c. 
-- induction mu1; intros. 
   {inversion  H0; subst. 
   exists nil. exists nil. exists nil. 
   split. apply E_nil. destruct H4. }
    { destruct a. 
    inversion H0; subst. clear H0.
    assert(ceval_single <{ skip }> (mu'0) (mu'0)).
    apply ceval_skip. 
    assert(exists  (mu1' : list (cstate * qstate s0 e0)) 
    (mu2' : list (cstate * qstate s1 e1)) 
    (mu'' :  list (cstate * qstate s e)),
    and (ceval_single <{ skip }> mu1 mu1') 
    (State_eval_dstate F mu2' /\
    d_combin mu1' mu2' mu'' /\ d_subseq mu'0 mu'')).
    apply (IHmu1 _ _ _ _ _ _ _ H0 H11). apply d_subseq_eq.
    reflexivity. assumption. assumption. admit.
    destruct H5. destruct H5. destruct H5. 
    destruct H5. apply ceval_skip_1 in H5.
    subst.
    exists (((c, q) :: x)). exists (((c, rho1) :: x0)).
    exists ((c, rho')::x1).
    split.  apply E_Skip. split. simpl.
    econstructor. inversion_clear H4. assumption.
    admit.
    split. econstructor.  intuition.  intuition.
    apply ceval_skip_1 in H. rewrite <-H. 
    apply d_subseq_trans with ((c, rho') :: mu'0).
    assumption. simpl. split. reflexivity.
    split. apply q_subseq_eq. reflexivity.
    intuition.
     }
-- admit.
--induction mu1; intros.
  {inversion  H0; subst. 
   exists nil. exists nil. exists nil.
   split. econstructor. destruct H4. }
   {destruct a0. inversion H0; subst. clear H0.
    destruct mu. simpl in H1. intuition.
    destruct p. inversion H; subst. simpl in H1.
    destruct H1. subst. 
  assert(exists
  (mu1' : list (cstate * qstate s0 e0)) 
  (mu2' : list (cstate * qstate s1 e1)) 
  (mu'' : list  (cstate * qstate s e)),
  (and (ceval_single <{ i := a }> mu1 mu1') 
   (State_eval_dstate F mu2'/\
   d_combin mu1' mu2' mu'' /\ d_subseq mu'1 mu''))).
  apply (IHmu1 _ _ _ _ _ _ _ H12 H11). intuition.
  assumption. assumption. admit. 
  destruct H0. destruct H0. destruct H0.
  exists (StateMap.Raw.map2 option_app 
  [(c_update i (aeval (c,q) a) c, q)] x).
  exists (StateMap.Raw.map2 option_app 
  [(c_update i (aeval (c,rho1) a) c,rho1)] x0).
  assert(exists (mu'': list (cstate *qstate s e)),
  d_combin
  (StateMap.Raw.map2 option_app
     [(c_update i (aeval (c, q) a) c, q)] x)
  (StateMap.Raw.map2 option_app
     [(c_update i (aeval (c, q) a) c, rho1)] x0) mu'').
  apply rule_6 with  (rho') x1. assumption. intuition. 
   destruct H5. exists x2. 
  split. apply E_Asgn. intuition.
  split. admit.
  split. rewrite (state_eq_aexp (c, rho1) (c,q)).
  intuition. reflexivity. 
  apply d_subseq_trans with 
  ((StateMap.Raw.map2 option_app
  [(c_update i (aeval (c, q) a) c, rho')] x1)).
  apply d_subseq_map2. simpl.
  rewrite (state_eq_aexp (c, q0) (c, q)).
  intuition. reflexivity. intuition.  
  apply rule_three with s0 e0 s1 e1 x x0 q rho1.
  assumption. intuition. assumption. } 
 --admit.
 --intros. destruct mu1; intros.
   { inversion  H0; subst.
     exists nil. exists nil. exists nil. 
     split; econstructor. destruct H4. 
     destruct H4. }
   { inversion H0; subst. clear H0.
     destruct mu. intuition.
     destruct p.   inversion H; subst.
      simpl in H1. destruct H1. destruct H0.
assert(exists
(mu1' : list (cstate * qstate s0 e0)) 
(mu2' : list (cstate * qstate s1 e1))
(mu'' : list (cstate * qstate s e)),
(and (ceval_single c1 (((c, rho0) :: mu1)) mu1') 
 (State_eval_dstate F mu2'  /\
 d_combin mu1' mu2' mu''  /\ d_subseq mu2 mu''))).
apply IHc1 with ((c, rho1) :: mu4) ((c, rho') :: mu'0) (((c, q) :: mu)) .
intuition. econstructor.  intuition.
intuition. simpl. split. reflexivity. apply H1.
admit.
admit. assumption.  
destruct H0. destruct H0. destruct H0.
assert( exists
(mu1' : list (cstate * qstate s0 e0)) 
(mu2' : list (cstate * qstate s1 e1))
(mu'' : list (cstate * qstate s e)),
(and (ceval_single c2 x mu1') 
 (State_eval_dstate F mu2' /\
 d_combin mu1' mu2' mu'' /\ d_subseq mu' mu'' ))).
 apply IHc2 with x0 x1 mu2. intuition. intuition.
 intuition. admit. admit. intuition.
 destruct H5. destruct H5. destruct H5.
 exists x2. exists x3. exists x4. split.
  apply E_Seq with x. 
  intuition. intuition. intuition. }

--induction mu1; intros.
{inversion  H0; subst. 
 exists nil. exists nil. exists nil.
 split. econstructor. destruct H4.
  } 
 { destruct a. inversion H0; subst. clear H0.
  destruct mu. simpl in H1. intuition.
  destruct p. inversion H; subst; simpl in H1.
  destruct H1; subst.
   {assert(exists
  (mu1' : list (cstate * qstate s0 e0)) 
  (mu2' : list (cstate * qstate s1 e1)) 
  (mu''0 : list  (cstate * qstate s e)),
  (and (ceval_single <{ if b then c1 else c2 end }> mu1 mu1') 
   (State_eval_dstate F mu2' /\
   d_combin mu1' mu2' mu''0 /\ d_subseq mu'' mu''0))).
  apply (IHmu1 _ _ _ _ _ _ _ H14 H11). intuition.
   assumption. assumption. admit.
  destruct H0. destruct H0. destruct H0.
  assert(exists
  (mu1' : list (cstate * qstate s0 e0)) 
  (mu2' : list (cstate * qstate s1 e1)) 
  (mu''0 : list  (cstate * qstate s e)),
  (and (ceval_single c1 [(c,q)] mu1') 
   (State_eval_dstate F mu2' /\
   d_combin mu1' mu2' mu''0 /\ d_subseq mu'1 mu''0))).
   apply IHc1 with [(c, rho1)] [(c,rho')] [(c,q0)]. intuition.
   econstructor. intuition. econstructor.
   simpl. intuition. admit. admit. simpl.
   econstructor. inversion_clear H4. assumption.
   econstructor.
   destruct H5. destruct H5. destruct H5. 
  exists (StateMap.Raw.map2 option_app 
  x2 x).
  exists (StateMap.Raw.map2 option_app 
  x3 x0).
  assert(exists (mu'': list (cstate *qstate s e)),
  d_combin (StateMap.Raw.map2 option_app x2 x)
  (StateMap.Raw.map2 option_app x3 x0) mu'').
  apply rule_7 with x1 x4. intuition. intuition.
   destruct H6. exists x5. 
   split. apply E_IF_true.
  rewrite (state_eq_bexp _ (c, q0)). intuition.
  reflexivity. intuition.
   intuition.
   split. admit.
   split. intuition. 
  apply d_subseq_trans with 
  ((StateMap.Raw.map2 option_app x4 x1)).
  apply d_subseq_map2. intuition. intuition. 
  apply rule_for with s0 e0 s1 e1 x x2 x0 x3.
  intuition. intuition. assumption. 
 }
 { admit. }
}
--admit.
--induction mu1; intros.
{inversion  H0; subst. 
 exists nil. exists nil. exists nil.
 split. econstructor. destruct H4. }
 {destruct a. inversion H0; subst. clear H0.
  destruct mu. simpl in H1. intuition.
  destruct p. inversion H; subst. simpl in H1. 
  destruct H1; subst.
assert(exists
(mu1' : list (cstate * qstate s0 e0)) 
(mu2' : list (cstate * qstate s1 e1)) 
(mu'' : list  (cstate * qstate s2 e2)),
(and (ceval_single <{ (s e) :Q= 0 }> mu1 mu1') 
 (State_eval_dstate F mu2' /\
 d_combin mu1' mu2' mu'' /\ d_subseq mu'1 mu''))).
apply (IHmu1 _ _ _ _ _ _ _ H13 H11). intuition.
assumption. assumption. admit. 
destruct H0. destruct H0. destruct H0.
exists (StateMap.Raw.map2 option_app 
[(c,(QInit_fun s e q))] x).
exists (StateMap.Raw.map2 option_app 
[(c,rho1)] x0).
assert(exists (mu'': list (cstate *qstate s2 e2)),
d_combin
(StateMap.Raw.map2 option_app
[(c,(QInit_fun s e q))] x)
(StateMap.Raw.map2 option_app
[(c,rho1)]  x0) mu'').
inversion H10; subst.
apply (rule_6 _ s2 e2 s2 s1 s1 e2 _ _ 
 (@kron (2^(s1-s2)) (2^(s1-s2)) (2^(e2-s1))
 (2^(e2-s1)) (QInit_fun s e q) rho1)_ _ x1).
apply combin_l; econstructor. intuition. 
apply (rule_6 _ s2 e2 s0 e2 s2 s0 _ _ 
 (@kron (2^(s0-s2))
 (2^(s0-s2)) (2^(e2-s0)) (2^(e2-s0))  rho1 (QInit_fun s e q) )_ _ x1).
apply combin_r; econstructor. intuition.
destruct H5. exists x2. 
split. apply E_Qinit. 
simpl in H2. admit.  intuition.
split. apply d_seman_app_aux. admit. admit.
simpl. econstructor. inversion_clear H4. assumption.
econstructor. intuition. 
split. 
intuition.  
inversion H10; subst.
apply d_subseq_trans with 
((StateMap.Raw.map2 option_app
[(c,(@kron (2^(s1-s2)) (2^(s1-s2)) (2^(e2-s1))
(2^(e2-s1)) (QInit_fun s e q) rho1) )] x1)).
apply d_subseq_map2.
simpl. split. reflexivity. split.
apply q_subseq_trans with ((@QInit_fun s2 e2 s e 
(@kron (2^(s1-s2)) (2^(s1-s2)) (2^(e2-s1))
(2^(e2-s1)) q rho1))).
apply QInit_fun_sub. intuition. intuition.
apply q_subseq_eq. 
apply QInit_fun_kron. 
admit. admit. intuition. intuition.
apply (rule_three s2 e2 s2 s1 s1 e2 x x0 (QInit_fun s e q) rho1).
econstructor; reflexivity.  intuition. assumption. 
apply d_subseq_trans with 
((StateMap.Raw.map2 option_app
[(c,(@kron (2^(s0-s2))
(2^(s0-s2)) (2^(e2-s0)) (2^(e2-s0))  rho1 (QInit_fun s e q) ) )] x1)).
apply d_subseq_map2.
simpl. split. reflexivity. split.
apply q_subseq_trans with ((@QInit_fun s2 e2 s e 
(@kron (2^(s0-s2))
 (2^(s0-s2)) (2^(e2-s0)) (2^(e2-s0))  rho1 q ))).
apply QInit_fun_sub. intuition. intuition.
apply q_subseq_eq. admit. 
 intuition. intuition.
apply (rule_three s2 e2 s0 e2 s2 s0 x x0 (QInit_fun s e q) rho1).
econstructor; reflexivity.  intuition. assumption. 
}

--induction mu1; intros.
{inversion  H0; subst. 
 exists nil. exists nil. exists nil.
 split. econstructor. destruct H4. }
 {destruct a. inversion H0; subst. clear H0.
  destruct mu. simpl in H1. intuition.
  destruct p. inversion H; subst. simpl in H1.
  destruct H1; subst.
  apply inj_pair2_eq_dec in H6.
  apply inj_pair2_eq_dec in H6.
  subst. 
assert(exists
(mu1' : list (cstate * qstate s0 e0)) 
(mu2' : list (cstate * qstate s1 e1)) 
(mu'' : list  (cstate * qstate s2 e2)),
(and (ceval_single (QUnit_One s e U) mu1 mu1') 
 (State_eval_dstate F mu2' /\
 d_combin mu1' mu2' mu'' /\ d_subseq mu'1 mu''))).
apply (IHmu1 _ _ _ _ _ _ _ H15 H11). intuition.
assumption. assumption.  admit.
destruct H0. destruct H0. destruct H0.
exists (StateMap.Raw.map2 option_app 
[(c,(QUnit_One_fun s e U q))] x).
exists (StateMap.Raw.map2 option_app 
[(c,rho1)] x0).
assert(exists (mu'': list (cstate *qstate s2 e2)),
d_combin
(StateMap.Raw.map2 option_app
[(c,(QUnit_One_fun s e U q))] x)
(StateMap.Raw.map2 option_app
[(c,rho1)]  x0) mu'').
apply (rule_6 _ s2 e2 s0 e0 s1 e1 _ _ 
 (@kron (2^(e0-s0)) (2^(e0-s0)) (2^(e1-s1))
 (2^(e1-s1)) (QUnit_One_fun s e U q) rho1)_ _ x1).
  admit. intuition. 
 destruct H5. exists x2. 
split. apply E_Qunit_One.  
simpl in H2. admit.  intuition.
intuition.
split. admit. 
split. 
intuition. 
apply d_subseq_trans with 
((StateMap.Raw.map2 option_app
[(c,(@kron (2^(e0-s0)) (2^(e0-s0)) (2^(e1-s1))
(2^(e1-s1)) (QUnit_One_fun s e U q) rho1) )] x1)).
apply d_subseq_map2.
simpl. split. reflexivity. split. 
admit. intuition. intuition. 
apply (rule_three s2 e2 s0 e0 s1 e1 x x0 (QUnit_One_fun s e U q) rho1).
admit. intuition. assumption. 
apply Nat.eq_dec. apply Nat.eq_dec. }

--induction mu1; intros.
{inversion  H0; subst. 
 exists nil. exists nil. exists nil.
 split. econstructor. destruct H4. }
 {destruct a. inversion H0; subst. clear H0.
  destruct mu. simpl in H1. intuition.
  destruct p. inversion H; subst. simpl in H1.
  destruct H1; subst.
  apply inj_pair2_eq_dec in H9.
  apply inj_pair2_eq_dec in H9.
  subst. 
assert(exists
(mu1' : list (cstate * qstate s2 e2)) 
(mu2' : list (cstate * qstate s3 e3)) 
(mu'' : list  (cstate * qstate s e)),
(and (ceval_single (QUnit_Ctrl s0 e0 s1 e1 U) mu1 mu1') 
 (State_eval_dstate F mu2' /\
 d_combin mu1' mu2' mu'' /\ d_subseq mu'1 mu''))).
apply (IHmu1 _ _ _ _ _ _ _ H17 H11). intuition.
assumption. assumption. admit. 
destruct H0. destruct H0. destruct H0.
exists (StateMap.Raw.map2 option_app 
[(c,(QUnit_Ctrl_fun s0 e0 s1 e1 U q))] x).
exists (StateMap.Raw.map2 option_app 
[(c,rho1)] x0).
assert(exists (mu'': list (cstate *qstate s e)),
d_combin
(StateMap.Raw.map2 option_app
[(c,(QUnit_Ctrl_fun s0 e0 s1 e1 U q))] x)
(StateMap.Raw.map2 option_app
[(c,rho1)]  x0) mu'').
apply (rule_6 _ s e s2 e2 s3 e3 _ _ 
 (@kron (2^(e2-s2)) (2^(e2-s2)) (2^(e3-s3))
 (2^(e3-s3)) (QUnit_Ctrl_fun s0 e0 s1 e1 U q)
  rho1)_ _ x1).
  admit. intuition. 
 destruct H5. exists x2. 
split. apply E_QUnit_Ctrl.  
simpl in H2. admit.  intuition.
intuition.
split. admit.
split. 
intuition. 
apply d_subseq_trans with 
((StateMap.Raw.map2 option_app
[(c,(@kron (2^(e2-s2)) (2^(e2-s2)) (2^(e3-s3))
(2^(e3-s3)) (QUnit_Ctrl_fun s0 e0 s1 e1 U q) rho1) )] x1)).
apply d_subseq_map2.
simpl. split. reflexivity.
split.
admit. intuition. intuition. 
apply (rule_three s e s2 e2 s3 e3 x x0 (QUnit_Ctrl_fun s0 e0 s1 e1 U q) rho1).
admit. intuition. assumption.
apply Nat.eq_dec. apply Nat.eq_dec. }

--induction mu1; intros.
{inversion  H0; subst. 
 exists nil. exists nil. exists nil.
 split. econstructor. destruct H4. }
 {destruct a. inversion H0; subst. clear H0.
  destruct mu. simpl in H1. intuition.
  destruct p. inversion H; subst. simpl in H1.
  destruct H1; subst.
assert(exists
(mu1' : list (cstate * qstate s0 e0)) 
(mu2' : list (cstate * qstate s1 e1)) 
(mu'' : list  (cstate * qstate s2 e2)),
(and (ceval_single (QMeas i s e ) mu1 mu1') 
 (State_eval_dstate F mu2' /\
 d_combin mu1' mu2' mu'' /\ d_subseq mu'1 mu''))).
apply (IHmu1 _ _ _ _ _ _ _ H14 H11). intuition.
assumption. assumption. admit. 
destruct H0. destruct H0. destruct H0.
exists (StateMap.Raw.map2 option_app 
(big_app (fun j : nat => [(c_update i j c, QMeas_fun s e j q)])
          (2 ^ (e - s))) x).
exists (StateMap.Raw.map2 option_app 
(big_app (fun j : nat => [(c_update i j c, rho1)])
          (2 ^ (e - s))) x0).
assert(exists (mu'': list (cstate *qstate s2 e2)),
d_combin
(StateMap.Raw.map2 option_app
(big_app (fun j : nat => [(c_update i j c, QMeas_fun s e j q)])
          (2 ^ (e - s))) x)
(StateMap.Raw.map2 option_app
(big_app (fun j : nat => [(c_update i j c, rho1)])
(2 ^ (e - s))) x0) mu'').
apply (rule_7 s2 e2 s0 e0 s1 e1 _ _  _ _
 x1 (big_app
(fun j : nat =>
 [(c_update i j c, @kron (2^(e0-s0)) (2^(e0-s0)) (2^(e1-s1))
 (2^(e1-s1)) (QMeas_fun s e j q) rho1 )])
(2 ^ (e - s))) ). 
  admit. intuition. 
 destruct H5. exists x2. 
split. apply E_Meas.   
simpl in H2. admit.  intuition.
split. admit.
split. 
intuition. 
apply d_subseq_trans with 
((StateMap.Raw.map2 option_app
(big_app
(fun j : nat =>
 [(c_update i j c, @kron (2^(e0-s0)) (2^(e0-s0)) (2^(e1-s1))
 (2^(e1-s1)) (QMeas_fun s e j q) rho1 )])
(2 ^ (e - s))) x1)).
apply d_subseq_map2. 
admit. intuition. 
apply (rule_for s2 e2 s0 e0 s1 e1 x (big_app (fun j : nat => [(c_update i j c, QMeas_fun s e j q)])
(2 ^ (e - s))) x0 (big_app (fun j : nat => [(c_update i j c, rho1)]) (2 ^ (e - s)))).
admit. intuition. assumption. }
Admitted.




(* Lemma QExp_eval_sub: forall (qs: QExp) s e c (q q': qstate s e) ,
q_subseq q q'->
State_eval qs (c, q')->
State_eval qs (c, q).
Proof. Admitted.



Lemma QExp_eval_sub: forall F s e c (q q': qstate s e) ,
q_subseq q q'->
State_eval F (c, q')->
State_eval F (c, q).
Proof. induction F; intros.
       apply state_eq_Pure with (c,q').
       reflexivity. intuition.
       inversion_clear H.
       subst. intuition.
       destruct H1.  subst.
       induction qs.
       simpl in H0. 
       simpl.  
       split. intuition.
       split. intuition.
       split. intuition.
       rewrite <-PMtrace_scale in *.
       rewrite PMtrace_plus in *.
       rewrite Mscale_plus_distr_r in *.
       destruct H0. destruct H0.
       destruct H1. 
       admit. lia. lia.
       

      



Lemma State_eval_sub: forall s e (mu mu': list (state s e)) F,
d_subseq mu mu'->
State_eval_dstate F mu'->
State_eval_dstate F mu.
Proof. induction mu.  intros. destruct mu'.
       simpl in H0. destruct H0.
       simpl in H. destruct H.
       intros. destruct mu'.
       destruct a.
       simpl in H. destruct H.
       destruct mu; destruct mu';
       destruct a; destruct s0.
       simpl in H. 
       simpl. econstructor.
       inversion_clear H0.
       admit. 
       
       econstructor.

       simpl in H. intuition.
       destruct s1.
       simpl in H. intuition.
       simpl. econstructor.
       admit.
       apply IHmu with (s2 :: mu').
       destruct s1. destruct s2.
       simpl in H. econstructor. intuition.
       split. intuition. intuition.
       inversion_clear H0. intuition.   
 Admitted. *)
Import Par_trace.

Lemma QExp_free_eval{s e:nat}:forall (qs: QExp) (st: state s e),
s<=(fst (Free_QExp' qs)) /\(fst (Free_QExp' qs)) <=
(snd (Free_QExp' qs))/\ (snd (Free_QExp' qs))<=e->
@WF_Matrix (2^(e-s)) (2^(e-s)) (snd st)->
QExp_eval qs st <-> QExp_eval qs (fst st, (PMpar_trace (snd st) ((fst (Free_QExp' qs))) ((snd (Free_QExp' qs))))).
Proof. induction qs; split; intros. 
      simpl in *. rewrite PMpar_trace_refl.
      split. lia.
      split. lia. split. lia. 
      rewrite <-PMtrace_scale in H1.
      rewrite Ptrace_trace. intuition.
      lia. assumption. lia. apply WF_scale.
      apply WF_PMpar_trace. lia. assumption.
      simpl in *.  rewrite PMpar_trace_refl in H1.
      rewrite Ptrace_trace in H1. 
      rewrite <-PMtrace_scale. 
      split. lia. split. lia. split. lia. 
      intuition. lia. assumption.  lia.
      apply WF_scale.
      apply WF_PMpar_trace. lia. assumption.
      simpl in H1. 
      simpl. split.  intuition.
      split. Admitted.

Lemma State_free_eval{s e:nat}:forall (F: State_formula) (st: state s e),
s<=(fst (Free_State F)) /\
(fst (Free_State F)) <=  (snd (Free_State F))
/\ (snd (Free_State F))<=e->
@WF_Matrix (2^(e-s)) (2^(e-s)) (snd st) ->
State_eval F st <-> 
State_eval F (fst st, (PMpar_trace (snd st) ((fst (Free_State F))) ((snd (Free_State F))))).
Proof. induction F; split; intros. destruct st. 
        eapply state_eq_Pure with (c, q). 
        reflexivity. apply H1.
        destruct st. simpl in *.
        eapply state_eq_Pure with (c, PMpar_trace q 0 0). 
        reflexivity. intuition. destruct st.
        apply (QExp_free_eval _  (c, q)) .
        intuition. intuition. intuition.
        destruct st. simpl in *.
        apply QExp_free_eval. intuition.
        intuition. intuition. 
        simpl in *.
        split. intuition. admit.
        simpl in *.
        split. intuition.
Admitted.


Lemma seman_eq_two{s e:nat}: forall F1 F2  c (q:qstate s e),
Considered_Formula (F1 ⊙ F2) ->
State_eval (F1 ⊙ F2) (c, q) <-> 
 ((s <= fst (Free_State ((F1 ⊙ F2))) /\
 snd (Free_State ((F1 ⊙ F2))) <= e)  /\
exists (q1:qstate ((fst (Free_State F1))) (snd (Free_State F1)))
(q2:qstate ((fst (Free_State F2))) (snd (Free_State F2))),
and (State_eval F1 (c, q1) /\ State_eval F2 (c, q2)) 
(q_combin q1 q2 (@PMpar_trace s e q ((fst (Free_State (((F1 ⊙ F2)))))) ((snd (Free_State (((F1 ⊙ F2))))))))).
Proof. intros. split; intros. 
       split. admit.
       simpl in H0.
Admitted.

Fixpoint d_par_trace{ s e: nat} (mu:list (cstate * qstate s e)) l r :=
  match mu with 
  | nil => nil 
  | (c, q)::mu' =>(c, PMpar_trace q l r):: (d_par_trace mu' l r)
  end.

Lemma seman_eq_three{s e:nat}: forall  (mu: list (cstate * qstate s e)) F1 F2,
Considered_Formula (F1 ⊙ F2) ->
State_eval_dstate (F1 ⊙ F2) mu <-> 
 ((s <= fst (Free_State ((F1 ⊙ F2))) /\
 snd (Free_State ((F1 ⊙ F2))) <= e)  /\
 (exists (mu0:list(cstate * qstate ((fst (Free_State F1))) (snd (Free_State F1)))) 
 (mu1:list(cstate * qstate ((fst (Free_State F2))) (snd (Free_State F2)))), 
 and (d_combin mu0 mu1 (d_par_trace mu ((fst (Free_State (((F1 ⊙ F2)))))) ((snd (Free_State (((F1 ⊙ F2))))))))
 ((State_eval_dstate F1 mu0 /\ State_eval_dstate F2 mu1)))).
Proof. induction mu;  intros; split; intros.
       destruct H0.  
       destruct H0. 
       destruct H1. 
       destruct H1.
       destruct H1. inversion H1; subst.
       destruct H2. destruct H2.
       destruct mu. 
      inversion H0; subst.
      destruct a.
      apply seman_eq_two in H3.
      split. intuition.  
      destruct H3.
      destruct H2. 
      destruct H2. 
      destruct H2. 
      exists [(c,x)]. exists [(c,x0)].
      split. econstructor. intuition.
      econstructor. simpl. intuition. 
      intuition. 
       assert((s <= fst (Free_State (F1 ⊙ F2)) /\
       snd (Free_State (F1 ⊙ F2)) <= e) /\
      (exists
         (mu0 : list
                  (cstate *
                   qstate (fst (Free_State F1))
                     (snd (Free_State F1)))) 
       (mu1 : list
                (cstate *
                 qstate (fst (Free_State F2))
                   (snd (Free_State F2)))),
         (d_combin mu0 mu1 (d_par_trace (p :: mu)
         (fst (Free_State (F1 ⊙ F2)))
         (snd (Free_State (F1 ⊙ F2)))) /\
          State_eval_dstate F1 mu0 /\
          State_eval_dstate F2 mu1)%type)).
      apply IHmu. intuition. inversion_clear H0.
      apply State_eval_dstate_Forall. discriminate.
      intuition.
      split. intuition. 
      destruct H1. destruct H2.
      destruct H2. destruct H2.
      destruct a.
      assert(exists (q1:qstate ((fst (Free_State F1))) (snd (Free_State F1)))
      (q2:qstate ((fst (Free_State F2))) (snd (Free_State F2))),
      and (State_eval F1 (c, q1) /\ State_eval F2 (c, q2)) 
      (q_combin q1 q2 (@PMpar_trace s e q ((fst (Free_State (((F1 ⊙ F2)))))) ((snd (Free_State (((F1 ⊙ F2))))))))).
      apply seman_eq_two. intuition.
      inversion_clear H0. intuition.
      destruct H4. destruct H4.
      exists ((c,x1)::x). exists ((c,x2)::x0).
      split. econstructor.  intuition.
      intuition. 
      split. econstructor. intuition.
      destruct x. econstructor.
      apply H3. econstructor. intuition.
      destruct x0. econstructor. 
      apply H3. 
      destruct H0. destruct H0.
      destruct H1. destruct H1.
      destruct H1.
      destruct mu.   
      destruct a.  simpl d_par_trace in *.
      inversion H1; subst. clear H1.
      econstructor.
      apply seman_eq_two.
      intuition. 
      split. intuition.
      exists rho0. exists rho1.
      destruct H3. inversion_clear H1.
      inversion_clear H3.
      split. intuition. intuition. econstructor.
      destruct a. destruct p.  
      inversion H1; subst. clear H1.
      inversion H10; subst. clear H10.
      econstructor.
      apply seman_eq_two.
      intuition. 
      split. intuition.
      exists rho0. exists rho1.
      destruct H3. inversion_clear H1.
      inversion_clear H3.
      split. intuition. intuition.
      apply IHmu. intuition.
      split. intuition. 
      exists ((c0,rho2)::mu2).
       exists ((c0,rho3)::mu3).
      split. econstructor. intuition.
      intuition. 
      destruct H3. inversion_clear H1.
      inversion_clear H3.
      split. intuition. intuition. 
Qed.




(* Lemma QExp_eval_pure: forall qs s e c (q: qstate s e) ,
QExp_eval qs (c, q)->
exists (p:R) (φ: Vector (2^((snd (Free_QExp' qs))-(fst (Free_QExp' qs))))),
p .* (@PMpar_trace s e q ((fst (Free_QExp' qs))) (((snd (Free_QExp' qs)))) )
= φ  × φ†.
Proof. induction qs; intros. 
       simpl in H. 
       exists ((R1 / Cmod (@trace (2^(e0-s0)) q))%R).
       exists v.
       simpl. 
       rewrite PMtrace_scale.
       unfold outer_product in H.
       intuition.
       simpl QExp_eval in H.  
       destruct H. 
       destruct H0.
       apply IHqs1 in H0.
       apply IHqs2 in H1.
       destruct H0.
       destruct H0.
       destruct H1.
       destruct H1.
Admitted. *)


Lemma QExp_eval_sub: forall (qs: QExp) s e c (q q': qstate s e) ,
q_subseq q q'->
State_eval qs (c, q')->
State_eval qs (c, q).
Proof. induction qs; intros.
      inversion_clear H. subst. intuition.
      destruct H1. subst.
      simpl in *.  
      split. intuition.
      split. intuition.
      split. intuition.
      rewrite <-PMtrace_scale in *.
      rewrite PMtrace_plus in *.
      rewrite Mscale_plus_distr_r in *.
      destruct H0. destruct H0.
      destruct H1.  
      admit. 
      simpl in *.
      split. intuition.
      split. apply IHqs1 with (q').
     intuition. intuition.
     apply IHqs2 with q'.
     intuition. intuition.
Admitted.

Lemma State_eval_sub: forall F s e c (q q': qstate s e) ,
q_subseq q q'->
State_eval F (c, q')->
State_eval F (c, q).
Proof. induction F; intros.
       apply state_eq_Pure with (c,q').
       reflexivity. intuition.
       apply QExp_eval_sub with q'.
       intuition. intuition.
       simpl in *.
       split. intuition.
       split. apply IHF1 with (q').
      intuition. intuition.
      apply IHF2 with q'.
      intuition. intuition.
      simpl in *.
       split. apply IHF1 with (q').
      intuition. intuition.
      apply IHF2 with q'.
      intuition. intuition.
Qed.



Lemma State_eval_sub': forall s e (mu mu': list (state s e)) F,
d_subseq mu mu'->
State_eval_dstate F mu'->
State_eval_dstate F mu.
Proof.
induction mu.  intros. destruct mu'.
       simpl in H0. destruct H0.
       simpl in H. destruct H.
       intros. destruct mu'.
       destruct a.
       simpl in H. destruct H.
       destruct mu; destruct mu';
       destruct a; destruct s0.
       simpl in H. 
       simpl. econstructor.
       inversion_clear H0.
       apply State_eval_sub with q0.
       intuition. destruct H. subst.
       intuition. 
       
       econstructor.

       simpl in H. intuition.
       destruct s1.
       simpl in H. intuition.
       simpl. econstructor.
       destruct H. subst.
       apply State_eval_sub with q0.
       intuition. 
       inversion_clear H0. intuition.
       apply IHmu with (s2 :: mu').
       destruct s1. destruct s2.
       simpl in H. econstructor. intuition.
       split. intuition. intuition.
       inversion_clear H0. intuition.
Qed.

(* Lemma State_eval_combin: forall s e (mu:list(cstate * qstate s e)) (F1 F2:State_formula),
(exists s0 e0 s1 e1 (mu0:list(cstate * qstate s0 e0)) (mu1:list(cstate * qstate s1 e1)), 
and (d_combin mu0 mu1 mu ) 
((State_eval_dstate F1 mu0 /\ State_eval_dstate F2 mu1)))
-> State_eval_dstate (F1 ⊙ F2) mu.
Proof. 
induction mu; intros. destruct H. destruct H.
destruct H. destruct H. destruct H.
destruct H. destruct H. inversion H; subst.
destruct H0. destruct H0.

simpl. 
econstructor.

Admitted. *)


Theorem rule_qframe_aux: forall (c : com) (F1 F2 F3 : State_formula)
(s e : nat) ( mu mu' :list (cstate *qstate s e)),
Considered_Formula ((F1 ⊙ F3))->
Considered_Formula ((F2 ⊙ F3))->
Sorted (StateMap.Raw.PX.ltk (elt:=qstate s e)) mu->
WF_dstate_aux mu ->
(forall (s e : nat) (mu mu' : list (cstate *qstate s e)),
 ceval_single c mu mu' -> State_eval_dstate  F1 mu -> State_eval_dstate  F2 mu')->
NSet.inter (fst (Free_state F3)) (fst (MVar c)) = NSet.empty ->
NSet.Subset (snd (MVar c)) (snd (Free_state F1)) ->
ceval_single c mu mu' ->
State_eval_dstate (F1 ⊙ F3) mu ->
State_eval_dstate (F2 ⊙ F3) mu'.
Proof.  induction mu; intros mu' Hc1 Hc2 Hs Hw; intros.
         simpl in *. destruct H3.
       inversion_clear H3. destruct mu.
       destruct a. 
       apply (ceval_4  c _ _ _ mu') in Hs.
       destruct Hs. destruct H3. destruct H3.
       destruct H6. inversion H6; subst. 
       rewrite map2_nil_r.
       (* rewrite State_free_eval in H4. *)
       rewrite seman_eq_two in H4.
       (* rewrite PMpar_trace_refl in H4. *)
       remember ((PMpar_trace q (fst (Free_State (F1 ⊙ F3)))
       (snd (Free_State (F1 ⊙ F3))))).
       destruct H4. destruct H7. destruct H7. 
       remember (d_par_trace x (fst (Free_State (F1 ⊙ F3)))
       (snd (Free_State (F1 ⊙ F3)))).
       assert(exists
       (mu1' : list (cstate * qstate (fst (Free_State F1))
       (snd (Free_State F1)))) 
     (mu2' : list (cstate * qstate (fst (Free_State F3))
     (snd (Free_State F3)))) 
     (mu'' : list (cstate * qstate (fst (Free_State (F1 ⊙ F3)))
     (snd (Free_State (F1 ⊙ F3))))),
       and (ceval_single c [(c0,x0)] mu1')
       (State_eval_dstate F3 mu2' /\
       d_combin mu1' mu2' mu'' /\ d_subseq l mu'')).
       apply rule_two with [(c0,x1)] [(c0, q0)] [(c0, q0)].
      admit. econstructor. intuition.
      econstructor. apply d_subseq_eq.
      reflexivity. assumption. admit.
      econstructor. intuition. econstructor.
      destruct H8. destruct H8. destruct H8.
      assert(State_eval_dstate (F2 ⊙ F3) l).
      apply State_eval_sub' with x4.
      intuition. apply seman_eq_three.
      intuition. split. admit.  
      exists (fst (Free_State F1)). exists (snd (Free_State F1)).
       exists (fst (Free_State (F3))). exists (snd (Free_State (F3))).
      exists x2. exists x3. split.
      intuition. split. apply H with [(c0,x0)].
      intuition. econstructor. intuition.
      econstructor. intuition. admit.
      intuition. apply WF_PMpar_trace. 
      admit. apply WF_Mixed. inversion_clear Hw.
      apply H7. intuition.  intuition.
      destruct a. destruct p.  
      inversion Hs; subst.
       apply (ceval_4  c _ _ _ mu') in Hs.
       destruct Hs. destruct H3. destruct H3.
       destruct H6. subst.
       rewrite seman_eq_three in H4.
       rewrite seman_eq_two in H4.
       rewrite PMpar_trace_refl in H4.
       remember ((PMpar_trace q (fst (Free_State (F1 ⊙ F3)))
       (snd (Free_State (F1 ⊙ F3))))).
       remember ((d_par_trace ((StateMap.Raw.map2 option_app x x0)) (fst (Free_State (F1 ⊙ F3)))
       (snd (Free_State (F1 ⊙ F3))))).
       destruct H4. destruct H9. destruct H9.

       assert(exists
       (mu1' : list (cstate * qstate (fst (Free_State F1)) (snd (Free_State F1)))) 
     (mu2' : list (cstate * qstate (fst (Free_State F3)) (snd (Free_State F3)))) 
     (mu'' : list (cstate * qstate (fst (Free_State (F1 ⊙ F3)))
     (snd (Free_State (F1 ⊙ F3))))),
       and (ceval_single c [(c0,x1)] mu1' )
       (State_eval_dstate F3 mu2' /\
       d_combin mu1' mu2' mu'' /\ d_subseq l mu'')).
       apply rule_two with [(c0,x2)] [(c0, q1)] [(c0, q1)].
       admit. econstructor. intuition.
      econstructor. apply d_subseq_eq.
      reflexivity. assumption. admit.
      econstructor. intuition. econstructor.
      assert(State_eval_dstate (F2 ⊙ F3) l).
      destruct H10. destruct H10. destruct H10.
      (* apply d_seman_app_aux.
      apply WF_ceval with c ([(c0, q)]).
      apply WF_state_dstate_aux. inversion_clear Hw.
      assumption. intuition. 
      apply WF_ceval with c (((c1, q0) :: mu)).
      inversion_clear Hw. assumption. intuition.  *)
      apply State_eval_sub with x5.
      intuition. apply State_eval_combin.
      exists (fst (Free_State F1)). exists (snd (Free_State F1)). 
      exists (fst (Free_State F3)). exists (snd (Free_State F3)).
      exists x3. exists x4. split.
      intuition. split. apply H with [(c0,x1)].
      intuition. econstructor. intuition.
      econstructor. intuition.
      admit. intuition.
      apply WF_PMpar_trace. admit.
      inversion_clear Hw. apply WF_Mixed.
       apply H9.
      intuition. intuition.
Admitted.


Theorem rule_qframe: forall (F1 F2 F3: State_formula) c,
         Considered_Formula ((F1 ⊙ F3))->
         Considered_Formula ((F2 ⊙ F3))->
         ({{F1}} c {{F2}}) /\ 
          (NSet.inter (fst (Free_state F3)) (fst (MVar c)) =NSet.empty) 
         /\ NSet.Subset (snd (MVar c)) (snd (Free_state F1))
         ->  {{F1 ⊙ F3}} c {{F2 ⊙ F3}}.
Proof. unfold hoare_triple. intros F1 F2 F3 c. intros Hc1 Hc2 H.
       intros s e (mu ,IHmu) (mu', IHmu');
       intros. inversion_clear H0. simpl in H4.
       rewrite sat_Assert_to_State in *.
       inversion_clear H1. econstructor.
       intuition. simpl in H5. apply rule_qframe_aux with c F1 mu.
       intuition. intuition.  intuition. intuition.
       destruct H. admit.
       intuition. intuition. assumption.
       assumption.
Admitted.

              



(* Inductive derivable : Assertion -> com -> Assertion-> Type :=
  | H_Skip : forall D,
      derivable D <{skip}> D
  | H_Asgn : forall D X a,
      derivable (Assn_sub X a D) <{X := a}> D
  | H_Seq : forall P Q R c1 c2,
      derivable Q c2 R -> derivable P c1 Q -> derivable P <{c1;c2}> R
  | H_conseq: forall (P P' Q Q': Assertion) c,
      derivable P' c Q' -> (P ->> P') -> (Q'->> Q) -> derivable P c Q
  | H_conj: forall (F1 F1' F2 F2': State_formula) c,
     derivable F1 c F1' -> derivable F2 c F2' -> derivable (F1 /\ F2) c (F1' /\ F2')
  | H_If: forall (F1 F1' F2 F2': State_formula) (c1 c2:com) (b:bexp) (p:R),
      0<p<1->
     derivable (F1 /\ b) c1 (F1') -> derivable (F2 /\ (BNot b)) c2 (F2')
  -> derivable (APro [(p, (F1 /\ b)) ; ((1 - p), (F2 /\ (BNot b)))])
                <{if b then c1 else c2 end}>
                (APro [(p, F1') ; ((1 - p), F2')])
  |H_while: forall F0 F1 (b:bexp) (c:com),
         derivable (F0 /\ (b)) c (ANpro[(F0 /\ b); (F1/\ (BNot b))])
      -> derivable (ANpro[(F0 /\ b); (F1/\ (BNot b))])
                   <{while b do c end}>
                   (F1 /\ (BNot b))
  | H_sum': forall (nF1 nF2:npro_formula) p_n  c,
                    (Forall (fun x=> x<>0%R) p_n)->
                    length nF1 = length p_n -> 
                    (big_hoare nF1 nF2 c)
        -> derivable (npro_to_pro_formula nF1 p_n) c
                    (npro_to_pro_formula nF2 p_n)
  | H_Init: forall s e , derivable (BTrue) <{( s e ) :Q= 0}> ((QExp_s s e  (Vec (2^(e-s)) 0)))
  | H_QUnit: forall s' e' s e (U: Square (2^(e'-s'))) (v: Vector (2^(e-s))), (s<=s')%nat /\ (e' <=e)%nat ->WF_Matrix v->
             derivable   (QExp_s s  e  (U_v s' e' s e U† v)) (QUnit_One s' e' U) (QExp_s s  e  v)
  | H_QMeas: forall s' e' s e (v: Vector (2^(e-s))) x (P :nat-> (Pure_formula)),
             (s<=s')%nat /\ (e'<=e)%nat->(norm v = 1)%R -> WF_Matrix v->
   derivable ((QExp_s  s  e  v) /\ big_Sand (fun i:nat => (Assn_sub_P x i (P i))) (2^(e'-s')) )
             (QMeas x s' e')
             (big_pOplus (fun i:nat=> (@norm (2^(e-s)) ((U_v s' e' s e (∣ i ⟩_ (e'-s') × ⟨ i ∣_ (e'-s')) v))) ^ 2)%R
   (fun i:nat=> SAnd ((P i))  (QExp_s  s  e ((R1 / ( (@norm (2^(e-s)) ((U_v s' e' s e (∣ i ⟩_ (e'-s') × ⟨ i ∣_ (e'-s')) v)))))%R.* 
   (U_v s' e' s e (∣ i ⟩_ (e'-s') × ⟨ i ∣_ (e'-s')) v)))) (2^(e'-s')))
  | H_Absurd: forall D c, derivable (BFalse) c D
  | H_QFrame: forall (F1 F2 F3: State_formula) c,
  (NSet.inter (fst (Free_state F3)) (fst (MVar c)) = NSet.empty /\
   NSet.Subset (snd (MVar c)) (snd (Free_state F1))) ->
   derivable F1 c F2
  ->derivable (F1 ⊙ F3) c (F2 ⊙ F3).

  (* Theorem rule_qframe: forall c (F1 F2 F3: State_formula) ,
          derivable F1 c F2 ->
         (NSet.inter (fst (Free_state F3)) (fst (MVar c)) =NSet.empty) 
         /\ (NSet.inter (snd (Free_state F3)) (snd (MVar c)) =NSet.empty) 
         ->  {{F1 ⊙ F3}} c {{F2 ⊙ F3}}.
Proof.  unfold hoare_triple. induction c; intros;
        inversion_clear H1.
     --admit.
     --admit.
     -- admit.
     -- admit.
     --inversion H.
       F1 F2 F3 c. intros H.
       intros s e (mu ,IHmu). induction mu; intros (mu', IHmu');
       intros. destruct H. destruct H2.
       inversion_clear H1. inversion_clear H4.
       inversion_clear H1. simpl in H5. destruct H5. 
       constructor. constructor. constructor.
       admit. destruct mu. 
      inversion_clear H0. simpl in H4.
      simpl. inversion_clear H1. 
      inversion_clear H0. inversion_clear H1.
      destruct a.
      inversion H4;subst;   simpl in H5.
        simpl. admit.  admit. inversion H10; subst.
        rewrite map2_nil. rewrite map2_l_refl.
        simpl. admit.
        inversion H12; subst.
        rewrite map2_nil. rewrite map2_l_refl.
        simpl. 
destruct H5. destruct H1.  
destruct H1. destruct H1.
destruct H1. destruct H1. 
destruct H1. inversion H1;subst.
simpl in H.
exists s. exists x1. exists x1. existn.
exists (fst x3, q_update ((I (2 ^ (s' - s)) ⊗ U ⊗ I (2 ^ (x1 - e')))) (snd x3)).
exists (fst x3, q_update (I (2 ^ (e - x1))) (snd x4)).
split. admit. split. admit. split. admit.
split. admit. admit.


exists s. exists x. exists x. existn.
exists((fst x3, q_update ((I (2 ^ (s' - x)) ⊗ U ⊗ I (2 ^ (e - e')))) (snd x3))).
exists ((fst x3, q_update ((I (2 ^ (x - s)))) (snd x4))).

 split.   admit. 
 split. admit. split. admit.
 split. admit. admit. *)



  Theorem  soundness: forall F1 F2 c,
   derivable F1 c F2 -> {{F1}} c {{F2}} .
  Proof. intros. induction H. 
  -- apply rule_skip.
  -- apply QRule_Q_L.rule_assgn.
  --apply rule_seq with Q. assumption. assumption.
  --apply rule_conseq with P' Q'. assumption. assumption. assumption.
  --apply rule_conj. assumption. assumption.
  -- apply rule_cond. assumption. split.  assumption.
      assumption.
  -- apply rule_while. assumption. 
  --apply rule_sum. assumption. assumption. assumption.
  --apply rule_QInit.
  --apply rule_QUnit_One; assumption.
  --apply rule_QMeas; assumption.
  --admit.
  --  unfold hoare_triple. induction c; intros;
  inversion_clear H1.
--admit.
--admit.
-- admit.
-- admit.
  Qed.
  
   *)

(* Theorem rule_qframe: forall (F1 F2 F3: State_formula) c,
         ({{F1}} c {{F2}}) /\  (NSet.inter (fst (Free_state F3)) (fst (MVar c)) =NSet.empty) 
         /\ (NSet.inter (snd (Free_state F3)) (snd (MVar c)) =NSet.empty) 
         ->  {{F1 ⊙ F3}} c {{F2 ⊙ F3}}.
Proof. unfold hoare_triple. intros F1 F2 F3 c. intros H.
       intros s e (mu ,IHmu). induction mu; intros (mu', IHmu');
       intros. destruct H. destruct H2.
       inversion_clear H1. inversion_clear H4.
       inversion_clear H1. simpl in H5. destruct H5. 
       constructor. constructor. constructor.
       admit. destruct mu. 
      inversion_clear H0. simpl in H4.
      simpl. inversion_clear H1. 
      inversion_clear H0. inversion_clear H1.
      destruct a.
      inversion H4;subst;   simpl in H5.
        simpl. admit.  admit. inversion H10; subst.
        rewrite map2_nil. rewrite map2_l_refl.
        simpl. admit.
        inversion H12; subst.
        rewrite map2_nil. rewrite map2_l_refl.
        simpl. 
destruct H5. destruct H1.  
destruct H1. destruct H1.
destruct H1. destruct H1. 
destruct H1. inversion H1;subst.
simpl in H.
exists s. exists x1. exists x1. existn.
exists (fst x3, q_update ((I (2 ^ (s' - s)) ⊗ U ⊗ I (2 ^ (x1 - e')))) (snd x3)).
exists (fst x3, q_update (I (2 ^ (e - x1))) (snd x4)).
split. admit. split. admit. split. admit.
split. admit. admit.


exists s. exists x. exists x. existn.
exists((fst x3, q_update ((I (2 ^ (s' - x)) ⊗ U ⊗ I (2 ^ (e - e')))) (snd x3))).
exists ((fst x3, q_update ((I (2 ^ (x - s)))) (snd x4))).

 split.   admit. 
 split. admit. split. admit.
 split. admit. admit.


 inversion H12; subst.
 rewrite map2_nil. rewrite map2_l_refl.
 simpl.  
destruct H5. destruct H1.  
destruct H1. destruct H1.
destruct H1. destruct H1. 
destruct H1. inversion H1;subst.
simpl in H. admit. admit. admit.









      
Admitted.   *)


(* Theorem rule_qframe_aux: forall (c : com) (F1 F2 F3 : State_formula)
(s e : nat) ( mu mu' :list (cstate *qstate s e)),
(forall (s e : nat) (mu mu' : list (cstate *qstate s e)),
 ceval_single c mu mu' -> State_eval_dstate  F1 mu -> State_eval_dstate  F2 mu')->
NSet.inter (fst (Free_state F3)) (fst (MVar c)) = NSet.empty ->
NSet.Subset (snd (MVar c)) (snd (Free_state F1)) ->
ceval_single c mu mu' ->
State_eval_dstate (F1 ⊙ F3) mu ->
State_eval_dstate (F2 ⊙ F3) mu'.
Proof. induction c; intros.
--admit.
--admit.
--admit.
--admit.
--inversion H2; subst. admit.
   apply IHc2 with F1 mu1.


--assert (ceval_single <{ abort }>
[(fst x3, snd x3)] []). apply E_Abort. 
apply H in H4. simpl in H4. destruct H4. 
simpl. admit.

assert (ceval_single <{ abort }>
[(fst x3, snd x3)] []). apply E_Abort. 
apply H in H4. simpl in H4. destruct H4. 
simpl. admit.

--inversion H8; subst.  rewrite map2_nil. rewrite map2_l_refl.
simpl. exists s. exists x1. exists x1. existn.
exists ((c_update i (aeval (fst x3, snd x3 ) a)
(fst x3), snd x3)). 
exists (c_update i (aeval (fst x3,snd x4) a)
(fst x3), snd x4). split. admit.
split. admit. split. admit. split. 
assert( ceval_single <{ i := a }>
[(fst x3, snd x3)]
(StateMap.Raw.map2 option_app
   [(c_update i
       (aeval (fst x3, snd x3) a)
       (fst x3), snd x3)] [])). apply E_Asgn.
apply E_nil. rewrite map2_nil in H4. rewrite map2_l_refl in H4.
simpl in H4. apply H in H4. simpl in H4. intuition.
simpl. admit.  admit.

inversion H8; subst.  rewrite map2_nil. rewrite map2_l_refl.
simpl. exists x. existn. exists s. exists x.
exists ((c_update i (aeval (fst x3, snd x3 ) a)
(fst x3), snd x3)). 
exists (c_update i (aeval (fst x3,snd x4) a)
(fst x3), snd x4).
 split. admit.
split. admit. split. admit. split. 
assert( ceval_single <{ i := a }>
[(fst x3, snd x3)]
(StateMap.Raw.map2 option_app
   [(c_update i
       (aeval (fst x3, snd x3) a)
       (fst x3), snd x3)] [])). apply E_Asgn.
apply E_nil. rewrite map2_nil in H4. rewrite map2_l_refl in H4.
simpl in H4. apply H in H4. simpl in H4. intuition.
simpl. admit.  admit.

--admit. admit.

--admit. admit.
   admit. admit.
-- admit. admit.
   admit. admit.
(* --inversion H8; subst.  rewrite map2_nil. rewrite map2_l_refl.
simpl. exists s. exists x1. exists x1. existn.
exists (fst x3, q_update ((I (2 ^ (s' - s)) ⊗ U ⊗ I (2 ^ (x1 - e')))) (snd x3)).
exists (fst x3, q_update (I (2 ^ (e - x1))) (snd x4)).
split. admit. split. admit. split. admit.
split. admit. admit. *)
Admitted. *)
(* 

Theorem rule_qframe: forall (F1 F2 F3: State_formula) c,
         ({{F1}} c {{F2}}) /\  (NSet.inter (fst (Free_state F3)) (fst (MVar c)) =NSet.empty) 
         /\ (NSet.inter (snd (Free_state F3)) (snd (MVar c)) =NSet.empty) 
         ->  {{F1 ⊙ F3}} c {{F2 ⊙ F3}}.
Proof.  unfold hoare_triple.  intros. destruct H.
        assert(sat_Assert mu F1 -> sat_Assert mu' F2).
        apply H. assumption. 
        destruct mu as [mu IHmu].
        destruct mu' as [mu' IHmu'].
        inversion_clear H0. simpl in H5.
        repeat rewrite sat_Assert_to_State in *.
        inversion_clear H1.  simpl in *.
        econstructor. assumption. simpl in *.
        inversion_clear H3.  
        simpl in H6.
        rewrite State_eval_odot in *.
        destruct H6. destruct H6.
        split. 
        assert(sat_Assert (StateMap.Build_slist IHmu') F2).
        apply H with (StateMap.Build_slist IHmu).
        apply E_com. assumption. assumption.
        assumption. rewrite sat_Assert_to_State.
        econstructor. assumption. assumption.
        rewrite sat_Assert_to_State in *.
        inversion_clear H8. assumption.
        split. apply rule_f with c mu.
        assumption. assumption. 
        assumption. admit.
Admitted. *)