Require Import Reals.
Require Import Coquelicot.Complex.
Require Import Strings.String.
Require Import Lists.List.
Require Import
  Coq.FSets.FMapList
  Coq.Structures.OrderedTypeEx.


From Quan Require Import Matrix.
From Quan Require Import Quantum.
From Quan Require Import Mixed_State.
From Quan Require Import QState_L.
From Quan Require Import Reduced.
From Quan Require Import Basic.
From Quan Require Import QIMP_L.

Delimit Scope C_scope with C.
Local Open Scope C_scope.
Local Open Scope com_scope.
Local Open Scope state_scope.
Import Sorted.


Lemma ceval_app_while{s e:nat}: 
forall b c,
(forall  x y mu : list (cstate * qstate s e),
WF_dstate_aux x ->
WF_dstate_aux y ->
ceval_single c (x +l y) mu ->
exists mu1 mu2 : list (cstate * qstate s e),
ceval_single c x mu1 /\
ceval_single c y mu2 /\ mu = (mu1 +l mu2))->

(forall (mu mu' : list (cstate *qstate s e)),
ceval_single <{ while b do c end }> mu mu' ->
(forall x y ,  mu=(StateMap.Raw.map2 option_app x y)->
WF_dstate_aux x ->
WF_dstate_aux y ->
exists mu1 mu2 , (ceval_single <{ while b do c end }> x mu1
/\ceval_single <{ while b do c end }> y mu2 
/\mu'=StateMap.Raw.map2 option_app mu1 mu2))).
Proof. intros b c Hc mu mu' H.

      remember <{while b do c end}> as original_command eqn:Horig. 
      induction H;  try inversion Horig; subst.
      intros x y H0 Hx Hy. apply map2_app_nil in H0. destruct H0. 
      exists []. exists []. rewrite H0. rewrite H1. 
      split; try split; try apply E_nil. intuition. 

      destruct x; destruct y;
      intros H3 Hx Hy. discriminate H3.
      destruct p.
      simpl in H3. 
      rewrite map2_r_refl in H3.

      exists []. exists ((mu' +l mu'')).
      split. apply E_nil. split.

      inversion H3.  rewrite <-H5. rewrite <-H6.
      rewrite <-H7. apply E_While_true with mu1.
      assumption. assumption. assumption. assumption.
      rewrite map2_nil_l.  reflexivity.

      destruct p.
      simpl in H3. 
      rewrite map2_l_refl in H3.

      exists ((mu' +l mu'')). exists nil.
      split.   inversion H3.  rewrite <-H5. rewrite <-H6.
      rewrite <-H7. apply E_While_true with mu1.
      assumption. assumption. assumption. assumption.
      split. apply E_nil. simpl. 
      rewrite map2_nil_r.  reflexivity.

      destruct p. destruct p0.
      simpl in H3.
      destruct (Cstate_as_OT.compare c0 c1).
      injection H3. intros. 


      assert( exists mu1 mu2 : list (cstate * qstate s e),
      ceval_single <{ while b do c end }> x mu1 /\
      ceval_single <{ while b do c end }> ((c1, q0) :: y) mu2 /\
      mu'' = (mu1 +l mu2)).

      apply IHceval_single1.
      reflexivity. apply H4.
      inversion_clear Hx. assumption.
      assumption.
      destruct H7. destruct H7.
      exists (mu' +l x0).
      exists x1.
      split. rewrite<-H6. rewrite <-H5.
      apply E_While_true with mu1.
      assumption. intuition. intuition. 
      intuition. 
      split. intuition. rewrite <-map2_assoc. 
      destruct H7. destruct H8. rewrite <-H9.
      reflexivity. 

      injection H3. intros.
      assert(exists mu2 mu3 : list (cstate * qstate s e),
      ceval_single c [(c0,q)] mu2 /\ ceval_single c [(c0,q0)] mu3 /\ mu1 = (mu2 +l mu3)).
      apply (Hc [(c0, q)] [(c0, q0)] mu1).
      apply WF_state_dstate_aux. inversion_clear Hx.
      assumption. apply WF_state_dstate_aux.
      inversion_clear Hy. assumption.

      rewrite <-H6. 
      simpl.  
      destruct (Cstate_as_OT.compare sigma sigma).
      apply Cstate_as_OT.lt_not_eq in l. intuition. rewrite <-H5.
      assumption.

      apply Cstate_as_OT.lt_not_eq in l. intuition.


      destruct H7. destruct H7.
      assert(exists mu1 mu2 : list (cstate * qstate s e),
      ceval_single <{ while b do c end }> x mu1 /\
      ceval_single <{ while b do c end }> y mu2 /\ mu'' = (mu1 +l mu2)).

      apply IHceval_single1. reflexivity. assumption.
      inversion_clear Hx. 
      assumption.  inversion_clear Hy. assumption.
      destruct H8. destruct H8. 


      destruct H7. destruct H9. 

      assert(exists mu1 mu2 : list (cstate * qstate s e),
      ceval_single <{ while b do c end }> x0 mu1 /\
      ceval_single <{ while b do c end }> x1 mu2 /\ mu' = (mu1 +l mu2)).
      apply IHceval_single3. 
      reflexivity. assumption.
      apply WF_ceval with c [(c0, q)].
      apply WF_state_dstate_aux. inversion_clear Hx.
      assumption. assumption.
      apply WF_ceval with c [(c0, q0)].
      apply WF_state_dstate_aux.
      inversion_clear Hy. assumption. assumption.
      destruct H11. destruct H11.

      exists (x4 +l x2). 
      exists (x5 +l x3).
      split. 
      apply E_While_true with x0.
      rewrite <-H6.
      rewrite (state_eq_bexp  _ (sigma, rho) _ ). assumption.
      reflexivity.
      intuition. assumption.
      intuition. split.
      apply E_While_true with x1.
      unfold Cstate_as_OT.eq in e0.
      rewrite <-e0. rewrite <-H6. 
      rewrite (state_eq_bexp  _ (sigma, rho) _ ). assumption.
      reflexivity. 
      intuition. 
      unfold Cstate_as_OT.eq in e0.
      rewrite <-e0.
      intuition. intuition. rewrite (map2_comm x4 x2).
      rewrite map2_assoc.  rewrite <-(map2_assoc _ _ x2 _ _).
      destruct H11. destruct H12. rewrite H13. 
      destruct H8. destruct H14. rewrite H15.
      rewrite (map2_comm x2  ((x4 +l x5))). 
      rewrite map2_assoc. reflexivity. 

      injection H3. intros.


      assert( exists mu1 mu2 : list (cstate * qstate s e),
      ceval_single <{ while b do c end }> ((c0,q)::x) mu1 /\
      ceval_single <{ while b do c end }> y mu2 /\ mu'' = (mu1 +l mu2)).
      apply IHceval_single1.
      reflexivity. simpl.
      apply H4. assumption. inversion_clear Hy. assumption.
      
      destruct H7. 
      destruct H7. 
      exists (x0).
      exists (mu' +l x1).
      split. intuition.
      split. apply E_While_true with mu1.
      rewrite <-H6. rewrite (state_eq_bexp  _ (sigma, rho) _ ).
      assumption. reflexivity.
      intuition. rewrite <-H6. rewrite<-H5. assumption. 
      intuition. rewrite (map2_comm mu' x1). 
      rewrite map2_assoc. destruct H7. destruct H8. rewrite H9.
      apply map2_comm. 

      destruct x; destruct y;  intros H2 Hx Hy;
      simpl  in H2;
      try discriminate H2; try destruct p. 
      rewrite map2_r_refl in H2.

      exists []. exists ([(sigma, rho)] +l mu'). 
      split. apply E_nil. split. inversion H2; subst. 
      apply E_While_false. assumption. assumption. assumption.
      rewrite map2_nil_l.  reflexivity.

      rewrite map2_l_refl in H2. 
      exists ([(sigma, rho)] +l mu'). exists []. split. 
      inversion H2; subst. 
      apply E_While_false. assumption. assumption. assumption.
      split. apply E_nil.
      rewrite map2_nil_r.  reflexivity. 

      destruct p0.   
      destruct (Cstate_as_OT.compare c0 c1).
      injection H2; intros ; subst.
      assert( exists mu1 mu2 : list (cstate * qstate s e),
      ceval_single <{ while b do c end }> x mu1 /\
      ceval_single <{ while b do c end }> ((c1, q0) :: y) mu2 /\
      mu' = (mu1 +l mu2)).     apply IHceval_single.
      reflexivity.  
      reflexivity. inversion_clear Hx. assumption.
      assumption. 
      destruct H3. destruct H3.
      exists ( [(c0, q)] +l x0).
      exists x1.
      split. 
      apply E_While_false. assumption.
      assumption. intuition.  split. intuition. 
      rewrite <-map2_assoc. destruct H3. destruct H4.
      rewrite H5. reflexivity.

      assert(exists mu1 mu2 : list (cstate * qstate s e),
      ceval_single <{ while b do c end }> x mu1 /\
      ceval_single <{ while b do c end }> y mu2 /\ mu' = (mu1 +l mu2)).

      apply IHceval_single. reflexivity. injection H2. intros; subst.
      reflexivity. inversion_clear Hx. 
      assumption. inversion_clear Hy. assumption.
      destruct H3. destruct H3.  destruct H3; destruct H4.

      exists ( [(c0, q)] +l x0). exists ( [(c1, q0)] +l x1).
      split. apply E_While_false. unfold Cstate_as_OT.eq in e0.
      subst. injection H2; intros. subst. 
      rewrite (@state_eq_bexp s e s e _ (c1, q .+ q0) _ ). assumption.
      reflexivity. assumption. assumption. split. 
      apply E_While_false. unfold Cstate_as_OT.eq in e0.
      subst. injection H2; intros. subst. 
      rewrite (@state_eq_bexp s e s e _ (c1, q .+ q0) _ ). assumption.
      reflexivity. assumption. assumption. injection H2; intros. subst.
      remember ((@cons (prod cstate (qstate s e))
      (@pair cstate (qstate s e) c0
      (q_plus q q0))
      (@nil (prod cstate (qstate s e))))).  
      remember ([(c0, q_plus q q0)]). 
      assert(l=l0). rewrite Heql. rewrite Heql0. reflexivity. 
      assert([(c0, q_plus q q0)] = ([(c0, q )] +l  [(c1, q0)])).
      simpl.  destruct (Cstate_as_OT.compare c0 c1). 
      rewrite e0 in l1. apply Cstate_as_OT.lt_not_eq in l1. intuition.
      reflexivity. rewrite e0 in l1. apply Cstate_as_OT.lt_not_eq in l1. 
      intuition. rewrite H5. rewrite Heql0.    rewrite H6.  rewrite map2_assoc. 
      rewrite (map2_comm ([(c0, q)]) ([(c1, q0)])).
      rewrite<- (map2_assoc _ _ ([(c1, q0)]) ).
      rewrite (map2_comm ([(c1, q0)]) _). 
      rewrite map2_assoc. reflexivity. 


      injection H2. intros. subst.
      assert(exists mu1 mu2 : list (cstate * qstate s e),
      ceval_single <{ while b do c end }> ((c0,q)::x) mu1 /\
      ceval_single <{ while b do c end }> y mu2 /\ mu' = (mu1 +l mu2)).
      apply IHceval_single.
      reflexivity. reflexivity. assumption.
      inversion_clear Hy. assumption.
      
      destruct H3. destruct H3.
      destruct H3. destruct H4. 

      exists (x0). 
      exists ( [(c1, q0)] +l x1).
      split. assumption. split. 
      apply E_While_false. assumption.
      assumption. intuition. rewrite (map2_comm _ x1). 
      rewrite map2_assoc. rewrite map2_comm. rewrite H5.  reflexivity.
      Qed.

Lemma  map_nil:forall (s e : nat) (p: R) (x : list (cstate * qstate s e)),
([] = StateMap.Raw.map (fun i: Square (2 ^ (e-s)) => @scale (2^(e-s)) (2^(e-s)) p i) x)
-> x = [].
Proof. destruct x. simpl. intuition. destruct p0. simpl.
intros. discriminate H. 
Qed.


Lemma ceval_scale_while{s e:nat}: 
forall b c,
(forall  (p:R) (x  mu : list (cstate * qstate s e)),
(0<p)%R ->
ceval_single c (StateMap.Raw.map (fun i => p .* i) x) mu ->
exists mu1 : list (cstate * qstate s e),
ceval_single c x mu1  /\ mu = (StateMap.Raw.map (fun i => p .* i)mu1))->

(forall (mu mu' : list (cstate *qstate s e)),
ceval_single <{ while b do c end }> mu mu' ->
(forall (p:R) x,  mu=(StateMap.Raw.map (fun i => p .* i) x )->
(0<p)%R->
exists mu1, (ceval_single <{ while b do c end }> x mu1
/\mu'=StateMap.Raw.map (fun i => p .* i) mu1))).
Proof.  intros b c Hc mu mu' H.

      remember <{while b do c end}> as original_command eqn:Horig. 
      induction H;  try inversion Horig; subst.
      intros p x H0 Hp.   apply map_nil in H0. rewrite H0.
      exists []. split.   try apply E_nil. intuition. 

      destruct x; intros H3 Hp. discriminate H3.
      destruct p0. simpl in H3.  
      inversion H3. 
      assert( exists mu1 : list (cstate * qstate s e),
      ceval_single <{ while b do c end }> x mu1 /\
      mu''= StateMap.Raw.map
      (fun i : Square (2 ^ (e-s)) => p .* i) mu1).
      apply IHceval_single1. reflexivity. assumption.
      assumption.
      destruct H4.  
      assert(exists mu2 : list (cstate * qstate s e),
      ceval_single c [(c0,m)] mu2 /\ mu1 = StateMap.Raw.map
      (fun i : Square (2 ^ (e-s)) => p .* i) mu2 ).
      apply (Hc p [(c0, m)] mu1). assumption. simpl. 
      rewrite <-H5. rewrite <-H6. assumption.
      destruct H8.   
      assert(exists mu1 : list (cstate * qstate s e),
      ceval_single <{ while b do c end }> x1
        mu1 /\ mu' =
      StateMap.Raw.map
        (fun i : Square (2 ^ (e-s)) => p .* i)
        mu1). apply IHceval_single3. reflexivity.
        intuition. assumption. destruct H9.
      exists (x2 +l x0) .  split.
      apply E_While_true with x1. 
      rewrite <-H5. rewrite (state_eq_bexp _ (sigma, rho)).
      assumption. reflexivity. intuition. intuition. intuition.
      rewrite <-map_map2_distr.
      f_equal. intuition. intuition.

      destruct x; intros H2 Hp. discriminate H2.
      destruct p0. simpl in H2.  
      inversion H2. 
      assert( exists mu1 : list (cstate * qstate s e),
      ceval_single <{ while b do c end }> x mu1 /\
      mu'= StateMap.Raw.map
      (fun i : Square (2 ^ (e-s)) => p .* i) mu1).
      apply IHceval_single. reflexivity. assumption.
      assumption.
      destruct H3.  
      exists (([(c0 , m)]) +l x0) .  split.
      pose (@E_While_false s e). unfold qstate in c1.
      apply c1. rewrite <-H4. rewrite (state_eq_bexp _ (sigma, rho)).
      assumption. reflexivity. assumption. intuition. 
      rewrite <-map_map2_distr.
      f_equal. intuition.

Qed.



Fixpoint dstate_fst_eq{s e:nat} (mu1 mu2:list(cstate * qstate s e)) :=
  match mu1, mu2 with
  |[], [] => True
  |(c0,q0)::mu1', (c1,q1)::mu2' => c0= c1 /\ dstate_fst_eq mu1' mu2'
  |_, _ =>False
  end.


Lemma big_app_plus{s e:nat}: forall n0 (f g: nat -> list(cstate * qstate s e)), 
(big_app f n0) +l (big_app g n0) =
big_app (fun j:nat => (f j) +l (g j)) n0.
Proof. induction n0; intros. 
      simpl. reflexivity.

      simpl.  repeat rewrite map2_assoc. 
      repeat rewrite <-(map2_assoc _ _ _ (f n0)).
     rewrite (map2_comm (f n0) ).
      rewrite map2_assoc. 
      rewrite <-(map2_assoc _ _ ((big_app f n0 +l big_app g n0))).
      f_equal. apply IHn0.
Qed.

Lemma fst_plus: forall (c1 c2: C),
 fst(c1 + c2)= (fst c1 + fst c2)%R.
Proof. intros. destruct c1. destruct c2.
      simpl. reflexivity.
Qed.

Local Open Scope nat_scope.
Lemma big_app'_plus{s e:nat}: forall n0 (f g: nat -> (cstate * qstate s e)) mu mu1 mu2, 
(forall i, i < n0 -> WWF_qstate ( snd ( f i))\/ ( snd ( f i))= Zero)->
(forall i, i < n0 -> WWF_qstate ( snd ( g i))\/ ( snd ( g i))= Zero)->
(forall i,  fst (f i) = fst ( g i))->
(big_app' f n0 mu1) ->
(big_app' g n0 mu2) ->
big_app' (fun j:nat =>(fst (f j), snd (f j) .+ snd (g j))) n0 mu->
mu1 +l mu2 = mu.
Proof. induction n0; intros f g mu mu1 mu2 Hf Hg; intros. 
      simpl. inversion_clear H0. inversion_clear H1.
      inversion_clear H2. reflexivity.

      inversion_clear H0. inversion_clear H1.
      inversion_clear  H2. 
      apply IHn0 with f g;  auto.
      rewrite H3 in *. rewrite H0 in *.
      simpl in H1. rewrite Mplus_0_r in H1.
      destruct H1.  reflexivity.

      inversion_clear H2. rewrite H3 in *.
      simpl in H1. rewrite Mplus_0_l in H1.
      rewrite H1 in H0. destruct H0. reflexivity.

      rewrite H3 in *. simpl in *. rewrite Mplus_0_l in *.
      rewrite map2_assoc. f_equal. apply IHn0 with f g; auto.
      rewrite H. destruct (g n0). reflexivity.
      
      inversion_clear H1.  inversion_clear H2.
      rewrite H0 in *.
      simpl in H1. rewrite Mplus_0_r in H1.
      rewrite H1 in H3. destruct H3. reflexivity.

      rewrite H0 in *. simpl in *. rewrite Mplus_0_r in *.
      rewrite <-map2_assoc.  rewrite (map2_comm [f n0] ).
      rewrite map2_assoc.  f_equal. apply IHn0 with f g; auto.
       destruct (f n0). reflexivity.

       inversion_clear H2. simpl in *.
       assert(fst (@trace (2^(e-s)) (snd (f n0) .+ snd (g n0)))= 0%R).
       rewrite H1. rewrite Zero_trace. reflexivity.
       rewrite trace_plus_dist in H2. rewrite fst_plus in H2.
       pose(Hf n0). pose (Hg n0).
       destruct o. lia. destruct o0. lia. 
       destruct H7. 
       apply nz_mixed_state_trace_gt0_aux in H7.
       destruct H8.
       apply nz_mixed_state_trace_gt0_aux in H8.
       lra. rewrite H8 in H0.  destruct H0.
       reflexivity. rewrite H7 in H3. destruct H3.
       reflexivity.
  
      repeat rewrite map2_assoc. 
      repeat rewrite <-(map2_assoc _ _ _ [f n0]).
     rewrite (map2_comm [f n0] ).
      rewrite map2_assoc. 
      rewrite <-(map2_assoc _ _ (l +l l0)).
      f_equal. apply IHn0 with f g; auto.
      assert(fst (f n0) = fst (g n0)). apply H.
      destruct (f n0). destruct ( g n0). 
      simpl in *. rewrite H2. MC.elim_comp. 
      reflexivity.
Qed.

Lemma big_app_scale{s e:nat}: forall n0 (p:R) (f: nat -> list(cstate * qstate s e)), 
StateMap.Raw.map (fun x0 : qstate s e =>@scale (2^(e-s)) (2^(e-s)) p  x0) (big_app f n0)=
big_app (fun j:nat => StateMap.Raw.map (fun x0 : qstate s e => @scale (2^(e-s)) (2^(e-s))  p  x0) (f j)) n0.
Proof. induction n0; intros.
     simpl. reflexivity.

     simpl . unfold qstate.
     apply Logic.eq_trans with  (StateMap.Raw.map (fun x0 : Square (2 ^ (e-s)) => p .* x0)
    ((big_app f n0) +l f n0)). f_equal. 
      rewrite <-(map_map2_distr).
      f_equal.  apply IHn0.
Qed.


Lemma big_app'_scale{s e:nat}: forall n0 (p:R) (f: nat -> (cstate * qstate s e)) mu mu', 
(p<>0)%R->
(big_app' f n0 mu)-> 
big_app' (fun j:nat =>s_scale p (f j)) n0 mu'->
StateMap.Raw.map (fun x0 : qstate s e =>@scale (2^(e-s)) (2^(e-s)) p  x0) mu = mu'.
Proof. induction n0; intros.
      inversion_clear H0. inversion_clear H1.
     simpl. reflexivity.

     inversion_clear H0. inversion_clear H1.
     apply IHn0 with f; auto.
     unfold s_scale in *.
     rewrite H2 in *. unfold q_scale in *. rewrite Mscale_0_r in *.
     simpl in H0. destruct H0. reflexivity.

     inversion_clear H1.  
     unfold s_scale in *. simpl in *.
     assert((p,0%R)<> C0)%C. apply C0_fst_neq. apply H.
     pose (scale_Zero _ _ H0 H1). rewrite e0 in H2.
     destruct H2. reflexivity.

     rewrite <-(map_map2_distr). f_equal.
     apply IHn0 with f; auto.
     unfold s_scale. simpl. destruct (f n0).
     reflexivity.
Qed.

Require Import
  Coq.FSets.FMapList
  Coq.Structures.OrderedTypeEx.
Require Import OrderedType.
Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Arith.Peano_dec.
Module Import MC := OrderedTypeFacts(Cstate_as_OT).

Lemma big_app_eq_bound'' {s e : nat}: forall (f1 f2 : nat -> cstate * qstate s e) 
(n0 : nat) (mu1 : list (cstate * qstate s e)),
big_app' f1 n0 mu1 ->
(forall i : nat, i < n0 -> f1 i = f2 i) ->
big_app' f2 n0 mu1.
Proof. induction n0; intros; inversion H; subst.
       econstructor. econstructor. rewrite <-H0. assumption. lia.
       apply IHn0. assumption. intros. apply H0.
       lia. rewrite H0.  
       apply (QIMP_L.big_app_cons).  
       rewrite <-H0. assumption. lia.
       apply IHn0. assumption.  intros. apply H0.
       lia. lia. 
Qed.

Lemma ceval_clet_1{s e:nat}: forall i a (mu mu':list (cstate *qstate s e)),
ceval_single (Clet i a) mu mu'->mu=mu'.
Proof.   induction mu; intros; inversion H; subst; try
        reflexivity. Qed.


Lemma ceval_app_aux{s e:nat}:  forall c  ( x y mu: list (cstate *qstate s e)),
WF_dstate_aux x-> WF_dstate_aux y->
ceval_single c (StateMap.Raw.map2 option_app x y) mu ->
exists mu1 mu2 , (ceval_single c x mu1
/\ceval_single c y mu2 
/\mu=StateMap.Raw.map2 option_app mu1 mu2).
Proof.  induction c. 
    -{ intros. exists x. exists y.
      split. apply ceval_skip. 
      split. apply ceval_skip.
      apply ceval_skip_1 in H1. intuition. } 
    -{ induction x; induction y; intros.
      exists nil. exists nil.
      split. apply E_nil. split. apply E_nil.
      simpl. simpl in H1. inversion_clear H1. reflexivity. 
      destruct a0. simpl in H1. rewrite map2_r_refl in H1.
      inversion H1;subst. 
      exists nil. exists ((StateMap.Raw.map2 option_app
      [(c_update i (aeval (c, q) a) c, q)] mu')).
      split. apply E_nil. split. intuition.
      rewrite map2_nil_l.  reflexivity.
      destruct a0. simpl in H1. rewrite map2_l_refl in H1.
      inversion H1;subst. 
      exists ((StateMap.Raw.map2 option_app
      [(c_update i (aeval (c, q) a) c, q)] mu')).
      exists nil.
      split.  intuition. split.  apply E_nil.
      rewrite map2_nil_r.  reflexivity.
      destruct a0. destruct a1. simpl in H1.
      destruct (Cstate_as_OT.compare c c0).
      inversion H1;subst.
      apply IHx in H8.  destruct H8. destruct H2.
      destruct H2. destruct H3. 
      remember (StateMap.Raw.map2 option_app
      [(c_update i (aeval (c, q) a) c, q)] x0).
      exists t. exists x1.
      split. rewrite Heqt. apply E_Asgn.
      intuition. split. intuition. 
      rewrite H4. rewrite Heqt. apply map2_assoc.
      inversion_clear H. assumption.
      assumption.
      inversion H1;subst.
      apply IHx in H8.
      destruct H8. destruct H2.
      destruct H2. destruct H3.
      remember (StateMap.Raw.map2 option_app
      [(c_update i (aeval (c, q) a) c, q)] x0).
      remember (StateMap.Raw.map2 option_app
      [(c_update i (aeval (c0, (q0)) a) c0, q0)] x1).
      exists t. exists t0.
      split. rewrite Heqt. 
      apply E_Asgn. intuition. 
      split. rewrite Heqt0. apply E_Asgn. intuition.
      rewrite H4. rewrite Heqt. rewrite Heqt0.
      repeat rewrite map2_assoc. repeat rewrite <-(map2_assoc _ _ _ x0).
      rewrite (map2_comm x0 ([(c_update i (aeval (c0, q0) a) c0, q0)])).
      rewrite <-map2_assoc. rewrite <-map2_assoc.
      rewrite (map2_assoc _ _ _ _ ((x0 +l x1))).
      f_equal. simpl. unfold Cstate_as_OT.eq in e0.
      rewrite e0. rewrite (state_eq_aexp (c0, q) (c0, q0) a ).
      MC.elim_comp.  
      rewrite (@state_eq_aexp s e s e (c0, q0) (c0, q.+ q0) a ).
      f_equal. reflexivity. reflexivity. reflexivity.
      inversion_clear H. assumption.
      inversion_clear H0. assumption.

      inversion H1;subst.
      apply IHy in H8. 
      destruct H8. destruct H2.
      destruct H2. destruct H3.
      exists x0. 
      remember (StateMap.Raw.map2 option_app [(c_update i (aeval (c0, q0) a) c0, q0)] x1).
      exists t. 
      rewrite Heqt. split. intuition.
      split. apply E_Asgn. intuition.
      rewrite H4. rewrite (map2_comm ([(c_update i (aeval (c0, q0) a) c0, q0)]) x1).
      rewrite (map2_assoc _ _ x0). apply map2_comm.
      assumption. inversion_clear H0. assumption. }
    --   induction x; induction y; intros. 
    exists []. exists []. split. econstructor. 
    split. econstructor. simpl in *. inversion_clear H1. reflexivity.
    destruct a0.  simpl in *. rewrite map2_r_refl in *. 
    exists []. exists mu. split. econstructor. 
    split. assumption. simpl. rewrite map2_r_refl. reflexivity.
     exists mu. exists [].  rewrite map2_nil_r in *. 
    split. assumption. split.  econstructor. reflexivity. 
    destruct a0. destruct a1.  
    simpl in H1. destruct (Cstate_as_OT.compare c c0);
     inversion H1; subst;
     exists ((c, q) :: x); exists ((c0, q0) :: y); 
     split; try econstructor; try assumption; try   econstructor; try assumption;
     simpl; try MC.elim_comp; try reflexivity. 
    -{intros x y mu Hx Hy; intros. inversion H; subst.
      apply map2_app_nil in H2. destruct H2.
      subst. exists nil. exists nil.
      split. apply E_nil. split. apply E_nil.
      simpl. reflexivity.
      rewrite H2 in H3. 
      apply IHc1 in H3.
      destruct H3. destruct H0. destruct H0.
      destruct H1. rewrite H3 in H5.
      apply IHc2 in H5. 
      destruct H5. destruct H4.
      destruct H4. destruct H5.
      exists x2. exists x3.
      split. apply ceval_seq with x0.
      intuition. intuition.
      split.  apply ceval_seq with x1.
      intuition. intuition. intuition. 
      apply WF_ceval with c1 x; try assumption.
      apply WF_ceval with c1 y; try assumption.
      assumption. assumption.
       }
      -{induction x; induction y; intros  mu Hx Hy; intros.
      simpl in H. inversion_clear H.
      exists nil. exists nil.
      split. apply E_nil. split. apply E_nil.
      simpl. reflexivity.
      destruct a. simpl in H. rewrite map2_r_refl in H. 
      exists nil. exists (mu).
      split. apply E_nil. split. intuition.
      rewrite map2_nil_l.  reflexivity.
      destruct a. simpl in H. rewrite map2_l_refl in H.
      exists (mu).
      exists nil.
      split.  intuition. split.  apply E_nil.
      rewrite map2_nil_r.  reflexivity.
      destruct a. destruct a0. simpl in H.
      destruct (Cstate_as_OT.compare c c0).
      inversion H;subst. 
      apply IHx in H9. destruct H9. destruct H0.
      destruct H0. destruct H1. 
      exists (StateMap.Raw.map2 option_app mu' x0). exists x1.
      split.  apply E_IF_true. intuition. intuition.
      intuition. assumption. split. intuition. 
      rewrite H2. apply map2_assoc.
      inversion_clear Hx. assumption. 
      assumption.
      apply IHx in H9. destruct H9. destruct H0.
      destruct H0. destruct H1. 
      exists (StateMap.Raw.map2 option_app mu' x0). exists x1.
      split.  apply E_IF_false. intuition. intuition.
      intuition. assumption. split. intuition. 
      rewrite H2.  apply map2_assoc.
      inversion_clear Hx. assumption.
      assumption.

      inversion_clear H.
      apply IHx in H2. destruct H2. destruct H.
      destruct H. destruct H2.
      assert(exists mu1 mu2 : list (cstate * qstate s e),
      ceval_single c1 [(c,q)] mu1 /\
      ceval_single c1 [(c, q0)] mu2 /\
      mu' = StateMap.Raw.map2 option_app mu1 mu2).
      apply IHc1. apply WF_state_dstate_aux.
      inversion_clear Hx. assumption.
      apply WF_state_dstate_aux. inversion_clear Hy.
      assumption. 
      
      simpl.  destruct (Cstate_as_OT.compare c c).
      apply Cstate_as_OT.lt_not_eq in l. intuition.
      intuition.  apply Cstate_as_OT.lt_not_eq in l. intuition.
      destruct H5. destruct H5. destruct H5. destruct H6. 
      exists (StateMap.Raw.map2 option_app x2 x0). 
      exists ((StateMap.Raw.map2 option_app x3 x1)).
      split.  apply E_IF_true.
       rewrite (@state_eq_bexp s e s e _ (c, q .+ q0)).
      intuition. intuition.
      intuition.  intuition. assumption.   split.  apply E_IF_true.
       rewrite (@state_eq_bexp s e s e _ (c, q .+ q0)).
      intuition. intuition. assumption. 
      intuition.  unfold Cstate_as_OT.eq in e0. rewrite <-e0. intuition.
      rewrite H7. rewrite H4. 
      rewrite (map2_comm x2 _).  rewrite map2_assoc.

      rewrite<-(map2_assoc _ _ x3 x2 x0). rewrite (map2_comm x3 _).
      rewrite <-map2_assoc. reflexivity.

      inversion_clear Hx. assumption.
      inversion_clear Hy. assumption.

      apply IHx in H2. destruct H2. destruct H.
      destruct H. destruct H2.
      assert(exists mu1 mu2 : list (cstate * qstate s e),
      ceval_single c2 [(c,q)] mu1 /\
      ceval_single c2 [(c, q0)] mu2 /\
      mu' = StateMap.Raw.map2 option_app mu1 mu2).
      apply IHc2. apply WF_state_dstate_aux.
      inversion_clear Hx. assumption.
      apply WF_state_dstate_aux. inversion_clear Hy.
      assumption. 
      
      simpl.  destruct (Cstate_as_OT.compare c c).
      apply Cstate_as_OT.lt_not_eq in l. intuition.
      intuition.  apply Cstate_as_OT.lt_not_eq in l. intuition.
      destruct H5. destruct H5. destruct H5. destruct H6. 
      exists (StateMap.Raw.map2 option_app x2 x0). 
      exists ((StateMap.Raw.map2 option_app x3 x1)).
      split.  apply E_IF_false. 
      rewrite (@state_eq_bexp s e s e _ (c, q .+ q0)).
      intuition. intuition.
      intuition.  intuition. assumption.   split.  apply E_IF_false. 
      rewrite (@state_eq_bexp s e s e _ (c, q .+ q0)).
      intuition. intuition. 
      intuition. assumption.  unfold Cstate_as_OT.eq in e0. rewrite <-e0. intuition.
      rewrite H7. rewrite H4. rewrite (map2_comm x2 _).  rewrite map2_assoc.
      rewrite<-(map2_assoc _ _ x3 x2 x0). rewrite (map2_comm x3 _).
      rewrite <-map2_assoc. reflexivity.
      inversion_clear Hx. assumption.
      inversion_clear Hy. assumption.
      inversion H;subst.
      apply IHy in H9. destruct H9. destruct H0.
      destruct H0. destruct H1. 
      exists x0. exists (StateMap.Raw.map2 option_app mu' x1).
      split. intuition.  split.
      apply E_IF_true. intuition. intuition.
      intuition. assumption.  
      rewrite H2. rewrite map2_assoc. rewrite (map2_comm mu' _).
      rewrite <-map2_assoc. reflexivity.
      assumption. inversion_clear Hy. assumption.

      apply IHy in H9. destruct H9. destruct H0.
      destruct H0. destruct H1. 
      exists x0. exists (StateMap.Raw.map2 option_app mu' x1).
      split. intuition.  split.
      apply E_IF_false. intuition. intuition.
      intuition. assumption.  
      rewrite H2.  rewrite map2_assoc. rewrite (map2_comm mu' _).
      rewrite <-map2_assoc. reflexivity.
      assumption. inversion_clear Hy. assumption. }

    -{intros.  apply ceval_app_while with ((x +l y)).
      intros. apply IHc; try assumption.  assumption.
      reflexivity. assumption. assumption. }

    -{ induction x; induction y; intros mu Hx Hy; intros.
      exists nil. exists nil.
      split. apply E_nil. split. apply E_nil.
      simpl. simpl in H. inversion_clear H. reflexivity. 
      destruct a. simpl in H. rewrite map2_r_refl in H.
      inversion H;subst. 
      exists nil. exists ((StateMap.Raw.map2 option_app
      [(c, QInit_fun s0 e0 q)] mu')).
      split. apply E_nil. split. apply H.  rewrite map2_nil_l.  reflexivity.
      destruct a. simpl in H. rewrite map2_l_refl in H.
      inversion H;subst. 
      exists ((StateMap.Raw.map2 option_app
      [(c, QInit_fun s0 e0 q)] mu')).
      exists nil.
      split.  intuition. split.  apply E_nil.
      rewrite map2_nil_r.  reflexivity.
      destruct a0. destruct a. simpl in H.
      destruct (Cstate_as_OT.compare c0 c).
      inversion H;subst.
      apply IHx in H7. destruct H7. destruct H0.
      destruct H0. destruct H1. 
      remember (StateMap.Raw.map2 option_app
      [(c0, QInit_fun s0 e0 q0)] x0).
      exists t. exists x1.
      split. rewrite Heqt. apply E_Qinit. intuition.
      intuition. split. intuition. 
      rewrite H2. rewrite Heqt. apply map2_assoc.
      inversion_clear Hx. assumption.
      assumption.
      inversion H;subst.
      apply IHx in H7. destruct H7. destruct H0.
      destruct H0. destruct H1.
      remember (StateMap.Raw.map2 option_app
      [(c0, QInit_fun s0 e0 q0)] x0).
      remember (StateMap.Raw.map2 option_app
      [(c, QInit_fun s0 e0 q)] x1).
      exists t. exists t0.
      split. rewrite Heqt. 
      apply E_Qinit. intuition. intuition.  
      split. rewrite Heqt0. apply E_Qinit. intuition.
      intuition.
      rewrite H2. rewrite Heqt. rewrite Heqt0.
      repeat rewrite map2_assoc. repeat rewrite <-(map2_assoc _ _ _ x0).
      rewrite (map2_comm x0 ([(c, QInit_fun s0 e0 q)])).
      rewrite <-map2_assoc. rewrite <-map2_assoc.
      rewrite (map2_assoc _ _ _ _ ((x0 +l x1))).
      f_equal. simpl. unfold Cstate_as_OT.eq in e1.
      rewrite e1.  MC.elim_comp. unfold q_plus.
      rewrite <-QInit_fun_plus. reflexivity.
      inversion_clear Hx. assumption. 
      inversion_clear Hy. assumption.  

      inversion H;subst.
      apply IHy in H7. 
      destruct H7. destruct H0.
      destruct H0. destruct H1.
      exists x0. 
      remember (StateMap.Raw.map2 option_app [(c, QInit_fun s0 e0 q)] x1).
      exists t. 
      rewrite Heqt. split. intuition.
      split. apply E_Qinit. intuition. intuition.
      rewrite H2. rewrite (map2_comm ([(c, QInit_fun s0 e0 q)]) x1).
      rewrite (map2_assoc _ _ x0). apply map2_comm.
      assumption. inversion_clear Hy. assumption. } 

    -{induction x; induction y; intros nmu Hx Hy; intros.
      exists nil. exists nil.
      split. apply E_nil. split. apply E_nil.
      simpl. simpl in H. inversion_clear H. reflexivity. 
      destruct a. simpl in H. rewrite map2_r_refl in H.
      inversion H;subst. apply inj_pair2_eq_dec in H2. 
      apply inj_pair2_eq_dec in H2. destruct H2.
      exists nil. exists ((StateMap.Raw.map2 option_app
      [(c, QUnit_One_fun s0 e0 U1 q)] mu')).
      split. apply E_nil. split. intuition.
      rewrite map2_nil_l.  reflexivity.
      apply Nat.eq_dec. apply Nat.eq_dec.
      destruct a. simpl in H. rewrite map2_l_refl in H.
      inversion H;subst.  apply inj_pair2_eq_dec in H2. 
      apply inj_pair2_eq_dec in H2. destruct H2.
      exists ((StateMap.Raw.map2 option_app
      [(c, QUnit_One_fun s0 e0 U1 q)] mu')).
      exists nil. 
      split.  intuition. split.  apply E_nil.
      rewrite map2_nil_r.  reflexivity.
      apply Nat.eq_dec. apply Nat.eq_dec.
      destruct a0. destruct a. simpl in H.
      destruct (Cstate_as_OT.compare c0 c).
      inversion H;subst. 
      apply inj_pair2_eq_dec in H2. 
      apply inj_pair2_eq_dec in H2. destruct H2.
      apply IHx in H9. destruct H9. destruct H0.
      destruct H0. destruct H1. 
      remember (StateMap.Raw.map2 option_app
      [(c0, QUnit_One_fun s0 e0 U1 q0)] x0).
      exists t. exists x1.
      split. rewrite Heqt. apply E_Qunit_One.
      intuition. intuition.  intuition. split. intuition. 
      rewrite H2. rewrite Heqt. apply map2_assoc.
       inversion_clear Hx. assumption. assumption.
      apply Nat.eq_dec. apply Nat.eq_dec.
      inversion H;subst. 
      apply inj_pair2_eq_dec in H2. 
      apply inj_pair2_eq_dec in H2. destruct H2.
      apply IHx in H9. destruct H9. destruct H0.
      destruct H0. destruct H1.
      remember (StateMap.Raw.map2 option_app
      [(c0, QUnit_One_fun s0 e0 U1 (q0))] x0).
      remember (StateMap.Raw.map2 option_app
      [(c, QUnit_One_fun s0 e0 U1 (q))] x1).
      exists t. exists t0.
      split. rewrite Heqt. 
      apply E_Qunit_One. intuition. intuition. intuition. 
      split. rewrite Heqt0. apply E_Qunit_One. intuition. intuition.
      intuition. 
      rewrite H2. rewrite Heqt. rewrite Heqt0.
      repeat rewrite map2_assoc. repeat rewrite <-(map2_assoc _ _ _ x0).
      rewrite (map2_comm x0 ([(c, QUnit_One_fun s0 e0 U1 q)])).
      rewrite <-map2_assoc. rewrite <-map2_assoc.
      rewrite (map2_assoc _ _ _  _ ((x0 +l x1))).
      f_equal. simpl. unfold Cstate_as_OT.eq in e1.
      rewrite e1.  MC.elim_comp. unfold q_plus.
      rewrite QUnit_One_fun_plus. reflexivity. 
      inversion_clear Hx. assumption.
      inversion_clear Hy. assumption.  
      apply Nat.eq_dec. apply Nat.eq_dec.

      inversion H;subst. apply inj_pair2_eq_dec in H2. 
      apply inj_pair2_eq_dec in H2. destruct H2.
      apply IHy in H9. 
      destruct H9. destruct H0.
      destruct H0. destruct H1.
      exists x0. 
      remember (StateMap.Raw.map2 option_app [(c, QUnit_One_fun s0 e0 U1 ( q))] x1).
      exists t. 
      rewrite Heqt. split. intuition.
      split. apply E_Qunit_One. intuition. intuition. intuition.
      rewrite H2. rewrite (map2_comm ([(c, QUnit_One_fun s0 e0 U1 (q))]) x1).
      rewrite (map2_assoc _ _ x0). apply map2_comm.
      assumption. inversion_clear Hy. assumption. 
      apply Nat.eq_dec. apply Nat.eq_dec. } 

    -{induction x; induction y; intros mu Hx Hy H.
      exists nil. exists nil.
      split. apply E_nil. split. apply E_nil.
      simpl. simpl in H. inversion_clear H. reflexivity. 
      destruct a. simpl in H. rewrite map2_r_refl in H.
      inversion H;subst. apply inj_pair2_eq_dec in H5. 
      apply inj_pair2_eq_dec in H5. destruct H5.
      exists nil. exists ((StateMap.Raw.map2 option_app
      [(c, QUnit_Ctrl_fun s0 e0 s1 e1 U1 q)] mu')).
      split. apply E_nil. split. intuition.
      rewrite map2_nil_l.  reflexivity.
      apply Nat.eq_dec. apply Nat.eq_dec.
      destruct a. simpl in H. rewrite map2_l_refl in H.
      inversion H;subst.  apply inj_pair2_eq_dec in H5. 
      apply inj_pair2_eq_dec in H5. destruct H5.
      exists ((StateMap.Raw.map2 option_app
      [(c, QUnit_Ctrl_fun s0 e0 s1 e1 U1 q)] mu')).
      exists nil. 
      split.  intuition. split.  apply E_nil.
      rewrite map2_nil_r.  reflexivity.
      apply Nat.eq_dec. apply Nat.eq_dec.
      destruct a0. destruct a. simpl in H.
      destruct (Cstate_as_OT.compare c0 c).
      inversion H;subst. 
      apply inj_pair2_eq_dec in H5. 
      apply inj_pair2_eq_dec in H5. destruct H5.
      apply IHx in H11. destruct H11. destruct H0.
      destruct H0. destruct H1. 
      remember (StateMap.Raw.map2 option_app
      [(c0, QUnit_Ctrl_fun s0 e0 s1 e1 U1 q0)] x0).
      exists t. exists x1.
      split. rewrite Heqt. apply E_QUnit_Ctrl.
      intuition. intuition.  intuition. split. intuition. 
      rewrite H2. rewrite Heqt. apply map2_assoc.
      inversion_clear Hx. assumption.
      assumption.
      apply Nat.eq_dec. apply Nat.eq_dec.
      inversion H;subst. 
      apply inj_pair2_eq_dec in H5. 
      apply inj_pair2_eq_dec in H5. destruct H5.
      apply IHx in H11. destruct H11. destruct H0.
      destruct H0. destruct H1.
      remember (StateMap.Raw.map2 option_app
      [(c0, QUnit_Ctrl_fun s0 e0 s1 e1 U1 q0)] x0).
      remember (StateMap.Raw.map2 option_app
      [(c, QUnit_Ctrl_fun s0 e0 s1 e1 U1 q)] x1).
      exists t. exists t0.
      split. rewrite Heqt. 
      apply E_QUnit_Ctrl. intuition. intuition. intuition. 
      split. rewrite Heqt0. apply E_QUnit_Ctrl. intuition. intuition.
      intuition. 
      rewrite H2. rewrite Heqt. rewrite Heqt0.
      repeat rewrite map2_assoc. repeat rewrite <-(map2_assoc _ _ _ x0).
      rewrite (map2_comm x0 ([(c, QUnit_Ctrl_fun s0 e0 s1 e1 U1 q)])).
      rewrite <-map2_assoc. rewrite <-map2_assoc.
      rewrite (map2_assoc _ _ _ _((x0 +l x1))).
      f_equal. simpl. unfold Cstate_as_OT.eq in e2.
      rewrite e2.  MC.elim_comp. unfold q_plus.
      rewrite QUnit_Ctrl_fun_plus. reflexivity. 
      inversion_clear Hx. assumption. inversion_clear Hy.
      assumption.  
      apply Nat.eq_dec. apply Nat.eq_dec.

      inversion H;subst. apply inj_pair2_eq_dec in H5. 
      apply inj_pair2_eq_dec in H5. destruct H5.
      apply IHy in H11. 
      destruct H11. destruct H0.
      destruct H0. destruct H1.
      exists x0. 
      remember (StateMap.Raw.map2 option_app [(c, QUnit_Ctrl_fun s0 e0 s1 e1 U1 q)] x1).
      exists t. 
      rewrite Heqt. split. intuition.
      split. apply E_QUnit_Ctrl. intuition. intuition. intuition.
      rewrite H2. rewrite (map2_comm ([(c, QUnit_Ctrl_fun s0 e0 s1 e1 U1 q)]) x1).
      rewrite (map2_assoc _ _ x0). apply map2_comm.
      assumption. inversion_clear Hy. assumption. 
      apply Nat.eq_dec. apply Nat.eq_dec. }


      -{induction x; induction y; intros mu Hx Hy H.
      exists nil. exists nil.
      split. apply E_nil. split. apply E_nil.
      simpl. simpl in H. inversion_clear H. reflexivity. 
      destruct a. simpl in H. rewrite map2_r_refl in H.
      inversion H;subst. 
      exists nil. exists ((
       mu'' +l mu')).
      split. apply E_nil. split. intuition.
      rewrite map2_nil_l.  reflexivity.
      destruct a. simpl in H. rewrite map2_l_refl in H.
      inversion H;subst.  
      exists (mu'' +l mu').
      exists nil.
      split.  intuition. split.  apply E_nil.
      rewrite map2_nil_r.  reflexivity.
      destruct a0. destruct a. simpl in H.
      destruct (Cstate_as_OT.compare c0 c);
      inversion H;subst.  
      apply IHx in H8. destruct H8. destruct H0.
      destruct H0. destruct H1. 
      remember (mu'' +l x0).
      exists t. exists x1.
      split. rewrite Heqt. apply E_Meas.
      intuition. intuition. assumption. split. intuition. 
      rewrite H2. rewrite Heqt. apply map2_assoc.
      inversion H;subst. inversion_clear Hx. assumption.
      assumption.
      apply IHx in H8. destruct H8. destruct H0.
      destruct H0. destruct H1.
      pose (big_app'_exsist (2 ^ (e0 - s0)) (fun j : nat =>
      (c_update i j c0, QMeas_fun s0 e0 j (q0 )))).
      pose (big_app'_exsist (2 ^ (e0 - s0)) (fun j : nat =>
      (c_update i j c, QMeas_fun s0 e0 j (q)))).
      destruct e2. destruct e3.
      remember (x2+l x0).
      remember (x3+l x1).
      exists t. exists t0.
      split. rewrite Heqt. 
      apply E_Meas. intuition. intuition. assumption. 
      split. rewrite Heqt0. apply E_Meas. intuition.
      intuition.  assumption.
      rewrite H2. rewrite Heqt. rewrite Heqt0.
      repeat rewrite map2_assoc. repeat rewrite <-(map2_assoc _ _ _ x0).
      rewrite (map2_comm x0 x3).
      rewrite <-map2_assoc. rewrite <-map2_assoc.
      rewrite (map2_assoc _ _ _ _ ((x0 +l x1))).
      f_equal.  symmetry.
       apply big_app'_plus with ((2 ^ (e0 - s0))) 
       ((fun j : nat =>
       (c_update i j c0, QMeas_fun s0 e0 j q0))) 
       ((fun j : nat =>
       (c_update i j c, QMeas_fun s0 e0 j q))).
      simpl. intros. apply mixed_super_ge_0'; try lia.
      auto_wf. 
      inversion_clear Hx. apply WWF_qstate_to_WF_qstate. apply H6.
       intros. apply mixed_super_ge_0'; try lia; auto_wf.
      inversion_clear Hy. apply WWF_qstate_to_WF_qstate. apply H6.
      intros. simpl.  unfold Cstate_as_OT.eq in e1. rewrite e1.
      reflexivity.
      f_equal. assumption. assumption. simpl.
      apply big_app_eq_bound'' with 
      (fun j : nat => (c_update i j c0, QMeas_fun s0 e0 j (q0 .+ q))).
      assumption. intros.
      rewrite (QMeas_fun_plus); try lia. reflexivity.
      inversion_clear Hx. assumption.
      inversion_clear Hy. assumption.

      apply IHy in H8. 
      destruct H8. destruct H0.
      destruct H0. destruct H1.
      exists x0. 
      remember (mu'' +l x1).
      exists t. 
      rewrite Heqt. split. intuition.
      split. apply E_Meas. intuition. intuition.
      assumption.
      rewrite H2. rewrite (map2_comm mu''  x1).
      rewrite (map2_assoc _ _ x0). apply map2_comm.
      assumption. inversion_clear Hy. assumption. }
Qed.

 
Lemma ceval_dscale_aux{s' e':nat}:  forall c  (y mu: list (cstate *qstate s' e')) (p:R),
(0<p)%R->
ceval_single c (StateMap.Raw.map (fun x: qstate s' e' => p .* x) y) mu ->
exists mu', (and (ceval_single c y mu')
(mu=StateMap.Raw.map (fun x: qstate s' e' => p .* x) mu')).
Proof. induction c.
  -{intros y mu p Hp; intros. apply ceval_skip_1 in H. exists y. 
    split. apply ceval_skip. intuition. }
  -{induction y; intros mu p Hp; intros. exists []. split. apply E_nil.
    inversion_clear H. reflexivity. destruct a0. inversion H; subst.
    assert(exists y' : list (cstate * qstate s' e'),
    ceval_single <{ i := a }> y y' /\
    mu' =
    StateMap.Raw.map (fun x : qstate s' e' => p .* x)
    y'). apply IHy. assumption. assumption. 
    destruct H0. destruct H0.
    exists  ([(c_update i (@aeval s' e' (c, q) a) c,  q)] +l x).
    split.  apply E_Asgn. intuition.
    rewrite H1. rewrite <-map_map2_distr.
     simpl StateMap.Raw.map.  
     rewrite (state_eq_aexp (c, p .* q)  (c, q)).
    reflexivity. reflexivity. }
    -{   induction y; intros. 
    exists [].  split. econstructor.  
    simpl in *. inversion_clear H0. reflexivity.
    destruct a0.   simpl in *. inversion H0; subst.
    exists ((c, q) :: y). split. econstructor. assumption. 
    simpl. reflexivity.  }
    -{ destruct y; intros mu p0 Hp; intros. inversion H; subst.
    exists []. split. apply E_nil. reflexivity.
    destruct p. inversion H; subst. 
    assert((@cons (prod cstate (qstate s' e'))
    (@pair cstate (qstate s' e') c
    (@scale (Nat.pow (S (S O)) (e'-s'))
    (Nat.pow (S (S O)) (e'-s')) 
    (RtoC p0) q))
    (@StateMap.Raw.map (qstate s' e')
    (Matrix (Nat.pow (S (S O)) (e'-s'))
    (Nat.pow (S (S O)) (e'-s')))
    (fun x : qstate s' e' =>
    @scale (Nat.pow (S (S O)) (e'-s'))
    (Nat.pow (S (S O)) (e'-s')) 
    (RtoC p0) x) y))=
    StateMap.Raw.map
          (fun x : qstate s' e' => p0 .* x) ((c,q)::y)).
    reflexivity.  
    rewrite H0 in H6. 
    assert( exists mu' : list (cstate * qstate s' e'),
    ceval_single c1 ((c, q) :: y) mu' /\
    mu1 =
    StateMap.Raw.map
    (fun x : qstate s' e' => p0 .* x) mu'). apply IHc1.
    assumption. assumption. destruct H1.  destruct H1. 
    rewrite H2 in H7. 
    assert( exists mu' : list (cstate * qstate s' e'),
    ceval_single c2 x mu' /\
    mu =
    StateMap.Raw.map
    (fun x : qstate s' e' => p0 .* x) mu'). apply IHc2.
    assumption. assumption. destruct H3.  destruct H3.
    exists (x0). split. apply E_Seq with x.
    assumption. assumption. apply H4. }

  -{induction y; intros mu p Hp H. inversion H; subst.
      exists []. split. apply E_nil. reflexivity.
      destruct a. inversion H; subst.

      assert(exists y' : list (cstate * qstate s' e'),
      ceval_single <{ if b then c1 else c2 end }> y y' /\
      mu'' =
      StateMap.Raw.map (fun x : qstate s' e' => p .* x)
      y'). apply IHy. assumption. assumption.
      destruct H0. destruct H0.
      assert( exists q' : list (cstate * qstate s' e'),
      ceval_single c1 [(c,q)] q' /\
      mu' =
      StateMap.Raw.map
      (fun x : qstate s' e' => p .* x) q'). 
      apply IHc1. assumption. simpl. assumption. 
      destruct H2. destruct H2. 
      exists  (x0 +l x).
      split.  apply E_IF_true.
      rewrite (@state_eq_bexp s' e' s' e' _ (c, p .* q)). intuition.
      reflexivity. assumption. assumption. assumption.
      rewrite H1. rewrite H3.   apply map_map2_distr.

      assert(exists y' : list (cstate * qstate s' e'),
      ceval_single <{ if b then c1 else c2 end }> y y' /\
      mu'' =
      StateMap.Raw.map (fun x : qstate s' e' => p .* x)
      y'). apply IHy. assumption. assumption.
      destruct H0. destruct H0.
      assert( exists q' : list (cstate * qstate s' e'),
      ceval_single c2 [(c,q)] q' /\
      mu' =
      StateMap.Raw.map
      (fun x : qstate s' e' => p .* x) q'). 
      apply IHc2. simpl. assumption. assumption. 
      destruct H2. destruct H2. 
      exists  (x0 +l x).
      split.  apply E_IF_false.
      rewrite (@state_eq_bexp s' e' s' e' _ (c, p .* q)). intuition.
      reflexivity. assumption. assumption. assumption.
      rewrite H1. rewrite H3.   apply map_map2_distr. }

    -{intros y mu p Hp H. apply ceval_scale_while with ((StateMap.Raw.map
    (fun x : qstate s' e' => p .* x) y)). intros.
    apply IHc. assumption. assumption. assumption. reflexivity.
    assumption. }

    -{induction y; intros mu p Hp H. exists []. split. apply E_nil.
    inversion_clear H. reflexivity. destruct a. inversion H; subst.
    assert(exists y' : list (cstate * qstate s' e'),
    ceval_single <{ [[ s e ]] :Q= 0 }> y y' /\
    mu' =
    StateMap.Raw.map (fun x : qstate s' e' => p .* x)
    y'). apply IHy; try assumption.
    destruct H0. destruct H0.
    exists  ([(c, QInit_fun s e  q)] +l x).
    split.  apply E_Qinit. intuition. intuition.
    rewrite H1.  
    assert ([(c, @QInit_fun s' e' s e (p .* q))]=  StateMap.Raw.map (fun x0 : qstate s' e' => p .* x0) [(c, QInit_fun s e q)]).
    simpl. rewrite QInit_fun_scale. reflexivity. 
    rewrite H2. apply map_map2_distr. }

  -{induction y; intros mu p Hp H. exists []. split. apply E_nil.
    inversion_clear H. reflexivity. destruct a. inversion H; subst.
    apply inj_pair2_eq_dec in H2. apply inj_pair2_eq_dec in H2.
    destruct H2.
    assert(exists y' : list (cstate * qstate s' e'),
    ceval_single (QUnit_One s e U1) y y' /\
    mu' =
    StateMap.Raw.map (fun x : qstate s' e' => p .* x)
      y'). apply IHy; try assumption.
    destruct H0. destruct H0.
    exists  ([(c, QUnit_One_fun s e U1 ( q))] +l x).
    split.  apply E_Qunit_One. intuition.
    assumption. assumption. 
    rewrite H1.  
    assert ([(c, @QUnit_One_fun s' e' s e U1 (p .* q))]=  
    StateMap.Raw.map (fun x0 : qstate s' e' => p .* x0) 
    [(c, QUnit_One_fun s e U1 ( q))]).
    simpl. rewrite QUnit_One_fun_scale. reflexivity. 
    rewrite H2. apply map_map2_distr.
    apply Nat.eq_dec. apply Nat.eq_dec. }

  -{induction y; intros mu p Hp H. exists []. split. apply E_nil.
    inversion_clear H. reflexivity. destruct a. inversion H; subst.
    apply inj_pair2_eq_dec in H5. apply inj_pair2_eq_dec in H5.
    destruct H5.
    assert(exists y' : list (cstate * qstate s' e'),
    ceval_single (QUnit_Ctrl s0 e0 s1 e1 U1) y y' /\
    mu' =
    StateMap.Raw.map (fun x : qstate s' e' => p .* x)
    y'). apply IHy; try assumption.
    destruct H0. destruct H0.
    exists  ([(c, QUnit_Ctrl_fun s0 e0 s1 e1 U1 (q))] +l x).
    split.  apply E_QUnit_Ctrl. intuition.
    assumption. assumption. 
    rewrite H1. 
    assert ([(c, @QUnit_Ctrl_fun s' e' s0 e0 s1 e1 U1 (p .* q))]=  
    StateMap.Raw.map (fun x0 : qstate s' e' => p .* x0) 
    [(c, QUnit_Ctrl_fun s0 e0 s1 e1 U1 q)]).
    simpl. rewrite QUnit_Ctrl_fun_scale . reflexivity.
   rewrite H2. apply  map_map2_distr.
    apply Nat.eq_dec. apply Nat.eq_dec. }


  -{induction y; intros mu p Hp H. exists []. split. apply E_nil.
    inversion_clear H. reflexivity. destruct a. inversion H; subst.
    assert(exists y' : list (cstate * qstate s' e'),
    ceval_single <{ i :=M [[s e]] }> y y' /\
    mu' =
    StateMap.Raw.map (fun x : qstate s' e' => p .* x)
    y'). apply IHy; try assumption.
    destruct H0. destruct H0.
    pose (big_app'_exsist (2 ^ (e - s)) (fun j : nat =>
    (c_update i j c, QMeas_fun s e j (q)))).
    destruct e0.
    exists  (x0 +l x).
    split.  apply E_Meas. intuition. intuition.
    assumption.
    rewrite H1.  
    rewrite <-map_map2_distr.
    f_equal. symmetry.
    apply (@big_app'_scale s' e') with ((2 ^ (e - s)))
    (fun j : nat =>
        (c_update i j c, QMeas_fun s e j q)).
    lra. assumption. unfold s_scale.
    simpl. apply big_app_eq_bound'' with 
    (fun j : nat => (c_update i j c, QMeas_fun s e j (p .* q))). 
    assumption. intros. unfold q_scale.
     rewrite QMeas_fun_scale; try lia.
    reflexivity.  } 
    
   
Qed.



 Lemma ceval_4{s' e':nat}:  forall c sigma (rho: qstate s' e') 
(mu mu': list (cstate *qstate s' e')),
Sorted (StateMap.Raw.PX.ltk (elt:=qstate s' e')) ((sigma, rho)::mu)->
WF_dstate_aux ((sigma, rho)::mu) ->
ceval_single c ((sigma, rho)::mu) mu' ->
exists mu1 mu2 , (ceval_single c [(sigma,rho)] mu1
/\ ceval_single c mu mu2 /\
mu'=StateMap.Raw.map2 option_app mu1 mu2).
Proof. intros c sigma rho mu mu' H Hw. intros.
       assert((sigma, rho) :: mu= ([(sigma, rho)] +l mu)).
       destruct mu. simpl. reflexivity. destruct p.
       inversion_clear H. inversion_clear H2. simpl in *.
       destruct (Cstate_as_OT.compare sigma c0). 
       rewrite map2_r_refl. reflexivity.  unfold Cstate_as_OT.eq in e.
       rewrite e in H. apply Cstate_as_OT.lt_not_eq  in H. simpl in *. intuition.
       unfold StateMap.Raw.PX.ltk in H. simpl in H.
       rewrite <-H in l. apply Cstate_as_OT.lt_not_eq  in l. intuition.
       rewrite H1 in H0. apply ceval_app_aux in H0. 
       destruct H0. destruct H0. destruct H0. 
       exists x. exists x0. intuition.
       apply WF_state_dstate_aux. inversion_clear Hw.
       assumption. inversion_clear Hw. assumption.
Qed. 



Lemma ceval_app{s e:nat}:  forall c  (x y mu mu': dstate s e) ,
WF_dstate x-> WF_dstate y->
dstate_eq mu (d_app x y)->
ceval c mu mu' ->
exists mu1 mu2 , ( and (ceval c x mu1) 
(ceval c y mu2 
/\ dstate_eq mu' (d_app mu1 mu2))).
Proof. unfold dstate_eq.
    intros c (x, IHx) (y,IHy) (mu,IHmu) (mu', IHmu') Hx Hy;
    simpl in *. intros.
    inversion_clear H0.  simpl in *. 
    rewrite H in H2. 
    assert( exists mu1 mu2 , (and (ceval_single c x mu1)
    (ceval_single c y mu2 
    /\mu'=StateMap.Raw.map2 option_app mu1 mu2))).
    apply ceval_app_aux; try assumption.
    destruct H0. destruct H0. 
    destruct H0. destruct H3.
    assert(Sorted.Sorted (StateMap.Raw.PX.ltk (elt:=qstate s e)) x0).
    apply ceval_sorted with c x.
    assumption. assumption.
    assert(Sorted.Sorted (StateMap.Raw.PX.ltk (elt:=qstate s e)) x1).
    apply ceval_sorted with c y.
    assumption. assumption.
    exists (StateMap.Build_slist H5).
    exists (StateMap.Build_slist H6).
    simpl. split. econstructor.
    assumption. assumption.  
    split. econstructor.
    assumption. assumption. 
    assumption.
Qed.



Lemma ceval_scale{s e:nat}:  forall c  (x mu mu': dstate s e) (p:R),
WF_dstate x-> (0<p)%R->
dstate_eq mu (d_scale_not_0 p x)->
ceval c mu mu' ->
exists y, (and (ceval c x y)
(dstate_eq mu' (d_scale_not_0 p y))).
Proof. unfold dstate_eq.
intros c (x, IHx) (mu,IHmu) (mu', IHmu') p Hw Hp; simpl.
intros. inversion_clear H0. simpl in *.
rewrite H in H2.
assert(exists y, (and (ceval_single c x y)
(mu'=StateMap.Raw.map (fun x: qstate s e => p .* x) y))).
apply ceval_dscale_aux; try assumption.  
 destruct H0. destruct H0.
assert(Sorted.Sorted (StateMap.Raw.PX.ltk (elt:=qstate s e)) x0).
apply ceval_sorted with c x.
assumption. assumption. 
exists (StateMap.Build_slist H4).
split. econstructor. assumption.
assumption. assumption.
Qed.


Local Open Scope R_scope.
Lemma sum_over_list_ge_0: forall p_n,
Forall (fun x : R => 0 <= x) p_n->
sum_over_list p_n >=0 .
Proof. induction p_n. simpl in *. rewrite sum_over_list_nil. lra. 
       intros. rewrite sum_over_list_cons.
       inversion_clear H. 
       apply IHp_n in H1.
       assert (0=0+0). rewrite Rplus_0_l. reflexivity.
       rewrite H.
       apply Rplus_ge_compat. intuition.
       assumption.
Qed.

Lemma sum_over_list_gt_0: forall p_n,
Forall (fun x : R => 0 < x) p_n->
p_n <> nil->
sum_over_list p_n >0 .
Proof. induction p_n. simpl in *. rewrite sum_over_list_nil.
       intros. destruct H0. reflexivity.
       intros. rewrite sum_over_list_cons.
       inversion_clear H. destruct p_n. 
       rewrite sum_over_list_nil. rewrite Rplus_0_r.
       assumption. 
       apply IHp_n in H2.
       assert (0=0+0). rewrite Rplus_0_l. reflexivity.
       rewrite H.
       apply Rplus_gt_compat. intuition.
       assumption. discriminate.
Qed.

Local Open Scope R_scope.
Fixpoint big_dapp{s e:nat} (g:list R) (f:list (dstate s e))  : dstate s e := 
match g ,f with 
|[], [] => d_empty s e
|[], _ => d_empty s e
| _ ,[]=>  d_empty s e 
| hg::tg, hf:: tf =>d_app (d_scale_not_0 hg hf) (big_dapp tg tf)
end.
   

Lemma big_dapp'_to_app{s e:nat}: forall (p_n:list R) (mu_n:list (dstate s e)) ,  
length p_n= length mu_n->
(Forall (fun x => 0<x%R) p_n)->
big_dapp' p_n mu_n (big_dapp p_n mu_n).
Proof.  induction p_n; intros. inversion H0; subst. destruct mu_n.
 simpl. apply big_dapp_nil. discriminate H.
 destruct mu_n. discriminate H. 
  simpl.  apply big_dapp_cons. econstructor.  inversion_clear H0.
  lra. apply IHp_n. injection H. intuition.
  inversion_clear H0.
assumption.
Qed.


Lemma WF_d_scale_not_0{s e}: forall (mu:dstate s e) p, 
(0<p<=1)
->WF_dstate mu 
->WF_dstate(d_scale_not_0 p mu).
Proof. unfold WF_dstate.
        unfold d_trace.
        unfold d_scale_not_0.
        simpl. intros  (mu,IHmu) p H0 H.
        unfold map.  simpl. 
        apply WF_dstate_map. intuition.
        intuition.
Qed.

Lemma ceval_big_dapp{s e:nat}: forall (p_n :list R) (mu_n:list (dstate s e)) (mu mu':dstate s e)   c,
Forall (fun x : R => 0 < x) p_n ->
sum_over_list p_n <=1 -> 
Forall_two (fun x y=> 0<y -> WF_dstate x) mu_n p_n->
length p_n =length mu_n->
dstate_eq mu (big_dapp p_n mu_n)->
ceval c mu mu' ->
exists (mu_n': list (dstate s e)), 
 and (Forall_two (fun x y=> ceval c x y) mu_n  mu_n') 
 (dstate_eq mu' (big_dapp p_n mu_n')).
Proof. induction  p_n; intros mu_n mu mu' c Hp Hs Hw; intros; destruct mu_n. 
       simpl in *; exists ([]);
       split; try econstructor. 
       inversion H1; subst. unfold dstate_eq in *.
       simpl in *.    unfold StateMap.Raw.empty in *. 
       rewrite H0 in H3. inversion_clear H3. reflexivity.
       discriminate H. discriminate H. 
       simpl. 
       assert(exists mu1 mu2 ,  and (ceval c (d_scale_not_0 a d) mu1)
       ((ceval c (big_dapp p_n mu_n) mu2)  /\
        (dstate_eq mu' (d_app mu1 mu2)))).
       apply (ceval_app c (d_scale_not_0 a d) (big_dapp p_n mu_n ) mu mu').
       apply WF_d_scale_not_0. split. inversion_clear Hp. assumption.
       rewrite sum_over_list_cons in Hs. 
       destruct p_n. rewrite sum_over_list_nil in Hs. 
       rewrite Rplus_0_r in Hs. assumption.
       inversion_clear Hp. apply sum_over_list_gt_0 in H3.
       lra. discriminate.
       inversion_clear Hw. apply H2.  inversion_clear Hp. assumption. 
       apply WF_dstate_big_dapp with p_n mu_n.  inversion_clear Hw. assumption.
       apply big_dapp'_to_app. injection H. intuition.
         inversion_clear Hp. assumption. 
         inversion_clear Hp. apply Forall_impl with ((fun x : R => 0 < x)).
         intros. lra. assumption.
       rewrite sum_over_list_cons in Hs. inversion_clear Hp.
       lra.
       assumption. assumption.
       destruct H2. destruct H2.
       destruct H2.
       assert(exists y, (and (ceval c d y)
       (dstate_eq x (d_scale_not_0 a y)))).
       apply ceval_scale with ((d_scale_not_0 a d)).
       inversion_clear Hw. apply H4. inversion_clear Hp.  assumption. 
       inversion_clear Hp. lra.
       unfold dstate_eq. reflexivity.
       assumption. destruct H4. 
       assert( exists mu_n' : list (dstate s e),
       and (Forall_two (fun x y : dstate s e => ceval c x y) mu_n mu_n') 
       (dstate_eq x0 (big_dapp p_n mu_n' ))).
       apply IHp_n with ((big_dapp p_n mu_n)).
       inversion_clear Hp. assumption.
       rewrite sum_over_list_cons in Hs. inversion_clear Hp.
       lra.
       inversion_clear Hw. assumption. 
       injection H; intuition.
       unfold dstate_eq . 
       reflexivity.
       intuition. destruct H5.
       exists (x1::x2). 
       split. econstructor.  intuition.
       intuition. apply dstate_eq_trans with ((d_app x x0)).
       intuition. 
       apply d_app_eq. intuition.
       intuition.
Qed.




Lemma  WF_dstate_Forall{s e:nat}: forall (mu_n: list (dstate s e)),
Forall  (fun x : dstate s e => WF_dstate x)  mu_n ->
Forall (fun x : list (cstate * qstate s e) =>
   WF_dstate_aux x) (dstate_to_list mu_n).
Proof. induction mu_n.  simpl. econstructor. 
        econstructor. inversion_clear H. apply H0.
        apply IHmu_n. inversion_clear H. assumption.
Qed.



Lemma  WF_big_ceval{s e:nat}: forall c (mu_n mu_n': list (list (state s e))),
Forall_two (fun x y : list (cstate * qstate s e) =>
        ceval_single c x y) mu_n mu_n'->
        Forall (fun x => WF_dstate_aux x) mu_n ->
        Forall (fun x => WF_dstate_aux x) mu_n' .
Proof. induction mu_n; intros. inversion_clear H. 
       econstructor. 
       inversion H; subst. inversion_clear H0.
       econstructor. 
       apply WF_ceval with c a; try assumption.
       apply IHmu_n; try assumption.
Qed.

Lemma  big_ceval_sorted{s e:nat}: forall c (mu_n mu_n': list (list (state s e))),
Forall_two (fun x y : list (cstate * qstate s e) =>
        ceval_single c x y) mu_n mu_n'->
        ((Forall (fun i : list (state s e) =>Sorted (StateMap.Raw.PX.ltk (elt:=qstate s e)) i) mu_n ))->
        ((Forall (fun i : list (state s e) =>Sorted (StateMap.Raw.PX.ltk (elt:=qstate s e)) i) mu_n' )).
Proof. induction mu_n; intros. inversion_clear H. 
       econstructor. 
       inversion H; subst. inversion_clear H0.
       econstructor. 
       apply ceval_sorted with c a; try assumption.
       apply IHmu_n; try assumption.
Qed.

Lemma Forall_ceval{s e:nat}:forall c (mu_n mu_n':list (dstate s e)),
(Forall (fun i=> WF_dstate i) mu_n) ->
Forall_two (fun x y  => ceval_single c x y) (dstate_to_list mu_n) (dstate_to_list mu_n')->
Forall_two (fun x y : dstate s e => ceval c x y) mu_n mu_n'.
Proof. induction mu_n; intros; destruct mu_n'; simpl  in *; inversion H0; subst.
      econstructor.  inversion_clear H. 
      econstructor. 
      econstructor; try assumption.
      apply IHmu_n; try assumption.
Qed.

(*---------------------mv(c)\subseteq S =>[[c]]mu|_{S}= ([[c]]mu)|_{S}---------------------------------------------------------*)


Local Open Scope com_scope.
Local Open Scope nat_scope.

#[export] Hint Extern 1 (pow_gt_0) => lia : wf_db.

Ltac type_sovle':=
  try (repeat rewrite  <-Nat.pow_add_r; f_equal ; lia).

Lemma PMtrace_Super_swap{s e:nat}: forall l r  (M: Square (2^(r-l))) (A:qstate s e) ,
s<=l /\l<=r /\ r<=e -> WF_Matrix M->
super M (Reduced A  l r)= @Reduced s e (super (I (2 ^ (l-s)) ⊗ M ⊗ I (2 ^ (e-r))) A) l r.
Proof. intros. unfold super. repeat rewrite Ptrace_l_r'; try lia.   
       assert((2 ^ (r-l)) = 1 * (2 ^ (r- l)) * 1). lia.  destruct H1.
       rewrite (Mmult_Msum_distr_l ((2 ^ (l-s))) _ M).
       rewrite Mmult_Msum_distr_r.
       apply big_sum_eq_bounded.  intros.  
       assert((2 ^ (r-l)) = 1 * (2 ^ (r- l)) * 1). lia. destruct H2. 
       rewrite Mmult_Msum_distr_l. rewrite Mmult_Msum_distr_r.
       apply big_sum_eq_bounded.  intros. 
       rewrite Mmult_assoc_5.   rewrite Mmult_assoc_5. f_equal.  f_equal.

       apply Logic.eq_trans with ((I 1 ⊗ M ⊗ I 1) × (⟨ x ∣_ (2^(l-s)) ⊗ I (2 ^ (r- l)) ⊗ ⟨ x0 ∣_ (2^(e-r)))).
       rewrite kron_1_l; auto_wf. rewrite kron_1_r. f_equal; try lia. 
       apply Logic.eq_trans with (⟨ x ∣_ (2^(l-s)) ⊗ I (2 ^ (r- l)) ⊗ ⟨ x0 ∣_ (2^(e-r))
       × (I (2 ^ (l-s)) ⊗ M ⊗ I (2 ^ (e-r)))).
       repeat rewrite kron_mixed_product. repeat rewrite Mmult_1_l; auto_wf.
       repeat rewrite Mmult_1_r; auto_wf.  f_equal; auto_wf. 
       f_equal; lia. 

       apply Logic.eq_trans with ((∣ x ⟩_ (2^(l-s)) ⊗ I (2 ^ (r- l)) ⊗ ∣ x0 ⟩_ (2^(e-r)))× (I 1 ⊗ (M) † ⊗ I 1)  ).
       rewrite kron_1_l; auto_wf. rewrite kron_1_r. f_equal; try lia. 
       apply Logic.eq_trans with ((I (2 ^ (l-s)) ⊗ M ⊗ I (2 ^ (e-r))) †
       × (∣ x ⟩_ (2^(l-s)) ⊗ I (2 ^ (r- l)) ⊗ ∣ x0 ⟩_ (2^(e-r)))). 
       repeat rewrite kron_adjoint. repeat rewrite id_adjoint_eq.
       repeat rewrite kron_mixed_product. repeat rewrite Mmult_1_l; auto_wf.
       repeat rewrite Mmult_1_r; auto_wf.  f_equal; auto_wf. 
       f_equal; lia. 
Qed.




Lemma Mmult_kron_5: forall {m1 n1 m2 n2 m3 n3 m4 n4 m5 n5:nat} (A: Matrix m1 n1)
(B: Matrix m2 n2) (C: Matrix m3 n3) (D: Matrix m4 n4) (E: Matrix m5 n5), 
WF_Matrix A -> WF_Matrix B -> WF_Matrix C -> WF_Matrix D -> WF_Matrix E->
A ⊗ (B ⊗ C ⊗ D) ⊗ E= (A ⊗ B) ⊗ C ⊗ (D ⊗ E).
Proof. intros. repeat rewrite <-kron_assoc; try reflexivity;
       auto_wf.
Qed.

Lemma Reduced_ceval_swap_Qinit{ s e:nat}: forall (q: qstate s e ) s0 e0 l r,
s<=l /\ l<=s0 /\ s0<=e0 /\ e0<=r /\ r<=e-> 
@WF_Matrix (2^(e-s)) (2^(e-s)) q -> 
@Reduced  s e (QInit_fun s0 e0 q) l r = QInit_fun s0 e0 (Reduced q l r) .
Proof. intros. unfold QInit_fun. unfold q_update.
       rewrite big_sum_Reduced.
       apply big_sum_eq_bounded. 
       intros. assert(0<(2^(e0 - s0))). lia.  
      rewrite PMtrace_Super_swap. f_equal.
      f_equal; type_sovle'.  
      assert(  2 ^ (s0 - l) * 2 ^ (e0 - s0) * 2 ^ (r - e0)= 2 ^ (r - l)).
      type_sovle'. destruct H3.
      rewrite Mmult_kron_5; auto_wf. 
      repeat rewrite id_kron. f_equal; type_sovle';
      f_equal; type_sovle'; f_equal; type_sovle'.
      lia. auto_wf. lia.   
Qed. 

Lemma Reduced_ceval_swap_QUnit_one{ s e:nat}: forall (q: qstate s e ) s0 e0 
(U:Square (2^(e0-s0))) l r,
s<=l/\l<=s0 /\ s0<=e0 /\ e0<=r /\ r<=e-> 
@WF_Matrix (2^(e-s)) (2^(e-s)) q -> 
WF_Unitary U->
@Reduced  s e (QUnit_One_fun s0 e0 U q) l r = QUnit_One_fun s0 e0 U (Reduced q l r) .
Proof. intros. unfold QUnit_One_fun.
       unfold q_update. 
       rewrite PMtrace_Super_swap. 
      f_equal; f_equal; type_sovle'.
      assert( 2 ^ (s0 - l) * 2 ^ (e0 - s0) * 2 ^ (r - e0)= 2 ^ (r - l) ).
      type_sovle'. destruct H2.
      rewrite Mmult_kron_5; auto_wf. 
      repeat rewrite id_kron. f_equal; type_sovle';
      f_equal; type_sovle'; f_equal; type_sovle'.
       apply H1. lia. destruct H1. auto_wf. 
Qed.

Lemma Reduced_ceval_swap_QUnit_Ctrl{ s e:nat}: forall (q: qstate s e ) s0 e0 s1 e1  
(U: nat -> Square (2^(e1-s1))) l r,
s<=l /\ l<=s0 /\ s0<=e0 /\ e0 <=s1 /\ s1 <= e1 /\ e1<=r /\ r<=e-> 
@WF_Matrix (2^(e-s)) (2^(e-s)) q -> 
(forall j, WF_Unitary (U j ))->
@Reduced  s e (QUnit_Ctrl_fun s0 e0  s1 e1 U q) l r 
= QUnit_Ctrl_fun s0 e0 s1 e1 U (Reduced q l r) .
Proof. intros. unfold QUnit_Ctrl_fun.
       unfold q_update.
      rewrite PMtrace_Super_swap.
      f_equal. f_equal; type_sovle'.
      rewrite kron_Msum_distr_l.
      rewrite kron_Msum_distr_r.
      apply big_sum_eq_bounded.
      intros. 
      remember (I (2 ^ (s0 - l)) ⊗ (∣ x ⟩_ (2^(e0 - s0)) × ⟨ x ∣_ (2^(e0 - s0))) ⊗ I (2 ^ (r - e0))).
      remember ( (I (2 ^ (s1 - l)) ⊗ U x ⊗ I (2 ^ (r - e1)))).
      apply Logic.eq_trans with 
      (@kron (2^(l-s)) (2^(l-s)) (2 ^ (s0 - l) * 2 ^ (e0 - s0) * 2 ^ (r - e0))
      (2 ^ (s1 - l) * 2 ^ (e1 - s1) * 2 ^ (r - e1))
      (I (2 ^ (l - s)) × I (2 ^ (l - s)))
       (m × m0)
      ⊗ (I (2 ^ (e - r)) × I (2 ^ (e - r)))).
      repeat rewrite <-kron_mixed_product.
      rewrite Heqm. rewrite Heqm0.
       rewrite Mmult_kron_5; auto_wf.
       repeat rewrite id_kron.  
      f_equal; type_sovle'. f_equal; type_sovle';
      f_equal; type_sovle'. 
      f_equal; type_sovle'. 
      assert(2 ^ (s1 - l) * 2 ^ (e1 - s1) * 2 ^ (r - e1)= 
      2 ^ (s0 - l) * 2 ^ (e0 - s0) * 2 ^ (r - e0)).
      type_sovle'. destruct H3.
      rewrite Mmult_kron_5; auto_wf.
      repeat rewrite id_kron.  
      f_equal; type_sovle'; f_equal; type_sovle'.
      f_equal; type_sovle'.
      apply H1. repeat rewrite Mmult_1_r; auto_wf.
      f_equal; type_sovle'. f_equal; type_sovle'.
      f_equal; type_sovle'. lia. 
      apply WF_Msum.
      intros. assert(WF_Unitary (U i)). auto.
      destruct H3. auto_wf.
Qed.


Lemma Reduced_ceval_swap_QMeas{ s e:nat}: forall (q: qstate s e ) s0 e0 j l r,
s<=l/\l<=s0 /\ s0<=e0 /\ e0<=r /\ r<=e-> 
@WF_Matrix (2^(e-s)) (2^(e-s)) q -> 
j<2^(e0-s0)->
@Reduced  s e (QMeas_fun s0 e0 j q) l r = QMeas_fun s0 e0 j (Reduced q l r) .
Proof. intros. unfold QMeas_fun.
       unfold q_update. 
       rewrite PMtrace_Super_swap.
      assert( 2 ^ (s0 - l) * 2 ^ (e0 - s0) * 2 ^ (r - e0)= 2 ^ (r - l) ).
      type_sovle'. destruct H2.
      f_equal. f_equal; type_sovle'.
      rewrite Mmult_kron_5; auto_wf. 
      repeat rewrite id_kron. f_equal; type_sovle';
      f_equal; type_sovle'; f_equal; type_sovle'.
      lia.  auto_wf. 
Qed.
#[export]Hint Unfold Reduced: M_db.

Lemma  subset_union: forall x y z, NSet.Subset (NSet.union x y) z ->
NSet.Subset x z /\ NSet.Subset y z.
Proof. intros. unfold NSet.Subset in *. 
       split. intros. 
       apply H. apply NSet.union_2.
       assumption.
       intros. apply H. apply NSet.union_3.
       assumption.
       
Qed.

Lemma In_empty: forall s, NSet.In s NSet.empty -> False .
Proof. intros. pose (NSet.empty_1). unfold NSet.Empty in *. 
        apply e in H. destruct H.
Qed.

Lemma In_Qsys: forall r l s, 
l<r->
NSet.In s (Qsys_to_Set l r)<-> l<=s<r.
Proof. unfold Qsys_to_Set. 
induction r; intros.
lia.
destruct l.
simpl. split. intros.
bdestruct (s=?r).
rewrite H1. 
lia.
destruct r.  
apply NSet.add_3 in H0.
simpl in H0.
apply In_empty in H0.
destruct H0.
 intuition.
apply NSet.add_3 in H0.
apply IHr in H0. lia. 
lia.
intuition.
intros.
bdestruct (s=?r).
rewrite H1.
apply NSet.add_1.
reflexivity.
destruct r. 
assert(s=0). lia.
rewrite H2.  
apply NSet.add_1.
reflexivity.
apply NSet.add_2.
apply IHr. lia.  
lia.


simpl.  pose H.
apply Lt_n_i in l0.
rewrite l0.

bdestruct (S l <?r).
split; intros.
bdestruct (s=? r).
rewrite H2. lia.
apply NSet.add_3 in H1.
apply IHr in H1.
lia. intuition. intuition.

bdestruct (s=? r).
rewrite H2. apply NSet.add_1. reflexivity.
apply NSet.add_2. 
apply IHr . assumption.
lia. 

assert(forall l r, l>=r ->(Qsys_to_Set_aux l r NSet.empty = NSet.empty)).
intros. induction r0. 
 simpl. reflexivity.
 simpl. 
 assert(l1 <? S r0 = false).
 apply Nat.ltb_ge. 
 assumption.
 rewrite H2. reflexivity.
rewrite H1.
bdestruct (s=? r).
rewrite H2.
split;intros. lia.
apply NSet.add_1. reflexivity.
split; intros. 
apply NSet.add_3 in H3.
apply In_empty in H3.
destruct H3.
intuition.
lia. 
assumption.    
Qed.


Lemma In_Qsys_l_r: forall r l , 
l<r->
NSet.In l (Qsys_to_Set l r) /\
NSet.In (r-1) (Qsys_to_Set l r).
Proof. unfold Qsys_to_Set. induction r; induction l; intros; simpl.
 lia. lia.   
 simpl. split. destruct r.
 simpl.  
 apply NSet.add_1. reflexivity.
 apply NSet.add_2. 
 eapply IHr. lia.  
 rewrite Nat.sub_0_r.
 apply NSet.add_1. reflexivity.
 destruct r. lia.  
 pose H.
 apply Lt_n_i in l0. rewrite l0.
 split.
 bdestruct (l =? r).
 rewrite H0. apply NSet.add_1.
 reflexivity.
 apply NSet.add_2.
 apply IHr. lia.  
 rewrite Nat.sub_0_r.
 apply NSet.add_1.
 reflexivity.    
Qed.

Lemma subset_Qsys:forall s e l r, 
l<r-> 
NSet.Subset (Qsys_to_Set l r) (Qsys_to_Set s e ) ->
 s<=l /\ r<=e.
Proof. intro. intro. intro. intro. intro. 
apply NF_1. intros.
 apply Classical_Prop.not_and_or in H0.
unfold not. intros. 
destruct H0. unfold not in H0.
assert(s>l). intuition. 
unfold NSet.Subset in H1.
pose (H1 l). 
assert(NSet.In l (Qsys_to_Set s e)).
apply i. apply In_Qsys_l_r. assumption.
apply In_Qsys in H3. lia.
assert(s<e\/ ~ (s<e)).
apply Classical_Prop.classic.
destruct H5. assumption.
assert(s >= e). lia.
apply Nat.ltb_ge in H6.
unfold Qsys_to_Set in H3.
destruct e.  
simpl in H3.  
apply In_empty in H3.
destruct H3.
 simpl in H3. rewrite H6 in H3.
 apply In_empty in H3. destruct H3.

assert(r>e). intuition. 
unfold NSet.Subset in H1.
pose (H1 (r-1)). 
assert(NSet.In (r-1) (Qsys_to_Set s e)).
apply i. apply In_Qsys_l_r. assumption.
apply In_Qsys in H3. lia.
assert(s<e\/ ~ (s<e)).
apply Classical_Prop.classic.
destruct H5. assumption.
assert(s >= e). lia.
apply Nat.ltb_ge in H6.
unfold Qsys_to_Set in H3.
destruct e.  
simpl in H3.  
apply In_empty in H3.
destruct H3.
 simpl in H3. rewrite H6 in H3.
 apply In_empty in H3. destruct H3.
Qed.

Ltac Reduced_ceval_swap_solve mu:=
  induction mu; intros;
  try  match goal with 
   H:ceval_single ?x ?y ?z |-_ => inversion H; subst; clear H end;
   try  match goal with 
   H: existT ?a ?b ?c = existT ?x ?y ?z|-_ => apply inj_pair2_eq_dec in H end;
   try  match goal with 
   H: existT ?a ?b ?c = existT ?x ?y ?z|-_ => apply inj_pair2_eq_dec in H; destruct H end;
   try apply Nat.eq_dec;
   [simpl; econstructor|];
   try match goal with 
   H: WF_dstate_aux ((?sigma, ?rho) :: ?mu) |- _ => inversion_clear H end;
   try match goal with 
   H2: NSet.Subset ?a ?b |- _ =>simpl in H2 end;
   try match goal with 
   H2: NSet.Subset (NSet.union ?a ?b) ?c |- _ => pose H2 as H2'; apply subset_union in H2';
   destruct H2' as [H2' H2'']; apply subset_Qsys in H2' ; try lia end;
   try match goal with 
   H2'': NSet.Subset ?a ?b |- _ => pose H2'' as H2''';  apply subset_Qsys in H2'''; try lia end;
   try rewrite d_reduced_map2; try simpl d_reduced;
   try rewrite Reduced_ceval_swap_QUnit_one;  
   try rewrite Reduced_ceval_swap_Qinit;
   try rewrite Reduced_ceval_swap_QUnit_Ctrl; try lia; auto_wf; try assumption;
   econstructor; try lia; try assumption; 
   try match goal with IHmu:_ |- _ => apply IHmu; try assumption end.


Local Open Scope nat_scope.
Lemma Reduced_ceval_swap: forall c s e (mu mu': list (cstate *qstate s e)) l r,
s<=l /\ l<=r /\ r<=e ->
NSet.Subset (snd (MVar c)) (Qsys_to_Set l r)->
WF_dstate_aux mu ->
ceval_single c mu mu'->
ceval_single c (d_reduced mu l r )
(d_reduced mu' l r ).
Proof. induction c; try Reduced_ceval_swap_solve mu. 
       { induction mu; intros. inversion_clear H2.
        simpl. econstructor.
        destruct a0. inversion H2 ;subst.
        rewrite d_reduced_map2.
        simpl d_reduced.
        rewrite (state_eq_aexp  _ (c,(Reduced q l r) )).
        econstructor. apply IHmu. assumption.
        assumption. inversion_clear H1. intuition.
        assumption. reflexivity.  }
       intros.  
       apply (IHc1 _ _ _ mu1 l r) in H8. simpl in H8. apply H8.
       lia.  apply subset_union in H0. apply H0. 
       econstructor; try assumption. 
       apply subset_union in H0. apply H0. 
       apply WF_ceval with c1 ((sigma, rho) :: mu); try econstructor; try assumption.
       assumption.
       {induction mu; intros. inversion H2; subst.
       simpl. econstructor.
       inversion H2; subst. 
       rewrite d_reduced_map2.
      econstructor. rewrite (state_eq_bexp _  (sigma, rho)).
      intuition. reflexivity. simpl in H0.   apply subset_union in H0. apply H0.  
      apply IHmu.  intuition.
      intuition. inversion_clear H1.  assumption. assumption. 
      assert(d_reduced [(sigma, rho)] l r = [(sigma, Reduced rho l r)]).
      reflexivity. rewrite <-H3. apply IHc1. assumption.
      simpl in H0. apply subset_union in H0.
       intuition. apply WF_state_dstate_aux.
        inversion_clear H1.  assumption. assumption. 
      rewrite d_reduced_map2.
      apply E_IF_false. rewrite (state_eq_bexp _  (sigma, rho)).
      intuition. reflexivity. simpl in H0.   apply subset_union in H0. apply H0.  
      apply IHmu.  intuition.
      intuition. inversion_clear H1. assumption. assumption. 
      assert(d_reduced [(sigma, rho)] l r = [(sigma, Reduced rho l r)]).
      reflexivity. rewrite <-H3. apply IHc2.
      assumption.  
      simpl in H0. apply subset_union in H0.
       intuition.  inversion_clear H1. 
       apply WF_state_dstate_aux. assumption. 
      assumption. 
          }
      {   intros.  remember <{while b do c end}> as original_command eqn:Horig. 
      induction H2;  try inversion Horig; subst. 
       simpl. econstructor.  
       simpl. rewrite d_reduced_map2.   
       apply E_While_true with ((d_reduced mu1 l r)). rewrite (state_eq_bexp _  (sigma, rho)).
       intuition. reflexivity. 
       apply IHceval_single1; try reflexivity; try assumption. 
       inversion_clear H1. assumption.
       assert(d_reduced [(sigma, rho)] l r = [(sigma, Reduced rho l r)]).
       reflexivity. rewrite <-H3. apply IHc. assumption. apply H0.
       apply WF_state_dstate_aux.
        inversion_clear H1.  assumption. assumption.
        apply IHceval_single3; try reflexivity; try assumption. 
        eapply WF_ceval; try apply H2_0; try assumption. 
        apply WF_state_dstate_aux.
        inversion_clear H1.  assumption.
      
        rewrite d_reduced_map2.   
        apply E_While_false. rewrite (state_eq_bexp _  (sigma, rho)).
        intuition. reflexivity. assumption.
        apply IHceval_single; try reflexivity; try assumption. 
        inversion_clear H1. assumption.
        }
      apply (d_reduced_app' _ l r) in H11; try lia. 
      destruct H11. destruct H1. simpl in H1. 
      eapply big_app_eq_bound''. rewrite<-H5 in H1. apply H1.
      intros.
      rewrite  <-Reduced_ceval_swap_QMeas;try lia; auto_wf; try reflexivity.
    intros. simpl. apply mixed_super_ge_0; auto_wf. 
     apply WWF_qstate_to_WF_qstate. apply H2.
Qed.

Lemma subset_empty':forall a b,
NSet.Equal a NSet.empty->
NSet.Subset a b.
Proof. unfold NSet.Subset. unfold NSet.Equal; intros. 
       apply H in H0. 
       apply In_empty in H0. destruct H0.  
       
Qed.

Lemma Qsys_to_Set_not_empty:forall s e,
s<e->
~ (NSet.Equal (Qsys_to_Set s e) NSet.empty).
Proof. intros. unfold NSet.Equal. intro. 
       pose (H0 s). pose (In_Qsys_l_r e s H). destruct a. 
       apply i in H1. apply In_empty in H1. destruct H1.  
       
Qed.

Lemma union_empty:forall x y ,
  NSet.Equal ( (NSet.union x y)) NSet.empty <->
  NSet.Equal x NSet.empty /\ NSet.Equal y NSet.empty.
  Proof.  unfold NSet.Equal. split; intros.  
   split; split; intros.
    apply H. apply NSet.union_2. assumption. 
    inversion_clear H0. 
    apply H. apply NSet.union_3. assumption.
    inversion_clear H0.
    destruct H. 
    split. intros. apply NSet.union_1 in H1. destruct H1.
    apply H. assumption.
    apply H0. assumption.
    intros. inversion_clear H1. 
  Qed. 

Lemma ceval_single_classic{s e:nat}:  forall c (mu mu':list (state s e)) l r , 
NSet.Equal (snd (MVar c)) NSet.empty->
ceval_single c mu mu'->
ceval_single c (d_reduced mu l r) (d_reduced mu' l r).
Proof. induction c. intros. apply ceval_skip_1 in H0. subst. 
      apply ceval_skip. 
      induction mu; intros; inversion_clear H0. econstructor.
      rewrite d_reduced_map2. simpl d_reduced .
      rewrite (state_eq_aexp _ (sigma, Reduced rho l r)); try reflexivity.
      econstructor. apply IHmu; try assumption. 

      induction mu; intros; inversion H0; subst. econstructor.  simpl. econstructor.
      assumption.
     
      intros. simpl in H. apply union_empty in H.
      destruct H.    apply ceval_seq_1 in H0. destruct H0. destruct H0.
      eapply ceval_seq with (d_reduced x l r). apply IHc1; try assumption.
      apply IHc2; try assumption.

      induction mu; intros; inversion_clear H0. econstructor.
      rewrite d_reduced_map2; simpl d_reduced .
      econstructor. 
      rewrite (state_eq_bexp _ (sigma, rho)); try reflexivity; try assumption.
      simpl in H. apply union_empty in H.  destruct H.   
      apply subset_empty'. assumption.
      apply IHmu; try assumption. 
      simpl in H. apply union_empty in H.  destruct H.   
      pose (IHc1 [(sigma, rho)] mu'0 ). simpl in c. apply c; try assumption.
      
      rewrite d_reduced_map2; simpl d_reduced .
      apply E_IF_false. 
      rewrite (state_eq_bexp _ (sigma, rho)); try reflexivity; try assumption.
      simpl in H. apply union_empty in H.  destruct H.   
      apply subset_empty'. assumption.
      apply IHmu; try assumption. 
      simpl in H. apply union_empty in H.  destruct H.   
      pose (IHc2 [(sigma, rho)] mu'0 ). simpl in c. apply c; try assumption.

      intros.  remember <{while b do c end}> as original_command eqn:Horig. 
    induction H0;  try inversion Horig; subst. 
    econstructor. rewrite d_reduced_map2; simpl d_reduced . 
    econstructor. 
    rewrite (state_eq_bexp _ (sigma, rho)); try reflexivity; try assumption.
    apply IHceval_single1; try reflexivity; try assumption.   
    pose (IHc [(sigma, rho)] mu1 ). simpl in c0. apply c0; try assumption.
    apply IHceval_single3; try reflexivity; try assumption.

     rewrite d_reduced_map2; simpl d_reduced . 
    apply E_While_false. 
    rewrite (state_eq_bexp _ (sigma, rho)); try reflexivity; try assumption. 
    apply subset_empty'. assumption.
    apply IHceval_single; try reflexivity; try assumption.   
   
    intros. simpl in *.  inversion_clear H0. econstructor.
     pose (Qsys_to_Set_not_empty s0 e0). destruct n. lia. assumption. 
     intros. simpl in *.  inversion_clear H0. econstructor.
     pose (Qsys_to_Set_not_empty s0 e0). destruct n. lia. assumption.
     intros. simpl in *.  inversion_clear H0. econstructor.
     pose (Qsys_to_Set_not_empty s0 e0). destruct n. lia. 
     apply union_empty in H. apply H.
     intros. simpl in *.  inversion_clear H0. econstructor.
     pose (Qsys_to_Set_not_empty s0 e0). destruct n. lia. assumption. 
Qed.







