Require Import FSetInterface.
Require Import FMapInterface.
Require Import Reals.
Require Import Coquelicot.Complex.
Require Import Strings.String.
Require Import Lists.List.
Require Import
  Coq.FSets.FMapList
  Coq.Structures.OrderedTypeEx.
Require Import OrderedType.
Require Import Coq.MSets.MSetWeakList.
Require Import Coq.FSets.FSetList.

(*From Quan Require Import QMatrix.
From Quan Require Import QVector.
From Quan Require Import PVector1. *)
From Quan Require Import Matrix.
From Quan Require Import ParDensityO.
From Quan Require Import Basic_Supplement.

(*-----------------------------------Classic State----------------------------------------*)

Module D:=Nat_as_OT.
Local Open Scope nat_scope.
Definition  cstate := list nat.
Fixpoint c_find (i:nat) (s:cstate) : nat :=
  match i,s with
  | 0   ,  v :: _   => v
  | S i',  _ :: s'  => c_find i' s'
  | _   ,  _        => 0
  end.

Fixpoint c_update (i:nat) (v:nat) (s:cstate): cstate :=
    match i,s with
    | 0   , a :: s' => v :: s'
    | 0   , []      => v :: nil
    | S i', a :: s' => a :: (c_update i' v s' )
    | S i', []      => 0 :: (c_update i' v [] )
    end.

Lemma c_update_find_eq: forall (sigma:cstate) (i:nat) (v:nat), 
c_find i (c_update i v sigma)=v. 
Proof.  induction sigma ; induction i.
    -reflexivity.
    -simpl. assumption.
    -reflexivity.
    -simpl. apply IHsigma.
Qed.

Lemma c_update_find_not: forall (sigma:cstate) (i i0:nat) (v:nat),
i<>i0-> 
c_find i0 (c_update i v sigma)= c_find i0 sigma. 
Proof.  induction sigma; induction i; destruct i0; intros.
    -intuition. 
    -simpl. destruct i0. simpl. reflexivity. simpl. reflexivity. 
    -simpl. reflexivity. 
    -simpl. assert(0= c_find i0 []). destruct i0. reflexivity. 
       reflexivity. rewrite H0.  apply IHi. intuition.  
    -intuition.
    - simpl. reflexivity.
    -simpl. reflexivity.
    -simpl. apply IHsigma. intuition.
Qed.

Fixpoint equal (m m' :cstate) { struct m } : bool :=
  match m, m' with
   | nil, nil => true
   | h::l, h'::l' =>
      match D.compare h h' with
       | EQ _ => equal l l'
       | _ => false
      end
   | _, _ => false
  end.
(*--------------------------定义Cstate_as_OT---------------------------*)

Module Cstate_as_OT  <: OrderedType.

Module D := Nat_as_OT .
Module Data := D.
Module MD := OrderedTypeFacts(D).
Import MD.
Definition t := cstate .
Definition cmp e e' := match D.compare e e' with EQ _ => true | _ => false end.

Definition eq:= @eq t.

Fixpoint lt (m m' : t) {struct m} : Prop :=
  match m, m' with
   | nil, nil => False
   | nil, _ => True
   | _, nil => False
   | h::l, h'::l' =>
      match D.compare h h' with
       | LT _ => True
       | GT _ => False
       | EQ _ => lt l l'
      end
  end.

Definition eq_refl := @refl_equal t .
Definition eq_sym := @sym_eq t.
Definition eq_trans := @trans_eq t.

Lemma lt_trans : forall m1 m2 m3 : t, lt m1 m2 -> lt m2 m3 -> lt m1 m3.
 Proof. 
induction m1; destruct m2 ;destruct m3;try intuition.
 simpl in H. simpl in H0. 
 destruct (D.compare a n);
 destruct (D.compare n n0);simpl;
 MD.elim_comp;  intuition. 
 refine (IHm1 _ _ H H0).   
 Qed. 

 Lemma eq_equal : forall m m', eq m m' <-> equal m m' = true.
 Proof. induction m; destruct m'; unfold eq.
 -simpl. intuition.
 -simpl. intuition. discriminate.
 -simpl. intuition. discriminate.
 -simpl. split. intros. 
   *injection H;intros. 
    MD.elim_comp. apply IHm. unfold eq. assumption.  
   *MD.elim_comp; try intuition. 
                 intros. f_equal. apply H. 
                 apply IHm. assumption.
Qed.


Lemma lt_not_eq : forall m1 m2 : t, lt m1 m2 -> ~ eq m1 m2.
Proof.
 induction m1; destruct m2; unfold eq.
 -simpl. intuition. 
 -simpl.  intuition. discriminate.
 -simpl. intuition.
 -simpl.  destruct (D.compare a n); unfold not; 
          intros; injection  H0; intros. 
          apply D.lt_not_eq in l. intuition.
          apply IHm1 in H1. intuition. assumption.
          intuition.
Qed.

Ltac cmp_solve := unfold eq, lt; simpl;  try MD.elim_comp; auto.

Definition compare : forall m1 m2, Compare lt eq m1 m2.
Proof.
  induction m1; destruct m2;
  [ apply EQ | apply LT | apply GT | ]; cmp_solve.
  destruct (D.compare a n); 
  [ apply LT | | apply GT ]; 
  cmp_solve.
   destruct(IHm1 m2);
  [ apply LT | apply EQ | apply GT ]; 
  cmp_solve. f_equal; intuition. 
Qed.


Definition eq_dec : forall x y : t, sumbool (eq x y)  (~ eq x y).
 intros; elim (compare x y); intro H; [ right | left | right ]; auto.
 auto using lt_not_eq.
 assert (~ eq y x). auto using lt_not_eq.
 unfold not. unfold not in H0. intros.  
 apply eq_sym in H1. apply H0 in H1.  apply H1.
Qed.

End Cstate_as_OT. 

(*------------------------------Quantum State----------------------------------------*)
Local Open Scope R_scope.

Lemma trace_mult: forall (n:nat) (A B :Square n),
trace(Mmult A B) =trace (Mmult B A).
Proof. intros. unfold trace. unfold Mmult. 
       rewrite big_sum_swap_order. 
       apply big_sum_eq. apply functional_extensionality.
       intros. apply big_sum_eq. apply functional_extensionality.
       intros.
apply Cmult_comm. 
Qed.

Lemma trace_mult_Unitary{n:nat}: forall (A B:Square n) ,
 WF_Unitary A -> WF_Matrix B-> trace B=trace (A × B ×  A†).
Proof. intros. rewrite trace_mult. rewrite<-Mmult_assoc. 
destruct H. rewrite H1. rewrite Mmult_1_l. reflexivity.
assumption. 
Qed.


Definition qstate (n :nat):= Density (2^n).

Definition WF_qstate{n:nat} (rho : qstate n ):=
    @Mixed_State (2^(n)) rho.

Definition WWF_qstate{n:nat} (rho : qstate n ):=
  @Mixed_State_aux (2^(n)) rho.

Definition q_update{n:nat} (U: Square (2^n)) (rho :qstate n): qstate n:=
  super U rho.

Lemma WF_qstate_update{n:nat}:forall  (U:Square (2^n)) (q:qstate n),
WF_Unitary U-> WF_qstate q->WF_qstate (q_update U q).
Proof.  unfold WF_qstate. intros. unfold q_update.
         apply mixed_unitary. intuition. intuition.
Qed.



(*----------------------C-Q state------------------------------------------*)
Module NSet := FSetList.Make Nat_as_OT.
Definition QSet:=NSet.t.
Local Open Scope nat_scope.
Fixpoint Qsys_to_Set_aux (n m :nat)(l: QSet): QSet:=
  if n<?m then 
 (match m with 
  | O => l 
  | S m' => (NSet.add m' (Qsys_to_Set_aux n (m') l)) 
  end) 
  else l .

Definition Qsys_to_Set (n m :nat): QSet:= Qsys_to_Set_aux n m (NSet.empty) .


Local Open Scope R_scope.

Definition state(n: nat) := (cstate * (qstate n))%type.

Definition WF_state{n:nat} (st:state n): Prop:=
          WF_qstate (snd st).

Definition WWF_state{n:nat} (st:state n): Prop:=
  WWF_qstate (snd st).

Definition s_update_cstate{n:nat} (i v :nat) (m:state n): state n:=
  match m with 
  |(sigma, rho) => ((c_update i v sigma), rho)
  end.
  
Local Open Scope matrix_scope.
Definition s_update_qstate{n:nat} (U: Square (2^(n))) (m:state n): state n:=
    (fst m, q_update U (snd m)).

Definition s_update{n:nat} (i v:nat) (U: Square (2^(n))) (m:state n): state n:=
 (c_update i v (fst m),  q_update U (snd m)).

Definition s_find{n:nat} (sigma:cstate) (st:state n): qstate n:=
  match Cstate_as_OT.compare sigma (fst st) with
  |EQ _=> (snd st) 
  |_ => Zero
  end.

Definition s_scale{n:nat} (p:R) (st: state n) :=
 ((fst st), (@scale (2^(n)) (2^(n)) p (snd st))).

Definition s_trace{n:nat} (st:state n): R:=
      Cmod (@trace (2^(n))  (snd st)). 

Local Open Scope nat_scope.

Lemma WF_state_cupdate{n:nat}: forall (i n:nat) (st:state n),
WF_state st-> WF_state (s_update_cstate i n st).
Proof. unfold WF_state. destruct st. simpl. intuition. Qed.

Lemma WF_state_qupdate{n:nat}: forall (U:Square (2^(n))) (st:state n),
WF_Unitary U->WF_state st-> WF_state (s_update_qstate U st).
Proof. unfold WF_state. destruct st. simpl. apply WF_qstate_update. Qed.

Lemma WF_state_update{n:nat}: forall (i n:nat) (U: Square (2^(n))) (st:state n),
WF_Unitary U->WF_state st-> WF_state (s_update i n U st).
Proof. unfold WF_state. destruct st. simpl. apply WF_qstate_update. Qed.

Local Open Scope R_scope.
Lemma WF_state_scale{n}: forall c (q: qstate n) (p:R), 
(0<p<=1) /\ WF_state (c,q)-> @WF_state n ((c, p .* q)).
Proof.
        unfold WF_state. unfold WF_qstate. simpl. 
        intros. destruct H. apply Mixed_State_scale. intuition.
        intuition. 
Qed. 

Lemma WF_state_gt_0{n:nat}: forall (st:state n), 
WF_state st -> s_trace st > 0.
Proof. unfold WF_state. unfold WF_qstate. unfold s_trace. intros.
       apply mixed_state_Cmod_1. intuition. 
Qed.


Lemma  WF_state_not_Zero{n:nat}: forall (st:state n),  
WF_state st -> snd st <> Zero .
Proof. unfold WF_state. unfold WF_qstate. simpl.  intros.
apply mixed_state_trace_gt0 in H.
unfold not. intros.  rewrite H0 in H.  
rewrite Zero_trace in H. simpl in H.
lra.
Qed.

Lemma WF_state_eq { n:nat}: forall (st st':state n), 
snd st= snd st' -> WF_state st -> WF_state st' .
Proof. unfold WF_state. unfold WF_qstate. intros. rewrite <-H.
      assumption.   
Qed.

Lemma  s_find_scale{n:nat}: forall (st:state n) p x, 
s_find x (s_scale p st)= p .* (s_find x st).
Proof. intros. unfold s_scale. unfold s_find.
simpl. destruct (Cstate_as_OT.compare x (fst st)).
rewrite Mscale_0_r. reflexivity.  reflexivity.
rewrite Mscale_0_r. reflexivity. 
Qed. 

Lemma s_find_not_Zero{n:nat}: forall sigma (st: state n), 
s_find sigma st <>Zero ->  sigma= (fst st).
Proof. unfold s_find. intros. destruct (Cstate_as_OT.compare sigma
(fst st)) in H. destruct H. reflexivity.
 assumption. destruct H. reflexivity.
Qed.

Lemma s_find_eq{n:nat}: forall sigma (st:state n),
sigma = (fst st) -> s_find sigma st =snd st.
Proof. intros. unfold s_find. 
destruct (Cstate_as_OT.compare sigma (fst st)). 
apply Cstate_as_OT.lt_not_eq in l. unfold not in l. 
 apply l in H. intuition.
reflexivity.
apply Cstate_as_OT.lt_not_eq in l. unfold not in l.
apply Cstate_as_OT.eq_sym in H.  apply l in H. intuition. 
Qed.


(*------------------------Distribution state------------------------------*)

Module Import StateMap:= FMapList.Make(Cstate_as_OT).

Definition dstate(n:nat) := StateMap.t (qstate n).

Definition d_empty(n:nat) := StateMap.empty (qstate n).

Definition state_to_dstate{n:nat} (st:state n): dstate n:=
   StateMap.add (fst st) (snd st) (d_empty n).

Coercion state_to_dstate : state >-> dstate.

Definition dstate_eq{n:nat} (mu mu': dstate n): Prop:=
    (StateMap.this mu)= (StateMap.this mu').

Fixpoint d_trace_aux{n:nat} (mu :list(cstate * (qstate n))): R:=
  match (mu) with
  |nil => 0
  |st::mu' =>  (s_trace st) + d_trace_aux mu'
  end.

Definition d_trace{n:nat} (mu :dstate n): R:=
         d_trace_aux (this mu).

Inductive WF_dstate_aux{n:nat}: list(cstate * (qstate n)) -> Prop:=
|WF_nil: WF_dstate_aux nil
|WF_cons st mu': WF_state st -> WF_dstate_aux mu'->
                         (d_trace_aux (st::mu')) <=1 
                        -> WF_dstate_aux (st::mu').

Inductive WWF_dstate_aux{n:nat}: list(cstate * (qstate n)) -> Prop:=
|WF_nil': WWF_dstate_aux nil
|WF_cons' st mu': WWF_state st -> WWF_dstate_aux mu' 
                        -> WWF_dstate_aux (st::mu').

Definition WF_dstate{n:nat} (mu: dstate n):Prop:=
    WF_dstate_aux (this mu).

Definition WWF_dstate{n:nat} (mu: dstate n):Prop:=
  WWF_dstate_aux (StateMap.this mu).

Definition option_qstate{n:nat} (q: option (qstate n)): (qstate n) :=
    match q with 
    |None => Zero
    |Some  x => x
end.

Definition d_find{n:nat} (sigma:cstate) (mu: dstate n): qstate n := 
          option_qstate (StateMap.find sigma mu).
 
Definition d_update{n:nat} (p: state n) (m: dstate n) :=
  StateMap.add (fst p) (snd p) m.

Definition option_app {n:nat} (x y: option (qstate n)): option (qstate n) := 
   match x ,y with
   |None,_ => y
   |_, None =>x 
   |Some x', Some y'=> Some (x'.+ y')
   end.


Declare Scope state_scope.
Notation "mu1 +l mu2" := (StateMap.Raw.map2 option_app mu1 mu2)(at level 70, no associativity)
  : state_scope.
Local Open Scope state_scope.

Definition d_app{n:nat} (mu1 mu2: dstate n): dstate n:=
           StateMap.map2 (option_app) mu1 mu2.

Definition d_scale_not_0{n:nat} (p:R) (mu:dstate n): dstate n:=
 StateMap.map (fun (x:(qstate n)) => (p.* x)) mu.

Inductive d_scale{n:nat}: (R) -> (dstate n) -> (dstate n) ->Prop :=
|d_scalar_0 mu : d_scale 0 mu (d_empty n)
|d_scalar_r r mu: r<>0-> d_scale r mu (d_scale_not_0 r mu).


Definition dstate_pro{n:nat}  (mu:dstate n) (m:state n) :R :=
    let rho:= d_find (fst m) mu in
   Cmod(@trace (2^(n)) rho).


Require Import Classical_Prop.
Lemma d_scale_exsits{n:nat}: forall r (mu:dstate n),
exists (mu':dstate n), d_scale r mu mu' .
Proof. intros. assert(r=0 \/ r<>0). apply classic. 
   destruct H. exists (d_empty n). rewrite H. apply d_scalar_0.
   exists (d_scale_not_0  r mu). apply d_scalar_r. assumption.
Qed.


Lemma d_trace_eq{n:nat}: forall (mu mu':dstate n),
dstate_eq mu mu' ->
d_trace mu = d_trace mu'.
Proof. unfold d_trace; unfold dstate_eq. intros.
        rewrite H. reflexivity.
        
Qed.


Lemma trace_state_dstate{n:nat}: forall  (st:state n), 
d_trace st= s_trace st .
Proof. intros. unfold d_trace. simpl. unfold s_trace. rewrite Rplus_0_r.
reflexivity.   
Qed.


Require Import ParDensityO.

Lemma WF_dstate_eq{n}: forall (mu mu': dstate n),
dstate_eq mu mu'-> WF_dstate mu -> WF_dstate mu'.
Proof. unfold WF_dstate. unfold dstate_eq. 
      intros (mu,IHmu) (mu', IHmu').
      simpl. intros. rewrite <- H. 
     assumption.
Qed.



Lemma WF_state_dstate{n:nat}: forall (st:state n), 
WF_state st <-> WF_dstate st .
Proof. split; unfold WF_dstate;
       destruct st; simpl; intros. 
       apply WF_cons. intuition. apply WF_nil. 
       unfold WF_state in H.  unfold WF_qstate in H. simpl in H.
       unfold d_trace_aux. unfold s_trace. simpl. rewrite Rplus_0_r.
       apply mixed_state_Cmod_1. intuition.
       inversion_clear H. intuition. 
Qed.


Lemma WWF_state_gt_0{n:nat}: forall (st:state n), 
WWF_state st -> s_trace st>0.
Proof. unfold WWF_state. unfold WWF_qstate. unfold s_trace. intros.
       apply mixed_state_Cmod_1_aux. intuition. 
Qed.

Lemma WWF_dstate_gt_0_aux{n:nat}: forall (mu:list( cstate*qstate n)),
WWF_dstate_aux mu-> 0 <= ((d_trace_aux mu)).
Proof. intros. induction mu.
--simpl.  intuition.
--inversion_clear H. apply IHmu in H1. 
 simpl. apply Rplus_le_le_0_compat. 
apply WWF_state_gt_0 in H0. simpl in H0. 
intuition. intuition. 
Qed.


Lemma WWF_dstate_aux_to_WF_dstate_aux{n}: forall (mu: list (cstate *qstate n)),
WWF_dstate_aux mu /\ d_trace_aux mu <=1 <-> WF_dstate_aux mu.
Proof.  intros. split; intros. induction mu. apply WF_nil. 
        destruct H. inversion_clear H. simpl in H0.
        apply WF_cons. unfold WF_state. unfold WWF_state in H1.
        destruct a. simpl in *.  unfold WF_qstate. unfold WWF_qstate in H1.
        apply Mixed_State_aux_to_Mix_State. split.  assumption.
        unfold s_trace in H0. simpl in H0.
        apply Rplus_le_reg_pos_r with (d_trace_aux mu).
        apply WWF_dstate_gt_0_aux. assumption. assumption.
        apply IHmu.  split. intuition.  
        apply Rplus_le_1 with (s_trace a).
        apply WWF_state_gt_0. assumption. assumption.
        simpl. assumption.
        induction mu.   split. apply WF_nil'. simpl. 
        lra. inversion_clear H. split. apply WF_cons'.
        unfold WWF_state. unfold WF_state in H0.
          unfold WF_qstate in H0. unfold WWF_qstate.
        apply Mixed_State_aux_to_Mix_State. assumption.
         apply IHmu. assumption. assumption.  
Qed.

(*------------WF_d_scale-------------------*)

Local Open Scope R_scope.
Lemma s_trace_scale{n:nat}: forall c (q :(qstate n)) (p:R) ,
(0<p<=1)-> @s_trace n (c, p .* q)=
p * s_trace (c,q).
Proof. intros. unfold s_trace. simpl. rewrite trace_mult_dist.
       rewrite Cmod_mult. rewrite Cmod_R. rewrite Rabs_right. reflexivity.
intuition.
Qed.

Local Open Scope R_scope.
Lemma d_trace_scale_aux{n:nat}: forall (mu:list (cstate * qstate n)) (p:R),
(0<p<=1)-> @d_trace_aux n
(StateMap.Raw.map (fun x : qstate n => p .* x) mu)=
p * d_trace_aux mu.
Proof. intros. induction mu. intros. simpl. rewrite Rmult_0_r. intuition.
intros. destruct a. simpl.
unfold d_trace. unfold s_trace. simpl. 
rewrite trace_mult_dist.
rewrite IHmu.
rewrite Rmult_plus_distr_l.
rewrite Cmod_mult. rewrite Cmod_R.
rewrite Rabs_right. reflexivity. intuition.
Qed.


Lemma d_trace_scale_not_0{n:nat}:forall (mu: dstate n) (p:R), 
(0<p<=1)-> d_trace (d_scale_not_0 p mu)= p * (d_trace mu) .
Proof.  intros (mu, IHmu) p Hp.
        unfold d_trace. 
        unfold d_scale_not_0. 
        unfold map. simpl.
        rewrite d_trace_scale_aux.
        reflexivity. 
        assumption.
Qed.

Lemma d_trace_scale{n:nat}:forall (mu mu': dstate n) (p:R), 
(0<=p<=1)->d_scale p mu mu'-> d_trace (mu')= p * (d_trace mu).
Proof. intros. inversion_clear H0. 
-unfold d_trace. unfold d_empty.  simpl. rewrite Rmult_0_l. reflexivity.
-apply d_trace_scale_not_0. lra.
Qed.



Lemma WF_dstate_in01_aux{n:nat}: forall (mu:list( cstate*qstate n)),
WF_dstate_aux mu-> 0<=((d_trace_aux mu))<=1.
Proof. intros. induction mu.
--simpl.  intuition.
--inversion_clear H. apply IHmu in H1. 
split. simpl. apply Rplus_le_le_0_compat. 
apply WF_state_gt_0 in H0. simpl in H0. 
intuition. intuition. intuition. 
Qed.

Lemma WF_dstate_in01{n:nat}: forall (mu:dstate n),
WF_dstate mu-> 0<=((d_trace mu)) <=1.
Proof. unfold WF_dstate. intros (mu, IHmu) H.
       unfold d_trace. apply WF_dstate_in01_aux.
       intuition. 
Qed.

Lemma WF_d_scale_aux{n}: forall (mu:list (cstate *qstate n)) p, 
(0<p<=1)
->WF_dstate_aux mu 
->@WF_dstate_aux n
((StateMap.Raw.map (fun x : qstate n => p .* x) mu)).
Proof. intros. induction mu. 
        --simpl. intuition.
        --inversion_clear H0. destruct a. 
        simpl.  apply (@WF_cons n). 
        assert(WF_state (s_scale p (c, q))).
        apply WF_state_scale. split. intuition. intuition.
        unfold s_scale in H0.  simpl in H0. intuition.
        apply IHmu. intuition.
        simpl.   rewrite s_trace_scale. rewrite d_trace_scale_aux.
        rewrite <-Rmult_plus_distr_l. assert(1*1=1).
        apply Rmult_1_l. rewrite<-H0.
        apply Rmult_le_compat. intuition. 
        apply WF_dstate_in01_aux in H2. 
        apply WF_state_gt_0 in H1. 
        apply Rplus_le_le_0_compat. 
        intuition. intuition. intuition.
        simpl in H3. intuition.
        assumption. assumption.
Qed.


Lemma WWF_d_scale_aux{n}: forall (mu:list (cstate *qstate n)) p, 
(0<p)
->WWF_dstate_aux mu 
->@WWF_dstate_aux n
((StateMap.Raw.map (fun x : qstate n => p .* x) mu)).
Proof. intros. induction mu. 
        --simpl. intuition.
        --inversion_clear H0. destruct a. 
        simpl.  apply (@WF_cons' n). unfold WWF_state in *.
        unfold WWF_qstate in *.   apply Mixed_State_scale_aux.
        simpl in H1. assumption. assumption.
        apply IHmu. intuition.
Qed.
   
Lemma WF_d_scale_not_0{n}: forall (mu:dstate n) p, 
(0<p<=1)
->WF_dstate mu 
->WF_dstate(d_scale_not_0 p mu).
Proof. unfold WF_dstate.
        unfold d_trace.
        unfold d_scale_not_0.
        simpl. intros  (mu,IHmu) p H0 H.
        unfold map.  simpl. 
        apply WF_d_scale_aux. intuition.
        intuition.
Qed.


Lemma WF_dstate_empty: forall n, WF_dstate (d_empty n) .
Proof. intros. unfold d_empty.  unfold WF_dstate. simpl. unfold Raw.empty.
apply WF_nil. 
Qed.

Lemma WF_d_scale{n:nat}: forall (mu mu':dstate n) p,
(0<=p<=1)->
d_scale p mu mu'
->WF_dstate mu 
->WF_dstate(mu').
Proof. intros. inversion_clear H0. apply WF_dstate_empty.
       apply WF_d_scale_not_0. lra. assumption.
Qed.

(*------------------WF_d_app------------------------------*)


Lemma WF_s_plus{n}:forall (c c0:cstate) (q q0:qstate n ) (p1 p2:R),
(0<p1<=1/\0<p2<=1)-> (p1+p2<=1)-> 
WF_state (c, q)-> WF_state ( c0, q0)->
@WF_state n (c, (p1 .* q .+ p2 .* q0)).
Proof. unfold WF_state.  unfold s_trace. unfold WF_qstate. simpl. 
       intros. apply Mix_S; intuition. 
Qed.


Lemma WWF_s_plus{n}:forall (c c0:cstate) (q q0:qstate n ) ,
WWF_state (c, q)-> WWF_state ( c0, q0)->
@WWF_state n (c, q .+ q0).
Proof. unfold WF_state.  unfold s_trace. unfold WF_qstate. simpl. 
       intros. apply Mix_S_aux; intuition. 
Qed.

Lemma map2_r_refl{n}: forall (mu: list (cstate * qstate n)), 
 StateMap.Raw.map2_r option_app (mu) =  mu.
Proof. intros .
       induction mu. simpl. reflexivity.
       destruct a. simpl.   f_equal.
        apply (IHmu).
Qed.

Lemma map2_l_refl{n:nat}: forall (mu: list (cstate * qstate n)), 
 StateMap.Raw.map2_l option_app (mu) =  mu.
Proof. intros .
       induction mu. simpl. reflexivity.
       destruct a. simpl.   f_equal.
        apply (IHmu).
Qed.

Lemma map2_nil_l{n:nat}: forall (mu:list (cstate * qstate n)), 
 ( [] +l mu) = mu.
Proof. intros.  
       simpl. rewrite map2_r_refl. reflexivity.
Qed.

Lemma map2_nil_r{n:nat}:forall (mu:list (cstate *qstate n)),
 mu +l []= mu.
Proof. induction mu. 
     --reflexivity.
     --destruct a. simpl. rewrite map2_l_refl. reflexivity. 
Qed.

Lemma d_app_empty_l{n:nat}: forall (mu:dstate n), 
dstate_eq (d_app (d_empty n) mu)  mu .
Proof. intros (mu , IHmu).
       unfold d_app. unfold d_empty.
       unfold empty.
       unfold Raw.empty.
       unfold map2. unfold dstate_eq.
       simpl. apply map2_r_refl.
Qed.

Lemma nil_d_app{n:nat}: forall (mu mu': dstate n), 
 this mu = [] -> this mu'=[]  ->  this (d_app mu mu') = [] .
Proof. intros  (mu ,IHmu); induction mu; intros (mu', IHmu');
       induction mu';  simpl;
       intros; simpl. reflexivity.
       simpl in H. discriminate.
       discriminate.
       discriminate.
Qed.

Lemma d_trace_app_aux{n:nat}: forall (mu mu':list (cstate *qstate n)),
WWF_dstate_aux mu ->WWF_dstate_aux mu'->
d_trace_aux (StateMap.Raw.map2 option_app  mu mu') = (d_trace_aux mu) + (d_trace_aux mu').
Proof. intros mu; induction mu. 
 --simpl. intros. rewrite map2_r_refl. rewrite Rplus_0_l. reflexivity.
 --simpl. induction mu'. destruct a. rewrite map2_l_refl.
          simpl. rewrite Rplus_0_r. reflexivity.
  --intros. inversion H; subst. inversion H0; subst. 
    destruct a. destruct a0.  simpl. 
     destruct (Cstate_as_OT.compare c c0). 
     simpl. rewrite IHmu. simpl.  
     rewrite Rplus_assoc. reflexivity.
     intuition. intuition.  simpl. 
     rewrite IHmu. unfold s_trace. 
    simpl. rewrite mixed_state_Cmod_plus_aux.
    repeat rewrite <-Rplus_assoc. 
    f_equal. repeat rewrite Rplus_assoc.   
    f_equal. apply Rplus_comm. unfold WF_state in *.
    unfold WF_qstate in *. simpl in *. intuition.
    intuition. intuition. intuition.
    simpl. rewrite Rplus_assoc.
    rewrite <-Rplus_assoc with (r2:=d_trace_aux mu).
     rewrite <-Rplus_comm with  (r1:=d_trace_aux mu').
     rewrite <-Rplus_assoc. 
     rewrite Rplus_comm with (r2:= s_trace (c0, q0)).
     f_equal. apply IHmu'. intuition. intuition. 
Qed. 



Lemma d_trace_app{n:nat}: forall (mu mu':dstate n),
WWF_dstate mu -> WWF_dstate mu'->
d_trace (d_app  mu mu') = (d_trace mu) + (d_trace mu').
Proof.  intros  (mu,IHmu) (mu',IHmu'). unfold WF_dstate. unfold d_trace.
    unfold d_app. unfold StateMap.map2. simpl. intros.
     apply d_trace_app_aux. intuition. intuition. 
Qed.

Lemma WWF_d_app_aux{n:nat}: forall (mu mu':list (cstate*qstate n)),
WWF_dstate_aux mu -> WWF_dstate_aux mu'-> @WWF_dstate_aux n
(StateMap.Raw.map2 option_app mu mu').
Proof. intros mu; induction mu;
        intros mu'; simpl.
    --intros. rewrite map2_r_refl.  assumption.
    --intros.  induction mu'.  destruct a.
        simpl. rewrite map2_l_refl. intuition.
    --destruct a. destruct a0.  
        inversion H0; subst.
        inversion H; subst. 
        simpl.
        destruct (Cstate_as_OT.compare c c0).
        apply WF_cons'. intuition.
        apply IHmu.  assumption. assumption.
      --apply WF_cons'.  apply WWF_s_plus with c.
        intuition. intuition. 
        apply IHmu. intuition. intuition. 
    --apply WF_cons'.   intuition.
        apply IHmu'.
        assumption.
Qed.


Lemma WF_d_app_aux{n:nat}: forall (mu mu':list (cstate*qstate n)), 
WF_dstate_aux mu -> WF_dstate_aux mu'-> (d_trace_aux (mu +l mu')<=1)
->
WF_dstate_aux (mu +l mu').
Proof. intros. apply WWF_dstate_aux_to_WF_dstate_aux. 
        apply WWF_dstate_aux_to_WF_dstate_aux in H.
       apply WWF_dstate_aux_to_WF_dstate_aux in H0.
       split. apply WWF_d_app_aux. intuition. intuition. 
       assumption.
Qed.


Lemma WF_d_app{n:nat}: forall (mu mu':dstate n),
WF_dstate mu -> WF_dstate mu'-> (d_trace (d_app mu mu')<=1)->
WF_dstate  (d_app mu mu').
Proof. unfold WF_dstate. unfold d_app. unfold d_trace. unfold StateMap.map2. 
 intros  (mu, IHmu) (mu', IHmu') p1 p2. simpl.
 apply WF_d_app_aux. assumption. assumption. 
Qed.


(*-------------------------d_find---------------------------------------------*)

Lemma s_d_find_eq{n:nat} (x:cstate) (st: state n): 
d_find x st = s_find x st.
Proof. unfold d_find. simpl. unfold s_find.
     unfold StateMap.find. simpl. 
    destruct  (Cstate_as_OT.compare x (fst st)).
    reflexivity.
    reflexivity.
    reflexivity. 
Qed.

Lemma d_find_empty{n:nat}: forall x, d_find x (d_empty n)=Zero.
Proof. intros. unfold d_find. simpl. reflexivity. Qed.


Lemma d_find_eq{n:nat}: forall (mu1 mu2:dstate n) , 
dstate_eq mu1 mu2 ->forall x, d_find x mu1=d_find x mu2.
Proof.
unfold d_find; unfold StateMap.find; simpl; unfold dstate_eq;
simpl. intuition. rewrite H. reflexivity.
Qed.


Lemma  d_find_scale_not_0{n:nat}: forall (mu:dstate n) p x, 
d_find x (d_scale_not_0 p mu)= p .* (d_find x mu) .
Proof. intros (mu, IHmu) p x.
       induction mu. simpl. intros.
        rewrite Mscale_0_r. reflexivity.
        destruct a.  unfold d_scale_not_0. unfold map.
        simpl. unfold d_find. unfold StateMap.find. simpl.
        destruct (Cstate_as_OT.compare x c).
        simpl.  rewrite Mscale_0_r.  reflexivity.
        simpl. reflexivity.
        simpl. unfold d_scale_not_0 in IHmu0. unfold map in IHmu0.
        simpl in IHmu0. unfold d_find in IHmu0. unfold find in IHmu0. 
        simpl in IHmu0. inversion_clear IHmu.
         apply (IHmu0 H).
Qed.


Lemma d_find_scale{n:nat}: forall (mu mu':dstate n) p x, 
d_scale p mu mu'->
d_find x mu'= p .* (d_find x mu) .
Proof. intros. inversion H;subst.
-rewrite d_find_empty. rewrite Mscale_0_l. reflexivity.
-apply d_find_scale_not_0.
Qed.


Require Import Classical_Prop.

Lemma DeMoGen:forall P Q, ~(P\/Q) -> (~P/\~Q) .
Proof. intros. split. intro. 
       unfold not in H.
       assert(P\/Q). left. intuition.
       intuition. 
       intro. 
       unfold not in H.
       assert(P\/Q). right. intuition.
       intuition. 
Qed.


Lemma In_mem{n:nat}: forall (mu:dstate n) x,
(StateMap.In ( elt := qstate n) x mu) <-> mem x mu =true .
Proof. intros. split. apply StateMap.mem_1.
       apply StateMap.mem_2.
Qed.

Lemma not_in_Zero{n:nat}:forall (mu: dstate n) x,
~ StateMap.In (elt:=qstate n) x mu -> d_find x mu=Zero .
Proof.  
 intros (mu, IHmu) x.
      unfold not. rewrite In_mem. unfold mem. 
      unfold d_find. unfold StateMap.find.
      simpl.
      intros.
      induction mu. 
      - simpl. reflexivity.
      - destruct a. 
        simpl. simpl in H.
        destruct (Cstate_as_OT.compare x c).
        simpl. reflexivity.
        destruct H. reflexivity.
        inversion IHmu. 
        apply (IHmu0 H2 H). 
Qed.

Lemma  not_in_app{n:nat}: forall (mu mu': list (cstate * qstate n)) x,
 Raw.mem  x mu =false/\ 
 Raw.mem  x mu'=false->
Raw.mem x (Raw.map2 option_app mu mu')=false.
Proof. 
       induction mu.
       intros  mu' x;  
       unfold d_app; unfold map2; 
       simpl. 
      - rewrite (map2_r_refl mu'). intuition.
      -intros. destruct a. simpl. induction mu'. 
       rewrite map2_l_refl.
       intuition. destruct a. 
       destruct (Cstate_as_OT.compare c c0).
       destruct H.
       simpl. simpl in H.
       destruct (Cstate_as_OT.compare x c).
       intuition. intuition.
       intuition.
       simpl.
       simpl in H.
       destruct H. 
       destruct (Cstate_as_OT.compare x c).
       intuition.  intuition. 
       destruct (Cstate_as_OT.compare x c0).
       rewrite <-e in l0.
       rewrite l0 in l. apply Cstate_as_OT.lt_not_eq  in l. intuition.
       intuition.
       apply IHmu. split. assumption. assumption.
       destruct H. 
       simpl. simpl in H0.
       destruct (Cstate_as_OT.compare x c0).
       intuition. intuition.
       apply IHmu'.
       split. intuition. intuition.
Qed.

Lemma  not_in_app'{n:nat}: forall (mu1 mu2: dstate n) x,
~ StateMap.In  x mu1 /\ 
~ StateMap.In  x mu2->
~StateMap.In x (d_app mu1 mu2).
Proof. intros (mu1,IHmu1) (mu2 , IHmu2) x.
       repeat rewrite In_mem. 
       unfold mem. unfold d_app. unfold map2.
       simpl.
       assert(forall b:bool, b=false<-> b<>true).
       intros.  split. intros. unfold not. 
       intros. rewrite H in H0. intuition.
       apply not_true_is_false. 
       repeat rewrite <-H.
       apply not_in_app.
Qed.  


Lemma d_app_find{n:nat}:  forall (mu1 mu2:dstate n) x , 
d_find x (d_app mu1 mu2)= (d_find x mu1) .+ (d_find x mu2).
Proof.   
        intros.  assert((StateMap.In (elt:=qstate n) x mu1 \/
        StateMap.In (elt:=qstate n) x mu2) \/
        ~((StateMap.In (elt:=qstate n) x mu1 \/
        StateMap.In (elt:=qstate n) x mu2))).
        apply classic.
        destruct H.
        unfold d_find.
        unfold d_app.
        rewrite StateMap.map2_1.
        unfold option_app.
        destruct (StateMap.find (elt:=qstate n) x mu1).
        destruct (StateMap.find (elt:=qstate n) x mu2).
        simpl. reflexivity.
        simpl. rewrite Mplus_0_r. reflexivity.
        simpl. rewrite Mplus_0_l. reflexivity.
        assumption.
        apply DeMoGen in H.
        destruct H.
        assert(~ StateMap.In x (d_app mu1 mu2)).
        apply not_in_app'. intuition.
        apply not_in_Zero in H.
        apply not_in_Zero in H0.
        apply not_in_Zero in H1.
        rewrite H. rewrite H0. rewrite H1. 
        rewrite Mplus_0_r. reflexivity.
Qed.



(*-------------------------------dstate_eq-----------------------------*)

Lemma dstate_eq_refl{n:nat}:forall (mu:dstate n),
 dstate_eq mu mu .
Proof. unfold dstate_eq. intuition.
Qed.

Lemma dstate_eq_sym{n:nat}:forall (mu1 mu2: dstate n),
dstate_eq mu1 mu2-> dstate_eq mu2 mu1 .
Proof. intros  (mu1,IHmu1) (mu2,IHmu2).
unfold dstate_eq. simpl. intuition.
Qed.

Lemma dstate_eq_trans: forall n (mu mu1 mu2: dstate n),
dstate_eq mu mu1 -> dstate_eq mu1 mu2
-> dstate_eq mu mu2.
Proof. intros n (mu, IHmu) (mu1,IHmu1) (mu2,IHmu2).
  unfold dstate_eq. simpl.
  intros. rewrite H. assumption.
  Qed.

Lemma d_app_eq{n:nat}: forall (mu mu' mu1 mu1': dstate n),
dstate_eq mu mu'->
dstate_eq mu1 mu1'->
dstate_eq (d_app mu mu1) (d_app mu' mu1') .
Proof. unfold dstate_eq. intros
 (mu, IHmu) (mu',IHmu') (mu1,IHmu1) (mu1', IHmu1').
       simpl. intuition. rewrite H. rewrite H0. reflexivity. 
Qed.

Lemma d_scale_not_0_eq{n:nat}: forall (mu mu' : dstate n) (p:R),
dstate_eq mu mu'->
dstate_eq (d_scale_not_0 p mu) (d_scale_not_0 p mu'). 
Proof. intros (mu, IHmu) (mu',IHmu') . unfold dstate_eq.
unfold d_scale_not_0.
       simpl. intros. rewrite H. intuition.
Qed.


Lemma d_scale_eq{n:nat}: forall (mu mu' mu1 mu'1: dstate n) (p:R),
dstate_eq mu mu'->
d_scale p mu mu1->
d_scale p mu' mu'1->
dstate_eq mu1 mu'1.
Proof. intros. inversion H0; subst; inversion H1; subst.
-apply dstate_eq_refl.
-lra. 
-lra.
-apply d_scale_not_0_eq. assumption.
Qed.
       


(*--------------------------d_scale----------------------------------------*)

Lemma d_scale_nil{n:nat}: forall (mu:dstate n) p, 
this (d_scale_not_0 p mu) = nil -> this mu = [].
Proof. intros (mu, IHmu) p. destruct mu. intuition.
       destruct p0.
       simpl. discriminate.
Qed.


Lemma nil_d_scale'{n:nat}: forall (mu : dstate n) (p : R),
 this mu = []  ->  this (d_scale_not_0 p mu) = [] .
Proof. intros  (mu ,IHmu).
       intros. simpl.
       induction mu. simpl. reflexivity.
       simpl in H. discriminate.
Qed.


Lemma nil_d_scale{n:nat}: forall (mu mu': dstate n) (p : R),
d_scale p mu mu'->
this mu = []  ->  this mu' = [].
Proof. intros. inversion H;subst. 
       unfold d_empty. simpl. unfold Raw.empty. reflexivity.
       apply nil_d_scale'. assumption.
Qed.

Lemma d_scale_not_nil{n:nat}: forall (mu:dstate n) p, 
(0<p<=1) -> this mu<>nil <-> this (d_scale_not_0 p mu) <> nil.
Proof. intros (mu, IHmu) p Hp.
      destruct mu. intuition.
       intros. 
       split;
        unfold not; intros.
        apply d_scale_nil in H0.
        apply H in H0. intuition.
        apply nil_d_scale' with (p:=p) in H0.
        apply H in H0.
       intuition.
Qed.

Lemma d_scale_empty'{n:nat}: forall p, 
   dstate_eq (d_scale_not_0 p (d_empty n)) (d_empty n).
  Proof. intros . unfold d_empty. unfold dstate_eq.
     unfold d_scale_not_0. simpl. unfold Raw.empty. reflexivity.
  Qed.


Lemma d_scale_not_0_1_l{n:nat}: forall (mu:dstate n), 
dstate_eq (d_scale_not_0 1 mu)  mu.
Proof. intros (mu, IHmu). unfold dstate_eq. 
        unfold d_scale_not_0; unfold map;
        simpl; induction mu. reflexivity.
        destruct a. inversion_clear IHmu.
        apply IHmu0 in H.
        simpl. rewrite Mscale_1_l.
        rewrite H.  reflexivity. 
Qed.

Lemma d_scale_1_l{n:nat}: forall (mu mu':dstate n), 
d_scale 1 mu mu'->
dstate_eq (mu') mu.
Proof. intros. inversion H;subst. lra.
apply d_scale_not_0_1_l.
Qed.

Lemma d_scale_assoc'{n:nat}: forall (p1 p2:R) (mu:dstate n), 
   dstate_eq (d_scale_not_0 p1 (d_scale_not_0 p2 mu)) (d_scale_not_0 (Rmult p1  p2) mu).
  Proof.
  intros p1 p2 (mu, IHmu). unfold dstate_eq.
  induction mu. simpl. reflexivity.
          destruct a.
          unfold d_scale_not_0. unfold map. simpl.
          unfold d_scale_not_0 in  IHmu0. unfold map in IHmu0. 
          simpl in IHmu0.
          inversion_clear IHmu.
          apply IHmu0 in H.
          rewrite H.
          rewrite Mscale_assoc.
          assert(((Cmult (RtoC p1) (RtoC p2)))=
          ((RtoC (Rmult p1 p2)))).
          unfold RtoC.
          unfold Cmult. simpl.
          repeat rewrite Rmult_0_l.
          repeat rewrite Rmult_0_r.
          rewrite Rplus_0_r.
          rewrite Rminus_0_r.
          intuition.
          rewrite H1.
          reflexivity.
  Qed.


  Lemma d_scale_assoc{n:nat}: forall (p1 p2:R) (mu mu' mu'' mu''':dstate n), 
  d_scale p2 mu mu'->
  d_scale p1 mu' mu''->
  d_scale (Rmult p1 p2) mu mu'''->
  dstate_eq mu'' mu'''.
  Proof. intros. inversion H;subst; inversion H0; subst; inversion H1;subst;
  try reflexivity; try lra.
  -symmetry in H5. apply Rmult_integral in H5. lra. 
  - apply d_scale_assoc'.
Qed.


Lemma d_scale_integral{n:nat}: forall (mu mu':dstate n) p, 
 (d_scale p mu mu') ->this mu'=[]-> p=0 \/ this mu =[].
Proof. intros.  inversion H;subst. left. reflexivity.
   right.  apply d_scale_nil with p. assumption.
Qed.




(*------------------------------d_app-----------------------------*)

Lemma map2_app_not_nil{n:nat}: forall  (mu mu':list (cstate * qstate n)),
mu<>nil -> mu'<>nil->
StateMap.Raw.map2 option_app mu mu' <> [] .
Proof. intros. induction mu; induction mu'.
       simpl. intuition.
       destruct H. intuition.
       destruct H0. reflexivity.
       destruct a. destruct a0.
       simpl. 
       destruct (Cstate_as_OT.compare c c0).
       discriminate. discriminate.
     discriminate.
Qed.

Lemma map2_app_not_nil_l{n:nat}: forall  (mu mu':list (cstate * qstate n)),
(mu<>nil)-> StateMap.Raw.map2 option_app mu mu' <> [].
Proof. induction mu. intros. destruct H. reflexivity.
       intros. induction mu'. destruct a. simpl. 
       rewrite map2_l_refl. intuition.
       destruct a. destruct a0. 
       simpl. 
       destruct (Cstate_as_OT.compare c c0).
       discriminate. discriminate.
     discriminate.
Qed. 

Lemma map2_comm{n:nat}: forall (mu mu': list (cstate * qstate n)),
(StateMap.Raw.map2 option_app mu mu')=
(StateMap.Raw.map2 option_app mu' mu).
Proof.  induction mu. induction mu'.
      -- simpl. reflexivity.
      --destruct a. simpl. rewrite map2_r_refl. rewrite map2_l_refl.
         reflexivity.
      --induction mu'. destruct a. simpl. rewrite map2_r_refl. rewrite map2_l_refl.
       reflexivity.
      -- destruct a. destruct a0.  simpl.
        destruct (Cstate_as_OT.compare c c0);
        destruct (Cstate_as_OT.compare c0 c).
        rewrite l0 in l. apply Cstate_as_OT.lt_not_eq in l.
        unfold not in l. intuition.
        rewrite e in l. apply Cstate_as_OT.lt_not_eq in l.
        unfold not in l. intuition.
        simpl. f_equal. 
        apply IHmu. 
        rewrite e in l. apply Cstate_as_OT.lt_not_eq in l.
        unfold not in l. intuition.
        simpl. f_equal. unfold Cstate_as_OT.eq in e.
        unfold Cstate_as_OT.eq in e0. rewrite e. rewrite e0.
        f_equal. apply Mplus_comm. apply IHmu.
        rewrite e in l. apply Cstate_as_OT.lt_not_eq in l.
        unfold not in l. intuition.
        f_equal. 
        apply IHmu'.
        rewrite e in l. apply Cstate_as_OT.lt_not_eq in l.
        unfold not in l. intuition.
        rewrite l0 in l. apply Cstate_as_OT.lt_not_eq in l.
        unfold not in l. intuition.   
Qed.

Require Import Classical_Prop.
Lemma map2_app_nil: forall n (x y: list (cstate *qstate n)),
[] = StateMap.Raw.map2 option_app x y -> x=nil /\ y=nil.
Proof. intros. assert(x=[]\/x<>[]).
        apply classic.
        assert(y=[]\/y<>[]).
       apply classic. destruct H0. destruct H1.
       intuition. apply (map2_app_not_nil_l y x) in H1.
       rewrite map2_comm in H1. rewrite H in H1. destruct H1.
       reflexivity.   
       apply (map2_app_not_nil_l x y) in H0.
        rewrite H in H0. destruct H0. reflexivity.
Qed.






Lemma d_app_comm{n:nat}: forall (mu mu':dstate n),
 dstate_eq ( (d_app mu' mu) )  ( ((d_app mu mu'))).
Proof. unfold dstate_eq. unfold d_app. unfold map2.
      intros (mu, IHmu) (mu', IHmu'). simpl.
      apply map2_comm.
Qed.



From Quan Require Import Matrix.
Local Open Scope matrix_scope.
Local Open Scope R_scope.
Lemma Mscale_0: forall (m n:nat) (A:Matrix m n) (p: R), 
(p <> 0) /\ (p .* A = Zero) -> A = Zero .
Proof. intros. destruct H.  
assert(((1%R)/p) .* (p .* A ) = Zero).
rewrite H0. rewrite Mscale_0_r. reflexivity.  
rewrite Mscale_assoc in H1.  
rewrite Cdiv_unfold in H1.
assert((/ p * p)%C = 1).
rewrite Cinv_l. reflexivity.
unfold RtoC. unfold not. intros. injection H2. 
intros. intuition.
rewrite <- Cmult_assoc in H1.
rewrite H2 in H1.
rewrite Cmult_1_l in H1.
rewrite Mscale_1_l in H1.
assumption.
Qed.

Local Open Scope R_scope.
Lemma Mscale_not_0:forall (m n:nat) (A:Matrix m n) (p: R), 
(p <> 0)/\ (A<>Zero )-> p.* A <> Zero .
Proof. unfold not. intros. 
intros. assert(A=Zero). apply (Mscale_0 _ _ _ p). 
split. lra.
assumption. apply H in H1. intuition.  
Qed.

Local Open Scope R_scope.
Lemma Mscale_not_0':forall (m n:nat) (A:Matrix m n) (p: R), 
p.* A <> Zero -> A<>Zero .
Proof. unfold not.  intros.  rewrite H0 in H.  rewrite Mscale_0_r in H.
intuition. 
Qed.

Module Import MC := OrderedTypeFacts(Cstate_as_OT).

Lemma map_assoc: forall n (x y z: list (cstate *qstate n)),
(x +l (y +l z)) = (x +l y +l z).
Proof. induction x. simpl; intros. 
       -repeat rewrite map2_r_refl.
        reflexivity. 
      - destruct a.
             induction y; intros. rewrite map2_nil_l. rewrite map2_nil_r.
                 reflexivity.
           induction z. repeat rewrite map2_nil_r.
          reflexivity.
          destruct a. destruct a0. 
          simpl.   
          destruct (Cstate_as_OT.compare c0 c1).
          destruct (Cstate_as_OT.compare c c0).
          remember ((x +l (c0, q0) :: y) +l (c1, q1) :: z).
          simpl. MC.elim_comp. 
          f_equal. rewrite <-(IHx ((c0, q0) :: y) ((c1, q1) :: z)).
          simpl. MC.elim_comp. reflexivity. 
          
          rewrite IHx.  simpl. MC.elim_comp. reflexivity. 
          simpl. MC.elim_comp.
          f_equal. apply IHy.

        destruct (Cstate_as_OT.compare c c0).  simpl.
        MC.elim_comp.  f_equal.
         rewrite <-IHx.  simpl. MC.elim_comp. 
        reflexivity. 
          
           simpl. MC.elim_comp.
             f_equal. rewrite Mplus_assoc. reflexivity.
           apply IHx. 
           simpl. MC.elim_comp.  f_equal.  apply IHy.
      
  destruct (Cstate_as_OT.compare c c1).
  MC.elim_comp. simpl. MC.elim_comp.  
f_equal.  rewrite<- IHx. f_equal.  simpl.
MC.elim_comp.  reflexivity.   
MC.elim_comp. simpl. MC.elim_comp.
 f_equal. rewrite<- IHx. reflexivity. 

 MC.elim_comp. simpl. MC.elim_comp.
 f_equal. simpl in IHz. rewrite IHz.
 MC.elim_comp. reflexivity.
simpl.  MC.elim_comp.  f_equal. simpl in IHz. rewrite IHz.
MC.elim_comp. unfold Cstate_as_OT.eq in H1. subst.
simpl. reflexivity. simpl. MC.elim_comp.
f_equal. 
simpl in IHz.
rewrite IHz.  MC.elim_comp. simpl. f_equal. 
Qed.


Lemma d_app_assoc': 
forall {n : nat} (mu1 mu2 mu3 : dstate n),
dstate_eq (d_app (d_app mu1 mu2) mu3) (d_app mu1 (d_app mu2 mu3)).
Proof.   unfold dstate_eq. unfold d_app. unfold StateMap.map2.
     simpl. intros n (mu1, IHmu1) (mu2, IHmu2) (mu3, IHmu3).
     simpl.  rewrite map_assoc. reflexivity.
Qed.


Lemma  d_scalar_app_distr_aux:forall {n : nat} (mu mu' : list( state n)) (p : R),
 ( StateMap.Raw.map2 (@option_app  n)
 (StateMap.Raw.map (fun x => p .* x) mu)  (StateMap.Raw.map (fun x => p .* x) mu'))=
  (StateMap.Raw.map (fun x => p .* x) ( StateMap.Raw.map2 option_app mu  mu')) .
Proof. induction mu. simpl; intros. repeat rewrite map2_r_refl.
       reflexivity. 
       intros. destruct a. induction mu'.  
       simpl. repeat rewrite map2_l_refl. reflexivity.
       destruct a. simpl.
       destruct (Cstate_as_OT.compare c c0).
       simpl. f_equal. 
       assert((c0, p .* q0)
       :: StateMap.Raw.map
            (fun x : Square (2 ^ n) => p .* x) mu'=
            StateMap.Raw.map
            (fun x : Square (2 ^ n) => p .* x) ((c0, q0)::mu')     ).
      simpl. reflexivity. rewrite H. 
       apply IHmu.  simpl. f_equal. 
       rewrite Mscale_plus_distr_r. reflexivity.
       apply IHmu.  
       simpl. f_equal. apply IHmu'. 
Qed.

Lemma  d_scalar_app_distr':forall {n : nat} (mu mu': dstate n) (p : R),
dstate_eq (d_app (d_scale_not_0 p mu) (d_scale_not_0 p mu')) (d_scale_not_0 p (d_app mu mu')) .
Proof. intros. 
    unfold dstate_eq. unfold d_app. unfold StateMap.map2.
    unfold d_scale_not_0. unfold StateMap.map.  destruct mu as [mu IHmu].
    destruct mu' as [mu' IHmu']. 
    simpl. apply d_scalar_app_distr_aux.  
Qed.

Lemma  d_scale_app_distr:forall {n : nat} (mu mu' mu1 mu2 mu3: dstate n) (p : R),
d_scale p mu mu1->
d_scale p mu' mu2->
d_scale p (d_app mu mu') mu3->
dstate_eq (d_app mu1 mu2) mu3 .
Proof. intros. assert(p=0\/p<>0). apply Classical_Prop.classic.
   destruct H2. subst. inversion H0; subst.  inversion_clear H.
   inversion_clear H1. apply d_app_empty_l. lra. lra. lra. 
   inversion H0; subst. lra. inversion H; subst. lra.
   inversion H1; subst. lra.  
    unfold dstate_eq. unfold d_app. unfold StateMap.map2.
    unfold d_scale_not_0. unfold StateMap.map.  destruct mu as [mu IHmu].
    destruct mu' as [mu' IHmu']. 
    simpl. apply d_scalar_app_distr_aux.  
Qed.


(*--------------------------------------------------------------------*)

       
Lemma dstate_1{n:nat}: forall (mu: list (cstate *qstate n))
(t x:cstate) (q:qstate n),
Sorted (Raw.PX.ltk (elt:=qstate n))
          ((t, q) :: mu)->
option_qstate (StateMap.Raw.find x mu)<>Zero -> Cstate_as_OT.lt t x.
Proof. induction mu.
  --simpl. intros. destruct H0. reflexivity.
  --destruct a. simpl. intros. 
    destruct (Cstate_as_OT.compare x c) .
    simpl in H0. destruct H0. reflexivity.
    assert(Cstate_as_OT.lt t0 c).
    inversion_clear H. inversion_clear H2.
    unfold Raw.PX.ltk in H.  
    simpl in H. unfold Cstate_as_OT.lt. assumption.
    rewrite <-e in H1. assumption.
    inversion_clear H. 
    inversion_clear H2.
    inversion_clear H1. 
    apply (IHmu t0 x q0) . 
    apply Sorted_cons. assumption.
    inversion_clear H3. apply HdRel_nil.
    apply HdRel_cons. unfold Raw.PX.ltk. 
    simpl. unfold Raw.PX.ltk in H1. simpl in H1.
    unfold Raw.PX.ltk in H . simpl in H.
    assert(forall (m1 m2 m3 : cstate),
    Cstate_as_OT.lt m1 m2 
    -> Cstate_as_OT.lt m2 m3 ->Cstate_as_OT.lt m1 m3).
    apply Cstate_as_OT.lt_trans.
    unfold Cstate_as_OT.lt in  H3.
   apply H3 with (m2:=c). assumption.
   assumption. assumption.
Qed.


Lemma NF:forall (P Q:Prop),
(P->Q)->(~Q->~P).
Proof. intros.  intros. unfold not. intuition.
Qed.

Lemma  NNP: forall (P:Prop),
P->~~P .
Proof. intros. unfold not. intros.
apply H0 in H. assumption.
  
Qed.

Lemma NF_1:forall (P Q:Prop),
(~Q->~P)-> (P->Q).
Proof. intro.  intro. intro. 
       assert(~ ~ P -> ~ ~ Q).
      apply (NF (~Q) (~P) ).
      assumption. 
  
    intros. apply NNP in H1. apply H0 in H1.
    apply NNPP . assumption.
Qed.


(* Lemma NF_inv: forall (P:Prop),
~(~P)->P .
Proof. intro. unfold not. intro.  
  
Qed. *)
Lemma find_dec{n:nat}: forall x (mu:list (cstate * qstate n)),
option_qstate
(Raw.find (elt:=qstate n) x mu)= Zero
\/ option_qstate
(Raw.find (elt:=qstate n) x mu)<>Zero.
Proof. intros. 
    induction mu.
    --simpl. intuition.
    --simpl. destruct a. 
      destruct (Cstate_as_OT.compare x c).
       intuition.
       simpl.  apply classic. 
       intuition.
  
Qed.


Lemma dstate_2{n:nat}: forall x (mu1 mu2: list (cstate *qstate n)),
(option_qstate (StateMap.Raw.find x mu1)<>
option_qstate (StateMap.Raw.find x mu2))->
option_qstate (StateMap.Raw.find x mu1)<>Zero \/
option_qstate (StateMap.Raw.find x mu2)<>Zero.
Proof. intros  x mu1 mu2.    apply NF_1.
    intros.
       apply not_or_and in H. destruct H.
       unfold not. intros.
       assert(option_qstate
(Raw.find  x mu1)= Zero
\/ option_qstate
(Raw.find  x mu1)<>Zero).
apply classic. destruct H2.
assert(option_qstate
(Raw.find x mu2)= Zero
\/ option_qstate
(Raw.find  x mu2)<>Zero).
apply classic.
destruct H3. 
rewrite <-H2 in H3. symmetry in H3. apply H1 in H3.
assumption. 
(* unfold not in H. unfold not in H3. *)
 apply H0 in H3. assumption.
 apply H in H2. assumption.
 Qed.

Lemma Nexist: forall (A:Type) (x:A) (P:A->Prop),
(~(exists x, (P x)))->(forall x, ~(P x) ).
Proof. intros. unfold not in H. unfold not.
       intros. assert((exists x : A, P x)).
       exists x0. assumption.
       apply H in H1.
      assumption.
Qed.

Lemma Nforall{n:nat}:  forall  (mu1 mu2:dstate n),
(forall x : cstate,
 d_find x mu1 = d_find x mu2) ->
~
(exists x : cstate,
   d_find x mu1 <> d_find x mu2).
Proof. intros. unfold not. intros. 
destruct H0. assert(d_find x mu1 = d_find x mu2). apply H. apply H0 in H1. assumption.
Qed.


  
Lemma and_imply: forall (P Q R T:Prop),
(P/\Q/\R->T) -> (P-> Q ->R->T) .
Proof. intros.  assert(P/\Q/\R2). intuition.
 intuition.
  
Qed.


Lemma d_eq{n:nat}: forall (mu1 mu2:dstate n),
WF_dstate mu1 -> WF_dstate mu2->
  (~ dstate_eq mu1 mu2-> exists x, d_find x mu1<>d_find x mu2) .
Proof. intros  (mu1, IHmu1); induction mu1; intros (mu2, IHmu2);
         induction mu2; simpl; intros. 
       -- simpl. intros. destruct H1. reflexivity. 
      -- simpl. 
        unfold d_find. unfold StateMap.find. simpl. intros.
        destruct a. exists c. MC.elim_comp. 
        inversion H0; subst. apply WF_state_not_Zero in H5.
        simpl in *. intuition.
      -- simpl. 
      unfold d_find. unfold StateMap.find. simpl. 
      destruct a. exists c. 
      MC.elim_comp. 
        inversion H; subst. apply WF_state_not_Zero in H5.
        simpl in *. intuition.
      -- simpl.  unfold d_find. unfold StateMap.find. simpl.
        destruct a. destruct a0. 
        destruct (Cstate_as_OT.compare c c0).
        -exists c. MC.elim_comp. 
        MC.elim_comp. 
        inversion H; subst. apply WF_state_not_Zero in H6. simpl in H6.
        simpl. intuition. 
       -
        simpl in IHmu0.  inversion H;subst. 
         inversion H0;subst. inversion_clear IHmu1.
        inversion_clear IHmu2.
        unfold not in H1. unfold dstate_eq in H1.
        simpl in H1. 
        assert(q=q0\/~(q=q0)). apply classic.
        destruct H12.
        *unfold dstate_eq in IHmu0. 
         simpl in IHmu0.
        unfold Cstate_as_OT.eq in e.
        rewrite e in H1. rewrite H12 in H1. 
        assert(mu1<>mu2). unfold not. intros.
        destruct H1. f_equal. assumption.
        assert( exists x : cstate,
        d_find x
          {|
            this := mu1; sorted := H2
          |} <> d_find x (Build_slist H10)).
        apply (IHmu0 H2 (Build_slist H10) H5 H8 H13).
        destruct H14. unfold d_find in H14.
        unfold find in H14. simpl in H14.
        assert(option_qstate (Raw.find (elt:=qstate n) x mu1) <>
        option_qstate (Raw.find (elt:=qstate n) x mu2)).
        assumption.
        apply dstate_2 in H14. 
         destruct H14. 
        **apply dstate_1  with (t:=c) (q:=q) in H14.
        exists x.  MC.elim_comp.   MC.elim_comp.
        assumption. assumption. 
        **apply dstate_1 with (t:=c0) (q:=q0) in H14.
        exists x. MC.elim_comp. MC.elim_comp. 
         assumption.
         assumption.
         exists c. MC.elim_comp.  MC.elim_comp.
         simpl. intuition.
      -exists c0. MC.elim_comp. MC.elim_comp. 
      inversion H0; subst. apply WF_state_not_Zero in H6. simpl in H6.
      simpl. intuition.
Qed.



 
Lemma d_eq_1{n:nat}: forall (mu1 mu2:dstate n),
 WF_dstate mu1 -> WF_dstate mu2->
  ( forall x, d_find x mu1=d_find x mu2)-> dstate_eq mu1 mu2 .
Proof.  intros  mu1 mu2 H1 H2. 
       apply NF_1. 
       intros.  assert( exists x, d_find x mu1<>d_find x mu2).
       apply d_eq. assumption. assumption. assumption.
       apply NF with (Q:=~(exists x : cstate,
       d_find x mu1 <> d_find x mu2)). apply Nforall.
       apply NNP. assumption. 
Qed.

Lemma dstate_equal{n:nat}: forall (mu1 mu2:dstate n),
  WF_dstate mu1 -> WF_dstate mu2->
( forall x, d_find x mu1=d_find x mu2)<-> dstate_eq mu1 mu2 .
Proof. split. apply d_eq_1. assumption. assumption.
     apply  d_find_eq.
Qed.


