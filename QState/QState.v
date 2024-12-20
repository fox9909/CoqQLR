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
Require Import QArith.
Import QArith.QOrderedType.
(*From Quan Require Import QMatrix.
From Quan Require Import QVector.
From Quan Require Import PVector1. *)
From Quan Require Import Matrix.
From Quan Require Import Mixed_State.

(*-----------------------------------Classic State----------------------------------------*)


Module D:=Nat_as_OT.

Local Open Scope nat_scope.
Definition  cstate := list nat.
Fixpoint c_find (i:nat) (s:cstate) : nat :=
  match i,s with
  | 0%nat   ,  v :: _   => v
  | S i',  _ :: s'  => c_find i' s'
  | _   ,  _        => 0
  end.

Fixpoint c_update (i:nat) (v:nat) (s:cstate): cstate :=
    match i,s with
    | 0%nat   , a :: s' => v :: s'
    | 0%nat   , []      => v :: nil
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
       | EQ _  => equal l l'
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

Definition Qsys_to_Set (n m :nat): QSet:= Qsys_to_Set_aux n m (NSet.empty).

Definition qstate (s e :nat):= Density (2^(e-s)).

Definition WF_qstate{s e :nat} (rho : qstate s e ):=
    @NZ_Mixed_State (2^(e-s)) rho /\ (s<=e)%nat.

Definition q_update{s e:nat} (U: Square   (2^(e-s))) (rho :qstate s e): qstate s e:=
  super U rho.

Definition q_kron{s x e:nat} (q :qstate s x) (q': qstate x e) := 
     (@kron  (2^(x-s)) (2^(x-s))  (2^(e-x)) (2^(e-x)) q  q').

Definition q_scale{s e:nat} (c:C) (q: qstate s e) := 
    @scale (2^(e-s)) (2^(e-s)) c  q.

Definition q_plus{s e:nat} (q1 q2: qstate s e) := 
    @Mplus (2^(e-s)) (2^(e-s)) q1 q2 .

Definition q_trace{s e:nat} (q: qstate s e) := 
Cmod (@trace (2^(e-s)) q).

#[export] Hint Unfold q_kron q_plus q_scale q_trace:core.

Lemma WF_qstate_update{s e:nat}:forall  (U:Square (2^(e-s))) (q:qstate s e),
WF_Unitary U-> WF_qstate q->WF_qstate (q_update U q).
Proof.  unfold WF_qstate. intros. unfold q_update.
        split.
         apply nz_mixed_unitary. intuition. intuition. 
         intuition.
Qed.

Local Open Scope R_scope.
Lemma WF_qstate_kron{s x e:nat}: forall (q :qstate s x) (q': qstate x e), 
WF_qstate q-> WF_qstate q'-> 
@WF_qstate s e (q_kron q q').
Proof.  unfold WF_qstate. intros.
        assert(2^(x-s)*2^(e-x)=2^(e-s))%nat. 
        rewrite <-Nat.pow_add_r. f_equal. lia.
        destruct H1.
        split.
        apply mixed_state_kron; intuition.
        intuition.
Qed. 


Lemma WF_qstate_scale{s e}: forall (q: qstate s e) (p:R), 
(0<p<=1)%R /\ WF_qstate q-> @WF_qstate s e (q_scale p q).
Proof.
         unfold WF_qstate. simpl. 
        intros. destruct H. split.  
         apply (@nz_Mixed_State_scale (2^(e-s))). intuition.
        intuition. intuition. 
Qed. 

Lemma WF_q_plus{s e}:forall (q q0:qstate s e ) (p1 p2:R),
(0<p1<=1/\0<p2<=1)-> (p1+p2<=1)-> 
WF_qstate q-> WF_qstate q0->
WF_qstate (q_plus (q_scale p1  q) (q_scale p2 q0)).
Proof. unfold WF_qstate.  unfold q_trace.  simpl. 
       intros. split. apply (@NZ_Mix_S (2^(e-s))); intuition. intuition. 
Qed.

Lemma WF_qstate_in_01{s e:nat}: forall (q:qstate s e), 
WF_qstate q -> 0<(q_trace q) <=1.
Proof.  unfold WF_qstate.  intros.  apply nz_mixed_state_Cmod_1.   intuition.  
Qed.

Lemma  WF_qstate_not_Zero{s e:nat}: forall (q:qstate s e),  
WF_qstate q -> q <> Zero.
Proof.  unfold WF_qstate. simpl.  intros.
apply (@NZ_Mixed_not_Zero (2^(e-s))). intuition.
Qed.

Definition WWF_qstate{s e:nat} (rho : qstate s e ):=
  @NZ_Mixed_State_aux (2^(e-s)) rho /\ (s<=e)%nat.

Lemma WWF_qstate_scale{s e}: forall (q: qstate s e) (p:R), 
(0<p) /\ WWF_qstate q-> WWF_qstate  (q_scale p q).
Proof.
         unfold WF_qstate. simpl. 
        intros. destruct H. unfold WWF_qstate in *.
        split. apply (@nz_Mixed_State_scale_aux (2^(e-s))). intuition.
        intuition. intuition. 
Qed. 


Lemma WWF_q_plus{s e}:forall (q q0:qstate s e ),
WWF_qstate q-> WWF_qstate q0->
WWF_qstate (q_plus q q0).
Proof. unfold WF_qstate.  unfold q_plus.  simpl. 
       intros. split; try 
       apply (@NZ_Mix_S_aux (2^(e-s))); try  apply H; try apply H0. 
Qed.

Lemma WWF_qstate_to_WF_qstate{s e:nat}:  forall (q:qstate s e), 
WF_qstate q <-> WWF_qstate q /\ q_trace q<=1.
Proof. intros. unfold WF_qstate in *. unfold WWF_qstate in *. split; intros.
       destruct H. apply nz_Mixed_State_aux_to_nz_Mix_State in H.
        intuition.
       split. apply nz_Mixed_State_aux_to_nz_Mix_State. intuition. lia. 
Qed.

Lemma WWF_qstate_gt_0{s e:nat}:  forall (q:qstate s e), 
WWF_qstate q ->0<q_trace q.
Proof. intros. apply nz_mixed_state_Cmod_1_aux. apply H. Qed.

Local Open Scope R_scope.
Lemma q_trace_scale{s e:nat}: forall (q :(qstate s e)) (p:R) ,
(0<p)-> q_trace (q_scale p q)=
p * q_trace q.
Proof. intros.  unfold q_trace. unfold q_scale.
 rewrite trace_mult_dist.
       rewrite Cmod_mult. rewrite Cmod_R. rewrite Rabs_right. reflexivity.
intuition.
Qed.


Lemma WF_Matrix_qstate : forall {s e:nat} (ρ : Density (2^(e-s))), WF_qstate ρ -> WF_Matrix ρ.
Proof.  induction 1; auto with wf_db. Qed.

#[export] Hint Resolve WF_qstate_update WF_qstate_kron : QState.


(*----------------------C-Q state------------------------------------------*)


Local Open Scope R_scope.

Definition state(s e: nat) := (cstate * (qstate s e))%type.

Definition WF_state{s e:nat} (st:state s e): Prop:=
          WF_qstate (snd st).

Definition s_update_cstate{s e:nat}  i (v :nat) (m:state s e): state s e:=
  match m with 
  |(sigma, rho) => ((c_update i v sigma), rho)
  end.
  
Local Open Scope matrix_scope.
Definition s_update_qstate{s e:nat} (U: Square (2^(e-s))) (m:state s e): state s e:=
    (fst m, q_update U (snd m)).

Definition s_update{s e:nat} i ( v:nat) (U: Square (2^(e-s))) (m:state s e): state s e:=
 (c_update i v (fst m),  q_update U (snd m)).

Definition s_find{s e:nat} (sigma:cstate) (st:state s e): qstate s e:=
  match Cstate_as_OT.compare sigma (fst st) with
  |EQ _=> (snd st) 
  |_ => Zero
  end.
    

Definition s_scale{s e:nat} (p:R) (st: state s e) :=
 ((fst st), q_scale p (snd st)).

Definition s_trace{s e:nat} (st:state s e): R:=
      q_trace (snd st). 

Local Open Scope R_scope.


Lemma WF_Matrix_state : forall {s e:nat} c (ρ : Density (2^(e-s))), WF_state (c,ρ) -> WF_Matrix ρ.
Proof.  induction 1; auto with wf_db. Qed.
#[export] Hint Resolve WF_Matrix_qstate : wf_db. 
#[export] Hint Resolve WF_Matrix_state : wf_db. 

Lemma WF_state_cupdate{s e:nat}: forall i ( n:nat) (st:state s e),
WF_state st-> WF_state (s_update_cstate i n st).
Proof. unfold WF_state. destruct st. simpl. intuition. Qed.

Lemma WF_state_qupdate{s e:nat}: forall (U:Square (2^(e-s))) (st:state s e),
WF_Unitary U->WF_state st-> WF_state (s_update_qstate U st).
Proof. unfold WF_state. destruct st. simpl. apply WF_qstate_update. Qed.

Lemma WF_state_update{s e:nat}: forall i ( n:nat) (U: Square (2^(e-s))) (st:state s e),
WF_Unitary U->WF_state st-> WF_state (s_update i n U st).
Proof. unfold WF_state. destruct st. simpl. apply WF_qstate_update. Qed.

Lemma WF_state_scale'{s e}: forall (st: state s e) (p:R), 
(0<p<=1) /\ WF_state st-> WF_state (s_scale p st).
Proof.
        unfold WF_state. unfold WF_qstate. simpl. 
        intros. destruct H. split. apply (@nz_Mixed_State_scale (2^(e-s))). intuition.
        intuition. intuition. 
Qed.

Lemma WF_state_in_01{s e:nat}: forall (st:state s e), 
WF_state st -> 0<s_trace st <=1.
Proof. unfold WF_state. intros. apply WF_qstate_in_01.  intuition. 
Qed.

From Quan Require Import Basic. 
Lemma  WF_state_not_Zero{s e:nat}: forall (st:state s e),  
WF_state st -> snd st <> Zero .
Proof. unfold WF_state. unfold WF_qstate. simpl.  intros.
destruct H.
apply nz_mixed_state_trace_gt0 in H.
unfold not. intros.  rewrite H1 in H.  
rewrite Zero_trace in H. simpl in H.
lra.
Qed.

Lemma WF_state_eq {s e:nat}: forall (st st':state s e), 
snd st= snd st' -> WF_state st -> WF_state st' .
Proof. unfold WF_state. unfold WF_qstate. intros. rewrite <-H.
      assumption.   
Qed.

Lemma  s_find_scale{s e:nat}: forall (st:state s e) p x, 
s_find x (s_scale p st)= p .* (s_find x st).
Proof. intros. unfold s_scale. unfold s_find.
simpl. destruct (Cstate_as_OT.compare x (fst st)).
rewrite Mscale_0_r. reflexivity.  reflexivity.
rewrite Mscale_0_r. reflexivity. 
Qed. 

Lemma s_find_not_Zero{s e:nat}: forall sigma (st: state s e), 
s_find sigma st <>Zero -> Cstate_as_OT.eq sigma (fst st).
Proof. unfold s_find. intros. destruct (Cstate_as_OT.compare sigma
(fst st)) in H. destruct H. reflexivity.
 assumption. destruct H. reflexivity.
Qed.

Lemma s_find_eq{s e:nat}: forall sigma (st:state s e),
Cstate_as_OT.eq sigma (fst st) -> s_find sigma st =snd st.
Proof. intros. unfold s_find. 
destruct (Cstate_as_OT.compare sigma (fst st)). 
apply Cstate_as_OT.lt_not_eq in l. unfold not in l. 
 apply l in H. intuition.
reflexivity.
apply Cstate_as_OT.lt_not_eq in l. unfold not in l.
apply Cstate_as_OT.eq_sym in H.  apply l in H. intuition. 
Qed.



Definition WWF_state{s e:nat} (st:state s e): Prop:=
  WWF_qstate (snd st).

Lemma WWF_state_gt_0{s e:nat}: forall (st:state s e), 
WWF_state st -> s_trace st>0.
Proof. unfold WWF_state. unfold WWF_qstate. unfold s_trace. intros.
        apply nz_mixed_state_Cmod_1_aux. intuition. 
Qed.

Lemma WWF_state_scale{s e}: forall (st: state s e) (p:R), 
(0<p) /\ WWF_state st-> WWF_state  (s_scale p st).
Proof.
        unfold WWF_state. unfold WWF_qstate. simpl. 
        intros. destruct H. unfold WWF_state in *.
        split. apply (@nz_Mixed_State_scale_aux (2^(e-s))). intuition.
        intuition. intuition. 
Qed. 

#[export] Hint Resolve WF_state_cupdate WF_state_qupdate WF_state_qupdate : QState.
(*------------------------Distribution state------------------------------*)


Module Import StateMap:= FMapList.Make(Cstate_as_OT).

Definition dstate(s e:nat) := StateMap.t (qstate s e).

Definition d_empty(s e:nat) := StateMap.empty (qstate s e).

Definition state_to_dstate{s e:nat} (st:state s e): dstate s e:=
   StateMap.add (fst st) (snd st) (d_empty s e).

Coercion state_to_dstate : state >-> dstate.

Definition dstate_eq{s e:nat} (mu mu': dstate s e): Prop:=
    (StateMap.this mu)= (StateMap.this mu').

Fixpoint d_trace_aux{s e:nat} (mu :list(cstate * (qstate s e))): R:=
  match (mu) with
  |nil => 0
  |st::mu' =>  (s_trace st) + d_trace_aux mu'
  end.

Definition d_trace{s e:nat} (mu :dstate s e): R:=
         d_trace_aux (this mu).

Local Open Scope R_scope.
Inductive WF_dstate_aux{s e:nat}: list(cstate * (qstate s e)) -> Prop:=
|WF_nil: WF_dstate_aux nil
|WF_cons st mu': WF_state st -> WF_dstate_aux mu'->
                         (d_trace_aux (st::mu')) <=1 
                        -> WF_dstate_aux (st::mu').
                      
Definition WF_dstate{s e:nat} (mu: dstate s e):Prop:=
  WF_dstate_aux (this mu).

Definition option_qstate{s e:nat} (q: option (qstate s e)): (qstate s e) :=
    match q with 
    |None => Zero
    |Some  x => x
end.

Definition d_find{s e:nat} (sigma:cstate) (mu: dstate s e): qstate s e := 
          option_qstate (StateMap.find sigma mu).
 
Definition d_update{s e:nat} (p: state s e) (m: dstate s e) :=
  StateMap.add (fst p) (snd p) m.


Definition option_app {s e:nat} (x y: option (qstate s e)): option (qstate s e) := 
   match x ,y with
   |None,_ => y
   |_, None =>x 
   |Some x', Some y'=> Some (q_plus x' y')
   end.


Declare Scope state_scope.
Notation "mu1 +l mu2" := (StateMap.Raw.map2 option_app mu1 mu2)(at level 70, no associativity)
  : state_scope.
Notation "p *l mu" := (StateMap.Raw.map (fun x => q_scale p x) mu)(at level 70, no associativity)
  : state_scope.
Local Open Scope state_scope.

Definition d_app{s e:nat} (mu1 mu2: dstate s e): dstate s e:=
           StateMap.map2 (option_app) mu1 mu2.

Definition d_scale_not_0{s e:nat} (p:R) (mu:dstate s e): dstate s e:=
 StateMap.map (fun (x:(qstate s e)) => q_scale p x) mu.

Inductive d_scale_aux{s e:nat}: (R) -> ((list (cstate *qstate s e))) -> ((list (cstate *qstate s e))) ->Prop :=
|d_scale_0 mu : d_scale_aux 0 mu []
|d_scale_r r mu:  (r<>0)%R-> d_scale_aux r mu (StateMap.Raw.map (fun i => q_scale r i) mu).

Inductive d_scale{s e:nat}: (R) -> (dstate s e) -> (dstate s e) ->Prop :=
|d_scalar_0 mu : d_scale 0 mu (d_empty s e)
|d_scalar_r r mu: r<>0-> d_scale r mu (d_scale_not_0 r mu).

Inductive big_map2'{s e:nat}: (list R) -> (list (list (cstate *qstate s e))) ->list (cstate *qstate s e)-> Prop :=
|big_map_nil: big_map2' [] [] []
|big_map_cons_0: forall hr hd tr td r d,  d_scale_aux hr hd r ->
                                           big_map2' tr td d -> 
                                           big_map2' (hr::tr) (hd::td) (StateMap.Raw.map2 option_app r  d).


Fixpoint dstate_to_list{s e:nat}  (mu_n: list (dstate s e)) : (list (list (cstate *qstate s e))):=
match mu_n with 
|nil => nil 
|muh::mut=> (StateMap.this muh) :: (dstate_to_list mut)
end.


Inductive big_dapp'{s e:nat} :list R -> list (dstate s e) -> dstate s e -> Prop :=
|big_dapp_nil: big_dapp' nil nil (d_empty s e)
|big_dapp_cons: forall hr hd tr td r d, d_scale hr hd r-> (big_dapp' tr td d)
               ->big_dapp' (hr::tr) (hd::td) (d_app r d).

Definition dstate_pro{s e:nat}  (mu:dstate s e) (m:state s e) :R :=
     q_trace (d_find (fst m) mu) .

Definition sum_over_list (p_n:list R) := 
  big_sum (fun i => (nth i p_n 0)) (length p_n).


Lemma sum_over_list_nil : sum_over_list [] = 0.
Proof. unfold sum_over_list. simpl. reflexivity. Qed.

Lemma sum_over_list_cons : forall x l,
  sum_over_list (x :: l) = ( x + sum_over_list l)%R.
Proof.
  intros x l.
  unfold sum_over_list.
  simpl length. 
  rewrite big_sum_shift.
  simpl nth.
  reflexivity.
Qed.


Inductive WWF_dstate_aux{s e:nat}: list(cstate * (qstate s e)) -> Prop:=
|WF_nil': WWF_dstate_aux nil
|WF_cons' st mu': WWF_state st -> WWF_dstate_aux mu' 
                        -> WWF_dstate_aux (st::mu').

Definition WWF_dstate{s e:nat} (mu: dstate s e):Prop:=
  WWF_dstate_aux (StateMap.this mu).

(*-------------------------------dstate_eq-----------------------------*)

Lemma dstate_eq_refl{ s e:nat}:forall (mu:dstate s e),
 dstate_eq mu mu .
Proof. unfold dstate_eq. intuition.
Qed.

Lemma dstate_eq_sym{s e:nat}:forall (mu1 mu2: dstate s e),
dstate_eq mu1 mu2-> dstate_eq mu2 mu1 .
Proof. intros  (mu1,IHmu1) (mu2,IHmu2).
unfold dstate_eq. simpl. intuition.
Qed.

Lemma dstate_eq_trans: forall s e (mu mu1 mu2: dstate s e),
dstate_eq mu mu1 -> dstate_eq mu1 mu2
-> dstate_eq mu mu2.
Proof. intros s e (mu, IHmu) (mu1,IHmu1) (mu2,IHmu2).
  unfold dstate_eq. simpl.
  intros. rewrite H. assumption.
  Qed.

Lemma d_trace_eq{s e:nat}: forall (mu mu':dstate s e),
dstate_eq mu mu' ->
d_trace mu = d_trace mu'.
Proof. unfold d_trace; unfold dstate_eq. intros.
        rewrite H. reflexivity.
        
Qed.

Lemma WF_dstate_eq{s e}: forall (mu mu': dstate s e),
dstate_eq mu mu'-> WF_dstate mu -> WF_dstate mu'.
Proof. unfold WF_dstate. unfold dstate_eq. 
      intros (mu,IHmu) (mu', IHmu').
      simpl. intros. rewrite <- H. 
     assumption.
Qed.

Lemma d_find_eq{s e:nat}: forall (mu1 mu2:dstate s e) , 
dstate_eq mu1 mu2 ->forall x, d_find x mu1=d_find x mu2.
Proof.
unfold d_find; unfold StateMap.find; simpl; unfold dstate_eq;
simpl. intuition. rewrite H. reflexivity.
Qed.

Lemma d_scale_aux_eq{s e:nat}: forall (mu mu' mu1 mu'1: list (state s e)) (p:R),
mu=mu' ->
d_scale_aux p mu mu1->
d_scale_aux p mu' mu'1->
mu1=mu'1.
Proof. intros.  inversion H0; subst; inversion H1; subst. reflexivity.
      lra. lra. reflexivity.    
Qed.


Lemma d_scale_not_0_eq{s e:nat}: forall (mu mu' : dstate s e) (p:R),
dstate_eq mu mu'->
dstate_eq (d_scale_not_0 p mu) (d_scale_not_0 p mu'). 
Proof. intros (mu, IHmu) (mu',IHmu') . unfold dstate_eq.
unfold d_scale_not_0.
       simpl. intros. rewrite H. intuition.
Qed.


Lemma d_scale_eq{s e:nat}: forall (mu mu' mu1 mu'1: dstate s e) (p:R),
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
       

Lemma d_app_eq{s e:nat}: forall (mu mu' mu1 mu1': dstate s e),
dstate_eq mu mu'->
dstate_eq mu1 mu1'->
dstate_eq (d_app mu mu1) (d_app mu' mu1') .
Proof. unfold dstate_eq. intros
 (mu, IHmu) (mu',IHmu') (mu1,IHmu1) (mu1', IHmu1').
       simpl. intuition. rewrite H. rewrite H0. reflexivity. 
Qed.


Lemma big_map_eq{s e:nat} :forall (g1 g2:list R)  (f1 f2:(list (list (state s e))))  (mu mu':list (state s e)), 
g1=g2 -> f1=f2 ->
big_map2' g1 f1 mu->
big_map2' g2 f2 mu'->
mu=mu' .
Proof.  induction g1; intros; destruct f1; subst;
 inversion_clear H1; inversion_clear H2.
reflexivity. f_equal. apply d_scale_aux_eq with l l a; try assumption.
 reflexivity. apply IHg1 with g1 f1 f1; try assumption; try reflexivity. 
Qed.


Lemma big_dapp_eq{s e:nat} :forall (g:list R)  (f:(list (dstate s e)))  (mu mu':dstate s e), 
big_dapp' g f mu->
big_dapp' g f mu'->
dstate_eq mu mu' .
Proof. induction g; intros; inversion H; subst. 
inversion_clear H0. apply dstate_eq_refl.
inversion_clear H0. apply d_app_eq.
apply d_scale_eq with hd hd a. apply dstate_eq_refl. assumption. 
assumption. apply IHg with td. assumption. assumption.  
Qed.
       
(*---------------------------------------WF--------------------------------------*)


Lemma trace_state_dstate{s e:nat}: forall  (st:state s e), 
d_trace st= s_trace st .
Proof. intros. unfold d_trace. simpl. unfold s_trace. rewrite Rplus_0_r.
reflexivity.   
Qed.

Lemma WF_state_dstate_aux{s e:nat}: forall (st:state s e), 
WF_state st <-> WF_dstate_aux [st] .
Proof. split; unfold WF_dstate;
       destruct st; simpl; intros. 
       apply WF_cons. intuition. apply WF_nil. 
       unfold WF_state in H.  unfold WF_qstate in H. simpl in H.
       unfold d_trace_aux. unfold s_trace. simpl. rewrite Rplus_0_r.
       apply nz_mixed_state_Cmod_1. intuition.
       inversion_clear H. intuition. 
Qed.


Lemma WF_state_dstate{s e:nat}: forall (st:state s e), 
WF_state st <-> WF_dstate st.
Proof. split; unfold WF_dstate;
       destruct st; simpl; intros;
       apply  WF_state_dstate_aux; try assumption.
Qed.



Lemma WWF_dstate_gt_0_aux{s e:nat}: forall (mu:list( cstate*qstate s e)),
WWF_dstate_aux mu-> 0 <= ((d_trace_aux mu)).
Proof. intros. induction mu.
--simpl.  intuition.
--inversion_clear H. apply IHmu in H1. 
 simpl. apply Rplus_le_le_0_compat.  
apply WWF_state_gt_0 in H0. simpl in H0. 
intuition. intuition. 
Qed.



Lemma WWF_dstate_not_0{s e:nat}:forall (mu: list (cstate *qstate s e)),
mu<>[]->
WWF_dstate_aux mu -> d_trace_aux mu <> 0 .
Proof. intros. destruct mu. intuition. simpl.
       assert(s_trace p + d_trace_aux mu>0).
       rewrite Rplus_comm.
       apply Rplus_le_lt_0_compat. 
       apply WWF_dstate_gt_0_aux. inversion_clear H0.
       assumption. 
       apply WWF_state_gt_0.
       inversion_clear H0. assumption.
      lra.
Qed.





Lemma WWF_dstate_aux_to_WF_dstate_aux{s e}: forall (mu: list (cstate *qstate s e)),
WWF_dstate_aux mu /\ d_trace_aux mu <=1 <-> WF_dstate_aux mu.
Proof.  intros. split; intros. induction mu. apply WF_nil. 
        destruct H. inversion_clear H. simpl in H0.
        apply WF_cons. apply WWF_qstate_to_WF_qstate.
        split. apply H1. 
        unfold s_trace in H0. simpl in H0.
        apply Rplus_le_reg_pos_r with (d_trace_aux mu); try assumption.
        apply WWF_dstate_gt_0_aux; try  assumption. 
        apply IHmu.  split. intuition.   
        apply Rplus_le_1 with (s_trace a); try assumption.
        apply WWF_state_gt_0. assumption. assumption.
        induction mu.   split. apply WF_nil'. simpl. 
        lra. inversion_clear H. split. apply WF_cons'.
        apply WWF_qstate_to_WF_qstate. apply H0.
         apply IHmu. assumption. assumption.  
Qed.


Lemma WWF_dstate_to_WF_dstate:forall {s e : nat} (mu : dstate s e),
WWF_dstate mu /\ d_trace mu <= 1 <-> WF_dstate mu .
Proof. intros s e(mu, IHmu). unfold WWF_dstate.
      unfold WF_dstate. unfold d_trace. simpl.
      apply WWF_dstate_aux_to_WF_dstate_aux.
Qed.


Lemma WF_dstate_in01_aux{s e:nat}: forall (mu:list( cstate*qstate s e)),
WF_dstate_aux mu-> 0<=((d_trace_aux mu))<=1.
Proof. intros. induction mu.
--simpl.  intuition.
--inversion_clear H. apply IHmu in H1. 
split. simpl. apply Rplus_le_le_0_compat. 
apply WF_state_in_01 in H0. simpl in H0. 
intuition. intuition. intuition. 
Qed.

Lemma WF_dstate_in01{s e:nat}: forall (mu:dstate s e),
WF_dstate mu-> 0<=((d_trace mu)) <=1.
Proof. unfold WF_dstate. intros (mu, IHmu) H.
       unfold d_trace. apply WF_dstate_in01_aux.
       intuition. 
Qed.


Lemma WF_dstate_gt0_le1{s e:nat}:forall (mu: list (cstate *qstate s e)),
mu<>[]->
WF_dstate_aux mu ->0< d_trace_aux mu <=1.
Proof.  intros. destruct mu. intuition. simpl.
rewrite Rplus_comm. split.
apply Rplus_le_lt_0_compat. 
apply WWF_dstate_gt_0_aux. inversion_clear H0.
apply WWF_dstate_aux_to_WF_dstate_aux.
assumption.  
apply WF_state_in_01.
inversion_clear H0.  assumption. 
assert(d_trace_aux mu + s_trace p= d_trace_aux ((p :: mu)))%R.
simpl. rewrite Rplus_comm.  
reflexivity. rewrite H1.
apply WF_dstate_in01_aux. assumption.
Qed.

Lemma WWF_dstate_empty: forall s e, WWF_dstate (d_empty s e) .
Proof. intros. unfold d_empty.  unfold WWF_dstate.
 simpl. unfold StateMap.Raw.empty.
apply WF_nil'. 
Qed.


Lemma WF_dstate_empty: forall s e, WF_dstate (d_empty s e) .
Proof. intros. unfold d_empty.  unfold WF_dstate. simpl. unfold Raw.empty.
apply WF_nil. 
Qed.

(*WF_d_scale*)

Local Open Scope R_scope.
Lemma d_trace_map{s e:nat}: forall (mu:list (cstate * qstate s e)) (p:R),
(0<p)-> d_trace_aux (StateMap.Raw.map (fun x : qstate s e =>q_scale p x) mu)=
p * d_trace_aux mu.
Proof. intros. induction mu.  simpl. rewrite Rmult_0_r. intuition.
destruct a. simpl.
unfold d_trace. unfold s_trace. 
rewrite IHmu. simpl.
unfold q_scale.
unfold q_trace. 
rewrite trace_mult_dist.
rewrite Rmult_plus_distr_l.
rewrite Cmod_mult. rewrite Cmod_R.
rewrite Rabs_right. reflexivity. intuition.
Qed.

Lemma d_trace_scale_aux{s e:nat}:forall (mu mu': list (state s e)) (p:R), 
(0<=p)-> d_scale_aux p mu mu'-> d_trace_aux (mu')= p * (d_trace_aux mu).
Proof.  intros.
inversion_clear H0. 
-unfold d_trace_aux.  rewrite Rmult_0_l. reflexivity.
-apply (d_trace_map ). lra.
Qed.

Lemma d_trace_scale_not_0{s e:nat}:forall (mu: dstate s e) (p:R), 
(0<p)-> d_trace (d_scale_not_0 p mu)= p * (d_trace mu) .
Proof.  intros (mu, IHmu) p Hp.
        unfold d_trace. 
        unfold d_scale_not_0. 
        unfold map. simpl.
        rewrite d_trace_map.
        reflexivity. 
        assumption.
Qed.

Lemma d_trace_scale{s e:nat}:forall (mu mu': dstate s e) (p:R), 
(0<=p)->d_scale p mu mu'-> d_trace (mu')= p * (d_trace mu).
Proof. intros. inversion_clear H0. 
-unfold d_trace. unfold d_empty.  simpl. rewrite Rmult_0_l. reflexivity.
-apply d_trace_scale_not_0. lra.
Qed.



Lemma WWF_dstate_map{s e}: forall (mu:list (cstate *qstate s e)) p, 
(0<p)
->WWF_dstate_aux mu 
->@WWF_dstate_aux s e
((StateMap.Raw.map (fun x : qstate s e =>q_scale p x) mu)).
Proof. intros. induction mu. 
        --simpl. intuition.
        --inversion_clear H0. destruct a. 
        simpl.  apply (@WF_cons' s e). unfold WWF_state in *.
        apply WWF_qstate_scale. split; assumption.
        apply IHmu. intuition.
Qed.

Lemma WWF_d_scale_aux{s e:nat}: forall (mu mu':list (state s e)) p,
(0<=p)->
d_scale_aux p mu mu'
->WWF_dstate_aux mu 
->WWF_dstate_aux (mu').
Proof. intros. inversion_clear H0. apply WWF_dstate_empty.
       apply WWF_dstate_map. lra. assumption.
Qed.


Lemma WWF_d_scale_not_0{s e}: forall (mu:dstate s e) p, 
(0<p)
->WWF_dstate mu 
->WWF_dstate(d_scale_not_0 p mu).
Proof. unfold WF_dstate.
        unfold d_trace.
        unfold d_scale_not_0.
        simpl. intros  (mu,IHmu) p H0 H.
        unfold map.  simpl. 
        apply WWF_dstate_map. intuition.
        intuition.
Qed.

Lemma WWF_d_scale{s e:nat}: forall (mu mu':dstate s e) p,
(0<=p)->
d_scale p mu mu'
->WWF_dstate mu 
->WWF_dstate(mu').
Proof. intros. inversion_clear H0. apply WWF_dstate_empty.
       apply WWF_d_scale_not_0. lra. assumption.
Qed.



Lemma WF_dstate_map{s e}: forall (mu:list (cstate *qstate s e)) p, 
(0<p<=1)
->WF_dstate_aux mu 
->@WF_dstate_aux s e
((StateMap.Raw.map (fun x : qstate s e => q_scale p x) mu)).
Proof. intros. induction mu. 
        --simpl. intuition.
        --inversion_clear H0. destruct a.  
        simpl. econstructor. apply WF_qstate_scale; split; try assumption.
        apply IHmu. intuition.  
        simpl. unfold s_trace. simpl. rewrite q_trace_scale. 
        rewrite d_trace_map.
        rewrite <-Rmult_plus_distr_l. rewrite<-Rmult_1_l.
        apply Rmult_le_compat; try lra; try assumption; try apply H. 
        apply Rplus_le_le_0_compat. apply WF_qstate_in_01 in H1. intuition.
        apply WF_dstate_in01_aux. assumption. apply H. apply H.  
Qed.
   
Lemma WF_d_scale_aux{s e}: forall (mu mu':list (state s e)) p, 
(0<=p<=1)->
d_scale_aux p mu mu'
->WF_dstate_aux mu 
->WF_dstate_aux mu'.
Proof. intros. inversion_clear H0. econstructor.
apply WF_dstate_map; try assumption. lra. 
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
        apply WF_dstate_map.  intuition.
        intuition.
Qed.


Lemma WF_d_scale{s e:nat}: forall (mu mu':dstate s e) p,
(0<=p<=1)->
d_scale p mu mu'
->WF_dstate mu 
->WF_dstate(mu').
Proof. intros. inversion_clear H0. apply WF_dstate_empty.
       apply WF_d_scale_not_0. lra. assumption.
Qed.

(*WF_d_app*)

Lemma map2_r_refl{s e}: forall (mu: list (cstate * qstate s e)), 
 StateMap.Raw.map2_r option_app (mu) =  mu.
Proof. intros .
       induction mu. simpl. reflexivity.
       destruct a. simpl.   f_equal.
        apply (IHmu).
Qed.

Lemma map2_l_refl{s e:nat}: forall (mu: list (cstate * qstate s e)), 
 StateMap.Raw.map2_l option_app (mu) =  mu.
Proof. intros .
       induction mu. simpl. reflexivity.
       destruct a. simpl.   f_equal.
        apply (IHmu).
Qed.

Lemma map2_nil_l{s e:nat}: forall (mu:list (cstate * qstate s e)), 
 ( [] +l mu) = mu.
Proof. intros.  
       simpl. rewrite map2_r_refl. reflexivity.
Qed.

Lemma map2_nil_r{s e:nat}:forall (mu:list (cstate *qstate s e)),
 mu +l []= mu.
Proof. induction mu. 
     --reflexivity.
     --destruct a. simpl. rewrite map2_l_refl. reflexivity. 
Qed.


Lemma d_app_empty_l{s e:nat}: forall (mu:dstate s e), 
dstate_eq (d_app (d_empty s e) mu)  mu .
Proof. intros (mu , IHmu).
       unfold d_app. unfold d_empty.
       unfold empty.
       unfold Raw.empty.
       unfold map2. unfold dstate_eq.
       simpl. apply map2_r_refl.
Qed.

Lemma d_app_empty_r{s e:nat}: forall (mu:dstate s e), 
dstate_eq (d_app mu (d_empty s e))  mu .
Proof. intros (mu , IHmu).
       unfold d_app. unfold d_empty.
       unfold empty.
       unfold Raw.empty.
       unfold map2. unfold dstate_eq.
       simpl. apply map2_nil_r.
Qed.

Lemma nil_d_app{s e:nat}: forall (mu mu': dstate s e), 
 this mu = [] -> this mu'=[]  ->  this (d_app mu mu') = [] .
Proof. intros  (mu ,IHmu); induction mu; intros (mu', IHmu');
       induction mu';  simpl;
       intros; simpl. reflexivity.
       simpl in H. discriminate.
       discriminate.
       discriminate.
Qed.

Lemma d_trace_app_aux{s e:nat}: forall (mu mu':list (cstate *qstate s e)),
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
     rewrite IHmu; try assumption. unfold s_trace. unfold q_trace. unfold q_plus. 
    simpl. rewrite nz_mixed_state_Cmod_plus_aux; try apply H3 ; try apply H5.
    repeat rewrite <-Rplus_assoc. 
    f_equal. repeat rewrite Rplus_assoc.   
    f_equal. apply Rplus_comm. 
    simpl. rewrite Rplus_assoc.
    rewrite <-Rplus_assoc with (r2:=d_trace_aux mu).
     rewrite <-Rplus_comm with  (r1:=d_trace_aux mu').
     rewrite <-Rplus_assoc. 
     rewrite Rplus_comm with (r2:= s_trace (c0, q0)).
     f_equal. apply IHmu'. intuition. intuition. 
Qed.


Lemma d_trace_app{s e:nat}: forall (mu mu':dstate s e),
WWF_dstate mu -> WWF_dstate mu'->
d_trace (d_app  mu mu') = (d_trace mu) + (d_trace mu').
Proof.  intros  (mu,IHmu) (mu',IHmu'). unfold WF_dstate. unfold d_trace.
    unfold d_app. unfold StateMap.map2. simpl. intros.
     apply d_trace_app_aux. intuition. intuition. 
Qed.

Lemma WWF_d_app_aux{s e:nat}: forall (mu mu':list (cstate*qstate s e)),
WWF_dstate_aux mu -> WWF_dstate_aux mu'-> @WWF_dstate_aux s e
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
      --apply WF_cons'.  apply WWF_q_plus. 
        intuition. intuition. 
        apply IHmu. intuition. intuition. 
    --apply WF_cons'.   intuition.
        apply IHmu'.
        assumption.
Qed.

Lemma WWF_d_app{s e:nat}: forall (mu mu':dstate s e),
WWF_dstate mu -> WWF_dstate mu'->
WWF_dstate  (d_app mu mu').
Proof. unfold WF_dstate. unfold d_app. unfold d_trace. unfold StateMap.map2. 
 intros  (mu, IHmu) (mu', IHmu') p1 p2. simpl.
 apply WWF_d_app_aux. assumption. assumption. 
Qed.


Lemma WF_d_app_aux{s e:nat}: forall (mu mu':list (cstate*qstate s e)), 
WF_dstate_aux mu -> WF_dstate_aux mu'-> (d_trace_aux (mu +l mu')<=1)
->
WF_dstate_aux (mu +l mu').
Proof. intros. apply WWF_dstate_aux_to_WF_dstate_aux. 
        apply WWF_dstate_aux_to_WF_dstate_aux in H.
       apply WWF_dstate_aux_to_WF_dstate_aux in H0.
       split. apply WWF_d_app_aux. intuition. intuition. 
       assumption.
Qed.

Lemma WF_d_app{s e:nat}: forall (mu mu':dstate s e),
WF_dstate mu -> WF_dstate mu'-> (d_trace (d_app mu mu')<=1)->
WF_dstate  (d_app mu mu').
Proof. unfold WF_dstate. unfold d_app. unfold d_trace. unfold StateMap.map2. 
 intros  (mu, IHmu) (mu', IHmu') p1 p2. simpl.
 apply WF_d_app_aux. assumption. assumption. 
Qed.




Lemma Rplus_mult_le_1': forall (p1 p2 r1 r2:R),
0 < p1 <=1->
0 < p2 <=1->
p1+p2<=1->
0<=r1 <= 1->
0<=r2<= 1->
p1 * r1 + p2 * r2<= 1 .
Proof. intros. 
assert(r1<r2\/ r2<=r1).
apply Rlt_or_le.
destruct H4.
apply Rle_trans with ((p1 * r2)%R + (p2 * r2)%R)%R.
apply Rplus_le_compat;
apply Rmult_le_compat;
intuition. 
rewrite <-Rmult_plus_distr_r. 
assert((p1 + p2) * r2 <= 1*1).
apply Rmult_le_compat. 
assert(0<p1 + p2). apply Rplus_lt_0_compat. intuition. intuition.
intuition. intuition. intuition. intuition. 
rewrite Rmult_1_l in H5.
intuition.

apply Rle_trans with (p1 * r1 + p2 * r1 ).
apply Rplus_le_compat;
apply Rmult_le_compat;
intuition. 
rewrite <-Rmult_plus_distr_r. 
assert((p1 + p2) * r1 <= 1*1).
apply Rmult_le_compat. 
assert(0<p1 + p2). apply Rplus_lt_0_compat. intuition. intuition.
intuition. intuition. intuition. intuition. 
rewrite Rmult_1_l in H5.
intuition.
Qed.

Lemma WF_d_app_aux'{s e:nat}: forall (mu mu':list (state s e)) (p1 p2:R),
(0<p1<=1/\0<p2<=1)-> (p1+p2<=1)->
WF_dstate_aux mu -> WF_dstate_aux mu'-> 
WF_dstate_aux ( (p1 *l mu) +l ( p2 *l mu')).
Proof.
 intros. 
 apply WF_d_app_aux. 
 apply WF_dstate_map. intuition. intuition.
 apply WF_dstate_map. intuition. intuition.
 rewrite d_trace_app_aux.  repeat rewrite d_trace_map.
 apply Rplus_mult_le_1'. intuition. intuition. intuition.
 apply WF_dstate_in01_aux. assumption. 
 apply WF_dstate_in01_aux. assumption.
 intuition. intuition. 
 apply WWF_dstate_map. intuition.
 apply WWF_dstate_aux_to_WF_dstate_aux.
  intuition.
 apply WWF_dstate_map. intuition. 
 apply WWF_dstate_aux_to_WF_dstate_aux.
 intuition.
Qed.

Lemma WF_d_app'{s e:nat}: forall (mu mu':dstate s e) (p1 p2:R),
(0<p1<=1/\0<p2<=1)-> (p1+p2<=1)->
WF_dstate mu -> WF_dstate mu'-> 
@WF_dstate s e (d_app (d_scale_not_0 p1 mu) (d_scale_not_0 p2 mu')).
Proof. unfold WF_dstate. unfold d_app. unfold d_trace.
 unfold StateMap.map2.
 intros  (mu, IHmu) (mu', IHmu') p1 p2. simpl. 
 intros. apply WF_d_app_aux'; try assumption.
Qed.

(*WF_big_dapp'*)

Lemma WWF_dstate_big_map{s e:nat}: forall (p_n:list R) (mu_n:list (list (state s e))) (mu:list (state s e)), 
Forall (fun x=> WWF_dstate_aux x) mu_n ->
big_map2' (p_n) mu_n mu->
(Forall (fun x => 0<= (x) ) p_n)-> 
WWF_dstate_aux mu.
Proof. induction p_n; intros; inversion H0; subst.
     -econstructor.
     -inversion_clear H; inversion_clear H1.
     apply WWF_d_app_aux. eapply WWF_d_scale_aux. apply H.  apply H4.
      assumption.
      apply IHp_n with td; try assumption.
Qed.

Lemma  Forall_WWF_WF{s e:nat}: forall (mu_n:list (dstate s e)),
Forall (fun x : dstate s e => WF_dstate x) mu_n<->
Forall (fun x : dstate s e => WWF_dstate x) mu_n /\
Forall  (fun x : dstate s e =>  d_trace x <=1 ) mu_n.
Proof. induction mu_n; split; intros;
      try split; try apply Forall_nil;
       inversion_clear H;
      econstructor; try  apply WWF_dstate_to_WF_dstate;
      try assumption; try apply H0;try  apply IHmu_n; try assumption.
      inversion_clear H0. inversion_clear H1.
      auto. 
      inversion_clear H0. inversion_clear H1.
      auto. 
Qed.

Lemma WWF_dstate_to_list{ s e:nat}: forall mu_n, 
Forall (fun x : dstate s e => WWF_dstate x) mu_n <->
Forall (fun x : list (cstate * qstate s e) =>
  WWF_dstate_aux x) (dstate_to_list mu_n) .
Proof. induction mu_n; simpl in*; split; intros; try econstructor; inversion_clear H.
       assumption. apply IHmu_n. apply H1. apply H0.
       apply IHmu_n. apply H1.
Qed.

From Quan Require Import Forall_two.
Lemma WWF_dstate_big_dapp{s e:nat}: forall (p_n:list R) (mu_n:list (dstate s e)) (mu:dstate s e), 
Forall_two (fun x y=> 0<y -> WWF_dstate x) mu_n p_n->
big_dapp' (p_n) mu_n mu->
(Forall (fun x => 0<= (x) ) p_n)-> 
WWF_dstate mu.
Proof. induction p_n. intros. inversion_clear H0.
    apply WWF_dstate_empty.
    intros. simpl in *.
    inversion H0; subst. 
    apply WWF_d_app. 
    destruct (Req_dec a 0). rewrite H2 in *. inversion_clear H4.
     apply WWF_dstate_empty. lra.  
    apply WWF_d_scale with hd a. 
    inversion_clear H1. intuition.
    assumption. inversion_clear H. apply H3. inversion_clear H1. lra.  
   apply IHp_n with td.
      inversion_clear H. assumption.
     assumption. inversion_clear H1. assumption.
Qed.

Lemma d_scale_aux_trace_le{s e:nat}:forall (mu mu':list (state s e)) r,  
0<=r->
WF_dstate_aux mu ->
d_scale_aux r mu mu'-> 
d_trace_aux mu' <=r.
Proof.  intros. inversion_clear H1. 
       simpl. lra.  rewrite d_trace_map.
       apply Rle_trans with (r * 1)%R.
       apply Rmult_le_compat_l. lra.
       apply WF_dstate_in01_aux . assumption.
       rewrite Rmult_1_r. lra. lra.  
Qed.


Lemma d_scale_trace_le{s e:nat}:forall (mu mu':dstate s e) r,  
0<=r->
WF_dstate mu ->
d_scale r mu mu'-> 
d_trace mu' <=r.
Proof.  intros. inversion_clear H1. 
       unfold d_trace. unfold d_empty.
       simpl. lra.  rewrite d_trace_scale_not_0.
       apply Rle_trans with (r * 1)%R.
       apply Rmult_le_compat_l. lra.
       apply WF_dstate_in01. assumption.
       rewrite Rmult_1_r. lra. lra.  
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


Lemma d_trace_le_1_big_dapp{s e:nat}: forall (p_n:list  R) (mu_n:list (dstate s e)) (mu:dstate s e), 
Forall_two (fun x y=> 0<y -> WF_dstate x) mu_n p_n->
big_dapp' (p_n) mu_n mu->
(Forall (fun x =>0<=  (x) ) p_n)->
d_trace mu <= sum_over_list p_n.
Proof. induction p_n. intros. inversion_clear H0.
        rewrite sum_over_list_nil.
        unfold d_trace. unfold StateMap.this.
        simpl. lra. 
        intros.  simpl in *.
         inversion H0; subst.
         rewrite d_trace_app.
         rewrite sum_over_list_cons.
         apply Rplus_le_compat. 
         destruct (Req_dec a 0). rewrite H2 in *. inversion_clear H4.
         unfold d_trace. simpl. lra. lra.  
          apply d_scale_trace_le with hd.
          inversion_clear H1. assumption.
           inversion_clear H. apply H3. inversion_clear H1. lra. 
         simpl. assumption.
         apply IHp_n with td. inversion_clear H.
         assumption. assumption.
         inversion_clear H1. assumption.
         destruct (Req_dec a 0). rewrite H2 in *. inversion_clear H4.
         apply WWF_dstate_empty. lra. 
         apply WWF_d_scale with  hd a. 
         inversion_clear H1. intuition.
         assumption. inversion_clear H.
         apply WWF_dstate_to_WF_dstate. apply H3.
         inversion_clear H1. lra.
         apply WWF_dstate_big_dapp with p_n td.
         inversion_clear H. eapply Forall_two_impli; try apply H3.
         simpl.  intros. apply WWF_dstate_to_WF_dstate. apply H. assumption.
         inversion_clear H. assumption. 
  inversion_clear H1. assumption.
Qed.



Lemma WF_dstate_big_dapp{s e:nat}: forall (p_n:list R) (mu_n:list (dstate s e)) (mu:dstate s e), 
Forall_two (fun x y=> 0<y -> WF_dstate x) mu_n p_n->
big_dapp' p_n mu_n mu->
(Forall (fun x => 0<= (x)) p_n)->
sum_over_list p_n<=1->
WF_dstate mu.
Proof. intros. apply WWF_dstate_to_WF_dstate.
split. apply WWF_dstate_big_dapp with p_n mu_n .
eapply Forall_two_impli; try apply H.
 simpl.  intros. apply WWF_dstate_to_WF_dstate. auto.
assumption. assumption. 
apply Rle_trans with (sum_over_list p_n).
apply d_trace_le_1_big_dapp with mu_n. 
assumption. assumption. assumption.
assumption.
Qed.


(*-------------------------d_find---------------------------------------------*)

Lemma s_d_find_eq{s e:nat} (x:cstate) (st: state s e): 
d_find x st = s_find x st.
Proof. unfold d_find. simpl. unfold s_find.
     unfold StateMap.find. simpl. 
    destruct  (Cstate_as_OT.compare x (fst st)).
    reflexivity.
    reflexivity.
    reflexivity. 
Qed.

Lemma d_find_empty{s e:nat}: forall x, d_find x (d_empty s e)=Zero.
Proof. intros. unfold d_find. simpl. reflexivity. Qed.

Module Import MC := OrderedTypeFacts(Cstate_as_OT).

(*d_find_scale*)
Lemma d_find_map{s e:nat}: forall (mu:list (state s e)) p x, 
 option_qstate (StateMap.Raw.find x (p *l mu))= p .* (option_qstate (StateMap.Raw.find x mu)).
Proof. intros. induction mu.  simpl.  rewrite Mscale_0_r.  reflexivity.
      simpl. destruct a.   destruct (Cstate_as_OT.compare x c); simpl;
       MC.elim_comp; simpl.
      rewrite Mscale_0_r.  reflexivity.
      reflexivity. apply IHmu.
Qed.

Lemma  d_find_scale_not_0{s e:nat}: forall (mu:dstate s e) p x, 
d_find x (d_scale_not_0 p mu)= p .* (d_find x mu) .
Proof. intros (mu, IHmu) p x.  unfold d_find. unfold d_scale_not_0. 
       unfold StateMap.map. unfold StateMap.find. simpl.  
       rewrite d_find_map. reflexivity.
Qed.


Lemma d_find_scale{s e:nat}: forall (mu mu':dstate s e) p x, 
d_scale p mu mu'->
d_find x mu'= p .* (d_find x mu) .
Proof. intros. inversion H;subst.
-rewrite d_find_empty. rewrite Mscale_0_l. reflexivity.
-apply d_find_scale_not_0.
Qed.

(*d_find_app*)

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


Lemma In_mem{s e:nat}: forall (mu:dstate s e) x,
(StateMap.In ( elt := qstate s e) x mu) <-> mem x mu =true .
Proof. intros. split. apply StateMap.mem_1.
       apply StateMap.mem_2.
Qed.

Lemma not_in_Zero{s e:nat}:forall (mu: dstate s e) x,
~ StateMap.In (elt:=qstate s e) x mu -> d_find x mu=Zero .
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

Lemma  not_in_app{s e:nat}: forall (mu mu': list (cstate * qstate s e)) x,
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
       rewrite <-e0 in l0.
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

Lemma  not_in_app'{s e:nat}: forall (mu1 mu2: dstate s e) x,
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


Lemma d_app_find{s e:nat}:  forall (mu1 mu2:dstate s e) x , 
d_find x (d_app mu1 mu2)= (d_find x mu1) .+ (d_find x mu2).
Proof.   
        intros.  assert((StateMap.In (elt:=qstate s e) x mu1 \/
        StateMap.In (elt:=qstate s e) x mu2) \/
        ~((StateMap.In (elt:=qstate s e) x mu1 \/
        StateMap.In (elt:=qstate s e) x mu2))).
        apply classic.
        destruct H.
        unfold d_find.
        unfold d_app.
        rewrite StateMap.map2_1.
        unfold option_app.
        destruct (StateMap.find (elt:=qstate s e) x mu1).
        destruct (StateMap.find (elt:=qstate s e) x mu2).
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


(*--------------------------d_scale----------------------------------------*)
Lemma d_scale_aux_exsits{s e:nat}: forall r (mu: list (state s e)),
exists (mu':list (state s e)), d_scale_aux r mu mu' .
Proof. intros. assert(r=0 \/ r<>0). apply classic. 
   destruct H. exists []. rewrite H. econstructor.
   exists (r *l mu). econstructor. assumption.
Qed.

Lemma  d_scale_aux_sorted{s e:nat}: forall a (mu mu': list (state s e)),
d_scale_aux a mu mu'->
Sorted.Sorted (StateMap.Raw.PX.ltk (elt:=qstate s e)) mu->
Sorted.Sorted (StateMap.Raw.PX.ltk (elt:=qstate s e)) mu'.
Proof. intros. inversion_clear H; try econstructor. 
        apply StateMap.Raw.map_sorted. assumption.
Qed.

Lemma d_scale_exsits{s e:nat}: forall r (mu:dstate s e),
exists (mu':dstate s e), d_scale r mu mu' .
Proof. intros. assert(r=0 \/ r<>0). apply classic. 
   destruct H. exists (d_empty s e). rewrite H. apply d_scalar_0.
   exists (d_scale_not_0  r mu). apply d_scalar_r. assumption.
Qed.

Lemma d_scale_not_0_nil{s e:nat}: forall (mu:dstate s e) p, 
this (d_scale_not_0 p mu) = nil <-> this mu = [].
Proof. intros (mu, IHmu) p. 
       split. destruct mu. intuition.
       destruct p0.
       simpl. discriminate.
       intros. simpl.
       induction mu. simpl. reflexivity.
       simpl in H. discriminate.
Qed.

Lemma d_scale_not_nil{s e:nat}: forall (mu:dstate s e) p, 
 this mu<>nil <-> this (d_scale_not_0 p mu) <> nil.
Proof. intros (mu, IHmu) p.
      destruct mu. intuition.
       intros. 
       split;  unfold not; intros.
        apply d_scale_not_0_nil in H0.
        apply H in H0. intuition.
        apply d_scale_not_0_nil with (p:=p) in H0.
        apply H in H0.
       intuition.
Qed.

Lemma d_scale_aux_intergral{s e:nat}: forall (mu mu': list (state s e)) (p : R),
d_scale_aux p mu mu'->
(mu = [] \/ p=0 <->  mu' = []).
Proof. intros. split; intros. inversion H;subst; try reflexivity.
       destruct H0. rewrite H0 in *. 
       inversion H; subst. lra.  simpl. reflexivity. lra.
       inversion H; subst. right. reflexivity.
       left. destruct mu. reflexivity. destruct s0.  simpl in H4. discriminate H4.
Qed.

Lemma d_scale_integral{s e:nat}: forall (mu mu':dstate s e) p, 
 (d_scale p mu mu') ->this mu'=[]-> p=0 \/ this mu =[].
Proof. intros.  inversion H;subst. left. reflexivity.
   right. apply d_scale_not_0_nil with p. assumption.
Qed.



Lemma d_scale_not_0_empty{s e:nat}: forall p, 
   dstate_eq (d_scale_not_0 p (d_empty s e)) (d_empty s e).
Proof. intros . unfold d_empty. unfold dstate_eq.
     unfold d_scale_not_0. simpl. unfold Raw.empty. reflexivity.
Qed.

(*scale 1 *)
Lemma map_1_l{s e:nat}: forall (mu:list (state s e)), 
(1 *l mu) = mu.
Proof.
induction mu. reflexivity.
destruct a. simpl.  f_equal. 
unfold q_scale. rewrite Mscale_1_l.
  reflexivity. assumption. 
Qed.


Lemma d_scale_not_0_1_l{s e:nat}: forall (mu:dstate s e), 
dstate_eq (d_scale_not_0 1 mu) mu.
Proof. intros (mu, IHmu). unfold dstate_eq. 
        unfold d_scale_not_0; unfold StateMap.map.
        simpl. apply map_1_l.
Qed.

Lemma d_scale_1_l{s e:nat}: forall (mu mu':dstate s e), 
d_scale 1 mu mu'->
dstate_eq (mu') mu.
Proof. intros. inversion H;subst. lra.
apply d_scale_not_0_1_l.
Qed.


(*scale assoc *)
Lemma map_assoc{s e:nat}: forall (p1 p2:R) (mu:list (state s e)), 
(p1 *l (p2 *l mu)) =  ((p1* p2)%R *l  mu).
Proof. intros. 
induction mu. simpl. reflexivity.
destruct a.
 simpl. rewrite IHmu. f_equal. f_equal.
unfold q_scale.
rewrite Mscale_assoc. 
rewrite RtoC_mult. 
reflexivity.
Qed.


Lemma d_scale_not_0_assoc{s e:nat}: forall (p1 p2:R) (mu:dstate s e), 
dstate_eq (d_scale_not_0 p1 (d_scale_not_0 p2 mu)) (d_scale_not_0 (Rmult p1  p2) mu).
Proof.
  intros p1 p2 (mu, IHmu). unfold dstate_eq. unfold d_scale_not_0. unfold StateMap.map.
  simpl.  apply map_assoc.
  Qed.

  Lemma d_scale_aux_assoc{s e:nat}: forall (p1 p2:R) (mu mu' mu'' mu''':list (state s e)), 
  d_scale_aux p2 mu mu'->
  d_scale_aux p1 mu' mu''->
  d_scale_aux (Rmult p1 p2) mu mu'''->
   mu''= mu'''.
  Proof. intros. inversion H;subst; inversion H0; subst; inversion H1;subst;
  try reflexivity; try lra.
  -symmetry in H5. apply Rmult_integral in H5. lra. 
  - apply map_assoc.
Qed.

Lemma d_scale_assoc{s e:nat}: forall (p1 p2:R) (mu mu' mu'' mu''':dstate s e), 
d_scale p2 mu mu'->
d_scale p1 mu' mu''->
d_scale (Rmult p1 p2) mu mu'''->
dstate_eq mu'' mu'''.
Proof. intros. inversion H;subst; inversion H0; subst; inversion H1;subst;
try reflexivity; try lra.
-symmetry in H5. apply Rmult_integral in H5. lra. 
- apply d_scale_not_0_assoc.
Qed.



(*------------------------------d_app-----------------------------*)

Lemma map2_app_not_nil{s e:nat}: forall  (mu mu':list (cstate * qstate s e)),
mu<>nil \/  mu'<>nil <->
mu +l mu' <> [] .
Proof. induction mu; intros; split; intros.  
       destruct H. intuition. destruct mu'. intuition.
       destruct p.   simpl. discriminate.
       rewrite map2_nil_l in *. right. assumption.
       destruct mu'. rewrite map2_nil_r. discriminate.
       destruct a. destruct p.   simpl.
       destruct (Cstate_as_OT.compare c c0).
       discriminate. discriminate.
     discriminate. left. discriminate.
Qed.


Require Import Classical_Prop.
Lemma map2_app_nil: forall s e (x y: list (cstate *qstate s e)),
[] = StateMap.Raw.map2 option_app x y <-> x=nil /\ y=nil.
Proof. intros. split; intros. assert(x=[]\/x<>[]).
        apply classic.
        assert(y=[]\/y<>[]).
       apply classic. destruct H0. destruct H1.
       intuition. pose (map2_app_not_nil x y).
       destruct i. destruct H2. right. assumption. symmetry. apply H.  
       destruct H1. 
       pose (map2_app_not_nil x y).
       destruct i. destruct H2. left. assumption. symmetry. apply H.  
       pose (map2_app_not_nil x y).
       destruct i. destruct H2. right. assumption. symmetry. apply H.  
        destruct H. rewrite H. rewrite H0. simpl. reflexivity.
Qed.

(*dapp comm*)
Lemma map2_comm{s e:nat}: forall (mu mu': list (cstate * qstate s e)),
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
        rewrite e0 in l. apply Cstate_as_OT.lt_not_eq in l.
        unfold not in l. intuition.
        simpl. f_equal. 
        apply IHmu. 
        rewrite e0 in l. apply Cstate_as_OT.lt_not_eq in l.
        unfold not in l. intuition.
        simpl. f_equal. unfold Cstate_as_OT.eq in e0.
        unfold Cstate_as_OT.eq in e1. rewrite e0. rewrite e1.
        f_equal. unfold q_plus. apply Mplus_comm. apply IHmu.
        rewrite e0 in l. apply Cstate_as_OT.lt_not_eq in l.
        unfold not in l. intuition.
        f_equal. 
        apply IHmu'.
        rewrite e0 in l. apply Cstate_as_OT.lt_not_eq in l.
        unfold not in l. intuition.
        rewrite l0 in l. apply Cstate_as_OT.lt_not_eq in l.
        unfold not in l. intuition.   
Qed.

Lemma d_app_comm{s e:nat}: forall (mu mu':dstate s e),
 dstate_eq ( (d_app mu' mu) )  ( ((d_app mu mu'))).
Proof. unfold dstate_eq. unfold d_app. unfold map2.
      intros (mu, IHmu) (mu', IHmu'). simpl.
      apply map2_comm.
Qed.



From Quan Require Import Matrix.
Local Open Scope matrix_scope.


Local Open Scope R_scope.

(*dapp assoc*)
Lemma map2_assoc: forall s e (x y z: list (cstate *qstate s e)),
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
forall {s e : nat} (mu1 mu2 mu3 : dstate s e),
dstate_eq (d_app (d_app mu1 mu2) mu3) (d_app mu1 (d_app mu2 mu3)).
Proof.   unfold dstate_eq. unfold d_app. unfold StateMap.map2.
     simpl. intros s e (mu1, IHmu1) (mu2, IHmu2) (mu3, IHmu3).
     simpl.  rewrite map2_assoc. reflexivity.
Qed.

(*dapp_scale_distr*)
Lemma  map_map2_distr:forall {s e : nat} (mu mu' : list( state s e)) (p : R),
 ( StateMap.Raw.map2 (@option_app  s e)
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
            (fun x : Square (2 ^ (e-s)) => p .* x) mu'=
            StateMap.Raw.map
            (fun x : Square (2 ^ (e-s)) => p .* x) ((c0, q0)::mu')     ).
      simpl. reflexivity. rewrite H. 
       apply IHmu.  simpl. f_equal. unfold q_plus. 
       rewrite Mscale_plus_distr_r. reflexivity.
       apply IHmu.  
       simpl. f_equal. apply IHmu'. 
Qed.

Lemma  d_scale_not_0_app_distr:forall {s e : nat} (mu mu': dstate s e) (p : R),
dstate_eq (d_app (d_scale_not_0 p mu) (d_scale_not_0 p mu')) (d_scale_not_0 p (d_app mu mu')) .
Proof. intros. 
    unfold dstate_eq. unfold d_app. unfold StateMap.map2.
    unfold d_scale_not_0. unfold StateMap.map.  destruct mu as [mu IHmu].
    destruct mu' as [mu' IHmu']. 
    simpl. apply map_map2_distr.  
Qed.

Lemma  d_scale_app_distr_aux:forall {s e : nat} (mu mu' mu1 mu2 mu3: list (state s e)) (p : R),
d_scale_aux p mu mu1->
d_scale_aux p mu' mu2->
d_scale_aux p (mu +l mu') mu3->
( mu1 +l mu2) = mu3 .
Proof. intros. assert(p=0\/p<>0). apply Classical_Prop.classic.
   destruct H2. subst. inversion H0; subst.  inversion_clear H.
   inversion_clear H1. reflexivity. lra. lra. lra. 
   inversion H0; subst. lra. inversion H; subst. lra.
   inversion H1; subst. lra.  
  apply map_map2_distr.
Qed.

Lemma  d_scale_app_distr:forall {s e : nat} (mu mu' mu1 mu2 mu3: dstate s e) (p : R),
d_scale p mu mu1->
d_scale p mu' mu2->
d_scale p (d_app mu mu') mu3->
dstate_eq (d_app mu1 mu2) mu3 .
Proof. intros. assert(p=0\/p<>0). apply Classical_Prop.classic.
   destruct H2. subst. inversion H0; subst.  inversion_clear H.
   inversion_clear H1. apply d_app_empty_l. lra. lra. lra. 
   inversion H0; subst. lra. inversion H; subst. lra.
   inversion H1; subst. lra.  apply d_scale_not_0_app_distr.
Qed.


(*--------------------------------------------------------------------*)

(*dstate equal*) 
Lemma dstate_1{s e:nat}: forall (mu: list (cstate *qstate s e))
(t x:cstate) (q:qstate s e),
Sorted (Raw.PX.ltk (elt:=qstate s e)) ((t, q) :: mu)->
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
    rewrite <-e0 in H1. assumption.
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


Lemma find_dec{s e:nat}: forall x (mu:list (cstate * qstate s e)),
option_qstate (Raw.find (elt:=qstate s e) x mu)= Zero
\/ option_qstate (Raw.find (elt:=qstate s e) x mu)<>Zero.
Proof. intros. 
    induction mu.
    --simpl. intuition.
    --simpl. destruct a. 
      destruct (Cstate_as_OT.compare x c).
       intuition.
       simpl.  apply classic. 
       intuition.
Qed.


Lemma dstate_2{s e:nat}: forall x (mu1 mu2: list (cstate *qstate s e)),
(option_qstate (StateMap.Raw.find x mu1)<>
option_qstate (StateMap.Raw.find x mu2))->
option_qstate (StateMap.Raw.find x mu1)<>Zero \/
option_qstate (StateMap.Raw.find x mu2)<>Zero.
Proof. intros  x mu1 mu2.    apply NF_1.
        intros.
       apply not_or_and in H. destruct H.
       unfold not. intros. pose (@find_dec s e x mu1).
       destruct o. 
       pose (@find_dec s e x mu2).
       destruct o. 
    rewrite <-H2 in H3. symmetry in H3. apply H1 in H3.
assumption. 
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

Lemma Nforall{s e:nat}:  forall  (mu1 mu2:dstate s e),
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


Lemma d_eq{s e:nat}: forall (mu1 mu2:dstate s e),
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
        unfold Cstate_as_OT.eq in e0.
        rewrite e0 in H1. rewrite H12 in H1. 
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
        assert(option_qstate (Raw.find (elt:=qstate s e) x mu1) <>
        option_qstate (Raw.find (elt:=qstate s e) x mu2)).
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

Lemma d_eq_1{s e:nat}: forall (mu1 mu2:dstate s e),
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

Lemma dstate_equal{s e:nat}: forall (mu1 mu2:dstate s e),
  WF_dstate mu1 -> WF_dstate mu2->
(forall x, d_find x mu1=d_find x mu2)<-> dstate_eq mu1 mu2 .
Proof. split. apply d_eq_1. assumption. assumption.
     apply  d_find_eq.
Qed. 


(*-------------------------big_d_app-------------------------------------------*)

(* Lemma big_dapp'_to_app{s e:nat}: forall (p_n:list R) (mu_n:list (dstate s e)) ,  
length p_n= length mu_n->
(Forall (fun x => 0<x%R) p_n)->
big_dapp' p_n mu_n (big_dapp p_n mu_n).
Proof.  induction p_n; intros. inversion H0; subst. destruct mu_n.
 simpl. apply big_app_nil. discriminate H.
 destruct mu_n. discriminate H. 
  simpl.  apply big_app_cons. 
  apply d_scalar_r. inversion_clear H0.
  lra. apply IHp_n. injection H. intuition.
  inversion_clear H0.
assumption.
Qed. *)

Lemma  big_dapp_exsist {s e:nat} : forall (p_n:list R) (mu_n:list (dstate s e)),
length p_n = length mu_n ->
exists mu, big_dapp' p_n mu_n mu.
Proof. induction p_n; intros;
        destruct mu_n.  exists (d_empty s e).
        econstructor.
        simpl in H. lia.
        simpl in H. lia.
        pose (d_scale_exsits a d).
        destruct e0. injection H.
        intros.
        apply IHp_n  in H1.
        destruct H1.
        exists  (d_app x x0).
        econstructor; try assumption.
Qed.



Lemma dstate_to_list_length{s e:nat}: forall (mu_n:list (dstate s e)),
length (dstate_to_list mu_n)= (length mu_n) .
Proof. induction mu_n; intros. simpl. reflexivity.
      simpl. rewrite IHmu_n. reflexivity.
Qed.


Lemma  big_map2_app'{s e:nat}: forall (f1 : list R) (g1: list( (list (cstate * qstate s e)))) ( f2: list R) (g2: list( (list (cstate * qstate s e)))) mu,
length f1 =length g1 ->length f2 = length g2->
big_map2' (f1 ++ f2 ) ( g1++g2) mu ->
(exists mu1 mu2, and  (and (big_map2' f1 g1 mu1)
(big_map2' f2 g2 mu2)) (mu = StateMap.Raw.map2 option_app mu1 mu2)).
Proof. induction f1;  induction g1; intros.
exists []. exists mu. split. econstructor.
econstructor. 
apply H1. simpl in H. simpl. rewrite map2_r_refl.
reflexivity.
 discriminate H.
 discriminate H.
 inversion H1; subst. 
 apply IHf1 in H8. destruct H8.
 destruct H2. 
 exists (StateMap.Raw.map2 option_app r x).
 exists x0. split. econstructor. econstructor.
  try assumption. apply H2. apply H2.
 rewrite <-map2_assoc. destruct H2. rewrite H3.
 reflexivity.
injection H. intuition. assumption.
Qed.


Lemma  big_map2_nil{s e:nat}: forall g (f:list (list (state s e))) (mu:list (state s e)),
big_map2' g f mu ->
g=[]\/f=[] -> mu= [].
Proof.  intros. destruct H0. subst. inversion_clear H. reflexivity.
       subst. inversion_clear H. reflexivity.
       
Qed.

Lemma  big_dapp_nil'{s e:nat}: forall g (f:list (dstate s e)) (d:dstate s e),
  g=[]\/f=[]-> big_dapp' g f d -> dstate_eq d (d_empty s e) . 
  Proof.  intros. inversion H0;subst.  apply dstate_eq_refl.
  destruct H;
  discriminate H.
  Qed.

(* Lemma  big_dapp_nil{s e:nat}: forall g (f:list (dstate s e)),
g=[]\/f=[] -> dstate_eq (big_dapp g f ) (d_empty s e) .
Proof. intros. destruct H. simpl. destruct g; destruct f.
    simpl. unfold dstate_eq ;try reflexivity.
    simpl. unfold dstate_eq ;try reflexivity. 
    discriminate H. discriminate H. 
    simpl. destruct g; destruct f.
    simpl. unfold dstate_eq ;try reflexivity.
    discriminate H.
    simpl. unfold dstate_eq ;try reflexivity. 
    discriminate H. 
Qed. *)

Lemma big_map2_length{s e:nat}: forall p_n (mu_n:list (list (state s e))) (mu:(list (state s e))),
big_map2' p_n mu_n mu -> length p_n = length mu_n.
Proof. induction p_n; intros; destruct mu_n. reflexivity.
      inversion_clear H. inversion_clear H.
      inversion H; subst.
      simpl. f_equal. apply IHp_n with d.
      assumption.
Qed.


Lemma big_dapp'_length{s e:nat}: forall p_n (mu_n:list (dstate s e)) (mu:dstate s e),
big_dapp' p_n mu_n mu -> length p_n = length mu_n.
Proof. induction p_n; intros; destruct mu_n. reflexivity.
      inversion_clear H. inversion_clear H.
      inversion H; subst.
      simpl. f_equal. apply IHp_n with d0 .
      assumption.
Qed.


Lemma big_dapp_this{s e:nat}:
forall  (p_n:list R)  (mu_n:list (dstate s e)) (mu':dstate s e),
big_dapp' p_n mu_n mu'->
big_map2' p_n (dstate_to_list mu_n) (StateMap.this (mu')).
Proof.  induction p_n; destruct mu_n; intros; inversion H;subst.
  simpl; try reflexivity; try econstructor.
  simpl.
  econstructor.
  inversion H5; subst. simpl. econstructor.
  econstructor. lra. 
   apply IHp_n. assumption.
Qed.


Lemma big_dapp'_out_empty{s e:nat}: forall  (p_n:list R) (mu_n:list (dstate s e)) (mu:dstate s e),
(Forall (fun i => ( i = 0%R)%R) p_n)->
big_dapp' p_n mu_n mu->
dstate_eq mu (d_empty s e).
Proof. induction p_n;destruct mu_n; intros; simpl in *. inversion_clear H0. reflexivity.
     inversion_clear H0.  
     inversion H0;subst.
         inversion H0; subst. inversion_clear H.
          pose (IHp_n _ _ H2 H7). 
          apply dstate_eq_trans with ((d_app r (d_empty s e))).
          apply d_app_eq. reflexivity. assumption.
          inversion H6; subst.  
          apply d_app_empty_l.
          lra.
Qed.


Lemma big_dapp'_app{s e:nat}:forall (p1 p2 : list R) (mu_n1 mu_n2 : list (dstate s e)) mu1 mu2 mu3,
big_dapp' p1 mu_n1 mu1->
big_dapp' p2 mu_n2 mu2->
big_dapp' (p1++p2) (mu_n1++mu_n2) mu3->
dstate_eq mu3 (d_app mu1 mu2).
Proof. induction p1; destruct mu_n1;  intros. simpl in *. 
       inversion_clear H. 
       eapply dstate_eq_trans with mu2. 
       eapply big_dapp_eq. apply H1. apply H0.
       apply dstate_eq_sym. apply d_app_empty_l.
       inversion_clear H. inversion_clear H.
       simpl in *. 
       inversion H; subst. 
       inversion H1; subst. 
       eapply IHp1 in H10; try apply H8; try apply H0.
       apply dstate_eq_trans with (d_app r (d_app d0 mu2)).
       apply d_app_eq. 
       eapply d_scale_eq; try apply H7; try apply H9.
       reflexivity. assumption. apply dstate_eq_sym.
       apply d_app_assoc'.
Qed.

Lemma big_dapp_eq_bound{s e:nat}: forall p_n q_n (mu_n: list (dstate s e)) mu,
Forall_two (fun i j: R=> i=j) p_n q_n->
big_dapp' p_n mu_n mu->
big_dapp' q_n mu_n mu .
Proof. induction p_n; intros; destruct mu_n; destruct q_n; inversion_clear H0; try econstructor;
        try inversion_clear H. rewrite H0 in *. assumption. auto.
Qed.

#[export] Hint Resolve WF_d_app' : DState.

(*-----------------------------------------------------------*)

(* 
Inductive emit_0{A:Type}:(list R) -> (list A)-> (list A)->Prop:=
|emit_nil: emit_0 [] [] []
|emit_cons_0: forall hf hg f g d,  (hf = 0)%R -> emit_0 f g d ->
                                        emit_0 (hf::f) (hg::g) d
|emit_cons: forall hf hg f g d,  (hf <> 0)%R -> emit_0 f g d ->
                                        emit_0 (hf::f) (hg::g) (hg::d).

Lemma  emit_0_exsist{A:Type}:forall (f:list R) (g:list A),
length f = length g->
exists d, emit_0 f g d.
Proof. induction f; intros; destruct g.
       exists []. econstructor.
       discriminate H. discriminate H.
       injection H. intros.
       apply IHf in H0. destruct H0.
       destruct (Req_dec a 0).
       exists x. econstructor; try assumption.  
       exists (a0:: x). apply emit_cons; try assumption.
Qed.

Lemma big_map2_emit_0{ s e:nat}:forall (f:list R) (g:list (list (state s e))) (mu:list (state s e)) r_n mu_n,
  big_map2' f g mu->
  (emit_0 f f r_n) ->
  (emit_0 f g mu_n) ->
  (exists mu', and (mu= mu') (big_map2' r_n mu_n mu')).
  Proof. induction f; intros; destruct g;
         inversion_clear H; inversion_clear H0; inversion_clear H1.
         exists [].
         split. reflexivity.
         econstructor.
         inversion H2; subst. 
         apply (IHf _ _  r_n mu_n) in H3; try assumption.
         destruct H3.
         exists x. split. rewrite map2_nil_l. apply H.
         apply H. lra.  rewrite H in *. lra.
         rewrite H0 in *. lra.  
         apply (IHf _ _  d0 d1) in H3; try assumption.
         destruct H3. destruct H1.
         exists ( r +l x).
         split. f_equal. assumption. 
        econstructor; try assumption.  
  Qed.

  Lemma  emit_0_dstate_to_list{s e:nat}: forall (f:list R)(g:list (dstate s e)) mu_n,
  emit_0 f g mu_n -> emit_0 f (dstate_to_list g) (dstate_to_list mu_n).
   Proof. induction f; intros; inversion H; subst. econstructor.
          simpl. econstructor. reflexivity. 
          apply IHf. assumption.
          simpl. 
          apply emit_cons. assumption.
          apply IHf. assumption.
  Qed.
  

  Lemma big_dapp_emit_0{ s e:nat}:forall (f:list R) (g:list (dstate s e)) (mu:dstate s e) r_n mu_n,
  big_dapp' f g mu->
  (emit_0 f f r_n) ->
  (emit_0 f g mu_n) ->
  (exists mu', and (dstate_eq mu mu') (big_dapp' r_n mu_n mu')).
  Proof. induction f; intros; destruct g;
         inversion_clear H; inversion_clear H0; inversion_clear H1.
         exists ((d_empty s e)).
         split. apply dstate_eq_refl.
         econstructor.
         inversion H2; subst. 
         apply (IHf _ _  r_n mu_n) in H3; try assumption.
         destruct H3.
         exists x. split.
         apply dstate_eq_trans with d0. 
         apply d_app_empty_l.
         intuition. intuition.
         lra. rewrite H in *. lra.
         rewrite H0 in *. lra.  
         apply (IHf _ _  d1 d2) in H3; try assumption.
         destruct H3. destruct H1.
         exists (d_app r  x).
         split. apply d_app_eq; auto. try reflexivity.
        econstructor; try assumption.  
  Qed.


  Lemma emit_0_eq(A:Type):forall (p_n:list R) (g_n :list A) g1 g2,
emit_0 p_n g_n g1->
emit_0 p_n g_n g2->
g1= g2.
Proof. induction p_n; destruct g_n; intros.
       inversion_clear H. inversion_clear H0.
       reflexivity.
       inversion_clear H. inversion_clear H.
       inversion H; subst; inversion H0; subst.
       apply IHp_n with g_n; try assumption.
       lra. lra. 
       f_equal; apply IHp_n with g_n; try assumption.  
Qed.


Lemma emit_0_app{A:Type}:forall (p_n1 p_n2 :list R) (g_n1 g_n2:list A) g1 g2 g,
emit_0 p_n1 g_n1 g1->
emit_0 p_n2 g_n2 g2->
emit_0 (p_n1++p_n2) (g_n1++g_n2) g->
g= g1++g2.
Proof. induction p_n1; destruct g_n1; intros.
       simpl in *. 
       inversion_clear H. simpl. 
       apply emit_0_eq with p_n2 g_n2; try assumption.
       inversion_clear H. inversion_clear H.
       inversion_clear H; simpl in H1;
       inversion_clear H1. 
       eapply IHp_n1; [apply H3 | apply H0| apply H4].
       lra. lra. 
       simpl. f_equal.  
       eapply IHp_n1; [apply H3 | apply H0| apply H4].
Qed. *)

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

(* Local Open Scope nat_scope.
From Quan Require Import Forall_two.
Lemma emit_0_dtrace{s e:nat}: forall (p_n:list R)  (mu_n:list (dstate s e)) (mu:dstate s e) ( mu':list (dstate s e)),
(Forall_two (fun p_i mu_i=> p_i <> 0%R -> d_trace mu_i = d_trace mu ) p_n mu_n)->
emit_0 p_n mu_n mu'->
Forall (fun mu_i : dstate s e => d_trace mu_i = d_trace mu) mu'.
Proof. induction p_n; destruct mu_n ; intros;
       inversion_clear H0;inversion_clear H. econstructor.
       apply IHp_n with mu_n; try assumption.    
       econstructor. apply H0. assumption. 
       apply IHp_n with mu_n; try assumption.  
Qed. *)

#[export] Hint Resolve WF_state_dstate WF_dstate_eq WWF_dstate_aux_to_WF_dstate_aux: DState.
(*------------WF_d_scale-------------------*)

#[export] Hint Resolve WF_d_scale WF_d_scale_aux  WF_dstate_empty 
WWF_d_scale_aux: DState.
(*------------------WF_d_app------------------------------*)


#[export] Hint Resolve  WF_d_app WF_d_app_aux WWF_d_app_aux: DState. 

















