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
    @Mixed_State (2^(e-s)) rho /\ (s<=e)%nat.

Definition q_update{s e:nat} (U: Square (2^(e-s))) (rho :qstate s e): qstate s e:=
  super U rho.

Definition qstate_kron{s x e:nat} (q :qstate s x) (q': qstate x e) := 
     (@kron  (2^(x-s)) (2^(x-s))  (2^(e-x)) (2^(e-x)) q  q').

Definition qstate_scale{s e:nat} (p:R) (q: qstate s e) := 
    @scale (2^(e-s)) (2^(e-s)) p  q.

Definition qstate_plus{s e:nat} (q1 q2: qstate s e) := 
    @Mplus (2^(e-s)) (2^(e-s)) q1 q2 .

Definition qstate_trace{s e:nat} (q: qstate s e) := 
Cmod (@trace (2^(e-s)) q).

#[export] Hint Unfold qstate_kron qstate_plus qstate_scale qstate_trace:qstate_uf.

Lemma WF_qstate_update{s e:nat}:forall  (U:Square (2^(e-s))) (q:qstate s e),
WF_Unitary U-> WF_qstate q->WF_qstate (q_update U q).
Proof.  unfold WF_qstate. intros. unfold q_update.
        split.
         apply mixed_unitary. intuition. intuition. 
         intuition.
Qed.

Local Open Scope R_scope.
Lemma WF_qstate_kron{s x e:nat}: forall (q :qstate s x) (q': qstate x e), 
WF_qstate q-> WF_qstate q'-> 
@WF_qstate s e (qstate_kron q q').
Proof.  unfold WF_qstate. intros.
        assert(2^(x-s)*2^(e-x)=2^(e-s))%nat. 
        rewrite <-Nat.pow_add_r. f_equal. lia.
        destruct H1.
        split.
        apply mixed_state_kron; intuition.
        intuition.
Qed. 


Lemma WF_qstate_scale{s e}: forall (q: qstate s e) (p:R), 
(0<p<=1)%R /\ WF_qstate q-> @WF_qstate s e (qstate_scale p q).
Proof.
         unfold WF_qstate. simpl. 
        intros. destruct H. split. apply Mixed_State_scale. intuition.
        intuition. intuition. 
Qed. 

Lemma WF_q_plus{s e}:forall (q q0:qstate s e ) (p1 p2:R),
(0<p1<=1/\0<p2<=1)-> (p1+p2<=1)-> 
WF_qstate q-> WF_qstate q0->
WF_qstate (qstate_plus (qstate_scale p1  q) (qstate_scale p2 q0)).
Proof. unfold WF_qstate.  unfold qstate_trace.  simpl. 
       intros. split. apply (@Mix_S (2^(e-s))); intuition. intuition. 
Qed.

Lemma WF_qstate_gt_0{s e:nat}: forall (q:qstate s e), 
WF_qstate q -> (qstate_trace q) > 0.
Proof.  unfold WF_qstate.  intros.  apply mixed_state_Cmod_1.   intuition.  
Qed.

Lemma WF_qstate_not_0{s e:nat}: forall (q:qstate s e), 
WF_qstate q ->  (qstate_trace q) <> 0.
Proof.  unfold WF_qstate.  intros. assert(qstate_trace q > 0).
apply mixed_state_Cmod_1.   intuition.  lra. 
Qed.

Definition WWF_qstate{s e:nat} (rho : qstate s e ):=
  @Mixed_State_aux (2^(e-s)) rho.

#[export] Hint Resolve WF_qstate_update WF_qstate_kron : QState.


(*----------------------C-Q state------------------------------------------*)


Local Open Scope R_scope.

Definition state(s e: nat) := (cstate * (qstate s e))%type.

Definition WF_state{s e:nat} (st:state s e): Prop:=
          WF_qstate (snd st).

Definition s_update_cstate{s e:nat} (i v :nat) (m:state s e): state s e:=
  match m with 
  |(sigma, rho) => ((c_update i v sigma), rho)
  end.
  
Local Open Scope matrix_scope.
Definition s_update_qstate{s e:nat} (U: Square (2^(e-s))) (m:state s e): state s e:=
    (fst m, q_update U (snd m)).

Definition s_update{s e:nat} (i v:nat) (U: Square (2^(e-s))) (m:state s e): state s e:=
 (c_update i v (fst m),  q_update U (snd m)).

Definition s_find{s e:nat} (sigma:cstate) (st:state s e): qstate s e:=
  match Cstate_as_OT.compare sigma (fst st) with
  |EQ _=> (snd st) 
  |_ => Zero
  end.
    

Definition s_scale{s e:nat} (p:R) (st: state s e) :=
 ((fst st), qstate_scale p (snd st)).

Definition s_trace{s e:nat} (st:state s e): R:=
      qstate_trace (snd st). 

Local Open Scope nat_scope.

Lemma WF_state_cupdate{s e:nat}: forall (i n:nat) (st:state s e),
WF_state st-> WF_state (s_update_cstate i n st).
Proof. unfold WF_state. destruct st. simpl. intuition. Qed.

Lemma WF_state_qupdate{s e:nat}: forall (U:Square (2^(e-s))) (st:state s e),
WF_Unitary U->WF_state st-> WF_state (s_update_qstate U st).
Proof. unfold WF_state. destruct st. simpl. apply WF_qstate_update. Qed.

Lemma WF_state_update{s e:nat}: forall (i n:nat) (U: Square (2^(e-s))) (st:state s e),
WF_Unitary U->WF_state st-> WF_state (s_update i n U st).
Proof. unfold WF_state. destruct st. simpl. apply WF_qstate_update. Qed.

Local Open Scope R_scope.
Lemma WF_state_scale{s e}: forall c (q: qstate s e) (p:R), 
(0<p<=1) /\ WF_state (c,q)-> @WF_state s e ((c, p .* q)).
Proof.
        unfold WF_state. unfold WF_qstate. simpl. 
        intros. destruct H. split. apply Mixed_State_scale. intuition.
        intuition. intuition. 
Qed.

Lemma WF_state_scale'{s e}: forall (st: state s e) (p:R), 
(0<p<=1) /\ WF_state st-> WF_state (s_scale p st).
Proof.
        unfold WF_state. unfold WF_qstate. simpl. 
        intros. destruct H. split. apply Mixed_State_scale. intuition.
        intuition. intuition. 
Qed. 

(* Lemma WF_s_plus{s e}:forall (c c0:cstate) (q q0:qstate s e ) (p1 p2:R),
(0<p1<=1/\0<p2<=1)-> (p1+p2<=1)-> 
WF_state (c, q)-> WF_state ( c0, q0)->
@WF_state s e (c, (p1 .* q .+ p2 .* q0)).
Proof. unfold WF_state.  unfold s_trace. unfold WF_qstate. simpl. 
       intros. split. apply Mix_S; intuition. intuition. 
Qed.   *)

(* Lemma WF_s_plus{s e}:forall (c c0:cstate) (q q0:qstate s e ) (p1 p2:R),
(0<p1<=1/\0<p2<=1)-> (p1+p2<=1)-> 
WF_state (c, q)-> WF_state ( c0, q0)->
@WF_state s e (c, (p1 .* q .+ p2 .* q0)).
Proof. unfold WF_state.  unfold s_trace. unfold WF_qstate. simpl. 
       intros. split. apply Mix_S; intuition. intuition. 
Qed.  *)


Lemma WF_state_in01{s e:nat}: forall (st:state s e), 
WF_state st -> 0<s_trace st <=1.
Proof. unfold WF_state. unfold WF_qstate. unfold s_trace. intros.
       apply mixed_state_Cmod_1. intuition. 
Qed.

Lemma WF_state_not_0{s e:nat}: forall (st:state s e), 
WF_state st -> s_trace st<>0.
Proof. intros. assert(0<s_trace st). apply WF_state_in01. intuition.
      lra.
Qed.

From Quan Require Import Basic. 
Lemma  WF_state_not_Zero{s e:nat}: forall (st:state s e),  
WF_state st -> snd st <> Zero .
Proof. unfold WF_state. unfold WF_qstate. simpl.  intros.
destruct H.
apply mixed_state_trace_gt0 in H.
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
s_find sigma st <>Zero ->  sigma= (fst st).
Proof. unfold s_find. intros. destruct (Cstate_as_OT.compare sigma
(fst st)) in H. destruct H. reflexivity.
 assumption. destruct H. reflexivity.
Qed.

Lemma s_find_eq{s e:nat}: forall sigma (st:state s e),
sigma = (fst st) -> s_find sigma st =snd st.
Proof. intros. unfold s_find. 
destruct (Cstate_as_OT.compare sigma (fst st)). 
apply Cstate_as_OT.lt_not_eq in l. unfold not in l. 
 apply l in H. intuition.
reflexivity.
apply Cstate_as_OT.lt_not_eq in l. unfold not in l.
apply Cstate_as_OT.eq_sym in H.  apply l in H. intuition. 
Qed.


Local Open Scope R_scope.
Lemma s_trace_scale{s e:nat}: forall c (q :(qstate s e)) (p:R) ,
(0<p)-> @s_trace s e (c, p .* q)=
p * s_trace (c,q).
Proof. intros. unfold s_trace. simpl. unfold qstate_trace.
 rewrite trace_mult_dist.
       rewrite Cmod_mult. rewrite Cmod_R. rewrite Rabs_right. reflexivity.
intuition.
Qed.



Definition WWF_state{s e:nat} (st:state s e): Prop:=
  WWF_qstate (snd st)/\ (s<=e)%nat.

#[export] Hint Resolve WF_state_cupdate WF_state_qupdate WF_state_qupdate WF_state_scale
 WF_state_eq: QState.
(*------------------------Distribution state------------------------------*)