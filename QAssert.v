Require Import Reals.
Require Import Coquelicot.Complex.
Require Import Strings.String.
Require Import Lists.List.

Require Import Coq.Init.Datatypes.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import Lia.

From Quan Require Import QIMP.
From Quan Require Import Matrix.
From Quan Require Import Quantum.
From Quan Require Import QState.
Require Import Basic_Supplement.


(*-------------------------------Synatx------------------------------------*)

Inductive Pure_formula:Type:=
|PBexp (b:bexp)
|PUniver(i:nat)( P: Pure_formula).

Inductive QExp : Type :=
|QExp_s (s e:nat) (v: Vector (2^(e-s))): QExp
|QExp_t (qs1 qs2:QExp) : QExp.

Inductive State_formula :Type:=
|SPure (P:Pure_formula) 
|SQuan (qs:QExp)
|SOdot (F1 F2:State_formula)
|SAnd (F1 F2:State_formula)
|SNot (F:State_formula)
|Assn_sub (i:nat) (a:aexp) (F:State_formula).

(* Inductive probabilistic_formula :Type := 
|PState (p:R) (F:State_formula)
|POplus   (pF1 pF2: probabilistic_formula).

Inductive unprobabilistic_formula: Type:=
|NState (F: State_formula)
|NOplus (nF1 nF2:unprobabilistic_formula). *)

(* Local Open Scope R_scope.
Fixpoint mode (pF: probabilistic_formula):=
  match pF with 
  |PState p F=> p
  |POplus pF1 pF2=> (mode pF1) + (mode pF2)
  end. *)

Definition pro_formula := list (R * State_formula).
Definition npro_formula := list (State_formula).
  

Inductive Assertion : Type:=
|APro (pF: pro_formula)
|ANpro (nF: npro_formula).

Definition State_formula_to_npro (F:State_formula):npro_formula:=
  [F] .


Local Open Scope R_scope.
Coercion PBexp : bexp >-> Pure_formula.
Coercion SPure : Pure_formula >-> State_formula.
Coercion SQuan : QExp >-> State_formula.
Coercion State_formula_to_npro : State_formula >-> npro_formula.
Coercion APro : pro_formula >-> Assertion.
Coercion ANpro : npro_formula >-> Assertion.

Declare Custom Entry assert.
Declare Scope assert_scope.
Bind Scope assert_scope with Pure_formula.
Bind Scope assert_scope with QExp.
Bind Scope assert_scope with State_formula.
(* Bind Scope assert_scope with probabilistic_formula. *)
Bind Scope assert_scope with Assertion.
Delimit Scope assert_scope with assertion.
Open Scope assert_scope.

Notation " 'univer' x P " :=(PUniver x P)(at level 80) :assert_scope.

(* Notation "  |emp>" := (QExp_nil)(at level 70) :assert_scope. *)
Notation "| v >[ s - e ]" := (QExp_s s e v) (at level 80) :assert_scope.

Infix " ⊗*  " := (QExp_t)(at level 80) :assert_scope. 

Notation "~ F" := (SNot F ) : assert_scope.
Notation "F1 /\ F2" := (SAnd F1  F2) : assert_scope.
Notation " F1 ⊙ F2" := (SOdot F1 F2)(at level 80):assert_scope.
(* Notation " F [ X |-> a ] " := (Assn_sub X a F)   (at level 10) : assert_scope. *)

(* Notation " p · F" :=(PState p F)(at level 80):assert_scope.
Infix "  ⊕p " :=  (POplus) (at level 80):assert_scope.
Infix " ⊕np " :=  (NOplus ) (at level 80):assert_scope. *)

Definition sum_over_list_formula (pF: pro_formula) := 
  big_sum (fun i => fst (nth i pF (0, SPure (PBexp BFalse)))) (length pF).

Definition distribution_formula (pF: pro_formula) := 
  and (Forall (fun x => 0 <= fst x) pF)  (sum_over_list_formula pF = 1).

Lemma sum_over_list_nil_formula : sum_over_list_formula [] = 0.
Proof. unfold sum_over_list_formula. simpl. reflexivity. Qed.


Lemma sum_over_list_cons_formula : forall x l,
  sum_over_list_formula (x :: l) = (fst x + sum_over_list_formula l)%R.
Proof.
  intros x l.
  unfold sum_over_list_formula.
  simpl length. 
  rewrite big_sum_shift.
  simpl nth.
  reflexivity.
Qed.

(*----------------------------------FreeV--------------------------------------*)
Local Open Scope assert_scope.
Import QIMP.
Fixpoint Free_pure (P: Pure_formula ): CSet :=
  match P with
      | PBexp b=> Free_bexp b
      | PUniver x P0 => Free_pure P0
  end.

Fixpoint Free_Qexp (qs: QExp) : QSet :=
  match qs with 
    |QExp_s s e v=> (Qsys_to_Set s e)
    |QExp_t qs1 qs2  =>NSet.union (Free_Qexp qs1) (Free_Qexp qs2)
  end.

Local Open Scope assert_scope.
Fixpoint Free_state (F: State_formula) : (CSet * QSet):=
  match F with 
    |SPure P => (Free_pure P , NSet.empty)
    |SQuan qs=> (NSet.empty, Free_Qexp qs)
    |SOdot F1 F2=>  (NSet.union (fst (Free_state F1)) (fst(Free_state F2)), NSet.union (snd (Free_state F1))  (snd (Free_state F2)))
    |SAnd F1 F2 => (NSet.union (fst (Free_state F1)) (fst(Free_state F2)), NSet.union (snd (Free_state F1))  (snd (Free_state F2)))
    |SNot F'=> Free_state F'
    | Assn_sub X a F => Free_state F
  end.

Fixpoint Free_pro(pF: pro_formula): (CSet * QSet) :=
  match pF with
  |[] => (NSet.empty, NSet.empty)
  |(p,F)::pF' => (NSet.union (fst (Free_state F)) (fst(Free_pro pF')),
                   NSet.union (snd (Free_state F))  (snd (Free_pro pF')))
  end.

Fixpoint Free_npro(nF: npro_formula): (CSet * QSet) :=
    match nF with
    |[] => (NSet.empty, NSet.empty)
    |F::nF'=> (NSet.union (fst (Free_state F)) (fst(Free_npro nF')), 
                      NSet.union (snd (Free_state F))  (snd (Free_npro nF')))
    end.

Definition Free (d: Assertion) : (CSet * QSet):=
  match d with 
    |APro pF => Free_pro pF
    |ANpro F=> Free_npro F
  end. 

(*-------------------------------Semantics-----------------------------------*)
Local Close Scope assert_scope.
Local Open Scope nat_scope.

Local Close Scope assert_scope.
Local Open Scope nat_scope.
Fixpoint Pure_eval{n:nat} (pf:Pure_formula) (st:state n): Prop :=
  match pf with 
 |PBexp b => if ((beval st b)) then True else False
 |PUniver x P=> forall a, Pure_eval P (s_update_cstate x a st)
 end. 


Fixpoint QExp_eval{n:nat} (qs: QExp) (st: state n){struct qs} :Prop:=
  match qs with 
  |QExp_s s e v=> (PMpar_trace ( @scale (2^(n)) (2^(n)) (C1 / (@trace (2^(n)) (snd st)))  (snd st)) s (n-e)= outer_product v v)
  |QExp_t qs1 qs2=> NSet.inter (Free_Qexp qs1) (Free_Qexp qs2) =NSet.empty  /\
                               QExp_eval qs1 st /\ QExp_eval qs2 st
                    
end.

Fixpoint State_eval{n:nat} (sf:State_formula) (st:state n): Prop:=
match sf with 
|SPure P => Pure_eval P st
|SQuan s=> QExp_eval s st
|SOdot F1 F2=> 
NSet.inter (snd (Free_state F1)) (snd (Free_state F2)) =NSet.empty /\
State_eval F1 st /\ State_eval F2 st
|SAnd F1 F2 => State_eval F1 st /\ State_eval F2 st
|SNot F => ~(State_eval F st)
|Assn_sub i a F => State_eval F  (s_update_cstate i (aeval st a) st)
end.

Fixpoint State_eval_dstate {n:nat} (F:State_formula) (mu:list (cstate *(qstate n))): Prop:=
  match mu with
  |nil=> False
  |[(sigma,rho)] =>State_eval F (sigma, rho)
  |(sigma,rho)::mu'=>State_eval F (sigma, rho) /\ State_eval_dstate F mu'
  end.


(* Fixpoint assert_scale (p:R) (nF: unprobabilistic_formula): probabilistic_formula := 
match nF with
|NState F => PState p F 
|NOplus nF1 nF2=> POplus p F1 (assert_scale p F2)
end.  *)

Local Open Scope R_scope.

Inductive sat_State {n:nat}:(dstate (2^n)) -> (State_formula)-> Prop:=
  |sat_F: forall (mu:dstate (2^n)) F, WF_dstate mu -> State_eval_dstate F (StateMap.this mu)
                                           ->sat_State mu F.

(* Fixpoint scale_pro ( p: R) ( pF: probabilistic_formula ): probabilistic_formula := 
  match pF with 
  |PState p1 F => PState (p*p1) F 
  |POplus pF1 pF2 =>POplus (scale_pro p pF1) (scale_pro p pF2)
  end. *)
                                           
(* Inductive sat_Pro {n:nat}: (dstate (2^n))-> (probabilistic_formula)-> Prop:=
|sat_PState: forall (mu:dstate (2^n)) (F:State_formula) (p:R),  (0<p<=1) 
                                  -> (exists (mu':dstate (2^n)), d_trace mu'=1/\ 
                                  (dstate_eq mu  (d_scalar p mu')) 
                                   /\ (sat_State  mu' F))
                                  -> sat_Pro  mu ((PState p F))
|sat_POplus: forall (mu:dstate (2^n))  (pF1 pF2:probabilistic_formula), 
                                  (0<mode pF1 + mode pF2 <=1) 
                                  -> (exists (mu1 mu2:dstate (2^n)),  
                                    dstate_eq mu (d_app mu1 mu2 )
                                  /\ sat_Pro mu1 pF1 /\ sat_Pro mu2 pF2)
                                  -> (sat_Pro  mu (POplus pF1 pF2)). *)

(* Inductive sat_Npro {n:nat}:  (dstate (2^n))-> (unprobabilistic_formula)-> Prop:=
|sat_NState: forall (mu:dstate (2^n)) F,(sat_State mu F) -> sat_Npro mu ((NState F))
|sat_NOplus: forall (mu:dstate (2^n)) F (nF:unprobabilistic_formula), 
WF_dstate mu->
                    (exists (mu1 mu2:dstate n), 
                   (dstate_eq mu (d_app mu1 mu2))
                    /\ (sat_Npro mu1 F /\ (sat_Npro mu2 nF ) ))
                    -> sat_Npro mu (NOplus F nF). *)
Fixpoint big_and (f : nat -> Prop) (n_0 : nat) : Prop := 
  match n_0 with
  | 0 => True
  | S n' => (big_and f n') /\ (f n')
  end.

Fixpoint big_pOplus (f : nat -> R) (g : nat -> State_formula) (n_0 : nat) : pro_formula := 
 match n_0 with
| 0 => []
| S n' =>(f n', g n')::(big_pOplus f g n')  
end.

Fixpoint big_Oplus  (g : nat -> State_formula) (n_0 : nat) : npro_formula := 
 match n_0 with
| 0 => []
| S n' =>(g n')::(big_Oplus g n')  
end.

(* Fixpoint big_app{n:nat} (f : nat -> list (cstate * qstate (2^n))) (n_0 : nat) : list (cstate * qstate n) := 
  match n_0 with
  | 0 => nil
  | S n' =>StateMap.Raw.map2 option_app (big_app f n')  (f n')
  end. *)

Fixpoint big_dapp{n:nat} (f : nat -> dstate (2^n)) (n_0 : nat) : dstate (2^n) := 
  match n_0 with
  | 0 => d_empty (2^n)
  | S n' =>d_app (big_dapp f n')  (f n')
  end.

Fixpoint npro_to_pro_formula (nF:npro_formula ) (p_n: list R): pro_formula:=
  match nF, p_n with 
  |[], _ => []
  |_, [] => []
  |F :: nF', h::p' => (h, F):: (npro_to_pro_formula nF' p')
  end.

  Fixpoint get_pro_formula (pF:pro_formula): list R:=
    match pF with 
    |[] => []
    |(p, F)::pF' => p:: (get_pro_formula pF')
    end. 

Local Open Scope R_scope.
Inductive sat_Assert {n:nat}: (dstate (2^n))-> (Assertion)-> Prop:=
|sat_APro: forall (mu:dstate (2^n)) pF (mu_n: list (dstate (2^n))), 
                 WF_dstate mu -> distribution_formula pF-> 
                dstate_eq mu (big_dapp (fun i:nat=>d_scalar (fst (nth i pF (0, SPure (PBexp BFalse)))) 
                   (nth i mu_n (d_empty (2^n)))) (length pF))
                /\ big_and (fun i:nat=> (sat_State (nth i mu_n (d_empty (2^n))) (snd (nth i pF (0, SPure (PBexp BFalse))))) 
                /\ d_trace mu= d_trace ((nth i mu_n (d_empty (2^n)))) ) (length pF)
                    -> sat_Assert mu (APro pF)
|sat_ANpro: forall (mu:dstate (2^n)) nF (p_n:list R), 
                    (nF <> []) -> sat_Assert mu (npro_to_pro_formula nF p_n)
                    ->sat_Assert mu (ANpro nF).


Lemma WF_sat_State{n:nat}: forall  (mu:dstate (2^n)) (F:State_formula), 
sat_State mu F -> StateMap.this mu <> [] /\ WF_dstate mu.
Proof. intros. 
      inversion_clear H. destruct mu as [mu IHmu].
      destruct mu.
      simpl in H1.  destruct H1.  
      split. discriminate. intuition. 
Qed.

Lemma WF_dstate_eq{n}: forall (mu mu': dstate (2^n)),
dstate_eq mu mu'-> WF_dstate mu -> WF_dstate mu'.
Proof. unfold WF_dstate. unfold dstate_eq. 
      intros (mu,IHmu) (mu', IHmu').
      simpl. intros. rewrite <- H. 
     assumption.
Qed.

Lemma dstate_eq_sym{n:nat}:forall (mu1 mu2: dstate (2^n)),
dstate_eq mu1 mu2-> dstate_eq mu2 mu1 .
Proof. intros  (mu1,IHmu1) (mu2,IHmu2).
unfold dstate_eq. simpl. intuition.
Qed.
       
(* Lemma WF_sat_Pro{n:nat}: forall  (mu:dstate (2^n)) (pF:probabilistic_formula), 
sat_Pro mu pF-> StateMap.this mu <> [] /\ WF_dstate mu.
Proof. intros. induction pF.
      inversion_clear H. 
        destruct H1. destruct H0. destruct H.
        destruct H2.   
        apply (WF_sat_State ) in H3. destruct H3.
        split. admit.       
      apply WF_dstate_eq with ((d_scalar p x)).
       apply dstate_eq_sym. assumption.
      apply WF_d_scalar. intuition. intuition.  
      inversion_clear H. destruct H1. destruct H.
      destruct H. destruct H1. 
      split. admit.
      apply WF_dstate_eq with ((d_app x x0)).
      apply dstate_eq_sym. assumption.
    admit.
Admitted.
       
Lemma WF_sat_Npro{n:nat}: forall (nF:unprobabilistic_formula)  (mu:dstate (2^n)) , 
sat_Npro mu nF-> StateMap.this mu <> [] /\ WF_dstate mu.
Proof. induction nF;intros; inversion_clear H.
       apply WF_sat_State in H0. assumption.
       split. admit. 
      intuition.
Admitted. *)


Lemma WF_sat_Assert{n:nat}: forall (mu:dstate (2^n)) (D:Assertion), 
sat_Assert  mu D-> StateMap.this mu <> [] /\ WF_dstate mu.
Proof. intros. induction D; 
        inversion_clear H. split.  admit.
        intuition. inversion_clear H1. split. admit.
        intuition.
Admitted.


Lemma state_eq_aexp{n:nat}: forall (st st':state n )  (a:aexp),
(fst st) = (fst st')-> (aeval st a) = aeval st' a.
Proof. intros. induction a.
      --reflexivity. 
      --simpl. rewrite H. reflexivity.
      --simpl.  rewrite IHa1. rewrite IHa2. reflexivity.
      --simpl.  rewrite IHa1. rewrite IHa2. reflexivity.
      --simpl.  rewrite IHa1. rewrite IHa2. reflexivity.
Qed.

Lemma state_eq_bexp{n:nat}: forall (st st':state n) (b:bexp),
(fst st) = (fst st')-> (beval st b) = beval st' b.
Proof. intros. induction b. 
       --simpl. reflexivity.
       --simpl. reflexivity.
       --simpl. rewrite (state_eq_aexp  st st' a1).
       rewrite (state_eq_aexp  st st'  a2). reflexivity.
        assumption. assumption.
      --simpl. rewrite (state_eq_aexp st st' a1).
      rewrite (state_eq_aexp st st' a2). reflexivity.
       assumption. assumption.
       --simpl. rewrite (state_eq_aexp st st' a1).
       rewrite (state_eq_aexp st st' a2). reflexivity.
        assumption. assumption.
      --simpl. rewrite (state_eq_aexp st st' a1).
      rewrite (state_eq_aexp  st st' a2). reflexivity.
       assumption. assumption.
      --simpl. rewrite IHb. reflexivity.
      --simpl. rewrite IHb1.
      rewrite IHb2. reflexivity.
Qed.

Local Open Scope bool_scope.
Lemma bexp_Pure_eq{n:nat}:  forall (st st':state n ) (b:bexp) , 
((beval st b) = beval st' b) -> (State_eval b st)<->(State_eval b st').
Proof.  simpl.  intros. destruct (beval st b).
       rewrite <-H. reflexivity. rewrite <-H.
       reflexivity. 
Qed.

Lemma state_eq_Pure{n:nat}: forall (P:Pure_formula) (st st':state n) ,
(fst st)= (fst st')-> (State_eval P st)<-> State_eval P st'.
Proof. induction P.
     --intros. apply (bexp_Pure_eq st st' b ).
      rewrite (state_eq_bexp st st' b). reflexivity.
       intuition.
    --simpl.  
      simpl. destruct st. destruct st'. unfold s_update_cstate. intros. 
      simpl in H. rewrite H.
      simpl in IHP. split; intros.
      apply IHP with  (c_update i a c0, q). simpl. reflexivity.
      apply H0. 
      apply (IHP  ((c_update i a c0), q0) ). simpl. reflexivity.
      apply H0. 
Qed.

Lemma qstate_eq_Qexp:forall (qs :QExp) { n:nat} (st st':state n) , 
 snd st= snd st' -> 
 QExp_eval  qs st -> QExp_eval  qs st'.
Proof.  simpl. intros. induction qs. 
simpl. 
simpl in H0.
rewrite <-H.
assumption.
destruct H0.
simpl.
split. assumption.
destruct H1.
apply IHqs1 in H1.
apply IHqs2 in H2.
split. assumption. assumption.  
Qed.

Definition assert_implies (P Q : Assertion) : Prop :=
    forall (n:nat) (mu:dstate (2^n)), sat_Assert  mu P -> sat_Assert  mu Q.

Notation "P ->> Q" := (assert_implies P Q)
    (at level 90) : assert_scope.
Local Open Scope assert_scope.
Notation "P <<->> Q" :=
    ((P ->> Q) /\ (Q ->> P)) (at level 80) : assert_scope.


Local Open Scope R_scope.
Lemma Mscale_not_0':forall (m n:nat) (A:Matrix m n) (p: R), 
p.* A <> Zero -> A<>Zero .
Proof. unfold not.  intros.  rewrite H0 in H.  rewrite Mscale_0_r in H.
intuition. 
Qed.


Local Open Scope C_scope.
Lemma s_seman_scalar_Qexp: forall  (qs:QExp) (p:R)  (n:nat) (st:state n),
0<p<=1 -> WF_state st ->
(QExp_eval qs st <-> QExp_eval qs (s_scalar p st)).
Proof. 
      split. intros.
      destruct st.
      induction qs.  
      simpl in H1.
      simpl.
      rewrite trace_mult_dist.
      rewrite Cdiv_unfold.
      rewrite Mscale_assoc.
      rewrite <-Cmult_assoc.
      rewrite Cinv_mult_distr.
      rewrite <- Cmult_assoc.
      rewrite Cmult_comm with (y:=(RtoC p)).
      rewrite Cmult_assoc with (y:=(RtoC p)).
      rewrite Cinv_l.
      rewrite Cmult_assoc.
      rewrite Cmult_1_l.
      assumption.
      apply RtoC_neq.
      intuition. rewrite H2 in H3. lra.
      apply RtoC_neq.
      intuition. rewrite H2 in H3. lra.
      apply WF_state_gt_0 in H0.
      simpl in H0. unfold not. 
      intros. unfold s_trace in *. simpl in *.
      rewrite H2 in H0.
      rewrite Cmod_0 in H0. 
      lra.
      simpl in H1.
      destruct H1. destruct H2.
      simpl.  split. assumption.
      apply IHqs1 in H2.
      apply IHqs2 in H3.
      split. assumption. assumption.
      destruct st.
      induction qs.  
      simpl.  
      rewrite trace_mult_dist.
      rewrite Cdiv_unfold.
      rewrite Mscale_assoc.
      rewrite <-Cmult_assoc.
      rewrite Cinv_mult_distr.
      rewrite <- Cmult_assoc.
      rewrite Cmult_comm with (y:=(RtoC p)).
      rewrite Cmult_assoc with (y:=(RtoC p)).
      rewrite Cinv_l.
      rewrite Cmult_assoc.
      rewrite Cmult_1_l.
      intuition.
      apply RtoC_neq.
      intuition. rewrite H1 in H2. lra.
      apply RtoC_neq.
      intuition. rewrite H1 in H2. lra.
      apply WF_state_gt_0 in H0.
      simpl in H0. unfold not. 
      intros. unfold s_trace in *. simpl in *. rewrite H1 in H0. 
      rewrite Cmod_0 in H0.
      lra. 
      intros.
      simpl in H1.
      destruct H1. destruct H2.
      simpl.  split. assumption.
      apply IHqs1 in H2.
      apply IHqs2 in H3.
      split. assumption. assumption.
Qed.


Local Open Scope R_scope.
Lemma s_seman_scalar: forall (F:State_formula) (p:R) n  (st:state n),
0<p<=1-> (WF_state st)->
(State_eval F st <-> State_eval F (s_scalar p st)).
Proof.  induction F. 
-- intros. split. apply (state_eq_Pure  P st (s_scalar p st)) . simpl. reflexivity.
                  apply (state_eq_Pure  P (s_scalar p st) st ) . simpl. reflexivity.
-- intros. apply s_seman_scalar_Qexp. assumption. assumption.
-- split; simpl; intros; destruct H1; destruct H2;
 split;  try assumption; split; try  apply (IHF1 p n st); try assumption;
 try apply (IHF2 p n st); try assumption.  
-- split; simpl; intros; destruct H1;
split; try apply (IHF1 p n st); try assumption;
try apply (IHF2 p n st); try assumption.
--intros. split; intros; simpl; unfold not; simpl in H1; unfold not in H1;
intros.
assert(State_eval  F st). apply (IHF p n st). assumption. assumption. assumption. apply H1 in H3.
assumption.
assert(State_eval F (s_scalar p st)). apply (IHF p n st). assumption. assumption. assumption. apply H1 in H3.
assumption.
--split; intros; destruct st; simpl in H1.  unfold s_update_cstate in H1.
  simpl State_eval;
 unfold s_scalar in IHF.
  apply (IHF p n (c_update i (aeval (c, q) a) c, q)) in H1; simpl in H1; unfold s_scalar;
  simpl. assert(aeval (c, q) a=(@aeval n (c, (p .* q)) a)).
  apply state_eq_aexp. simpl. reflexivity.
  rewrite <- H2. assumption. lra.
  unfold WF_state. simpl.
  unfold WF_state in H0. simpl in H0.
  intuition. 

  unfold s_trace in *. simpl in *. 

  unfold s_scalar in *. simpl in H1.
  assert(aeval (c,q) a=(@aeval n (c, p .* q)) a).
  apply state_eq_aexp. simpl. reflexivity.
  rewrite <-H2 in H1.  unfold s_scalar in IHF.
  simpl. 
  apply (IHF p n (
  (c_update i (aeval (c, q) a)
     c,  q)))in H1. simpl in H1.
   assumption. lra.

   unfold WF_state. simpl.
  unfold WF_state in H0. simpl in H0.
  assumption.
Qed.

Local Open Scope C_scope.
Lemma d_seman_scalar_Qexp: forall  (F:State_formula) (p:R)  (n:nat) (mu:list (cstate * qstate n)),
0<p<=1 -> WF_dstate_aux mu ->
(State_eval_dstate F mu ->@State_eval_dstate n F 
(StateMap.Raw.map (fun x : qstate n => p .* x) mu)).
Proof. induction mu; simpl; intros.
       destruct H1.
       destruct a. 
       destruct mu.
       simpl.  assert(State_eval  F (s_scalar p (c, q))).
       apply s_seman_scalar. intuition.
       inversion_clear H0. intuition. intuition.
       unfold s_scalar in H2. simpl in H2.
       intuition. 
       simpl.  destruct p0. split.
       assert(State_eval F (s_scalar p (c, q))).
       apply s_seman_scalar. intuition.
       inversion_clear H0. intuition. intuition.
       unfold s_scalar in H2. simpl in H2.
       intuition.  
       assert(@State_eval_dstate n F
       (StateMap.Raw.map (fun x : qstate n => p .* x)
          ((c0, q0) :: mu))). 
      apply IHmu. intuition. 
      inversion_clear H0. intuition.
      intuition. simpl StateMap.Raw.map in H2.
      intuition.
Qed.



Local Open Scope R_scope.
Lemma d_seman_scalar: forall n (p:R) (mu:dstate (2^n)) (F:State_formula),
0<p<=1->
sat_State mu F -> sat_State  (d_scalar p mu) F.
Proof. 
       intros. destruct mu as [mu IHmu].
       unfold d_scalar. 
       inversion H0; subst.
       simpl in H2.
       apply sat_F. 
       apply WF_d_scalar. intuition.
       intuition. simpl. apply d_seman_scalar_Qexp.
       intuition. unfold WF_dstate in H1. 
       simpl in H1. intuition. intuition.
Qed.


Require Import Classical_Prop.
  Lemma Mplus_not_0: forall (m n:nat) (A B:Matrix m n), A .+ B <> Zero -> (A <> Zero \/ B <> Zero).
  Proof. unfold not. intros. assert(A=Zero \/ A<>Zero).
         apply classic. destruct H0. right.
      intros.  rewrite H0 in H. rewrite H1 in H.
      destruct H. apply Mplus_0_l. 
      left. intuition.  
  Qed.
  

  Lemma d_app_mu_nil: forall (n : nat) (mu mu': dstate n),
  StateMap.this mu'= []->
  StateMap.this (d_app mu mu') = StateMap.this mu .
  Proof. intros n (mu, IHmu) (mu', IHmu').
         induction mu. simpl. rewrite map2_r_refl.
         intuition. 
         simpl. intros. rewrite H. destruct a.
          simpl. rewrite map2_l_refl.
          reflexivity.
    
  Qed.
  
  Lemma map2_nil:forall n (mu:list (cstate *qstate n)),
  StateMap.Raw.map2 option_app mu []=
  StateMap.Raw.map2_l option_app mu.
  Proof. induction mu. 
       --reflexivity.
       --destruct a. simpl. reflexivity. 
    
  Qed.
  
  
  Lemma  Rplus_le_1:forall (r1 r2:R), r1>0->r1+r2<=1 ->r2<=1 .
  Proof. intros. lra.
  Qed.


  Lemma map2_scale_not_nil: forall n (p:R) (mu :list (cstate * qstate n)),
  mu<>nil -> (p>0)->
  StateMap.Raw.map (fun x : qstate n =>@scale (2^n) (2^n) p x)
    mu <> [].
  Proof. intros. induction mu. destruct H. reflexivity.
          destruct a. simpl. discriminate.
  Qed. 


  Local Open Scope R_scope.
Lemma d_seman_app: forall n (F:State_formula)  (mu mu':dstate (2^n)) (p0 p1:R),
(0 < p0 <= 1)->(0 < p1 <= 1)
->(0<(p0+p1)<=1)->
sat_State mu F  -> sat_State  (mu') F
-> sat_State (d_app (d_scalar p0 mu)
   (d_scalar p1 mu')) F.
Proof. intros n F (mu, IHmu) (mu', IHmu'); intros.
       inversion H2; subst. inversion H3; subst.
       apply sat_F. 
       apply WF_d_app. intuition. intuition.
       intuition. intuition.
       simpl. 
Admitted.

