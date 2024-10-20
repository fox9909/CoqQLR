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

From Quan Require Import QIMP_L.
From Quan Require Import Matrix.
From Quan Require Import Quantum.
From Quan Require Import QState_L.
Require Import Par_trace.


(*-------------------------------Synatx------------------------------------*)

Inductive Pure_formula:Type:=
|PBexp (b:bexp)
|PUniver  (P: nat ->Pure_formula)
|PExists  (P: nat -> Pure_formula)
|Assn_sub_P (i:nat) (a:aexp) (P:Pure_formula).

Inductive QExp : Type :=
|QExp_s (s e:nat) (v: Vector (2^(e-s))): QExp
|QExp_t (qs1 qs2:QExp) : QExp.

Inductive State_formula :Type:=
|SPure (P:Pure_formula) 
|SQuan (qs:QExp)
|SOdot (F1 F2:State_formula)
|SAnd (F1 F2:State_formula).
(* |SNot (F:State_formula) *)




Definition pro_formula := list (R * State_formula).
Definition npro_formula := list (State_formula).


Fixpoint big_pOplus (f : nat -> R) (g : nat -> State_formula) (n_0 : nat) : pro_formula := 
match n_0 with
| 0 => []
| S n' =>(big_pOplus f g n')  ++ [(f n', g n')]
end.   


Inductive big_pOplus': (nat -> R)-> ( nat -> State_formula)-> (nat) -> pro_formula-> Prop := 
|big_pOplus_nil : forall f g, big_pOplus' f g 0 []
|big_pOplus_0: forall f g n pF, ((f n)= 0)%R -> big_pOplus' f g (n) pF
                                         ->big_pOplus' f g (S n) pF
|big_pOplus_cons: forall f g n pF, ((f n) <> 0)%R ->  big_pOplus' f g (n) pF
                                                ->big_pOplus' f g (S n) (pF  ++ [(f n, g n)]).

Fixpoint big_Oplus  (g : nat -> State_formula) (n_0 : nat) : npro_formula := 
match n_0 with
| 0 => []
| S n' =>(big_Oplus g n') ++ [(g n')]  
end.

Fixpoint npro_to_pro_formula (nF:npro_formula ) (p_n: list R): pro_formula:=
  match nF, p_n with 
  |[], [] =>[]
  |[], _ => []
  |_, [] => []
  |F :: nF', h::p' => (h, F):: (npro_to_pro_formula nF' p')
  end.

Fixpoint get_pro_formula (pF:pro_formula): list R:=
  match pF with 
  |[] => []
  |(p, F)::pF' => p:: (get_pro_formula pF')
  end. 

Fixpoint pro_to_npro_formula (pF:pro_formula ): npro_formula:=
  match pF with 
  |[] => [] 
  |(p, F) :: pF'=> F:: (pro_to_npro_formula pF')
  end.


(* Definition sum_over_list_formula (pF: pro_formula) := 
  big_sum (fun i => fst (nth i pF (0, SPure (PBexp BFalse)))) (length pF). *)

Definition distribution_formula (pF: pro_formula) := 
  and (Forall (fun x => 0 <= x) (get_pro_formula pF))  (sum_over_list (get_pro_formula pF) = 1).

(* Lemma sum_over_list_nil_formula : sum_over_list_formula [] = 0.
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
Qed. *)
  
Inductive Assertion : Type:=
|APro (pF: pro_formula)
|ANpro (nF: npro_formula)
|Assn_sub (i:nat) (a:aexp) (D:Assertion).

Definition State_formula_to_npro (F:State_formula):npro_formula:= [F] .

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

(* Notation "~ F" := (SNot F ) : assert_scope. *)
Notation "F1 /\ F2" := (SAnd F1  F2) : assert_scope.
Notation " F1 ⊙ F2" := (SOdot F1 F2)(at level 80):assert_scope.
(* Notation " F [ X |-> a ] " := (Assn_sub X a F)   (at level 10) : assert_scope. *)


Fixpoint big_Sand (g: nat->  (State_formula )) (n : nat) : State_formula := 
match n with
| 0 => BTrue
| S n' => g n' /\ big_Sand g n'
end. 

(*----------------------------------FreeV--------------------------------------*)
Local Open Scope assert_scope.
Import QIMP_L.
Fixpoint Free_pure (P: Pure_formula ): CSet :=
  match P with
      | PBexp b=> Free_bexp b
      | PUniver P0 => Free_pure (P0 1%nat)
      | PExists P0 => Free_pure (P0 1%nat)
      |Assn_sub_P i a P0 => Free_pure P0
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
    |SOdot F1 F2=> (NSet.union (fst (Free_state F1)) (fst(Free_state F2)), NSet.union (snd (Free_state F1))  (snd (Free_state F2)))
    |SAnd F1 F2 => (NSet.union (fst (Free_state F1)) (fst(Free_state F2)), NSet.union (snd (Free_state F1))  (snd (Free_state F2)))
    (* |SNot F'=> Free_state F'
    | Assn_sub X a F => Free_state F *)
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

Fixpoint Free (d: Assertion) : (CSet * QSet):=
  match d with 
    |APro pF => Free_pro pF
    |ANpro F=> Free_npro F
    |Assn_sub x i D => Free D
  end. 

(*-------------------------------Semantics-----------------------------------*)
Local Close Scope assert_scope.
Local Open Scope nat_scope.

Local Close Scope assert_scope.
Local Open Scope nat_scope.
Fixpoint Pure_eval{s e:nat} (pf:Pure_formula) (st:state s e): Prop :=
  match pf with 
 |PBexp b => if ((beval st b)) then True else False
 |PUniver P=> forall (a:nat),  Pure_eval (P a) st
 |PExists P=> exists (a:nat),  Pure_eval (P a) st
 |Assn_sub_P i a P => Pure_eval P (s_update_cstate i (aeval st a) st)
 end. 



Lemma kron_assoc : forall {m n p q r s : nat}
  (A : Matrix m n) (B : Matrix p q) (C : Matrix r s),
  WF_Matrix A -> WF_Matrix B -> WF_Matrix C ->
  ((A ⊗ B) ⊗ C) = A ⊗ (B ⊗ C).                                
Proof.
  intros.
  apply mat_equiv_eq; auto with wf_db.
  apply WF_kron; auto with wf_db; lia.
  apply kron_assoc_mat_equiv.
Qed.

Import ParDensityO.


Local Open Scope nat_scope.


Definition kron_qstate{s0 e0 s1 e1:nat}(q:qstate s0 e0) (q':qstate s1 e1):=
  @kron (2^(e0-s0)) (2^(e0-s0)) (2^(e1-s1)) (2^(e1-s1)) q q'.


Fixpoint QExp_eval{s' e':nat} (qs: QExp) (st: state s' e'){struct qs} :Prop:=
  (match qs with 
  |QExp_s s e v=>Pure_State_Vector v /\ s'<=s /\ s<e /\ e<=e' /\ ((PMpar_trace (@scale (2^(e'-s')) (2^(e'-s')) (R1 / (Cmod (@trace (2^(e'-s')) (snd st))))%R  (snd st)) s e = outer_product v v))
  |QExp_t qs1 qs2=>  NSet.Equal (NSet.inter (Free_Qexp qs1) (Free_Qexp qs2)) (NSet.empty)  /\
  QExp_eval qs1 st /\ QExp_eval qs2 st  
end).



Fixpoint State_eval{s e:nat} (F:State_formula) (st:state s e): Prop:=
(match F with 
|SPure P => Pure_eval P st
|SQuan s=> QExp_eval s st
|SOdot F1 F2=>  NSet.Equal (NSet.inter (snd (Free_state F1)) (snd (Free_state F2))) (NSet.empty) /\
State_eval F1 st /\ State_eval F2 st
|SAnd F1 F2 => State_eval F1 st /\ State_eval F2 st
(* |SNot F => ~(State_eval F st) *)
end).



Definition  State_eval_dstate{s e:nat} (F:State_formula) (mu:list (cstate *(qstate s e))): Prop:=
  match mu with 
  |nil => False 
  |_=>
  Forall (fun x=> State_eval F x) mu
  end.


Local Open Scope R_scope.
Inductive sat_State {s e:nat}:(dstate s e) -> (State_formula)-> Prop:=
  |sat_F: forall (mu:dstate s e) F, WF_dstate mu -> 
                       State_eval_dstate F (StateMap.this mu)
                           ->sat_State mu F.

(* Fixpoint big_and{s e:nat} (f : list (dstate s e)) (g: list (State_formula )) : Prop := 
match f , g with 
        |[], [] =>True 
        |[], _ =>False
        | _ ,[]=>False
        | hf:: tf , hg::tg=> (sat_State hf hg) /\ (big_and  tf tg)
end.            *)


Require Import Forall_two.
Inductive sat_Pro {s e:nat}: (dstate s e)-> (pro_formula)-> Prop:=
|sat_pro: forall (mu mu':dstate s e) pF (mu_n: list (dstate s e)),
                          big_dapp' (get_pro_formula pF) mu_n mu'
                          ->dstate_eq mu mu'
                          -> (Forall_two (fun mu_i nF_i => sat_State mu_i nF_i) mu_n (pro_to_npro_formula pF)) 
                          -> Forall (fun mu_i => d_trace  mu_i =d_trace mu) mu_n
                          -> sat_Pro mu pF.

Local Open Scope R_scope.

Fixpoint d_update_cstate_aux{s e:nat}  i a (mu:list (state s e)) := 
  match mu with
  |[] => []
  |(c, q):: mu' => (StateMap.Raw.map2 option_app [((c_update i (aeval (c,q) a) c), q)] (d_update_cstate_aux i a mu'))
  end.


Lemma d_update_cstate_sorted{s e:nat}: forall i a (mu:list (state s e)),
Sorted.Sorted (StateMap.Raw.PX.ltk (elt:=qstate s e))   mu -> 
Sorted.Sorted (StateMap.Raw.PX.ltk (elt:=qstate s e))  (d_update_cstate_aux i a mu).
Proof. intros. induction mu. simpl. apply Sorted.Sorted_nil. 
destruct a0.  unfold d_update_cstate_aux.
      apply StateMap.Raw.map2_sorted.
      apply Sorted.Sorted_cons.
      apply Sorted.Sorted_nil.
      apply Sorted.HdRel_nil.
      apply IHmu. 
     inversion_clear H.  assumption.  
Qed.


Definition d_update_cstate {s e:nat} i a (mu:dstate s e) := 
  StateMap.Build_slist (d_update_cstate_sorted i a (StateMap.this mu)
  (StateMap.sorted mu)).

 
Inductive sat_Assert {s e:nat}: (dstate s e)-> (Assertion)-> Prop:=
|sat_APro: forall (mu:dstate s e) pF , 
                 WF_dstate mu -> distribution_formula pF -> sat_Pro mu pF -> 
                 sat_Assert mu (APro pF)
|sat_ANpro: forall (mu:dstate s e) nF (p_n:list R), 
                     length p_n =length nF
                    ->sat_Assert mu (npro_to_pro_formula nF p_n)
                    ->sat_Assert mu (ANpro nF)
|sat_Assn: forall (mu:dstate s e) i a D, 
                    WF_dstate mu ->
                      sat_Assert (d_update_cstate i a mu) D
                   -> sat_Assert mu (Assn_sub i a D).





(* Lemma sum_over_list_formula_npro_to_pro: forall nF1 nF2 p_n,
length nF1 = length p_n ->
length nF2= length p_n->
sum_over_list_formula (npro_to_pro_formula nF1 p_n) =
sum_over_list_formula (npro_to_pro_formula nF2 p_n).
Proof. induction nF1; induction nF2; intros.
simpl. reflexivity.
      rewrite <-H in H0. discriminate H0.
      rewrite <-H0 in H. discriminate H.
      destruct p_n.
      discriminate H0.
      simpl.  repeat rewrite sum_over_list_cons_formula.
      simpl. f_equal. apply IHnF1. 
      injection H. intuition.
      injection H0. intuition.
Qed.

Lemma Forall_npro_to_pro: forall nF1 nF2 p_n,
length nF1 = length p_n ->
length nF2= length p_n->
Forall (fun x : R * State_formula => 0 <= fst x)  (npro_to_pro_formula nF1 p_n) ->
Forall (fun x : R * State_formula => 0 <= fst x) (npro_to_pro_formula nF2 p_n).
Proof. induction nF1; induction nF2; intros.
       assumption. rewrite <-H in H0. discriminate H0.
       rewrite <-H0 in H. discriminate H.
       destruct p_n.
       discriminate H0.
       simpl in *. 
       inversion_clear H1.
       econstructor. simpl in *.
       assumption.
       apply IHnF1. injection H. intuition.
       injection H0. intuition. assumption.
Qed.


Lemma distribution_formula_npro_to_pro: forall nF1 nF2 p_n,
length nF1 = length p_n ->
length nF2= length p_n->
distribution_formula  (npro_to_pro_formula nF1 p_n) ->
distribution_formula (npro_to_pro_formula nF2 p_n).
Proof. intros. unfold distribution_formula in *.
       destruct H1. split. apply Forall_npro_to_pro with nF1.
       assumption. assumption. assumption.
       rewrite <-H2.
       apply sum_over_list_formula_npro_to_pro.
       assumption. assumption.
Qed. *)

Lemma bexp_Pure_eq{s0 e0 s1 e1:nat}:  forall (st :state s0 e0) (st': state s1 e1) (b:bexp) , 
((beval st b) = beval st' b) -> (Pure_eval b st)<->(Pure_eval b st').
Proof.  simpl.  intros. destruct (beval st b).
       rewrite <-H. reflexivity. rewrite <-H.
       reflexivity. 
Qed.

Lemma state_eq_Pure{s0 e0 s1 e1:nat}: forall (P:Pure_formula) (st :state s0 e0)  (st': state s1 e1),
(fst st)= (fst st')-> (Pure_eval P st)<-> Pure_eval P st'.
Proof. induction P.
     --intros. apply (bexp_Pure_eq st st' b ).
      rewrite (state_eq_bexp st st' b). reflexivity.
       intuition.
    --simpl.  
      simpl. destruct st. destruct st'. unfold s_update_cstate.
       intros. split. intros. apply H with  (c, q). intuition. 
       apply H1. 
       intros. apply H with  (c0, q0). intuition. 
       apply H1. 
    -simpl.  
    simpl. destruct st. destruct st'. unfold s_update_cstate. intros.
    split. intros. destruct H1. exists x. apply H with  (c, q). intuition. 
    apply H1. 
    intros. destruct H1. exists x. apply H with  (c0, q0). intuition. 
    apply H1. 
    - split; intros; destruct st; destruct st'; 
      simpl in *; unfold s_update_cstate in *;
      simpl in H; subst.
     rewrite (state_eq_aexp (c0, q0) ((c0, q))).
     apply (IHP  ((c_update i (aeval (c0, q) a) c0, q))
     (c_update i (aeval (c0, q) a) c0, q0)) .
     reflexivity. assumption. reflexivity.
     rewrite <-(state_eq_aexp (c0, q0) ((c0, q))).
     apply (IHP  ((c_update i (aeval (c0, q0) a) c0, q))
     (c_update i (aeval (c0, q0) a) c0, q0)) .
     reflexivity. assumption. reflexivity.
Qed.



Lemma qstate_eq_Qexp:forall (qs :QExp) {s e:nat} (st st':state s e) , 
 snd st= snd st' -> 
 QExp_eval  qs st -> QExp_eval  qs st'.
Proof.   induction qs; intros;
destruct st; destruct st'; simpl in H; subst.
simpl in *. assumption.
simpl in *.  
destruct H0. destruct H0.
 split. assumption.
split.
apply IHqs1 with ((c, q0)).
reflexivity. intuition.
apply IHqs2 with ((c, q0)).
reflexivity. intuition. 
Qed.

(* Local Open Scope nat_scope.
Lemma State_free_eval{s e:nat}:forall (F: State_formula) (st: state s e),
s<=(fst (Free_State F)) /\
(fst (Free_State F)) <=  (snd (Free_State F))
/\ (snd (Free_State F))<=e->
@WF_Matrix (2^(e-s)) (2^(e-s)) (snd st) ->
State_eval F st <-> 
State_eval F (fst st, (PMpar_trace (snd st) ((fst (Free_State F))) ((snd (Free_State F))))).
Proof. induction F; split; intros. destruct st. 
       simpl. simpl in H0. split. intuition. eapply state_eq_Pure with (c, q). 
        reflexivity. apply H1.
        destruct st. simpl in *.
        split. intuition.
        eapply state_eq_Pure with (c, PMpar_trace q 0 0). 
        reflexivity. intuition. destruct st.
        simpl in *. split. intuition.
        apply (QExp_free_eval _  (c, q)) .
        intuition. intuition. intuition.
        destruct st. simpl in *.
        split. intuition. 
        apply QExp_free_eval. intuition.
        intuition. intuition. 
        simpl. rewrite PMpar_trace_refl.
        simpl in H1. 
        
        split. apply H1. 
        split. intuition.

      intuition.  intuition. 
      apply WF_PMpar_trace. 
      split. intuition. split.
       intuition. intuition.
       assumption. 
      simpl in *. 
      rewrite PMpar_trace_refl in H1.
      intuition. intuition.
      apply WF_PMpar_trace.
      intuition. assumption.

        simpl in *; split;
        try apply H1. admit.
        admit. 
Admitted. *)




Local Close Scope assert_scope.
(* Definition q_subseq{s e:nat} (q0 q1: qstate s e):Prop:=
  q0=q1 \/ exists x, @Mplus (2^(e-s))  (2^(e-s)) q0 x = q1. 

Lemma eq_i_j: forall (i j:nat),
i=j<-> (i=?j) = true.
Proof. induction i; destruct j.
      simpl. intuition.
      simpl. intuition.
      simpl. intuition.
      split; intros. apply IHi.
      injection H. intuition. 
      f_equal. apply IHi. intuition.
Qed.  *)

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
       destruct H1.
       destruct H1.
       assert(exists (p : R) (φ : Vector (2 ^ ((snd (Free_QExp' qs1)) - (fst (Free_QExp' qs1))))),
       p
       .* PMpar_trace x (fst (Free_QExp' qs1) ) (snd (Free_QExp' qs1) ) =
       φ × (φ) †).
       apply IHqs1 with c. intuition.
       assert(exists (p : R) (φ : Vector (2 ^ ((snd (Free_QExp' qs2)) - (fst (Free_QExp' qs2))))),
       p
       .* PMpar_trace x0 (fst (Free_QExp' qs2)) (snd (Free_QExp' qs2) ) =
       φ × (φ) †).
       apply IHqs2 with c. 
        intuition.
       destruct H2. destruct H2.
       destruct H3. destruct H3.
       rewrite PMpar_trace_refl in H2.
       rewrite PMpar_trace_refl in H3.
       destruct H1. inversion H4; subst; clear H4.
       assert(snd (Free_QExp' qs1) =? fst (Free_QExp' qs2)=true).
         rewrite <-eq_i_j. assumption. 
        rewrite H4 in *.  clear H7. 
        clear H10. 
       exists (x1*x3)%R. 
       exists (kron x2 x4). 
       simpl. rewrite H4. 
       rewrite <-H5. 
      admit.
      assert(snd (Free_QExp' qs2) =? fst (Free_QExp' qs1)=true).
      rewrite <-eq_i_j. assumption.
      simpl. 
     rewrite <-H7 in *. 
     rewrite <-H10  in   *.
    exists (x1*x3)%R. 
    exists (kron x2 x4). 
    rewrite <-H5.
      admit.

      intuition. admit.
      intuition. admit.

Admitted. *)


(* Lemma State_eval_pure: forall F s e c (q: qstate s e) ,
State_eval qs (c, q)->
exists (p:R) (φ: Vector (2^((snd (Free_State F))-(fst (Free_State F))))),
p .* (@PMpar_trace s e q ((fst (Free_State F))) (((snd (Free_State F)))) )
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
       destruct H1.
       destruct H1.
       assert(exists (p : R) (φ : Vector (2 ^ ((snd (Free_QExp' qs1)) - (fst (Free_QExp' qs1))))),
       p
       .* PMpar_trace x (fst (Free_QExp' qs1) ) (snd (Free_QExp' qs1) ) =
       φ × (φ) †).
       apply IHqs1 with c. intuition.
       assert(exists (p : R) (φ : Vector (2 ^ ((snd (Free_QExp' qs2)) - (fst (Free_QExp' qs2))))),
       p
       .* PMpar_trace x0 (fst (Free_QExp' qs2)) (snd (Free_QExp' qs2) ) =
       φ × (φ) †).
       apply IHqs2 with c. 
        intuition.
       destruct H2. destruct H2.
       destruct H3. destruct H3.
       rewrite PMpar_trace_refl in H2.
       rewrite PMpar_trace_refl in H3.
       destruct H1. inversion H4; subst; clear H4.
       assert(snd (Free_QExp' qs1) =? fst (Free_QExp' qs2)=true).
         rewrite <-eq_i_j. assumption. 
        rewrite H4 in *.  clear H7. 
        clear H10. 
       exists (x1*x3)%R. 
       exists (kron x2 x4). 
       simpl. rewrite H4. 
       rewrite <-H5. 
      admit.
      assert(snd (Free_QExp' qs2) =? fst (Free_QExp' qs1)=true).
      rewrite <-eq_i_j. assumption.
      simpl. 
     rewrite <-H7 in *. 
     rewrite <-H10  in   *.
    exists (x1*x3)%R. 
    exists (kron x2 x4). 
    rewrite <-H5.
      admit.

      intuition. admit.
      intuition. admit.

Admitted. *)


Local Open Scope R_scope.
Lemma Mscale_not_0':forall (m n:nat) (A:Matrix m n) (p: R), 
p.* A <> Zero -> A<>Zero .
Proof. unfold not.  intros.  rewrite H0 in H.  rewrite Mscale_0_r in H.
intuition. 
Qed.


Local Open Scope C_scope.
Lemma s_seman_scale_Qexp: forall  (qs:QExp) (p:R)  (s e:nat) (c:cstate) (q:qstate s e),
0<p-> 
(QExp_eval qs (c, q) <-> @QExp_eval s e qs  (c, p.* q)).
Proof. split. intros.
induction qs.  
simpl in H0.
simpl.
rewrite trace_mult_dist.
rewrite Rdiv_unfold.
rewrite Mscale_assoc.
rewrite Cmod_mult.
rewrite Rinv_mult.
rewrite Rmult_1_l.
rewrite Cmod_R. rewrite Rabs_right.   
rewrite Cmult_comm with (y:=(RtoC p)).
rewrite RtoC_mult. 
rewrite <-Rmult_assoc. 
rewrite Rinv_r. intuition.
lra. lra. 

simpl in H0.
destruct H0. destruct H1.
simpl.  split. assumption.
apply IHqs1 in H1.
apply IHqs2 in H2.
split. assumption. assumption.


induction qs.  
simpl; 
rewrite trace_mult_dist.
rewrite Rdiv_unfold.
rewrite Mscale_assoc.
rewrite Cmod_mult.
rewrite Rinv_mult.
rewrite Rmult_1_l.
rewrite Cmod_R. rewrite Rabs_right.   
rewrite Cmult_comm with (y:=(RtoC p)).
rewrite RtoC_mult. 
rewrite <-Rmult_assoc. 
rewrite Rinv_r. intuition.
lra. lra.
intros.
simpl in H0.
destruct H0. destruct H1.
simpl.  split. assumption.
apply IHqs1 in H1.
apply IHqs2 in H2.
split. assumption. assumption.
Qed.



(* Lemma State_eval_sub: forall qs s e c (q q': qstate s e) ,
q_subseq q q'->
QExp_eval qs (c, q')->
QExp_eval qs (c, q).
Proof. induction qs; intros; 
       destruct H; subst; try assumption.
       destruct H.  subst.
       admit.
       destruct H. subst.
       assert (exists (p:R) (φ: Vector (2^((snd (Free_QExp' ((qs1 ⊗* qs2))))-(fst (Free_QExp' ((qs1 ⊗* qs2))))))),
       p .* (PMpar_trace (q.+ x) ((fst (Free_QExp' ((qs1 ⊗* qs2))))) (((snd (Free_QExp' ((qs1 ⊗* qs2)))))) )= φ  × φ†).
       apply QExp_eval_pure with c. assumption.
       destruct H. destruct H.
       destruct H0. 
       destruct H1.
       destruct H2.
       destruct H2.
       destruct H2.
       destruct H2.
       simpl ((snd (c, q .+ x))) in H3.
    rewrite PMtrace_plus in *.
    simpl QExp_eval. split. apply H0. 
    split. apply H1.
     inversion H3; subst;
     simpl in *;  simpl in *;  
     rewrite <-H7 in *; rewrite <-H10 in *.
    assert(x0 .*  (@kron ((2^((snd (Free_QExp' qs1))-(fst (Free_QExp' qs1))))) 
    (2^((snd (Free_QExp' qs1))-(fst (Free_QExp' qs1)))) 
    (2^((snd (Free_QExp' qs2))-(fst (Free_QExp' qs2))))
    (2^((snd (Free_QExp' qs2))-(fst (Free_QExp' qs2))))x2 x3)= x1 × (x1) † ).
    rewrite H5. apply H. 
    rewrite Mscale_plus_distr_r in H.
    remember (PMpar_trace q (fst (Free_QExp' qs1))
    (snd (Free_QExp' qs2))).
    remember (PMpar_trace x (fst (Free_QExp' qs1))
    (snd (Free_QExp' qs2))).
    eapply (Mixed_pure (x0 .* q0) (x0 .* q1 )) in H.
    destruct H. destruct H.
    exists (sqrt x4 .* x2).
    exists (sqrt x4 .* x3).
    split. 
    split. apply s_seman_scale_Qexp.
    apply sqrt_lt_R0. 
    admit. intuition.
    apply s_seman_scale_Qexp.
    admit. intuition.
    admit.
     admit. admit. 
    admit. admit. 
  

    assert(x0 .*  (@kron ((2^((snd (Free_QExp' qs2))-(fst (Free_QExp' qs2))))) 
    (2^((snd (Free_QExp' qs2))-(fst (Free_QExp' qs2)))) 
    (2^((snd (Free_QExp' qs1))-(fst (Free_QExp' qs1))))
    (2^((snd (Free_QExp' qs1))-(fst (Free_QExp' qs1))))x3 x2)= x1 × (x1) † ).
    rewrite H5. try assumption.
    rewrite Mscale_plus_distr_r in H.
    remember (PMpar_trace q (fst (Free_QExp' qs2))
    (snd (Free_QExp' qs1))).
    remember (PMpar_trace x (fst (Free_QExp' qs2))
    (snd (Free_QExp' qs1))).
    eapply (Mixed_pure (x0 .* q0) (x0 .* q1 )) in H.
    destruct H. destruct H.
    exists (sqrt x4 .* x2).
    exists (sqrt x4 .* x3).
    split. 
    split. apply s_seman_scale_Qexp.
    admit. intuition.
    apply s_seman_scale_Qexp.
    admit. intuition.
     admit. admit. 
    admit. admit. admit.
Admitted.  *)


       

(* Lemma State_eval_sub': forall F s e c (q q': qstate s e) ,
q_subseq q q'->
State_eval F (c, q')->
State_eval F (c, q).
Proof. induction F; intros. simpl in *.
       split. intuition.
       apply state_eq_Pure with (c,q').
       reflexivity. intuition. simpl in *.
       split. intuition. 
       apply State_eval_sub with q'.
       assumption. intuition. 
       destruct H. subst.
        apply H0. 
       destruct H. subst.
       assert (exists (p:R) (φ: Vector (2^((snd (Free_State ((F1 ⊙ F2))))-(fst (Free_State ((F1 ⊙ F2))))))),
       p .* (PMpar_trace (q.+ x) ((fst (Free_State ((F1 ⊙ F2))))) (((snd (Free_State ((F1 ⊙ F2)))))) )= φ  × φ†).
       apply QExp_eval_pure with c. assumption.
       destruct H. destruct H.
       destruct H0. 
       destruct H1.
       destruct H2.
       destruct H2.
       destruct H2.
       destruct H2.
       simpl ((snd (c, q .+ x))) in H3.
    rewrite PMtrace_plus in *.
    simpl QExp_eval. split. apply H0. 
    split. apply H1.
     inversion H3; subst;
     simpl in *;  simpl in *;  
     rewrite <-H7 in *; rewrite <-H10 in *.
    assert(x0 .*  (@kron ((2^((snd (Free_QExp' qs1))-(fst (Free_QExp' qs1))))) 
    (2^((snd (Free_QExp' qs1))-(fst (Free_QExp' qs1)))) 
    (2^((snd (Free_QExp' qs2))-(fst (Free_QExp' qs2))))
    (2^((snd (Free_QExp' qs2))-(fst (Free_QExp' qs2))))x2 x3)= x1 × (x1) † ).
    rewrite H5. apply H. 
    rewrite Mscale_plus_distr_r in H.
    remember (PMpar_trace q (fst (Free_QExp' qs1))
    (snd (Free_QExp' qs2))).
    remember (PMpar_trace x (fst (Free_QExp' qs1))
    (snd (Free_QExp' qs2))).
    eapply (Mixed_pure (x0 .* q0) (x0 .* q1 )) in H.
    destruct H. destruct H.
    exists (sqrt x4 .* x2).
    exists (sqrt x4 .* x3).
    split. 
    split. apply s_seman_scale_Qexp.
    apply sqrt_lt_R0. 
    admit. intuition.
    apply s_seman_scale_Qexp.
    admit. intuition.
    admit.
     admit. admit. 
    admit. admit. 
  

    assert(x0 .*  (@kron ((2^((snd (Free_QExp' qs2))-(fst (Free_QExp' qs2))))) 
    (2^((snd (Free_QExp' qs2))-(fst (Free_QExp' qs2)))) 
    (2^((snd (Free_QExp' qs1))-(fst (Free_QExp' qs1))))
    (2^((snd (Free_QExp' qs1))-(fst (Free_QExp' qs1))))x3 x2)= x1 × (x1) † ).
    rewrite H5. try assumption.
    rewrite Mscale_plus_distr_r in H.
    remember (PMpar_trace q (fst (Free_QExp' qs2))
    (snd (Free_QExp' qs1))).
    remember (PMpar_trace x (fst (Free_QExp' qs2))
    (snd (Free_QExp' qs1))).
    eapply (Mixed_pure (x0 .* q0) (x0 .* q1 )) in H.
    destruct H. destruct H.
    exists (sqrt x4 .* x2).
    exists (sqrt x4 .* x3).
    split. 
    split. apply s_seman_scale_Qexp.
    admit. intuition.
    apply s_seman_scale_Qexp.
    admit. intuition.
     admit. admit. 
    admit. admit. admit.
       simpl in *.
       split. split. apply IHF1 with q'.
       assumption. intuition.
       apply IHF2 with q'.
       assumption. intuition.
       intuition.
Admitted. *)
        





Local Open Scope R_scope.
Lemma s_seman_scale: forall (F:State_formula) (p:R) s e  (st:state s e),
0<p->
(State_eval F st <-> State_eval F (s_scale p st)).
Proof.  induction F. 
-- intros. split. apply (state_eq_Pure  P st (s_scale p st)) . simpl. reflexivity.
                  apply (state_eq_Pure  P (s_scale p st) st ) . simpl. reflexivity.
-- intros. destruct st.  unfold s_scale. simpl. apply s_seman_scale_Qexp. assumption.
-- split; simpl; intros; destruct H0; destruct H1;
split;  try assumption; split; try  apply (IHF1 p s e st); try assumption;
try apply (IHF2 p s e st); try assumption.  
-- split; simpl; intros; destruct H0;
split; try apply (IHF1 p s e st); try assumption;
try apply (IHF2 p  s e st); try assumption.
(* --intros. split; intros; simpl; unfold not; simpl in H1; unfold not in H1;
intros.
assert(State_eval  F st). apply (IHF p n st). assumption. assumption. assumption. apply H1 in H3.
assumption.
assert(State_eval F (s_scalar p st)). apply (IHF p n st). assumption. assumption. assumption. apply H1 in H3.
assumption. *)
(* --split; intros; destruct st; simpl in H1.  unfold s_update_cstate in H1.
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
  assumption. *)
Qed.


Lemma s_seman_scale_c: forall (F:State_formula) (c:C) s e sigma (q:qstate s e),
0<(fst c) /\ snd c=0 ->
(State_eval F (sigma, q) <-> @State_eval s e F (sigma, c .* q)).
Proof. intros. destruct c.  simpl in *. destruct H. rewrite H0. 
apply s_seman_scale. assumption.  
Qed. 


Local Open Scope C_scope.
Lemma d_seman_scale_aux: forall  (F:State_formula) (p:R)  (s e:nat) (mu:list (cstate * qstate s e)),
0<p->
(State_eval_dstate F mu ->@State_eval_dstate s e F 
(StateMap.Raw.map (fun x : qstate s e => p .* x) mu)).
Proof. induction mu; simpl; intros.  destruct H0. 
       destruct a. inversion_clear H0.
       destruct mu.   
       simpl. econstructor.   assert(State_eval  F (s_scale p (c, q))).
       apply s_seman_scale. intuition. intuition.
       unfold s_scale in H0. simpl in H0.
       intuition. assumption. destruct p0.
       simpl. econstructor. 
       assert(State_eval  F (s_scale p (c, q))).
       apply s_seman_scale. intuition. intuition.
       unfold s_scale in H0. simpl in H0.
       intuition. apply IHmu. intuition. 
      simpl.  assumption.
Qed.



Local Open Scope R_scope.
Lemma d_seman_scalar: forall s e (p:R) (mu:dstate s e) (F:State_formula),
0<p<=1->sat_State mu F -> sat_State (d_scale_not_0 p mu) F.
Proof. 
       intros. destruct mu as [mu IHmu]. 
       inversion H0; subst. 
       simpl in H2.
       apply sat_F. 
       apply WF_d_scale_not_0. intuition.
       intuition. simpl. apply d_seman_scale_aux.
       intuition. unfold WF_dstate in H1. 
       simpl in H1. intuition. 
Qed.


Lemma seman_find_state_aux{s e:nat}:forall  (st: (cstate * qstate s e)) (F: State_formula),
( WF_dstate_aux [st]) -> (State_eval_dstate F [st] <->
(forall x:cstate, (option_qstate (StateMap.Raw.find x [st]) <> Zero) -> (State_eval F 
(x, (option_qstate (StateMap.Raw.find x [st])))))).
Proof. intros. 
      split; intros.
      destruct st. simpl in *. inversion_clear H0.
      destruct (Cstate_as_OT.compare x c).
      simpl in *. destruct H1. reflexivity.
      simpl. unfold Cstate_as_OT.eq in e0. rewrite e0. assumption.
      destruct H1. reflexivity.
      destruct st.
      assert( option_qstate (StateMap.Raw.find (elt:=qstate s e) c [(c, q)]) <>
     Zero ->
     State_eval F
       (c,
        option_qstate
          (StateMap.Raw.find (elt:=qstate s e) c [(c, q)]))).
      apply H0. clear H0.
      simpl in *.  
      destruct (Cstate_as_OT.compare c c).
      apply Cstate_as_OT.lt_not_eq in l. intuition.
      simpl in *. inversion_clear H.
      assert(q<>Zero).  apply (WF_state_not_Zero _ H0).
      apply H1 in H. econstructor. assumption.
      apply Forall_nil.
      apply Cstate_as_OT.lt_not_eq in l. intuition.
Qed.
      
      
      
Lemma seman_find_aux{s e}:forall  (mu:list (cstate * qstate s e)) (F: State_formula),
Sorted.Sorted
  (StateMap.Raw.PX.ltk (elt:=qstate s e)) mu->
(mu<> nil /\ WF_dstate_aux mu) -> 
(State_eval_dstate F mu <->
(forall x:cstate, (option_qstate (StateMap.Raw.find x mu) <> Zero) -> (State_eval F 
(x, (option_qstate (StateMap.Raw.find x mu)))))). 
Proof. induction mu; intros.
      -simpl. destruct H0. destruct H0. reflexivity.
      -destruct mu. apply seman_find_state_aux. 
        apply H0. 
        split. destruct a. destruct p. 
        intros.  simpl.
        simpl in *. inversion_clear H1.
        destruct  (Cstate_as_OT.compare x c ).
        simpl in H2. destruct H2. reflexivity.
        unfold Cstate_as_OT.eq in e0.
        rewrite e0. 
        simpl. assumption.
        apply IHmu. inversion_clear H.
        assumption. split. discriminate.
        destruct H0. inversion_clear H1.
        assumption. assumption.
        apply H2.

        destruct a. destruct p. intros.
        simpl.  econstructor.  
        assert(State_eval F
        (c,
         option_qstate
           (StateMap.Raw.find (elt:=qstate s e) c ((c, q) :: (c0, q0) :: mu)))).

       apply H1. 
       simpl. destruct (Cstate_as_OT.compare c c).
       apply Cstate_as_OT.lt_not_eq in l. intuition.
       simpl. destruct H0. inversion_clear H2.  apply (WF_state_not_Zero _ H3).
       apply Cstate_as_OT.lt_not_eq in l. intuition.
       simpl in H2. 
       destruct (Cstate_as_OT.compare c c).
       apply Cstate_as_OT.lt_not_eq in l. intuition.
       simpl. simpl in H2. assumption.
       apply Cstate_as_OT.lt_not_eq in l. intuition.
     
       apply IHmu. inversion_clear H. assumption.
       split. discriminate. destruct H0. inversion_clear H2.
       assumption. 
       intros. assert(Cstate_as_OT.lt c x).
       apply dstate_1 with ((c0, q0) :: mu) q.
       assumption. assumption. 
       assert(State_eval F
       (x, option_qstate
          (StateMap.Raw.find (elt:=qstate s e) x ((c, q) :: (c0, q0) :: mu)))).
      apply H1.  simpl. 
      destruct (Cstate_as_OT.compare x c);
      try rewrite l in H3; try apply Cstate_as_OT.lt_not_eq in H3; try intuition.
      simpl in H4.    
      destruct (Cstate_as_OT.compare x c);
      try rewrite l in H3; try apply Cstate_as_OT.lt_not_eq in H3; try intuition.
Qed.

Lemma WF_sat_State{s e:nat}: forall  (mu:dstate s e) (F:State_formula), 
sat_State mu F -> StateMap.this mu <> [] /\ WF_dstate mu.
Proof. intros. 
      inversion_clear H. destruct mu as [mu IHmu].
      destruct mu.
      simpl in H1.  destruct H1.  
      split. discriminate. intuition.
Qed.

Lemma seman_find{s e}:forall  (mu:dstate s e) (F: State_formula),
sat_State mu F <->
(WF_dstate mu /\ StateMap.this mu <> [] /\ (forall x:cstate, d_find x mu <>Zero -> (State_eval F 
(x, (d_find x mu))))).
Proof. intros. destruct mu as [mu IHmu]. simpl.
split. intros. split.  
inversion_clear H. assumption. split.
apply (WF_sat_State _ _ H). inversion_clear H.
unfold d_find. unfold StateMap.find. simpl in *.
apply  seman_find_aux. assumption. split.
unfold not. 
intros. rewrite H in H1. simpl in H1. destruct H1. apply H0.
assumption.
intros.  destruct H.
econstructor. assumption.
apply seman_find_aux;
simpl in *. assumption.
intuition. apply H0.  
Qed.


Lemma State_eval_dstate_Forall{s e}:forall (mu:list (cstate *qstate s e)) F,
mu<>nil->
(State_eval_dstate F mu <-> Forall (fun x : state s e => State_eval F x) mu).
Proof. induction mu. simpl. intuition.
      simpl. intros. intuition.
  
Qed.

(* Lemma State_eval_plus_dis{n:nat}: forall F c (q q0: qstate n),
@State_eval n F (c, q .+ q0)-> 
       State_eval F (c, q) \/ State_eval F (c, q0) .
Proof. induction F; intros. left. 
      -apply state_eq_Pure with  (c, q.+ q0). 
       reflexivity. intuition. admit.
       simpl in *. destruct H. destruct H0.
       apply IHF1 in H0. apply IHF2 in H1.
       destruct H0. destruct H1.
       left. intuition.

       
       
       left.  split. intuition. 
           
  
Qed. *)

Lemma  WF_qstate_gt_0{s e:nat}: forall (q:qstate s e), 
WF_qstate q -> (Cmod (@trace (2^(e-s)) q) > 0)%R.
Proof.
unfold WF_qstate.  intros.
apply mixed_state_Cmod_1. intuition. 
Qed.



Lemma  State_eval_plus{s e:nat}: forall F c (q q0: qstate s e),
WF_qstate q ->
WF_qstate q0->
State_eval F (c, q)->
State_eval F (c,q0) ->
@State_eval s e F (c, q .+ q0) .
Proof.  
       induction F; intros;  intros.
      -apply state_eq_Pure with  (c, q0). 
       reflexivity. intuition.   
      -induction qs. simpl in *.
        rewrite Rdiv_unfold in *.
        rewrite trace_plus_dist.
        rewrite <-PMtrace_scale.
        assert(q= (Cmod (@trace (2^(e-s)) q))%R .* (((R1 /  (Cmod (@trace  (2^(e-s)) q))))%R .* q) ).
        rewrite Mscale_assoc. 
         rewrite Rdiv_unfold.
         rewrite RtoC_mult. 
       rewrite <-Rmult_assoc . 
       rewrite Rmult_comm.  
         rewrite <-Rmult_assoc . 
         rewrite Rinv_l.   
         rewrite Rmult_1_r . 
         rewrite Mscale_1_l. reflexivity.
        unfold not. intros. apply WF_qstate_gt_0 in H.
        rewrite H3 in H. lra. 
        assert(q0= (Cmod (@trace (2^(e-s)) q0))%R .* (((R1 /  (Cmod (@trace  (2^(e-s)) q0))))%R .* q0) ).
        rewrite Mscale_assoc. 
         rewrite Rdiv_unfold.
         rewrite RtoC_mult. 
       rewrite <-Rmult_assoc . 
       rewrite Rmult_comm.  
         rewrite <-Rmult_assoc . 
         rewrite Rinv_l.   
         rewrite Rmult_1_r . 
         rewrite Mscale_1_l. reflexivity.
        unfold not. intros. apply WF_qstate_gt_0 in H0.
        rewrite H4 in H0. lra. 
         rewrite H3. rewrite H4.
          rewrite PMtrace_plus. 
          rewrite <-PMtrace_scale. 
          rewrite Rdiv_unfold in *.
          destruct H1. destruct H5. destruct H6. destruct H2.
          destruct H7.
          destruct H8. destruct H10.
          destruct H11.
          split. intuition. split. intuition.
          split. intuition. split. intuition.
          rewrite H9.
          rewrite <-PMtrace_scale. 
          rewrite Rdiv_unfold. rewrite H12.
        rewrite <-Mscale_plus_distr_l.
        rewrite Mscale_assoc. 
        rewrite<-H4. rewrite <-H3.
        rewrite <-RtoC_plus.
       rewrite RtoC_mult.
         rewrite Rmult_assoc.
         rewrite <-trace_plus_dist.
         rewrite mixed_state_Cmod_plus.
         rewrite Rinv_l. rewrite Rmult_1_l.
         rewrite Mscale_1_l. reflexivity.
         assert((Cmod (@trace (2^(e-s)) q) + Cmod (@trace  (2^(e-s)) q0) )%R<> 0%R).
         apply tech_Rplus. assert(Cmod(@trace (2^(e-s)) q)%R>0%R)%R.
         apply mixed_state_Cmod_1. apply H.
         intuition.  apply mixed_state_Cmod_1. apply H0.
         assumption.
         apply H. apply H0. 
       
        simpl in *. split. intuition.
        destruct H2. destruct H3. 
        destruct H1. destruct H5. 
        apply IHqs1 in H5. apply IHqs2 in H6.
        split. assumption. assumption. assumption.
        assumption.  
      -simpl in *. split. intuition.  split. intuition. intuition. 
      - simpl in *.  split. intuition. intuition. 
Qed.


Lemma d_seman_app_aux: forall s e  (mu mu':list (cstate * qstate s e))  (F:State_formula),
WF_dstate_aux mu ->
WF_dstate_aux mu'->
State_eval_dstate F mu-> State_eval_dstate  F (mu')
-> State_eval_dstate  F (StateMap.Raw.map2 option_app mu mu').
Proof.

       induction  mu; intros. simpl. rewrite map2_r_refl. 
       assumption.   
       destruct a. induction mu'. simpl. 
       rewrite map2_l_refl. apply H1.   
     
       destruct a. simpl. 
       destruct (Cstate_as_OT.compare c c0). 
       simpl. inversion_clear H1. econstructor.
       assumption. destruct mu. 
       simpl. econstructor. inversion_clear H2. 
       assumption. rewrite map2_r_refl. inversion_clear H2.
       assumption.   
       assert(State_eval_dstate F (StateMap.Raw.map2 option_app (p :: mu) ((c0, q0) :: mu'))).
       apply IHmu. inversion_clear H. assumption.
       assumption. simpl. assumption. assumption. 
       apply State_eval_dstate_Forall. 
       apply map2_app_not_nil. discriminate. discriminate.
       assumption.
       simpl. econstructor. apply State_eval_plus.
       inversion_clear H. apply H3. 
       inversion_clear  H0. apply H3. 
       inversion_clear H1. assumption.
       inversion_clear H2. unfold Cstate_as_OT.eq in e0.
       rewrite e0. assumption.  
       destruct mu. simpl. rewrite map2_r_refl.
       inversion_clear H2. assumption.
       destruct mu'. rewrite map2_nil_r. 
       inversion_clear H1. assumption.
       apply State_eval_dstate_Forall.
       apply map2_app_not_nil. 
       discriminate.  discriminate. 
       apply IHmu. inversion_clear H. assumption.
       inversion_clear H0. assumption.
       inversion_clear H1. assumption. inversion_clear H2. assumption.

       destruct mu'. econstructor. inversion_clear H2. assumption.
       rewrite map2_l_refl. intuition.
       econstructor. inversion_clear H2. assumption.
       apply State_eval_dstate_Forall.
       induction mu'. destruct p; 
       destruct (Cstate_as_OT.compare c c1);
       discriminate. destruct p.
       destruct a. destruct (Cstate_as_OT.compare c c1);
       discriminate.  apply IHmu'.  
       inversion_clear H0. assumption.
       inversion_clear H2. assumption.   
Qed.

Local Open Scope R_scope.
Lemma d_seman_app: forall s e (F:State_formula)  (mu mu':dstate s e) (p0 p1:R),
(0 < p0 <= 1)->(0 < p1 <= 1)
->(0<(p0+p1)<=1)->
sat_State mu F  -> sat_State  (mu') F
-> sat_State (d_app (d_scale_not_0 p0 mu)
   (d_scale_not_0 p1 mu')) F.
Proof. intros s e F (mu, IHmu) (mu', IHmu'); intros.
       inversion H2; subst. inversion H3; subst.
       apply sat_F. 
       apply WF_d_app'.  intuition. intuition.
       assumption. assumption. 
       simpl. apply d_seman_app_aux. 
       apply WF_d_scale_aux. assumption.
       assumption. 
       apply WF_d_scale_aux. assumption.
       assumption. 
       apply d_seman_scale_aux. intuition. 
       assumption. 
       apply d_seman_scale_aux. intuition. 
       assumption.  
Qed.

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



Lemma Rdiv_in01: forall p1 p2,
0 < p1 <=1->
0 < p2 <=1->
0 < p1 / (p1 + p2) <=1.
Proof. split.  rewrite Rdiv_unfold. apply Rmult_gt_0_compat.
intuition. apply Rinv_0_lt_compat. apply Rplus_lt_0_compat.
intuition. intuition. apply (Rcomplements.Rdiv_le_1 p1 _).
apply Rplus_lt_0_compat.
intuition. intuition.  assert(p1=p1+0). rewrite Rplus_0_r.
reflexivity. rewrite H1 at 1. apply Rplus_le_compat_l.
intuition. 
Qed.


Lemma  sat_State_dstate_eq: forall s e (D:State_formula) (mu mu': dstate s e),
dstate_eq mu mu'->
sat_State mu D-> sat_State mu' D.
Proof. intros.
        inversion_clear H0.
        apply sat_F.  apply WF_dstate_eq with mu.
        intuition. intuition. 
        unfold dstate_eq in H.
        destruct mu as [mu IHmu]. 
          destruct mu' as [mu' IHmu'].
          simpl in H. simpl in H2. 
          simpl. rewrite<- H.  intuition.
Qed.


Lemma  sat_Pro_dstate_eq: forall s e (D:pro_formula) (mu mu': dstate s e),
dstate_eq mu mu'->
sat_Assert mu D-> sat_Assert mu' D.
Proof.  induction D; intros.  
        inversion_clear H0.
        unfold distribution_formula in H2.
        destruct H2. simpl in H2. rewrite sum_over_list_nil in H2.
        lra.
        inversion_clear H0. inversion_clear H3.
        destruct mu_n. destruct a. simpl in H0. inversion H0; subst. 
        econstructor. apply WF_dstate_eq with mu.
        assumption. assumption.
        assumption. 
        econstructor. 
        apply H0. 
        apply dstate_eq_trans with mu. apply dstate_eq_sym.
        assumption. assumption. 
        assumption. rewrite <-(d_trace_eq  mu _ H).
        apply H6. 
Qed.


Lemma  sat_Npro_dstate_eq: forall s e (D:npro_formula) (mu mu': dstate s e),
dstate_eq mu mu'->
sat_Assert mu D-> sat_Assert mu' D.
Proof. intros. induction D.  
        inversion_clear H0. destruct p_n. simpl in *.
        inversion_clear H2. inversion_clear H3.
        simpl in *. 
        rewrite sum_over_list_nil in H5. lra.
        discriminate H1.  
        inversion_clear H0.
        econstructor. apply H1. destruct p_n. discriminate H1.
        apply sat_Pro_dstate_eq with mu. 
        assumption. apply H2.
Qed.

(* Lemma sat_Assn_dstate_eq:
forall n (D:Assertion) (mu mu': dstate n) i a,
dstate_eq mu mu'->
sat_Assert mu (Assn_sub i a D) -> sat_Assert mu' ((Assn_sub i a D)). 
Proof. intros. inversion_clear H0. econstructor. 
      destruct mu as [mu IHmu].
      destruct mu' as [mu' IHmu'].
      unfold dstate_eq in *. unfold d_update_cstate in *.
      simpl in *.  

Qed. *)




Lemma  sat_Assert_dstate_eq: forall s e (D:Assertion) (mu mu': dstate s e),
dstate_eq mu mu'->
sat_Assert mu D-> sat_Assert mu' D.
Proof.  induction D;  intros;
        [apply sat_Pro_dstate_eq with mu|
        apply sat_Npro_dstate_eq with mu | ]; 
        intuition; intuition.
       inversion_clear H0.
       econstructor. 
        apply WF_dstate_eq with mu.
        assumption. assumption.
      destruct mu as [mu IHmu].
      destruct mu' as [mu' IHmu'].
      unfold dstate_eq in *. unfold d_update_cstate in *.
      simpl in *.  apply IHD with ({|
        StateMap.this := d_update_cstate_aux i a mu;
        StateMap.sorted :=
          d_update_cstate_sorted i a mu IHmu
      |}).
        simpl. rewrite H. reflexivity.
        assumption. 
Qed.

Lemma d_app_not_nil:
forall {s e : nat} (mu mu' : dstate s e),
StateMap.this mu <> [] \/ StateMap.this mu' <> [] ->
StateMap.this (d_app mu mu') <> [] .
Proof. intros s e(mu,IHmu) (mu',IHmu'). 
       simpl. intros. destruct H. apply map2_app_not_nil_l.
       intuition. 
       rewrite map2_comm.  
       apply map2_app_not_nil_l.
       intuition. 
Qed.


Lemma WF_big_and{s e:nat}: forall (mu_n : list (dstate s e)) nF,
(Forall_two (fun mu_i nF_i => sat_State mu_i nF_i) mu_n nF)->
Forall (fun x : dstate s e => WF_dstate x) mu_n.
Proof. induction mu_n; destruct nF; intros; inversion_clear H;
   try econstructor.
   apply WF_sat_State in H0. intuition.
   apply IHmu_n with nF.  intuition.
Qed.


(* 
Lemma big_dapp_nil1: forall {s e : nat} (pF:pro_formula)
 (f : list (dstate s e)) (mu':dstate s e),
 distribution_formula pF->
big_dapp' (get_pro_formula pF) f mu'->
StateMap.this mu' <> [].
Proof.  induction pF; intros.   
destruct H. rewrite sum_over_list_nil_formula in H1.
lra.
destruct pF. destruct H. rewrite sum_over_list_cons_formula in H1.
rewrite sum_over_list_nil_formula in H1.
rewrite  Rplus_0_r in H1. destruct a. simpl in *. rewrite H1 in *. 
inversion H0; subst. inversion H7; subst.
inversion H0; subst.
apply IHpF in H0.
destruct hd.  
apply d_app_not_nil.
left. inversion H4. lra. discriminate. simpl. 

assert(StateMap.this (d_app r0 d0)<>[]).
apply d_app_not_nil. left. inversion_clear H6.  
  
Qed. *)

Lemma big_and_not_nil{s e:nat}: forall (mu_n : list (dstate s e)) nF,
(Forall_two (fun mu_i nF_i => sat_State mu_i nF_i) mu_n nF)->
nF <> []->
exists i, (i<length nF)%nat /\ StateMap.this (nth i mu_n (d_empty s e)) <> [] .
Proof. induction mu_n; destruct nF; intros; 
        inversion_clear H.
        destruct H0. reflexivity.  
   
exists 0%nat. simpl in * . split. lia. 
apply WF_sat_State in H1. intuition.
Qed.




Lemma big_dapp_nil1: forall {s e : nat} (pF:pro_formula)
(f : list (dstate s e)) (mu':dstate s e),
(Forall (fun x => 0<= (x)) (get_pro_formula pF))->
0<sum_over_list ((get_pro_formula pF)) <=1->
(Forall_two (fun f_i nF_i => sat_State f_i nF_i) f (pro_to_npro_formula pF))->
big_dapp' (get_pro_formula pF) f mu'->
StateMap.this mu' <> [].
Proof.  induction pF; intros. simpl in *.
 rewrite sum_over_list_nil in H0.
lra.   

destruct f. destruct a.  simpl in *. inversion_clear H1. 
destruct a.  simpl in *.
inversion H2; subst. clear H2.
assert(r=0\/ r<>0). 
apply Classical_Prop.classic. 
destruct H2. simpl in *. rewrite sum_over_list_cons in H0.
rewrite H2 in *. simpl in H0. rewrite Rplus_0_l in H0. 
apply d_app_not_nil.
right. apply IHpF with f. inversion_clear H. assumption.
assumption. inversion_clear H1. assumption.
assumption.
apply d_app_not_nil.
left. inversion H8. lra.
apply d_scale_not_nil .  
rewrite sum_over_list_cons in H0.
simpl in *. inversion_clear H. 
simpl in *. split. lra.
assert((sum_over_list (get_pro_formula pF))>=0).
apply sum_over_list_ge_0. 
assumption.  lra.  inversion_clear H1.
 apply WF_sat_State in H7. intuition.
Qed.

       
Lemma WF_sat_Pro{s e:nat}: forall   (pF:pro_formula) (mu:dstate s e), 
sat_Assert mu pF-> StateMap.this mu <> [] /\ WF_dstate mu.
Proof.  intros. 
      inversion_clear H.  
      inversion_clear H2. split. 
      unfold dstate_eq in H3. rewrite H3.
     
      apply big_dapp_nil1 with pF mu_n.
      destruct H1. assumption. destruct H1. rewrite H2.
       lra. assumption. assumption.
      apply WF_dstate_eq with mu'. apply dstate_eq_sym.
      assumption. 
      apply WF_dstate_big_dapp with  (get_pro_formula pF) mu_n.
      apply WF_big_and with ((pro_to_npro_formula pF)).
      assumption.  assumption. inversion_clear H1. assumption.
      inversion_clear H1. intuition.
Qed.
       
Lemma WF_sat_Npro{s e:nat}: forall (nF:npro_formula)  (mu:dstate s e) , 
sat_Assert mu nF-> StateMap.this mu <> [] /\ WF_dstate mu.
Proof.  intros.  inversion_clear H. apply (WF_sat_Pro _ _ H1) .
Qed.

(* Lemma d_trace_add{n:nat}: forall c (q:qstate n) (mu:list (state n)),
d_trace_aux (StateMap.Raw.add c q mu)<=
s_trace (c,q)+ d_trace_aux mu.
Proof. intros. induction mu. simpl. lra.
       destruct a. 
       simpl. destruct (Cstate_as_OT.compare c c0).
       simpl. lra.
       simpl. admit.
       simpl.  admit.  
Admitted.


Lemma WF_dstate_add{n:nat}: forall c (q:qstate n) (mu:list (state n)),
WF_state (c,q)->
WF_dstate_aux mu->
s_trace (c,q) + d_trace_aux mu <=1->
WF_dstate_aux (StateMap.Raw.add c q mu) .
Proof. induction mu; intros.
       simpl. admit.
       destruct a.
       simpl. destruct (Cstate_as_OT.compare c c0).
       econstructor. assumption.
       assumption.  simpl. assumption.
       econstructor. assumption.
       inversion_clear H0. assumption.
       simpl.  simpl in H1. admit.
       econstructor. inversion_clear H0.
       assumption. 
       apply IHmu. assumption.
       inversion_clear H0. assumption.
       simpl in H1. admit.
       simpl in H1.
       simpl. apply Rle_trans with (s_trace (c0, q0) +s_trace (c, q) + d_trace_aux mu).
       admit. admit.
Admitted.

Lemma d_trace_update{n:nat}: forall  (mu:list (state n)) i a,
d_trace_aux (d_update_cstate_aux i a mu)<=
d_trace_aux mu.
Proof. induction mu; intros.
      simpl. lra. destruct a.
      simpl.  
      apply Rle_trans with (s_trace ((c_update i (aeval (c, q) a0) c), q) +d_trace_aux (d_update_cstate_aux i a0 mu)).
      apply d_trace_add.
      unfold s_trace. simpl.
Admitted. *)
(* Lemma Mixed_plus{n:nat}: forall (q q1 q2:Square n),
Mixed_State_aux q->
q= (q1.+q2)->
Mixed_State_aux q1 /\ Mixed_State_aux q2.
Proof. intros. induction H. 
admit. 
       
       
  
Qed. *)


Lemma WWF_d_update_cstate{s e:nat}: forall i a (mu:list (state s e)),
WWF_dstate_aux mu->
WWF_dstate_aux (d_update_cstate_aux i a mu).
Proof. induction mu; intros.
     simpl. apply WF_nil'.
     unfold d_update_cstate_aux.
     destruct a0. apply WWF_d_app_aux.
     inversion_clear H. 
     econstructor. assumption. econstructor.
      apply IHmu.
     inversion_clear H.
     assumption.
Qed.

Lemma d_trace_update{s e:nat}: forall  (mu:list (state s e)) i a,
WWF_dstate_aux mu->
d_trace_aux (d_update_cstate_aux i a mu)=
d_trace_aux mu.
Proof. induction mu; intros.
      simpl. lra. destruct a.
      unfold d_update_cstate_aux.
      rewrite d_trace_app_aux.
      simpl d_trace_aux.
      f_equal. unfold s_trace.
      simpl. rewrite Rplus_0_r. reflexivity.
      apply IHmu. inversion_clear H. 
      assumption.  
      econstructor.
      inversion_clear H. 
      econstructor.
      simpl. unfold WWF_state in H0. intuition.
      unfold WWF_state in H0. intuition.
       apply WF_nil'.
      apply WWF_d_update_cstate.
      inversion_clear H. assumption.
Qed.

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

Lemma WF_d_update_cstate{s e:nat}: forall i a (mu:list (state s e)),
WF_dstate_aux mu ->
WF_dstate_aux (d_update_cstate_aux i a mu).
Proof.  intros. 
       induction mu. simpl. assumption.
       destruct a0. 
       unfold d_update_cstate_aux.
        apply WF_d_app_aux.
        rewrite <-WF_state_dstate_aux.
        inversion_clear H. assumption. 
        apply IHmu.
       inversion_clear H. assumption.
       rewrite d_trace_app_aux.
       rewrite d_trace_update.
       inversion H; subst. 
       simpl in *. unfold s_trace in *.
       simpl in *. rewrite Rplus_0_r. assumption. 
       apply WWF_dstate_aux_to_WF_dstate_aux.
       inversion_clear H. assumption.
       apply WWF_dstate_aux_to_WF_dstate_aux.
       rewrite <-WF_state_dstate_aux. 
       inversion_clear H. assumption.
       apply WWF_d_update_cstate.
      
       apply WWF_dstate_aux_to_WF_dstate_aux.
       inversion_clear H. assumption.
Qed.



Lemma WF_sat_Assert{s e:nat}: forall  (D:Assertion) (mu:dstate s e), 
sat_Assert mu D -> StateMap.this mu <> [] /\ WF_dstate mu.
Proof.  induction D; intros. 
       apply (WF_sat_Pro _ _ H).
       apply (WF_sat_Npro _ _ H).
       inversion_clear H.
       apply IHD in H1.
       destruct mu as [mu IHmu].  
       unfold d_update_cstate in *.
       unfold WF_dstate in *.
       simpl in *.
       induction mu. simpl in *.
       destruct H1. destruct H. reflexivity.
       split. discriminate. 
       assumption.    
Qed.





Require Import Classical_Prop.
  Lemma Mplus_not_0: forall (m n:nat) (A B:Matrix m n), A .+ B <> Zero -> (A <> Zero \/ B <> Zero).
  Proof. unfold not. intros. assert(A=Zero \/ A<>Zero).
         apply classic. destruct H0. right.
      intros.  rewrite H0 in H. rewrite H1 in H.
      destruct H. apply Mplus_0_l. 
      left. intuition.  
  Qed.
  

  Lemma d_app_mu_nil: forall (s e : nat) (mu mu': dstate s e),
  StateMap.this mu'= []->
  StateMap.this (d_app mu mu') = StateMap.this mu .
  Proof. intros s e (mu, IHmu) (mu', IHmu').
         induction mu. simpl. rewrite map2_r_refl.
         intuition. 
         simpl. intros. rewrite H. destruct a.
          simpl. rewrite map2_l_refl.
          reflexivity.
    
  Qed.
  
  
  Lemma  Rplus_le_1:forall (r1 r2:R), r1>0->r1+r2<=1 ->r2<=1 .
  Proof. intros. lra.
  Qed.


  Lemma map2_scale_not_nil: forall s e(p:R) (mu :list (cstate * qstate s e)),
  mu<>nil -> (p>0)->
  StateMap.Raw.map (fun x : qstate s e =>@scale (2^(e-s)) (2^(e-s)) p x)
    mu <> [].
  Proof. intros. induction mu. destruct H. reflexivity.
          destruct a. simpl. discriminate.
  Qed.


  (* Definition id_state : state 1:= ([0]%nat, I 2) .
  
  Lemma  WF_id_state: WF_state  id_state  .
  Proof. Admitted.
   *)

Notation " c *l d" := (StateMap.Raw.map (fun x => c .* x) d)
  (at  level 80, no associativity)
  : scope.