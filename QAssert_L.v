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
Require Import Basic_Supplement.


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

Fixpoint big_Oplus  (g : nat -> State_formula) (n_0 : nat) : npro_formula := 
match n_0 with
| 0 => []
| S n' =>(big_Oplus g n') ++ [(g n')]  
end.


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
    |SOdot F1 F2=>  (NSet.union (fst (Free_state F1)) (fst(Free_state F2)), NSet.union (snd (Free_state F1))  (snd (Free_state F2)))
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

Inductive q_combin{s0 e0 s1 e1 s2 e2}: (qstate s0 e0) -> (qstate s1 e1)-> (qstate s2 e2)->Prop:=
|combin_l: forall q0 q1, e0 = s1-> s0 = s2 -> e1 = e2 ->
             q_combin q0 q1 (@kron (2^(e0-s0)) (2^(e0-s0)) (2^(e1-s1))  
             (2^(e1-s1)) q0 q1)
|combin_r: forall q0 q1, e1 = s0-> s1= s2 -> e0 =e2 ->
             q_combin q0 q1 (@kron  (2^(e1-s1))  
            (2^(e1-s1)) (2^(e0-s0)) (2^(e0-s0)) q1 q0).


Lemma WF_qcombin{s0 e0 s1 e1 s2 e2:nat}: forall (q0: qstate s0 e0) (q1:qstate s1 e1)
(q2: qstate s2 e2),
WF_qstate q0-> WF_qstate q1-> q_combin q0 q1 q2->
WF_qstate q2 .
Proof. intros. 
inversion_clear H1; subst; apply WF_qstate_kron; try assumption.
Qed.

Lemma s_combin_com{s0 e0 s1 e1 s2 e2:nat}: forall (q0: qstate s0 e0) (q1:qstate s1 e1)
(q2: qstate s2 e2),
q_combin q0 q1 q2->q_combin q1 q0 q2.
 Proof. intros. 
       inversion_clear H. 
       apply combin_r.
       intuition. intuition. intuition. 
      apply combin_l.
       intuition. intuition. intuition.
Qed.

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

Lemma  s_combin_assoc{s0 e0 s1 e1 s2 e2 s_x e_x sy ey:nat}: forall (q0: qstate s0 e0) (q1:qstate s1 e1)
(q2: qstate s2 e2) (x: qstate s_x e_x) (y: qstate sy ey),
WF_qstate q0 -> WF_qstate x-> WF_qstate y ->
 q_combin q0 q1 q2->
 q_combin x y q1->
 exists (sz ez : nat) (z:qstate sz ez),
 q_combin q0 x z /\ q_combin z y q2.
Proof. intros. inversion H2; subst; inversion H3; subst.

       exists s2. exists sy.
       exists (@kron  (2^(s1-s2)) (2^(s1-s2))
       (2^(sy-s1)) (2^(sy-s1)) q0 x ).
       split. apply combin_l; try intuition.
       assert((2 ^ (sy - s1) * 2 ^ (e2 - sy))= 2^(e2-s1))%nat.
       admit. destruct H4. 
       assert(@kron (2^(s1-s2)) (2^(s1-s2)) (2 ^ (sy - s1) * 2 ^ (e2 - sy))
       (2 ^ (sy - s1) * 2 ^ (e2 - sy))
       (q0) (x ⊗ y) =@kron (2 ^ (s1 - s2) * 2 ^ (sy - s1))
       (2 ^ (s1 - s2) * 2 ^ (sy - s1)) (2 ^ (e2 - sy))
       (2 ^ (e2 - sy)) ((q0 ⊗ x))  (y)). 
        rewrite<- kron_assoc. reflexivity.  apply WF_Mixed. apply H.
         apply WF_Mixed. apply H0.   apply WF_Mixed. apply H1. 
      rewrite H4. 
       eapply (@combin_l s2 sy); reflexivity. 
Admitted.

Local Open Scope nat_scope.
Fixpoint QExp_eval{s' e':nat} (qs: QExp) (st: state s' e'){struct qs} :Prop:=
  match qs with 
  |QExp_s s e v=>s'<=s /\ s<=e /\e<=e' /\ ((PMpar_trace (@scale (2^(e'-s')) (2^(e'-s')) (R1 / (Cmod (@trace (2^(e'-s')) (snd st))))%R  (snd st)) (s-s') (e'-e) = outer_product v v))
  |QExp_t qs1 qs2=>exists (s0 e0 s1 e1:nat) (q1: qstate s0 e0) (q2:qstate s1 e1), 
                   q_combin q1 q2 (snd st)/\ QExp_eval qs1 (fst st, q1) /\ QExp_eval qs2 (fst st, q2)
end.

Fixpoint State_eval{s e:nat} (sf:State_formula) (st:state s e): Prop:=
match sf with 
|SPure P => Pure_eval P st
|SQuan s=> QExp_eval s st
|SOdot F1 F2=> 
exists (s0 e0 s1 e1:nat) (q1: qstate s0 e0) (q2:qstate s1 e1), 
q_combin q1 q2 (snd st) /\ State_eval F1 (fst st, q1) /\ State_eval F2 (fst st, q2)
|SAnd F1 F2 => State_eval F1 st /\ State_eval F2 st
(* |SNot F => ~(State_eval F st) *)
end.


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

                   
Fixpoint big_and{s e:nat} (f : list (dstate s e)) (g: list (State_formula )) : Prop := 
   match f , g with 
           |[], [] =>True 
           |[], _ =>False
           | _ ,[]=>False
           | hf:: tf , hg::tg=> (sat_State hf hg) /\ (big_and  tf tg)
   end.

Fixpoint big_Sand (g: nat->  (State_formula )) (n : nat) : State_formula := 
match n with
| 0 => BTrue
| S n' => g n' /\ big_Sand g n'
end. 

Fixpoint big_dapp{s e:nat} (g:list R) (f:list (dstate s e))  : dstate s e := 
   match g ,f with 
   |[], [] => d_empty s e
   |[], _ => d_empty s e
   | _ ,[]=>  d_empty s e 
   | hg::tg, hf:: tf =>d_app (d_scale_not_0 hg hf) (big_dapp tg tf)
   end.

Inductive big_dapp'{s e:nat} :list R -> list (dstate s e) -> dstate s e -> Prop :=
|big_app_nil: big_dapp' nil nil (d_empty s e)
|big_app_cons: forall hr hd tr td r d, d_scale hr hd r-> (big_dapp' tr td d)
               ->big_dapp' (hr::tr) (hd::td) (d_app r d).

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


(* Inductive Pro_eval{n:nat}:(list (cstate * qstate n)) -> pro_formula -> Prop:=
|pro_eval: forall (mu mu':list (cstate * qstate n) n) pF (mu_n: list (list (cstate * qstate n))),
big_dapp' (get_pro_formula pF) mu_n mu'
->dstate_eq mu mu'
-> (big_and mu_n (pro_to_npro_formula pF)) 
-> Forall (fun mu_i => d_trace  mu_i =d_trace mu) mu_n
-> sat_Pro mu pF.
       *)


Inductive sat_Pro {s e:nat}: (dstate s e)-> (pro_formula)-> Prop:=
|sat_pro: forall (mu mu':dstate s e) pF (mu_n: list (dstate s e)),
                          big_dapp' (get_pro_formula pF) mu_n mu'
                          ->dstate_eq mu mu'
                          -> (big_and mu_n (pro_to_npro_formula pF)) 
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
                    -> sat_Assert mu (npro_to_pro_formula nF p_n)
                    ->sat_Assert mu (ANpro nF)
|sat_Assn: forall (mu:dstate s e) i a D, 
                      sat_Assert (d_update_cstate i a mu) D
                   -> sat_Assert mu (Assn_sub i a D).

Lemma  big_dapp_nil{s e:nat}: forall g (f:list (dstate s e)),
g=[]\/f=[]-> dstate_eq (big_dapp g f ) (d_empty s e) .
Proof. intros. destruct H. simpl. destruct g; destruct f.
    simpl. unfold dstate_eq ;try reflexivity.
    simpl. unfold dstate_eq ;try reflexivity. 
    discriminate H. discriminate H. 
    simpl. destruct g; destruct f.
    simpl. unfold dstate_eq ;try reflexivity.
    discriminate H.
    simpl. unfold dstate_eq ;try reflexivity. 
    discriminate H. 
Qed.

Lemma  big_dapp_nil'{s e:nat}: forall g (f:list (dstate s e)) (d:dstate s e),
  g=[]\/f=[]-> big_dapp' g f d -> dstate_eq d (d_empty s e) . 
  Proof.  intros. inversion H0;subst.  apply dstate_eq_refl.
  destruct H;
  discriminate H.
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


Lemma get_pro_formula_length: forall pF, 
length (get_pro_formula pF) = length pF .
Proof. induction pF. simpl. reflexivity. destruct a. simpl.
     f_equal. apply IHpF. 
Qed.

Lemma pro_to_npro_formula_length: forall pF, 
length (pro_to_npro_formula  pF) = length pF .
Proof. induction pF. simpl. reflexivity. destruct a. simpl.
     f_equal. apply IHpF. 
  
Qed.

Lemma npro_to_pro_formula_length: forall pF p_n, 
length pF= length p_n->
length (npro_to_pro_formula  pF p_n) = length pF .
Proof. induction pF. destruct p_n. simpl. reflexivity. intros.
        discriminate H. destruct p_n; intros. discriminate H.
      simpl. f_equal. apply IHpF.
       injection H. intuition.
Qed.



Lemma  get_pro_formula_eq: forall nF1 nF2 p_n,
length nF1 =length p_n ->
length nF2 =length p_n->
(get_pro_formula (npro_to_pro_formula nF2 p_n))=
(get_pro_formula (npro_to_pro_formula nF1 p_n)) .
Proof. induction nF1; induction nF2; intros.
       simpl. reflexivity.
       rewrite<-H in H0. discriminate H0.
       rewrite <-H0 in H. discriminate H.
       destruct p_n.
       simpl. reflexivity.
       simpl. f_equal. apply IHnF1. 
       injection H. intuition.
       injection H0. intuition. 
Qed.

Lemma  pro_npro_inv:forall nF p_n,
length nF =length p_n->
(pro_to_npro_formula (npro_to_pro_formula nF p_n))= nF .
Proof. induction nF; intros.
       destruct p_n.
       simpl. reflexivity.
       discriminate H.
       destruct p_n.
       simpl. discriminate H.
       simpl. f_equal. apply IHnF.
       injection H. intuition.  
Qed.

Lemma seman_eq: forall s e (mu mu':dstate s e) (F:State_formula),
dstate_eq mu mu'->
sat_State  mu F-> sat_State  mu' F.
Proof. intros s e(mu, IHmu1) (mu', IHmu'). unfold dstate_eq. simpl. intros.
      inversion_clear H0. econstructor.
       apply WF_dstate_eq with (StateMap.Build_slist IHmu1).
       unfold dstate_eq. simpl. assumption. assumption.
      simpl in *. rewrite <-H. assumption.
Qed.

Lemma sat_Assert_to_State: forall s e (mu:dstate s e) (F:State_formula),
sat_Assert mu F <-> sat_State mu F.
Proof. split; intros. 
inversion_clear H. destruct p_n. inversion_clear H0.
destruct p_n. 
inversion_clear H1. inversion_clear H3.
simpl in *.  destruct mu_n. 
inversion_clear H1.
unfold distribution_formula in H2. 
destruct H2. rewrite sum_over_list_cons_formula in H3.
simpl in H3. rewrite sum_over_list_nil_formula in H3.
rewrite Rplus_0_r in H3. rewrite H3 in H1.
inversion H1; subst; inversion H13; subst. 
simpl in *.   
assert(dstate_eq mu d). 
apply (dstate_eq_trans _ _ _ _ _ H4).
apply dstate_eq_trans with ((d_app d (d_empty s e))).
apply d_app_eq. apply d_scale_1_l. assumption. 
apply dstate_eq_refl.
apply dstate_eq_trans with ((d_app (d_empty s e) d)).
apply d_app_comm.  apply d_app_empty_l.
apply seman_eq with d. apply dstate_eq_sym.
assumption. intuition.
discriminate H0.

econstructor. assert(length [1] = length [F]). reflexivity.
apply H0.  econstructor.
inversion_clear H. intuition.
simpl. unfold distribution_formula. 
intuition. rewrite sum_over_list_cons_formula.
simpl. rewrite sum_over_list_nil_formula. lra.
simpl. assert( exists mu', d_scale 1 mu mu').
apply d_scale_exsits. destruct H0.
assert(big_dapp' [1]
[mu] (d_app x (d_empty s e))). apply big_app_cons.
assumption. apply big_app_nil.
econstructor.  simpl. apply H1.
apply dstate_eq_trans with ((d_app mu (d_empty s e))).
apply dstate_eq_trans with ((d_app (d_empty s e) mu)).
apply dstate_eq_sym. apply d_app_empty_l.
apply d_app_comm. simpl. 
apply d_app_eq. apply dstate_eq_sym.
apply d_scale_1_l. assumption. apply dstate_eq_refl.
simpl. intuition. 
econstructor. reflexivity. apply Forall_nil. 
Qed.


Lemma sum_over_list_formula_npro_to_pro: forall nF1 nF2 p_n,
length nF1 = length p_n ->
length nF2= length p_n->
sum_over_list_formula  (npro_to_pro_formula nF1 p_n) =
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

Require Import ParDensityO.
Lemma WF_d_app'{s e:nat}: forall (mu mu':dstate s e) (p1 p2:R),
(0<p1<=1/\0<p2<=1)-> (p1+p2<=1)->
WF_dstate mu -> WF_dstate mu'-> 
@WF_dstate s e (d_app (d_scale_not_0 p1 mu) (d_scale_not_0 p2 mu')).
Proof. unfold WF_dstate. unfold d_app. unfold d_trace.
 unfold StateMap.map2.
 intros  (mu, IHmu) (mu', IHmu') p1 p2. simpl. 
 intros. 
 apply WF_d_app_aux. 
 apply WF_d_scale_aux. intuition. intuition.
 apply WF_d_scale_aux. intuition. intuition.
 rewrite d_trace_app_aux.  repeat rewrite d_trace_scale_aux.
 apply Rplus_mult_le_1'. intuition. intuition. intuition.
 apply WF_dstate_in01_aux. assumption. 
 apply WF_dstate_in01_aux. assumption.
 intuition. intuition. 
 apply WWF_d_scale_aux. intuition.
 apply WWF_dstate_aux_to_WF_dstate_aux.
  intuition.
 apply WWF_d_scale_aux. intuition. 
 apply WWF_dstate_aux_to_WF_dstate_aux.
 intuition.
Qed.

Local Open Scope bool_scope.
Lemma bexp_Pure_eq{s e:nat}:  forall (st st':state s e ) (b:bexp) , 
((beval st b) = beval st' b) -> (State_eval b st)<->(State_eval b st').
Proof.  simpl.  intros. destruct (beval st b).
       rewrite <-H. reflexivity. rewrite <-H.
       reflexivity. 
Qed.

Lemma state_eq_Pure{s e:nat}: forall (P:Pure_formula) (st st':state s e) ,
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
Proof.   induction qs; intros. 
simpl. 
simpl in H0.
rewrite <-H.
assumption.
destruct H0.
destruct H0.
destruct H0.
destruct H0.
destruct H0.
destruct H0.
simpl. exists x.
exists x0. exists x1. exists x2.
exists x3. exists x4.  split.
rewrite  <-H. intuition.
split. apply IHqs1 with (fst st, x3).
reflexivity. intuition.
apply IHqs2 with (fst st, x4).
reflexivity. intuition. 
Qed.




Local Open Scope R_scope.
Lemma Mscale_not_0':forall (m n:nat) (A:Matrix m n) (p: R), 
p.* A <> Zero -> A<>Zero .
Proof. unfold not.  intros.  rewrite H0 in H.  rewrite Mscale_0_r in H.
intuition. 
Qed.


Local Open Scope C_scope.
Lemma s_seman_scale_Qexp: forall  (qs:QExp) (p:R)  (s e:nat) (st:state s e),
0<p-> 
(QExp_eval qs st <-> QExp_eval qs (s_scale p st)).
Proof. induction qs; intros; destruct st.
      simpl.
      repeat rewrite trace_mult_dist.
      repeat rewrite Rdiv_unfold.
      repeat rewrite Mscale_assoc.
      repeat rewrite Cmod_mult.
      repeat rewrite Rinv_mult.
      repeat rewrite Rmult_1_l.
       rewrite Cmod_R.
       rewrite Rabs_right.   
      rewrite Cmult_comm with (y:=(RtoC p)).
      rewrite RtoC_mult. 
      rewrite <-Rmult_assoc. 
      rewrite Rinv_r. rewrite Rmult_1_l. intuition.
      lra. lra.

      split;
      simpl; intros; destruct H0;
      destruct H0; destruct H0;
      destruct H0; destruct H0;
      destruct H0;
      exists x; exists x0;
      exists x1; exists x2.
      exists (sqrt p .*  x3).
      exists (sqrt p .*  x4).
      split. admit.
      split. assert((c, √ p .* x3)= s_scale (√ p) (c, x3) ).
      unfold s_scale. reflexivity.
      unfold qstate. 
      rewrite H1. 
      apply IHqs1. admit. intuition. 
      assert((c, √ p .* x4)= s_scale (√ p) (c, x4) ).
      unfold s_scale. reflexivity.
      unfold qstate. 
      rewrite H1. 
      apply IHqs2. admit. intuition. 




      exists ((1/sqrt p)%R .*  x3).
      exists ((1/sqrt p)%R .*  x4).
      split. admit.
      split. assert((c, (1/√ p)%R .* x3)= s_scale (1/√ p) (c, x3) ).
      unfold s_scale. reflexivity.
      unfold qstate. 
      rewrite H1. 
      apply IHqs1. admit. intuition. 
      assert((c, (1/√ p)%R .* x4)= s_scale (1/√ p) (c, x4) ).
      unfold s_scale. reflexivity.
      unfold qstate. 
      rewrite H1. 
      apply IHqs2. admit. intuition. 
Admitted.


Local Open Scope R_scope.
Lemma s_seman_scale: forall (F:State_formula) (p:R) s e  (st:state s e),
0<p->
(State_eval F st <-> State_eval F (s_scale p st)).
Proof.  induction F. 
-- intros. split. apply (state_eq_Pure  P st (s_scale p st)) . simpl. reflexivity.
                  apply (state_eq_Pure  P (s_scale p st) st ) . simpl. reflexivity.
-- intros. apply s_seman_scale_Qexp. assumption.
-- admit.  
-- split; simpl; intros; destruct H0;
split; try apply (IHF1 p n st); try assumption;
try apply (IHF2 p n st); try assumption.
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
Admitted.

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
@State_eval s e F (c, q .+ q0).
Proof.  
       induction F. intros;  intros.
      -apply state_eq_Pure with  (c, q0). 
       reflexivity. intuition.   
      -induction qs; intros. simpl in *.
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
          destruct H1. destruct H5. 
          destruct H6. destruct H2.
          destruct H8. destruct H9.
          split. intuition. split. intuition.
          split. intuition.
          rewrite H7.
          rewrite <-PMtrace_scale. 
          rewrite Rdiv_unfold. rewrite H10.
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
         lia. lia.
         
         simpl in *.  admit.

      -simpl in *. admit.
      - simpl in *.  split. intuition. intuition. 
Admitted.



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
        destruct H2. rewrite sum_over_list_nil_formula in H2.
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
        rewrite sum_over_list_nil_formula in H5. lra.
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
        econstructor. inversion_clear H0.
      destruct mu as [mu IHmu].
      destruct mu' as [mu' IHmu'].
      unfold dstate_eq in *. unfold d_update_cstate in *.
      simpl in *. apply IHD with ({|
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

Lemma WWF_dstate_to_WF_dstate:forall {s e : nat} (mu : dstate s e),
WWF_dstate mu /\ d_trace mu <= 1 <-> WF_dstate mu .
Proof. intros s e(mu, IHmu). unfold WWF_dstate.
      unfold WF_dstate. unfold d_trace. simpl.
      apply WWF_dstate_aux_to_WF_dstate_aux.
  
Qed.

Lemma WWF_dstate_empty: forall s e, WWF_dstate (d_empty s e) .
Proof. intros. unfold d_empty.  unfold WWF_dstate.
 simpl. unfold StateMap.Raw.empty.
apply WF_nil'. 
Qed.

Lemma WWF_d_app{s e:nat}: forall (mu mu':dstate s e),
WWF_dstate mu -> WWF_dstate mu'->
WWF_dstate  (d_app mu mu').
Proof. unfold WF_dstate. unfold d_app. unfold d_trace. unfold StateMap.map2. 
 intros  (mu, IHmu) (mu', IHmu') p1 p2. simpl.
 apply WWF_d_app_aux. assumption. assumption. 
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
        apply WWF_d_scale_aux. intuition.
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


Lemma WWF_dstate_big_dapp{s e:nat}: forall (pF:pro_formula) (mu_n:list (dstate s e)) (mu:dstate s e), 
Forall (fun x=> WWF_dstate x) mu_n ->
big_dapp' (get_pro_formula pF) mu_n mu->
(Forall (fun x => 0<=fst (x) ) pF)->
WWF_dstate mu.
Proof. induction pF. intros. inversion_clear H0.
    apply WWF_dstate_empty.
    intros. destruct a. simpl in *.
    inversion H0; subst. 
    apply WWF_d_app.  
    apply WWF_d_scale with  hd r. 
    inversion_clear H1. intuition.
    assumption. inversion_clear H.
    assumption. apply IHpF with td.
      inversion_clear H. assumption.
     assumption. inversion_clear H1. assumption.
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

Lemma  Forall_WWF_WF{s e:nat}: forall (mu_n:list (dstate s e)),
Forall (fun x : dstate s e => WF_dstate x) mu_n->
Forall (fun x : dstate s e => WWF_dstate x) mu_n .
Proof. induction mu_n.  intros;
      apply Forall_nil.
       intros. inversion_clear H.
      econstructor. apply WWF_dstate_to_WF_dstate.
      assumption. apply IHmu_n. assumption.
Qed.



Lemma d_trace_le_1_big_dapp{s e:nat}: forall (pF:pro_formula) (mu_n:list (dstate s e)) (mu:dstate s e), 
Forall (fun x=> WF_dstate x) mu_n ->
big_dapp' (get_pro_formula pF) mu_n mu->
(Forall (fun x =>0<= fst (x) ) pF)->
d_trace mu <= sum_over_list_formula pF.
Proof. induction pF. intros. inversion_clear H0.
        rewrite sum_over_list_nil_formula.
        unfold d_trace. unfold StateMap.this.
        simpl. lra. 
        intros. destruct a. simpl in *.
         inversion H0; subst.
         rewrite d_trace_app.
         rewrite sum_over_list_cons_formula.
         apply Rplus_le_compat.
          apply d_scale_trace_le with hd.
          inversion_clear H1. assumption.
           inversion_clear H.
          assumption. simpl. assumption.
         apply IHpF with td. inversion_clear H.
         assumption. assumption.
         inversion_clear H1. assumption.
         apply WWF_d_scale with  hd r. 
         inversion_clear H1. intuition.
         assumption. inversion_clear H.
         apply WWF_dstate_to_WF_dstate. assumption.
         apply WWF_dstate_big_dapp with pF td.
        apply Forall_WWF_WF. inversion_clear H. assumption.
          assumption. inversion_clear H1. assumption.
Qed.


Lemma WF_dstate_big_dapp{s e:nat}: forall (pF:pro_formula) (mu_n:list (dstate s e)) (mu:dstate s e), 
Forall (fun x=> WF_dstate x) mu_n ->
big_dapp' (get_pro_formula pF) mu_n mu->
(Forall (fun x => 0<=fst (x)) pF)->
sum_over_list_formula pF <=1->
WF_dstate mu.
Proof. intros. apply WWF_dstate_to_WF_dstate.
split. apply WWF_dstate_big_dapp with pF mu_n .
apply Forall_WWF_WF.  assumption. assumption. assumption.
apply Rle_trans with (sum_over_list_formula pF).
apply d_trace_le_1_big_dapp with mu_n. 
assumption. assumption. assumption.
assumption.
Qed.

Lemma WF_big_and{s e:nat}: forall (mu_n : list (dstate s e)) nF,
big_and mu_n nF->
Forall (fun x : dstate s e => WF_dstate x) mu_n.
Proof. induction mu_n; destruct nF.
   simpl. intros. apply Forall_nil.
   intros. simpl in *. destruct H.
   intros. simpl in *. destruct H.
   intros. econstructor. simpl in H.
   destruct H.
   apply WF_sat_State in H. intuition.
   apply IHmu_n with nF. simpl in H. intuition.
Qed.

(* Lemma big_dapp_nil1: forall {n : nat} (g : list R) (f : list (dstate n)) (mu':dstate n),
big_dapp' g f mu'->
StateMap.this mu'=[] -> (f =[]) \/ (g=[]).
Proof. intros. destruct g.  right. reflexivity.
destruct f. left. reflexivity. 
inversion H; subst. 
assert(StateMap.this (d_app r0 d0)<>[]).
apply d_app_not_nil. left. inversion_clear H6.  
  
Qed. *)

       
Lemma WF_sat_Pro{s e:nat}: forall   (pF:pro_formula) (mu:dstate s e), 
sat_Assert mu pF-> StateMap.this mu <> [] /\ WF_dstate mu.
Proof.  intros. 
      inversion_clear H.  
      inversion_clear H2. split. 
      unfold dstate_eq in H3. rewrite H3.
      
      admit. 
      apply WF_dstate_eq with mu'. apply dstate_eq_sym.
      assumption. 
      apply WF_dstate_big_dapp with  pF mu_n.
      apply WF_big_and with ((pro_to_npro_formula pF)).
      assumption.  assumption. inversion_clear H1. assumption.
      inversion_clear H1. intuition.
Admitted.
       
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

Lemma WWF_d_update_cstate{s e:nat}: forall i a (mu:list (state s e)),
WWF_dstate_aux mu<->
WWF_dstate_aux (d_update_cstate_aux i a mu).
Proof. split. induction mu; intros.
     simpl. apply WF_nil'.
     unfold d_update_cstate_aux.
     destruct a0. apply WWF_d_app_aux.
     admit. apply IHmu.
     inversion_clear H.
     assumption.
     induction mu; intros.
     simpl. apply WF_nil'.
     unfold d_update_cstate_aux in H.
     destruct a0. 
     econstructor.
Admitted.

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
      admit. apply WF_nil'.
      apply WWF_d_update_cstate.
      inversion_clear H. assumption.
Admitted.


Lemma WF_d_update_cstate{s e:nat}: forall i a (mu:list (state s e)),
WF_dstate_aux mu<->
WF_dstate_aux (d_update_cstate_aux i a mu).
Proof. split; intros. 
       induction mu. simpl. assumption.
       destruct a0. 
       unfold d_update_cstate_aux.
        apply WF_d_app_aux.
       admit. apply IHmu.
       inversion_clear H. assumption.
       rewrite d_trace_app_aux.
       rewrite d_trace_update. 
       admit. admit.
       admit. 
       apply WWF_d_update_cstate.
       admit.
       


       induction mu. simpl. assumption.
       destruct a0.

       unfold d_update_cstate_aux in H.
      econstructor.
Admitted.



Lemma WF_sat_Assert{s e:nat}: forall  (D:Assertion) (mu:dstate s e), 
sat_Assert  mu D-> StateMap.this mu <> [] /\ WF_dstate mu.
Proof.  induction D; intros. 
       apply (WF_sat_Pro _ _ H).
       apply (WF_sat_Npro _ _ H).
       inversion_clear H.
       apply IHD in H0.
       destruct mu as [mu IHmu].  
       unfold d_update_cstate in *.
       unfold WF_dstate in *.
       simpl in *.
       induction mu. simpl in *.
       destruct H0. destruct H. reflexivity.
       split. discriminate.
       destruct H0. destruct a0.
       apply WF_d_update_cstate in H0.
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