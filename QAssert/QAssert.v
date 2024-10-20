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
From Quan Require Import QState.
Require Import Par_trace.


(*-------------------------------Synatx------------------------------------*)

Inductive Pure_formula:Type:=
|PBexp (b:bexp) 
|PUniver (i: nat) (P: Pure_formula)
|PExists (i:nat) ( P:  Pure_formula)
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

Fixpoint npro_to_pro_formula (nF:npro_formula ) (p_n: list R): pro_formula:=
  match nF, p_n with 
  |[], [] =>[]
  |[], _ => []
  |_, [] => []
  |F :: nF', h::p' => (h, F):: (npro_to_pro_formula nF' p')
  end.

Definition distribution_formula (pF: pro_formula) := 
  and (Forall (fun x => 0 <= x) (get_pro_formula pF))  (sum_over_list (get_pro_formula pF) = 1).
  
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
Bind Scope assert_scope with pro_formula.
Bind Scope assert_scope with Assertion.
Delimit Scope assert_scope with npro_formula.
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
(*----------------------------------FreeV--------------------------------------*)
Local Open Scope assert_scope.
Import QIMP_L.
Fixpoint Free_pure (P: Pure_formula ): CSet :=
  match P with
      | PBexp b=> Free_bexp b
      | PUniver a P0 => NSet.remove a (Free_pure (P0))
      | PExists a P0 => NSet.remove a  (Free_pure (P0))
      | Assn_sub_P i a P0 =>NSet.remove i (NSet.union (Free_pure P0) (Free_aexp a))
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
 |PUniver i P=> forall a:nat, Pure_eval P (s_update_cstate i a st)
 |PExists i P=> exists a:nat, Pure_eval P (s_update_cstate i a st)
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
  |_=> Forall (fun x=> State_eval F x) mu
  end. 

Local Open Scope R_scope.
From Quan Require Import Forall_two.
Inductive sat_State {s e:nat}:(dstate s e) -> (State_formula)-> Prop:=
|sat_F: forall (mu:dstate s e) F,  WF_dstate mu 
                                   -> State_eval_dstate F (StateMap.this mu)
                                   ->sat_State mu F.

Inductive sat_Pro {s e:nat}: (dstate s e)-> (pro_formula)-> Prop:=
|sat_pro: forall (mu mu':dstate s e) pF (mu_n: list (dstate s e)),
                            big_dapp (get_pro_formula pF) mu_n mu'
                            -> dstate_eq mu mu'
                            -> (Forall_two (fun mu_i nF_i => sat_State mu_i nF_i) mu_n (pro_to_npro_formula pF)) 
                            -> Forall (fun mu_i => d_trace  mu_i =d_trace mu) mu_n
                            -> sat_Pro mu pF.

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


(*--------------------------------------------------------------*)
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

Lemma pro_npro_swap: forall pF,
(npro_to_pro_formula (pro_to_npro_formula pF) (get_pro_formula pF))=
pF.
Proof. intros. induction pF.
       simpl. reflexivity. 
        destruct a.
        simpl.  f_equal. intuition. 
Qed.

Lemma  get_pro_formula_p_n: forall nF p_n,
length nF =length p_n ->
(get_pro_formula (npro_to_pro_formula nF p_n))=
p_n. 
Proof. induction nF; destruct p_n; simpl; intros; try reflexivity.
    discriminate H. f_equal. apply IHnF. injection H. intuition.
Qed.


Lemma  get_pro_app: forall (pF1 pF2:pro_formula),
get_pro_formula (pF1 ++pF2)= get_pro_formula pF1 ++ get_pro_formula pF2.
Proof. induction pF1. simpl. intuition.
       destruct a.
     simpl. intros. f_equal. intuition. 
Qed.

Lemma  pro_to_npro_formula_app: forall (pF1 pF2:pro_formula),
pro_to_npro_formula (pF1 ++pF2)= pro_to_npro_formula pF1 ++ pro_to_npro_formula pF2.
Proof. induction pF1. simpl. intuition.
destruct a.
   simpl. intros. f_equal. intuition. 
Qed.

Lemma sum_over_list_app : forall x l,
  sum_over_list (x ++ l) = (sum_over_list x + sum_over_list l)%R.
Proof. induction x; intros. simpl. rewrite sum_over_list_nil.
    rewrite Rplus_0_l. reflexivity.
    simpl. repeat  rewrite sum_over_list_cons.
    rewrite IHx. rewrite Rplus_assoc. reflexivity.
Qed.  

Lemma  big_pOplus_exsist: forall n (f:nat-> R) (g:nat->State_formula),
exists pF, big_pOplus' f g  n pF.
Proof. induction n; intros. exists [].
       econstructor. pose (IHn f g).
       destruct e. 
       destruct (Req_dec (f n) 0 ).
       exists x. econstructor. assumption.
       assumption.
       exists (x ++ [(f n, g n)]).
       apply big_pOplus_cons . assumption.
       assumption.
Qed.

Lemma big_pOplus_length: forall  (f : nat -> R) (g : nat -> State_formula) (n_0 : nat),
length (big_pOplus f g n_0) = n_0.
Proof. induction n_0. simpl. reflexivity.
       simpl. rewrite app_length. rewrite IHn_0. 
       simpl. intuition.
 
Qed.

                                               
Lemma  Forall_big_pOplus: forall (f1:nat-> R) f2 n0,
(forall i, (0 <= f1 i)%R)-> 
Forall (fun x0 : R  => (0 <= x0)%R) (get_pro_formula (big_pOplus f1 f2 n0)) .
Proof. intros.  induction n0. simpl. apply Forall_nil.
    simpl. rewrite get_pro_app.  apply Forall_app. split. assumption.
    econstructor. simpl. apply  H. apply Forall_nil.
Qed.

Lemma  Forall_big_pOplus': forall n0  (f1:nat-> R) f2  pF,
(forall i, (0 <= f1 i)%R)-> 
(big_pOplus' f1 f2 n0 pF )->
Forall (fun x0 : R  => (0 <= x0)%R) (get_pro_formula pF).
Proof.  induction n0; intros;
     inversion_clear H0.
     apply Forall_nil. 
     apply IHn0 with f1 f2; try assumption. rewrite get_pro_app.
     apply Forall_app. split. apply IHn0 with f1 f2; try assumption.
    econstructor. simpl. apply  H. apply Forall_nil.
Qed.
  

Lemma  sum_over_list_big_pOplus: forall (f1:nat-> R) f2 n0,
sum_over_list (get_pro_formula (big_pOplus  f1 f2 n0))=
big_sum f1 n0.
Proof. intros. induction n0. simpl. rewrite sum_over_list_nil.
    reflexivity.
    simpl. rewrite get_pro_app. rewrite sum_over_list_app. 
    f_equal. assumption. simpl. rewrite sum_over_list_cons.
    rewrite sum_over_list_nil. rewrite Rplus_0_r.
    simpl. reflexivity.
Qed.

Lemma  sum_over_list_big_pOplus': forall n0 (f1:nat-> R) f2 pF,
(big_pOplus' f1 f2 n0 pF) ->
sum_over_list (get_pro_formula pF)=
big_sum f1 n0.
Proof. induction n0; intros; inversion_clear H.
    simpl.
    rewrite sum_over_list_nil.
    reflexivity.
    simpl. rewrite H0. rewrite Rplus_0_r.
    apply IHn0 with f2; assumption.
    simpl. rewrite get_pro_app. rewrite sum_over_list_app. 
    f_equal.  apply IHn0 with f2; assumption.
     simpl.
     rewrite sum_over_list_cons.
    rewrite sum_over_list_nil. rewrite Rplus_0_r.
    simpl. reflexivity.
Qed.


Lemma big_pOplus_get_pro: forall  (f : nat -> R) (g : nat -> State_formula) (n_0 : nat),
get_pro_formula (big_pOplus f g n_0) = fun_to_list f n_0.
Proof. induction n_0. simpl. reflexivity.
       simpl. rewrite get_pro_app.  rewrite IHn_0. 
       simpl. intuition.
Qed. 


Lemma big_pOplus'_get_pro: forall  (f : nat -> R) (g : nat -> State_formula) (n_0 : nat) pF r_n,
(big_pOplus' f g n_0 pF) ->
(emit_0 (fun_to_list f n_0) ((fun_to_list f n_0)) r_n)->
get_pro_formula pF=r_n.
Proof. induction n_0; intros. inversion_clear H. inversion_clear H0.
        reflexivity.
       inversion_clear H; simpl in H0;
       pose (emit_0_exsist (fun_to_list f n_0) (fun_to_list f n_0));
       destruct e; try rewrite fun_to_list_length; try reflexivity.
       apply (emit_0_app _ _ _ _  x []) in H0; try assumption.
       rewrite app_nil_r in H0. 
       rewrite H0.    
       apply IHn_0 ; try assumption. 
       econstructor. assumption. econstructor.
       
       apply (emit_0_app _ _ _ _  x [f n_0]) in H0; try assumption.
       rewrite H0. rewrite get_pro_app. f_equal.     
       apply IHn_0 ; try assumption. 
       apply emit_cons. assumption. econstructor.
Qed.


Lemma big_pOplus_get_npro: forall  (f : nat -> R) (g : nat -> State_formula) (n_0 : nat),
  pro_to_npro_formula (big_pOplus f g n_0) = fun_to_list g n_0.
  Proof. induction n_0. simpl. reflexivity.
         simpl. rewrite pro_to_npro_formula_app.  rewrite IHn_0. 
         simpl. intuition.
  Qed. 


  Lemma big_pOplus_get_npro': forall  (f : nat -> R) (g : nat -> State_formula) (n_0 : nat) pF F_n,
  (big_pOplus' f g n_0 pF)->
  (emit_0 (fun_to_list f n_0) (fun_to_list g n_0) F_n)->
  pro_to_npro_formula pF = F_n.
  Proof. induction n_0; intros. 
       inversion_clear H. inversion_clear H0.
        reflexivity.
       inversion_clear H; simpl in H0;
       pose (emit_0_exsist (fun_to_list f n_0) (fun_to_list g n_0));
       destruct e; try repeat rewrite fun_to_list_length; try reflexivity.
       apply (emit_0_app _ _ _ _  x []) in H0; try assumption.
       rewrite app_nil_r in H0. 
       rewrite H0.    
       apply IHn_0 ; try assumption. 
       econstructor. assumption. econstructor.
       
       apply (emit_0_app _ _ _ _  x [g n_0]) in H0; try assumption.
       rewrite H0. rewrite pro_to_npro_formula_app. f_equal.     
       apply IHn_0 ; try assumption. 
       apply emit_cons. assumption. econstructor.
  Qed.


(*--------------------------------------------------------------*)

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
destruct H2. simpl in H3. rewrite sum_over_list_cons in H3.
 rewrite sum_over_list_nil in H3.
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
assumption. inversion_clear H5. intuition.
discriminate H0.

econstructor. assert(length [1] = length [F]). reflexivity.
apply H0.  econstructor.
inversion_clear H. intuition.
simpl. unfold distribution_formula. 
split.  econstructor. lra. intuition.
simpl. rewrite sum_over_list_cons.
 rewrite sum_over_list_nil. lra.
simpl. assert( exists mu', d_scale 1 mu mu').
apply d_scale_exsits. destruct H0.
assert(big_dapp' [1]
[mu] (d_app x (d_empty s e))). 
econstructor.
assumption. apply big_app_nil.
econstructor.  simpl. apply H1.
apply dstate_eq_trans with ((d_app mu (d_empty s e))).
apply dstate_eq_trans with ((d_app (d_empty s e) mu)).
apply dstate_eq_sym. apply d_app_empty_l.
apply d_app_comm. simpl. 
apply d_app_eq. apply dstate_eq_sym.
apply d_scale_1_l. assumption. apply dstate_eq_refl.
simpl. econstructor. intuition. 
econstructor. econstructor. reflexivity.  apply Forall_nil. 
Qed.



