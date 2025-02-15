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
Require Import Reduced.
Require Import Basic.


(*-------------------------------Synatx------------------------------------*)

Inductive Pure_formula:Type:=
|PBexp (b:bexp) 
|Pre (P: nat-> Prop) (a:aexp) 
|PAnd (P1 P2: Pure_formula)
|PNeg (P: Pure_formula)
|POr (P1 P2: Pure_formula)
|PUniver (i: nat) (P: Pure_formula)
|PAssn (i:nat) (a:aexp) (P:Pure_formula). 

Inductive QExp : Type :=
|QExp_s (s e:nat) (v: Vector (2^(e-s))): QExp
|QExp_t (qs1 qs2:QExp) : QExp.

Inductive State_formula :Type:=
|SPure (P:Pure_formula) 
|SQuan (qs:QExp)
|SOdot (F1 F2:State_formula)
|SAnd (F1 F2:State_formula)
|SAssn (i:nat) (a:aexp) (F:State_formula).


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

Definition get_pro_formula (pF:pro_formula): list R:=map (fun i=> fst i) pF.
Definition pro_to_npro_formula (pF:pro_formula): npro_formula:=map (fun i=> snd i) pF.

Fixpoint npro_to_pro_formula (nF:npro_formula ) (p_n: list R): pro_formula:=
  match nF, p_n with 
  |[], [] =>[]
  |[], _ => []
  |_, [] => []
  |F :: nF', h::p' => (h, F):: (npro_to_pro_formula nF' p')
  end.

  
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
Bind Scope assert_scope with pro_formula.
Bind Scope assert_scope with Assertion.
Delimit Scope assert_scope with npro_formula.
Open Scope assert_scope.

Notation " 'univer' x P " :=(PUniver x P)(at level 80) :assert_scope.

Notation "| v >[ s - e ]" := (QExp_s s e v) (at level 80) :assert_scope.

Infix " ⊗*  " := (QExp_t)(at level 80) :assert_scope. 

Notation "F1 /\s F2" := (SAnd F1  F2) (at level 80): assert_scope.
Notation " F1 ⊙ F2" := (SOdot F1 F2)(at level 80):assert_scope.

Fixpoint big_Sand (g: nat->  (State_formula )) (n : nat) : State_formula := 
match n with
| 0 => BTrue
| S n' => g n' /\s big_Sand g n'
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
      | Pre f a => Free_aexp a
      | PAnd P1 P2 =>  (NSet.union (Free_pure P1) (Free_pure P2))
      | PNeg P =>  (Free_pure P)
      | POr P1 P2 =>(NSet.union (Free_pure P1) (Free_pure P2))
      | PUniver a P0 => NSet.remove a (Free_pure (P0))
      | PAssn i a P0 => (NSet.union (Free_pure P0) (Free_aexp a))
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
    |SAssn i a F => (NSet.union (fst (Free_state F)) (Free_aexp a), snd (Free_state F))

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
        |Assn_sub i a D =>  (NSet.union (fst (Free D)) (Free_aexp a), snd (Free D))
    end. 

(*-------------------------------Semantics-----------------------------------*)

Local Close Scope assert_scope.
Local Open Scope nat_scope.

Local Close Scope assert_scope.
Local Open Scope nat_scope.
Fixpoint Pure_eval{s e:nat} (pf:Pure_formula) (st:state s e): Prop :=
  match pf with 
 | PBexp b => if ((beval st b)) then True else False
 | Pre f a => f (aeval st a)
 | PAnd P1 P2 => Pure_eval P1 st /\ Pure_eval P2 st
 | PNeg P => ~ Pure_eval P st
 | POr P1 P2 => Pure_eval P1 st \/ Pure_eval P2 st
 |PUniver i P=> forall a:nat, Pure_eval P (s_update_cstate i a st)
 |PAssn i a P => Pure_eval P (s_update_cstate i (aeval st a) st)
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

Import Reduced.
Local Open Scope nat_scope.
Fixpoint QExp_eval{s' e':nat} (qs: QExp) (st: state s' e'){struct qs} :Prop:=
  match qs with 
  |QExp_s s e v=>Pure_State_Vector v /\ s'<=s /\ s<e /\ e<=e' 
   /\ ((Reduced (@scale (2^(e'-s')) (2^(e'-s')) (R1 / (Cmod (@trace (2^(e'-s')) (snd st))))%R  (snd st)) s e = outer_product v v))
  |QExp_t qs1 qs2=>NSet.Equal (NSet.inter (Free_Qexp qs1) (Free_Qexp qs2)) (NSet.empty)/\
   QExp_eval qs1 st /\ QExp_eval qs2 st  
end.


Fixpoint State_eval{s e:nat} (F:State_formula) (st:state s e): Prop:=
match F with 
|SPure P => Pure_eval P st
|SQuan s=> QExp_eval s st
|SOdot F1 F2=>  NSet.Equal (NSet.inter (snd (Free_state F1)) (snd (Free_state F2))) (NSet.empty) /\
State_eval F1 st /\ State_eval F2 st
|SAnd F1 F2 =>
 State_eval F1 st /\ State_eval F2 st
|SAssn i a F => State_eval F (s_update_cstate i (aeval st a) st)
end.


Fixpoint WF_QExp (qs:QExp):=
  match qs with 
  |QExp_t qs1 qs2 => WF_QExp qs1 /\ WF_QExp qs2 /\ NSet.Equal (NSet.inter (Free_Qexp qs1) (Free_Qexp qs2)) (NSet.empty)
  |QExp_s s e v=>WF_Matrix v /\ s<e   
  end. 


Fixpoint WF_formula (F:State_formula):=
  match F with 
  |SPure P => True
  |SQuan qs => WF_QExp qs 
  |SAnd F1 F2 => WF_formula F1 /\ WF_formula F2
  |SOdot F1 F2 => WF_formula F1 /\ WF_formula F2 /\  NSet.Equal (NSet.inter (snd (Free_state F1)) (snd (Free_state F2))) (NSet.empty)
  |SAssn i a F => WF_formula F
  end.
  
Definition  State_eval_dstate{s e:nat} (F:State_formula) (mu:list (cstate *(qstate s e))): Prop:=
  match mu with 
  |[] => WF_formula F
  |_ =>Forall (fun x=> State_eval F x) mu
  end.


Lemma State_eval_WF_formula{s e:nat}: forall F c (q:qstate s e),
State_eval F (c, q)-> WF_formula F .
Proof. induction F; intros. simpl. auto. 
       induction qs; intros; simpl in *.
       split;  apply H. 
       split; [apply IHqs1|split; [apply IHqs2| ] ]; try apply H.
       simpl in *.
       split; [apply IHF1 with c q |split; [apply IHF2 with c q| ] ]; try apply H.
       split; [apply IHF1 with c q | apply IHF2 with c q  ]; try apply H.
       simpl in *.  eapply IHF. apply H. 
Qed.

Lemma State_eval_dstate_WF_formula{s e:nat}:forall  (F:State_formula) (mu:list (cstate *(qstate s e))),
State_eval_dstate F mu -> WF_formula F.
Proof. destruct mu;  intros. simpl in H. assumption.
       inversion_clear H. destruct p. 
       eapply State_eval_WF_formula. apply H0. 
Qed.

Local Open Scope R_scope.
Inductive sat_State {s e:nat}:(dstate s e) -> (State_formula)-> Prop:=
|sat_F: forall (mu:dstate s e) F,  WF_dstate mu 
                                   -> State_eval_dstate F (StateMap.this mu)
                                   -> sat_State mu F.

Lemma sat_State_WF_formula{s e:nat}:forall  (F:State_formula) (mu:dstate s e),
sat_State mu F -> WF_formula F.
Proof. intros. inversion_clear H. eapply State_eval_dstate_WF_formula. apply H1. 
Qed.


Inductive sat_Pro {s e:nat}: (dstate s e)-> (pro_formula)-> Prop:=
|sat_pro: forall (mu mu':dstate s e) pF (mu_n: list (dstate s e)),
                            big_dapp' (get_pro_formula pF) mu_n mu'
                            -> dstate_eq mu mu'
                            -> Forall_two (fun mu_i pF_i => (0<fst (pF_i))%R ->sat_State mu_i (snd (pF_i)) /\ d_trace mu_i =d_trace mu) mu_n pF
                            -> sat_Pro mu pF.

Definition distribution_formula (pF: pro_formula) := 
   (Forall (fun x => WF_formula x) (pro_to_npro_formula pF))
/\ ((Forall (fun x => 0 <= x) (get_pro_formula pF)) 
/\ (sum_over_list (get_pro_formula pF) = 1)).

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


(*----------------------------properties----------------------------------*)

Lemma get_pro_formula_length: forall pF, 
length (get_pro_formula pF) = length pF .
Proof. intros. unfold get_pro_formula. rewrite map_length. reflexivity. 
Qed.

Lemma pro_to_npro_formula_length: forall pF, 
length (pro_to_npro_formula  pF) = length pF .
Proof. intros. unfold pro_to_npro_formula. rewrite map_length. reflexivity. 
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
Proof.  induction nF1; induction nF2; intros.
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

Lemma big_pOplus_get_pro: forall  (f : nat -> R) (g : nat -> State_formula) (n_0 : nat),
get_pro_formula (big_pOplus f g n_0) = fun_to_list f n_0.
Proof. induction n_0. simpl. reflexivity.
       simpl. rewrite get_pro_app.  rewrite IHn_0. 
       simpl. intuition.
Qed. 


Lemma big_pOplus_get_npro: forall  (f : nat -> R) (g : nat -> State_formula) (n_0 : nat),
  pro_to_npro_formula (big_pOplus f g n_0) = big_Oplus g n_0.
  Proof. induction n_0. simpl. reflexivity.
         simpl. rewrite pro_to_npro_formula_app.  rewrite IHn_0. 
         simpl. intuition.
  Qed. 

  Lemma fun_to_list_big_Oplus_eq: forall n F_n,
  fun_to_list F_n n = big_Oplus F_n n.
  Proof. induction n; intros; simpl; try f_equal; auto.
  Qed.

(*--------------------------------------------------------------*)

Lemma sat_State_dstate_eq: forall s e (mu mu':dstate s e) (F:State_formula),
dstate_eq mu mu'->
sat_State  mu F-> sat_State  mu' F.
Proof. intros s e(mu, IHmu1) (mu', IHmu'). unfold dstate_eq. simpl. intros.
inversion_clear H0. econstructor.
 apply WF_dstate_eq with (StateMap.Build_slist IHmu1).
 unfold dstate_eq. simpl. assumption. assumption.
simpl in *. rewrite <-H. assumption.
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
        rewrite <-(d_trace_eq  mu _ H). assumption.
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


Lemma sat_Assert_to_State: forall s e (mu:dstate s e) (F:State_formula),
sat_Assert mu F <-> sat_State mu F.
Proof. split; intros. 
inversion_clear H. destruct p_n. inversion_clear H0.
destruct p_n. 
inversion_clear H1. inversion_clear H3.
simpl in *.  destruct mu_n. 
inversion_clear H1.
unfold distribution_formula in H2. 
destruct H2 as [H2' H2]. destruct H2. simpl in H3. rewrite sum_over_list_cons in H3.
 rewrite sum_over_list_nil in H3.
rewrite Rplus_0_r in H3. rewrite H3 in H1.
inversion H1; subst; inversion H12; subst. 
simpl in *.   
assert(dstate_eq mu d). 
apply (dstate_eq_trans _ _ _ _ _ H4).
apply dstate_eq_trans with ((d_app d (d_empty s e))).
apply d_app_eq. apply d_scale_1_l. assumption. 
apply dstate_eq_refl.
apply dstate_eq_trans with ((d_app (d_empty s e) d)).
apply d_app_comm.  apply d_app_empty_l.
apply sat_State_dstate_eq with d. apply dstate_eq_sym.
assumption. inversion_clear H5. simpl in H6. apply H6.  intuition.
discriminate H0.

econstructor. assert(length [1] = length [F]). reflexivity.
apply H0.  econstructor.
inversion_clear H. intuition.
simpl. unfold distribution_formula. 
split.  econstructor. simpl. eapply sat_State_WF_formula. apply H.
econstructor. split. econstructor. simpl. lra. econstructor.
simpl. rewrite sum_over_list_cons.
 rewrite sum_over_list_nil. lra.
simpl. assert( exists mu', d_scale 1 mu mu').
apply d_scale_exsits. destruct H0.
assert(big_dapp' [1]
[mu] (d_app x (d_empty s e))). 
econstructor.
assumption. econstructor.
econstructor.  simpl. apply H1.
apply dstate_eq_trans with ((d_app mu (d_empty s e))).
apply dstate_eq_trans with ((d_app (d_empty s e) mu)).
apply dstate_eq_sym. apply d_app_empty_l.
apply d_app_comm. simpl. 
apply d_app_eq. apply dstate_eq_sym.
apply d_scale_1_l. assumption. apply dstate_eq_refl.
simpl. econstructor. intuition. 
econstructor. 
Qed.

Lemma WF_sat_State{s e:nat}: forall  (mu:dstate s e) (F:State_formula), 
sat_State mu F ->  WF_dstate mu.
Proof. intros. 
      inversion_clear H. destruct mu as [mu IHmu]. assumption.
Qed.

Lemma n_th_eq{A:Type}: forall (mu_n:list A) (a default: A) (x:nat),
(nth x mu_n default)=nth (x+1) (a::mu_n) default.
Proof. induction mu_n; intros; destruct x.  simpl. reflexivity. destruct x.  simpl. reflexivity. simpl.
       reflexivity.
       simpl. reflexivity. simpl. apply IHmu_n. 
Qed.


Lemma WF_big_and{s e:nat}: forall (mu_n : list (dstate s e)) pF,
(Forall_two (fun mu_i pF_i =>0< fst (pF_i)-> sat_State mu_i (snd(pF_i))) mu_n pF)->
Forall_two (fun mu_i  pF_i =>0< fst (pF_i)-> WF_dstate mu_i) mu_n pF.
Proof. induction mu_n; destruct pF; intros; inversion_clear H;
   try econstructor. intros.
   apply WF_sat_State in H0. intuition. assumption. 
   apply IHmu_n.  intuition.
Qed.

Lemma WF_sat_Pro{s e:nat}: forall   (pF:pro_formula) (mu:dstate s e), 
sat_Assert mu pF-> WF_dstate mu.
Proof.  intros. 
      inversion_clear H.  
      inversion_clear H2. 
      apply WF_dstate_eq with mu'. apply dstate_eq_sym.
      assumption. 
      apply WF_dstate_big_dapp with  (get_pro_formula pF) mu_n.
      unfold get_pro_formula.
      eapply Forall_two_map ; try apply WF_big_and. simpl. auto. 
      eapply Forall_two_impli; try apply H4. simpl. intros. apply H2.  auto.
      assumption.
      inversion_clear H1.  intuition.
      inversion_clear H1. intuition.
Qed.
       
Lemma WF_sat_Npro{s e:nat}: forall (nF:npro_formula)  (mu:dstate s e) , 
sat_Assert mu nF->  WF_dstate mu.
Proof.  intros.  inversion_clear H. apply (WF_sat_Pro _ _ H1) .
Qed.

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
      simpl. apply H0. apply H0. econstructor.
      apply WWF_d_update_cstate.
      inversion_clear H. assumption.
Qed.

Require Import Mixed_State.
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
sat_Assert mu D ->  WF_dstate mu.
Proof.  induction D; intros. 
       apply (WF_sat_Pro _ _ H).
       apply (WF_sat_Npro _ _ H).
       inversion_clear H. assumption.    
Qed.

(***********************************properties************************************************)

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
     - intros. simpl. rewrite (state_eq_aexp st st' a). intuition. assumption. 
     - intros. simpl. split; intros; split; try eapply IHP1; try eapply IHP2; try apply H; try apply H0.
     - intros. simpl. split; intros; intro; destruct H0; eapply IHP; try apply H; assumption.
     - intros. simpl. split; intros; destruct H0;[left|right|left|right]; try eapply IHP1; try eapply IHP2; try apply H; try apply H0.
    --simpl.  destruct st. destruct st'. unfold s_update_cstate.
       intros. split. intros. simpl in H. subst. 
       eapply IHP with  (c_update i a c0, q). simpl. reflexivity.
       apply H0.
       intros. simpl in H. subst. 
       eapply IHP with  (c_update i a c0, q0). simpl. reflexivity.
       apply H0.
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

(* p .*  mu \models F*)
Local Open Scope C_scope.
Lemma s_seman_scale_Qexp: forall  (qs:QExp) (p:R)  (s e:nat) (c:cstate) (q:qstate s e),
0<p-> 
(QExp_eval qs (c, q) <-> QExp_eval  qs  (c, q_scale p q)).
Proof. unfold q_scale. split. intros.
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
--intros. split; intros; destruct st; unfold s_scale in *; unfold q_scale in *; simpl in *.
 rewrite (state_eq_aexp  _ (c,q)). 
  apply (IHF p s e ((c_update i (aeval (c, q) a) c, q))); try assumption.
  simpl. reflexivity.
  rewrite (@state_eq_aexp s e s e _ (c, p .* q)). 
  rewrite (IHF p s e ((c_update i (aeval (c, p .* q) a) c, q))); try assumption.
  simpl. reflexivity.

Qed.

Lemma s_seman_scale_c: forall (F:State_formula) (c:C) s e sigma (q:qstate s e),
0<(fst c) /\ snd c=0 ->
(State_eval F (sigma, q) <-> @State_eval s e F (sigma, c .* q)).
Proof. intros. destruct c.  simpl in *. destruct H. rewrite H0. 
apply (s_seman_scale _ _ s e). assumption.  
Qed. 


Local Open Scope C_scope.
Local Open Scope state_scope.
Lemma d_seman_scale_aux: forall  (F:State_formula) (p:R)  (s e:nat) (mu:list (cstate * qstate s e)),
0<p->
(State_eval_dstate F mu ->@State_eval_dstate s e F 
(p *l mu)).
Proof. induction mu; simpl; intros. assumption.  
destruct a. inversion_clear H0.
destruct mu.   
simpl. econstructor.  assert(State_eval  F (s_scale p (c, q))).
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
Lemma d_seman_scale_not_0: forall s e (p:R) (mu:dstate s e) (F:State_formula),
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

Lemma d_seman_scale: forall s e (p:R) (mu mu':dstate s e) (F:State_formula),
0<=p<=1->
d_scale p mu mu'->
sat_State mu F -> 
sat_State mu' F.
Proof. 
intros.
inversion H0; subst.
econstructor. apply WF_dstate_empty.
simpl. eapply sat_State_WF_formula. apply H1.
apply d_seman_scale_not_0; try assumption; try lra.  
Qed.

(*mu_1 .+ mu_2 \models F*)
Lemma  State_eval_plus{s e:nat}: forall F c (q q0: qstate s e),
@NZ_Mixed_State_aux (2^(e-s))q ->
@NZ_Mixed_State_aux (2^(e-s)) q0 ->
State_eval F (c, q)->
State_eval F (c,q0) ->
@State_eval s e F (c, q .+ q0).
Proof.   
       induction F; intros;  intros.
      -apply state_eq_Pure with  (c, q0). 
       reflexivity. intuition.   
      -induction qs. simpl in *.
        rewrite Rdiv_unfold in *.
        rewrite trace_plus_dist.
        rewrite <-Reduced_scale.
        assert(q= (Cmod (@trace (2^(e-s)) q))%R .* (((R1 /  (Cmod (@trace  (2^(e-s)) q))))%R .* q) ).
        rewrite Mscale_assoc. 
        rewrite Rdiv_unfold.
       rewrite RtoC_mult.
       rewrite <-Rmult_assoc . 
       rewrite Rmult_comm.  
         rewrite<-Rmult_assoc . 
         rewrite Rinv_l.   
         rewrite Rmult_1_r . 
         rewrite Mscale_1_l. reflexivity.
        unfold not. intros. apply nz_mixed_state_Cmod_1_aux in H.
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
        unfold not. intros. apply nz_mixed_state_Cmod_1_aux in H0.
        rewrite H4 in H0. lra. 
         rewrite H3. rewrite H4.
          rewrite Reduced_plus. 
          rewrite <-Reduced_scale. 
          rewrite Rdiv_unfold in *.
          destruct H1. destruct H5. destruct H6. destruct H2.
          destruct H8. destruct H9.
          split. intuition. split. intuition.
          split. intuition. split. intuition.
           destruct H7.
          rewrite H11.
          rewrite <-Reduced_scale. 
          rewrite Rdiv_unfold. destruct H10. rewrite H12.
        rewrite <-Mscale_plus_distr_l.
        rewrite Mscale_assoc. 
        rewrite<-H4. rewrite <-H3.
        rewrite <-RtoC_plus.
       rewrite RtoC_mult.
         rewrite Rmult_assoc.
         rewrite <-trace_plus_dist.
         rewrite nz_mixed_state_Cmod_plus_aux.
         rewrite Rinv_l. rewrite Rmult_1_l.
         rewrite Mscale_1_l. reflexivity.
         assert((Cmod (@trace (2^(e-s)) q) + Cmod (@trace  (2^(e-s)) q0) )%R<> 0%R).
         apply tech_Rplus. assert(Cmod(@trace (2^(e-s)) q)%R>0%R)%R.
         apply nz_mixed_state_Cmod_1_aux. apply H.
         intuition.  apply nz_mixed_state_Cmod_1_aux. apply H0.
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
      -simpl in *. eapply IHF; try assumption.
      rewrite (state_eq_aexp _ (c,q)); try reflexivity; try assumption.
      rewrite (state_eq_aexp _ (c,q0)); try reflexivity; try assumption.
Qed.


Lemma State_eval_dstate_Forall{s e}:forall (mu:list (cstate *qstate s e)) F,
mu<>nil->
(State_eval_dstate F mu <-> Forall (fun x : state s e => State_eval F x) mu).
Proof. induction mu. simpl. intuition.
      simpl. intros. intuition.
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
apply map2_app_not_nil. left. discriminate. 
assumption.
simpl. econstructor. apply State_eval_plus.
inversion_clear H. apply nz_Mixed_State_aux_to_nz_Mix_State. apply H3. 
inversion_clear  H0.  apply nz_Mixed_State_aux_to_nz_Mix_State. apply H3. 
inversion_clear H1. assumption.
inversion_clear H2. unfold Cstate_as_OT.eq in e0.
rewrite e0. assumption.  
destruct mu. simpl. rewrite map2_r_refl.
inversion_clear H2. assumption.
destruct mu'. rewrite map2_nil_r. 
inversion_clear H1. assumption.
apply State_eval_dstate_Forall.
apply map2_app_not_nil. left. 
discriminate. 
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
apply WF_dstate_map. assumption.
assumption. 
apply WF_dstate_map. assumption.
assumption. 
apply d_seman_scale_aux. intuition. 
assumption. 
apply d_seman_scale_aux. intuition. 
assumption.  
Qed.

Local Open Scope R_scope. 
Lemma d_seman_app': forall s e (F:State_formula)  (mu mu':dstate s e),
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



Lemma sum_over_list_eq_0: forall p_n, 
Forall (fun i : R => (i >= 0)%R) p_n -> 
~ (sum_over_list p_n > 0)%R->
sum_over_list p_n = 0%R .
Proof. induction p_n; intros. rewrite sum_over_list_nil. reflexivity.
        rewrite sum_over_list_cons in *.
        inversion_clear H.   
        assert(~(sum_over_list p_n) >0)%R. 
        intro. destruct H0. apply Rplus_le_lt_0_compat; try lra.
        pose(IHp_n H2 H). rewrite e in *. rewrite Rplus_0_r. lra. 
Qed. 

From Quan Require Import Ceval_Prop.
Lemma Forall_eq_0:  forall p_n,  
Forall (fun i : R => (i >= 0)%R) p_n ->
sum_over_list p_n = 0%R ->
Forall (fun i : R => i = 0%R) p_n.
Proof. induction p_n; intros. econstructor. 
       rewrite sum_over_list_cons in *. 
       inversion_clear H.
       assert(Forall (fun i : R => (0<=i)%R) p_n).
       apply Forall_impl with ((fun i : R => (i >= 0)%R)).
       intros. lra. assumption. 
       pose(sum_over_list_ge_0 p_n H). 
       assert(a=0)%R. lra. assert(sum_over_list p_n=0)%R. lra.  
       econstructor; try assumption. 
       apply IHp_n; try assumption.  
  
Qed.


Lemma big_dapp'_seman{s e:nat}:
 forall p_n  (mu_n:list (dstate s e)) (mu:dstate s e) F,
 (0<sum_over_list p_n <= 1)%R /\ ((Forall (fun i => i>=0) p_n))%R->
 (Forall_two (fun i j=> (j>0)%R-> sat_State i F) mu_n p_n)->
  big_dapp' p_n mu_n mu  ->
  sat_State mu F.
Proof. induction p_n; intros. inversion H1; subst.  
       rewrite sum_over_list_nil in H. lra.
       inversion H1; subst. 
       destruct (Req_dec a 0).
       subst. inversion H4; subst. 
       apply sat_State_dstate_eq with d.
       apply dstate_eq_sym. apply d_app_empty_l.
       apply IHp_n with td. 
       rewrite sum_over_list_cons in *. 
       rewrite Rplus_0_l in *. destruct H.
       inversion_clear H2. split; assumption.
       inversion_clear H0. assumption.
       assumption. lra. 
       assert(sum_over_list p_n >0 \/ ~(sum_over_list p_n >0))%R.
       apply Classical_Prop.classic. destruct H3. 
       apply d_seman_app'. 
       inversion H4; subst. lra.   
       apply  d_seman_scale_not_0.  
       rewrite sum_over_list_cons in H.
       destruct H.    inversion_clear H6.
       assert(sum_over_list p_n  >=0)%R. lra.
       lra. 
       inversion_clear H0. apply H6.  
       rewrite sum_over_list_cons in H.
       destruct H. inversion_clear H0. lra.  
       apply IHp_n with td. destruct H.
       rewrite sum_over_list_cons in H. 
       split. inversion_clear H5. lra.
       inversion_clear H5. assumption. 
       inversion_clear H0. assumption. 
       assumption. 
       eapply WF_dstate_big_dapp; try apply H1.
       apply Forall_two_impli with ((fun (i : dstate s e) (j : R) => (j > 0)%R -> sat_State i F)).
       intros. eapply WF_sat_State. apply H5. lra.
       assumption. 
       apply Forall_impl with ((fun i : R => (i >= 0)%R)).
       intros. lra. apply H. apply H.   
       apply big_dapp'_out_empty in H7. 
       apply sat_State_dstate_eq with r. 
       apply dstate_eq_trans with (d_app r (d_empty s e)).
       apply dstate_eq_sym. apply d_app_empty_r.
       apply d_app_eq. reflexivity. apply dstate_eq_sym. assumption.
       inversion H4; subst. lra.   
       apply  d_seman_scale_not_0.   
       rewrite sum_over_list_cons in H.
       destruct H.    inversion_clear H6.
       assert(sum_over_list p_n  =0)%R. 
       apply sum_over_list_eq_0; try assumption. 
        lra.
       inversion_clear H0. apply H6. 
       destruct H. inversion_clear H0. lra.
       destruct H. inversion_clear H5.    
       assert(sum_over_list p_n  =0)%R. 
       apply sum_over_list_eq_0; try assumption.
       apply Forall_eq_0; try assumption.
       Qed.

 (*-------------q1+q2 \models F -> q1 \models F /\ q2 \models F--------*)
Local Open Scope nat_scope.
 Lemma WF_qstate_big_sum{s e}:forall (f:nat -> qstate s e) i n,
(forall i, i<n ->@Mixed_State_aux  (2^(e-s)) (f i))->
(exists j, and (j<i) ( (f j) <> Zero))->
WF_qstate (@big_sum (Matrix (2^(e-s)) (2^(e-s))) _  f n)->
i<=n /\ i>0
->WF_qstate (@big_sum (Matrix (2^(e-s)) (2^(e-s))) _  f i).
Proof. intros.   destruct H1. econstructor.  
       rewrite<- nz_Mixed_State_aux_to_nz_Mix_State in *.
       destruct H1. split. apply nz_Mixed_State_aux_big_sum.
       lia. intros. apply H. lia. destruct H0.
       exists x.  intuition. 
       apply Rle_trans with (Cmod (@trace (2^(e-s)) (@big_sum (Matrix (2^(e-s)) (2^(e-s))) _  f n))).
        repeat  rewrite big_sum_Cmod.
        apply big_sum_le. intros. apply mixed_state_Cmod_ge_0_aux. apply H. lia. lia.   
         intros. apply H. assumption.
        intros. apply H. lia.   
        assumption. assumption.
Qed.


Lemma State_eval_sum{ s e:nat}: forall n c (f:nat -> qstate s e) F , 
(forall j, j<n -> ((@NZ_Mixed_State_aux (2^(e-s))  (f j) ) /\ State_eval F (c, (f j))) \/ (f j)= Zero)->
(exists j, and (j<n) (f j <> Zero)) ->
State_eval F (c, @big_sum  (Matrix (2^(e-s)) (2^(e-s))) (M_is_monoid (2^(e-s)) (2^(e-s))) f n)  .
Proof.
     induction n;   intros. simpl in *. destruct H0. destruct H0.  lia.
      simpl in *. destruct H0. 
      destruct(eq_dec x n). rewrite e0 in *.  
      assert( @big_sum  (Matrix (2^(e-s)) (2^(e-s))) (M_is_monoid (2^(e-s)) (2^(e-s))) f ( n)= Zero
      \/  @big_sum  (Matrix (2^(e-s)) (2^(e-s))) (M_is_monoid (2^(e-s)) (2^(e-s))) f (n) <> Zero).
     apply Classical_Prop.classic. destruct H1.
     rewrite H1 in *. rewrite Mplus_0_l in *.
     pose (H (n)). destruct o. lia. apply H2.

     rewrite H2 in *.  destruct H0. destruct H3.
     reflexivity. 
     assert(NZ_Mixed_State_aux (@big_sum  (Matrix (2^(e-s)) (2^(e-s))) _ f (n))).
     apply nz_Mixed_State_aux_big_sum. intro. rewrite H2 in *.
     simpl in *. destruct H1. reflexivity.
     intros.  rewrite NZ_Mixed_State_aux_equiv'.
      pose (H (i)). destruct o. lia. 
     left. intuition. right. assumption.  
     apply (@big_sum_not_0 (2^(e-s))). assumption.
     
     pose (H (n)). destruct o. lia. 
     apply State_eval_plus; try auto.  intuition.
     apply IHn. intros. apply H. lia.
     apply (@big_sum_not_0 (2^(e-s))). assumption.
     intuition. destruct H0. rewrite H3 in *.
     destruct H4. reflexivity.

     pose (H (n)). destruct o. lia. 
     assert( @big_sum  (Matrix (2^(e-s)) (2^(e-s))) (M_is_monoid (2^(e-s)) (2^(e-s))) f ( n)= Zero
     \/  @big_sum  (Matrix (2^(e-s)) (2^(e-s))) (M_is_monoid (2^(e-s)) (2^(e-s))) f (n) <> Zero).
    apply Classical_Prop.classic. destruct H2.
    rewrite H2 in *. rewrite Mplus_0_l in *.
    intuition. 

    assert(NZ_Mixed_State_aux (@big_sum  (Matrix (2^(e-s)) (2^(e-s))) _ f (n))).
    apply nz_Mixed_State_aux_big_sum. intro. rewrite H3 in *.
    simpl in *. destruct H2. reflexivity.
    intros.  rewrite NZ_Mixed_State_aux_equiv'.
     pose (H (i)). destruct o. lia.
    left. intuition. right. assumption.  
    apply (@big_sum_not_0 (2^(e-s))). assumption.


    apply State_eval_plus; try auto. intuition.
    apply IHn. intros. apply H. lia.
    apply (@big_sum_not_0 (2^(e-s))). assumption.
    intuition.  
    
    rewrite H1.
    rewrite Mplus_0_r. apply IHn.
    intros. apply H. lia. exists x.
    intuition.  
Qed. 





Lemma normalize_eq{n:nat}:forall (A B:Square n),
trace (B)= C1 ->
(exists (c:C), and (c <> C0) (A = c .* B))->
/(trace A) .* A =B.
Proof. intros. destruct H0. destruct H0. rewrite H1.
      rewrite trace_mult_dist. 
      rewrite Mscale_assoc.
      rewrite Cinv_mult_distr.
      rewrite Cmult_comm. rewrite Cmult_assoc.
      rewrite Cinv_r. rewrite H.
      rewrite Cinv_r.  rewrite Mscale_1_l.
      reflexivity. intro. injection H2. lra.
      assumption. assumption. 
      rewrite H. intro. injection H2.
      lra.
Qed.

Import Basic.
Lemma Rdiv_in01: forall p1 p2,
0 < p1 <=1->
0 < p2 <=1->
0 < p1 / (p1 + p2) <=1.
Proof. split.  rewrite Rdiv_unfold. apply Rmult_gt_0_compat.
intuition. apply Rinv_0_lt_compat. apply Rplus_lt_0_compat.
intuition. intuition. apply (Rcomplements.Rdiv_le_1 p1 _).
apply Rplus_lt_0_compat.
intuition. intuition.  assert(p1=p1+0)%R. rewrite Rplus_0_r.
reflexivity. rewrite H1 at 1. apply Rplus_le_compat_l.
intuition. 
Qed.

Lemma QExp_eval_sub: forall (qs: QExp) s e c (q1 q2 q': qstate s e) ,
@NZ_Mixed_State (2^(e-s)) q1 ->
@NZ_Mixed_State (2^(e-s)) q2->
@NZ_Mixed_State (2^(e-s)) (q')->
@Mplus (2^(e-s)) (2^(e-s)) q1  q2= q'->
State_eval qs (c, q')->
State_eval qs (c, q1) /\
State_eval qs (c, q2).
Proof. induction qs; intros s0 e0 c q1 q2 q' Hq1 Hq2 Hq'; intros.
       destruct H. 
       simpl in H0. destruct H0.
       destruct H0. destruct H1. destruct H2.
       assert(trace (outer_product v v) = C1).
       destruct H.  unfold outer_product.
       rewrite trace_mult. rewrite H4.
       rewrite trace_I. reflexivity.
      rewrite Mscale_plus_distr_r in H3.
      rewrite Reduced_plus in H3.
      apply (@nz_mixed_pure (2^(e-s))
      (Reduced ((R1 / Cmod (trace (q1 .+ q2)))%R .* q1) s e) 
      (Reduced ((R1 / Cmod (trace (q1 .+ q2)))%R .* q2) s e) ) in H3.
      destruct H3. destruct H3.
      destruct H3. 
      repeat rewrite <-Reduced_scale in H5.
      rewrite Rdiv_unfold in H5.
      rewrite Rmult_1_l in H5. 
      destruct H5. 

       simpl. repeat rewrite Rdiv_unfold.
      repeat  rewrite Rmult_1_l. repeat rewrite <-Reduced_scale.
       split. split. auto.
       split. auto. split. auto.
       assert( RtoC (Cmod (@trace (2^(e0-s0)) q1)) = @trace (2^(e0-s0)) q1).
       assert(@trace (2^(e0-s0)) (q1) = (fst (@trace (2^(e0-s0)) (q1 )), snd (@trace (2^(e0-s0)) (q1)))).
       destruct (@trace (2^(e0-s0)) (q1) ).
       reflexivity. rewrite H7. 
       rewrite nz_mixed_state_trace_real.
       rewrite Cmod_snd_0. simpl. reflexivity.
       simpl. apply nz_mixed_state_trace_gt0. assumption.
       simpl. reflexivity. assumption.
       rewrite RtoC_inv. split. intuition. 
       rewrite H7. rewrite <-(Reduced_trace _ _ _ s e).
       apply (@normalize_eq (2^(e-s))).
       assumption. 
       exists (Cmod (@trace (2^(e0-s0)) (q1 .+ q2)) * x)%R.
       split. 
       apply RtoC_neq. apply Rmult_integral_contrapositive_currified.
       rewrite nz_mixed_state_Cmod_plus; try assumption.
       apply Rgt_neq_0.
       apply Rplus_lt_0_compat; apply nz_mixed_state_Cmod_1; assumption.
       lra. rewrite RtoC_mult. rewrite<- Mscale_assoc.
       unfold outer_product.
       rewrite <-H5. rewrite Mscale_assoc.
       rewrite <-RtoC_mult. rewrite Rinv_r.
       rewrite Mscale_1_l. reflexivity.
       assert(Cmod (@trace (2^(e0-s0)) (q1 .+ q2)) >0)%R.
       apply nz_mixed_state_Cmod_1. assumption. lra.
       lia. apply WF_NZ_Mixed. assumption.
       assert(Cmod (@trace (2^(e0-s0)) (q1 )) >0)%R.
       apply nz_mixed_state_Cmod_1. assumption.
       lra. 
       
       split.  auto.
       split. auto. split. auto.
       assert( RtoC (Cmod (@trace (2^(e0-s0)) q2)) = @trace (2^(e0-s0)) q2).
       assert(@trace (2^(e0-s0)) (q2) = (fst (@trace (2^(e0-s0)) (q2)), snd (@trace (2^(e0-s0)) (q2)))).
       destruct (@trace (2^(e0-s0)) (q2) ).
       reflexivity. rewrite H7. 
       rewrite nz_mixed_state_trace_real.
       rewrite Cmod_snd_0. simpl. reflexivity. 
       simpl. apply nz_mixed_state_trace_gt0.
       assumption.
       simpl. reflexivity. assumption.
       rewrite RtoC_inv. split. intuition.
       rewrite H7. rewrite <-(Reduced_trace _ _ _ s e).
       apply (@normalize_eq (2^(e-s))).
       assumption. 
       exists (Cmod (@trace (2^(e0-s0)) (q1 .+ q2)) * x0)%R.
       split. apply RtoC_neq. apply Rmult_integral_contrapositive_currified.
       rewrite nz_mixed_state_Cmod_plus; try assumption.
       apply Rgt_neq_0.
       apply Rplus_lt_0_compat; apply nz_mixed_state_Cmod_1; assumption.
       lra. rewrite RtoC_mult. rewrite<- Mscale_assoc.
       unfold outer_product.
       rewrite <-H6. rewrite Mscale_assoc.
       rewrite <-RtoC_mult. rewrite Rinv_r.
       rewrite Mscale_1_l. reflexivity.
       assert(Cmod (@trace (2^(e0-s0)) (q1 .+ q2)) >0)%R.
       apply nz_mixed_state_Cmod_1. assumption. lra.
       lia. apply WF_NZ_Mixed. assumption.
       assert(Cmod (@trace (2^(e0-s0)) (q2)) >0)%R.
       apply nz_mixed_state_Cmod_1. assumption. lra.
       apply WF_qstate_Reduced. lia.
       split. apply nz_Mixed_State_aux_to_01'.
       apply nz_Mixed_State_aux_to_nz_Mix_State. assumption.
       rewrite Rdiv_unfold. rewrite Rmult_1_l.
       apply Rinv_0_lt_compat. apply nz_mixed_state_Cmod_1.
       assumption. 
       rewrite trace_mult_dist. rewrite Cmod_mult.
       rewrite Rdiv_unfold. rewrite Rmult_1_l.
       rewrite Cmod_R. rewrite Rabs_right.
       rewrite nz_mixed_state_Cmod_plus; try assumption. 
       rewrite Rmult_comm. rewrite <-Rdiv_unfold.
       apply Rdiv_in01; apply nz_mixed_state_Cmod_1; assumption.
       assert((/ Cmod (@trace (2^(e0-s0)) (q1 .+ q2)) > 0)%R).
       apply Rinv_0_lt_compat. apply nz_mixed_state_Cmod_1.
       assumption. lra.   lia.   
       apply WF_qstate_Reduced. lia.
       split. apply nz_Mixed_State_aux_to_01'.
       apply nz_Mixed_State_aux_to_nz_Mix_State.
       assumption. 
       rewrite Rdiv_unfold. rewrite Rmult_1_l.
       apply Rinv_0_lt_compat. apply nz_mixed_state_Cmod_1. assumption.
        rewrite trace_mult_dist. rewrite Cmod_mult.
       rewrite Rdiv_unfold. rewrite Rmult_1_l.
       rewrite Cmod_R. rewrite Rabs_right.
       rewrite nz_mixed_state_Cmod_plus; try assumption. 
       rewrite Rmult_comm. rewrite <-Rdiv_unfold.
       rewrite Rplus_comm.
       apply Rdiv_in01; apply nz_mixed_state_Cmod_1; assumption.
       assert((/ Cmod (@trace (2^(e0-s0)) (q1 .+ q2)) > 0)%R).
       apply Rinv_0_lt_compat. apply nz_mixed_state_Cmod_1.
       assumption. lra. 
       lia. assumption.
      simpl in H0.
      destruct H0. destruct H1.
      apply (IHqs1 _ _ _  q1 q2) in H1 .
      apply (IHqs2 _ _ _  q1 q2) in H2 .
      
      simpl. split. 
      intuition. intuition. assumption.
      assumption. assumption. assumption. 
      assumption. assumption. assumption.
      assumption.
Qed.



Lemma QExp_eval_sub': forall F s e c (q1 q2 q': qstate s e) ,
@NZ_Mixed_State (2^(e-s)) q1 ->
@NZ_Mixed_State (2^(e-s)) q2->
@NZ_Mixed_State (2^(e-s)) (q')->
@Mplus (2^(e-s)) (2^(e-s)) q1  q2= q'->
State_eval F (c, q')->
State_eval F (c, q1) /\
State_eval F (c, q2).
Proof. induction F; intros s0 e0 c q1 q2 q' Hq1 Hq2 Hq'; intros.
       split;
       apply state_eq_Pure with (c,q');
       try reflexivity; try assumption. 
        
       apply QExp_eval_sub with q'.
       assumption.
       assumption. assumption. assumption.
       assumption. 
      
      simpl in H0.
      destruct H0. destruct H1.
      apply (IHF1 _ _ _  q1 q2) in H1 .
      apply (IHF2 _ _ _  q1 q2) in H2 .
      
      simpl. split. 
      intuition. intuition. assumption. assumption.
      assumption. assumption. assumption.
      assumption. assumption. assumption. 

      simpl in H0.
      destruct H0. 
      apply (IHF1 _ _ _  q1 q2) in H0 .
      apply (IHF2 _ _ _  q1 q2) in H1 .
      
      simpl. split. 
      intuition. intuition. assumption. assumption.
      assumption. assumption. assumption.
      assumption. assumption. assumption.

      simpl. split. eapply IHF; [ try apply Hq2| try apply Hq1| apply Hq'| | ].
      rewrite Mplus_comm. assumption.
      simpl in H0. 
      rewrite (state_eq_aexp _ (c, q')); try reflexivity; try assumption.
      simpl in H0.
      eapply IHF; [ try apply Hq1| try apply Hq2| apply Hq'| apply H | ].
      simpl in H0. 
      rewrite (state_eq_aexp _ (c, q')); try reflexivity; try assumption.
Qed.

Local Open Scope nat_scope.
Lemma State_eval_sub_sum{ s e:nat}: forall n c (f:nat -> qstate s e) F , 
(forall i, i<n -> WF_qstate (f i) \/ (f i) = Zero)->
(WF_qstate (@big_sum  (Matrix (2^(e-s)) (2^(e-s))) (M_is_monoid (2^(e-s)) (2^(e-s)))  f n)) ->
State_eval F (c, @big_sum  (Matrix (2^(e-s)) (2^(e-s))) (M_is_monoid (2^(e-s)) (2^(e-s))) f n)->
(forall j, j<n-> WF_qstate (f j) -> State_eval F (c, (f j))).
Proof. induction n; intros. simpl in *. lia.
       simpl in H1. 
       assert(j =  n\/ j<  n).  lia. destruct H4.
       rewrite H4 in *.
       assert( @big_sum  (Matrix (2^(e-s)) (2^(e-s))) (M_is_monoid (2^(e-s)) (2^(e-s))) f (n)= Zero
       \/  @big_sum  (Matrix (2^(e-s)) (2^(e-s))) (M_is_monoid (2^(e-s)) (2^(e-s))) f (n) <> Zero).
      apply Classical_Prop.classic. destruct H5. rewrite H5 in *.
      rewrite Mplus_0_l in *. assumption.

      apply (QExp_eval_sub' F _ _ _ 
      (big_sum f (n)) (f ( n))) in H1.
      intuition. eapply WF_qstate_big_sum with (S n).
      intros.  rewrite NZ_Mixed_State_aux_equiv'.
        pose (H i). destruct o. lia.
      left. apply nz_Mixed_State_aux_to_nz_Mix_State.
      apply H7. right. assumption.
       apply (@big_sum_not_0 (2^(e-s))). assumption.
       apply H0. split. lia. assert( n<>0).
       intro. rewrite H6 in *. simpl in *. destruct H5.
       reflexivity. lia.     
      apply H3. apply H0.
      reflexivity. 
      apply IHn. intros. apply H. lia.

      eapply WF_qstate_big_sum with (S n).
      intros.  rewrite NZ_Mixed_State_aux_equiv'. pose (H i). destruct o. lia.
      left. apply nz_Mixed_State_aux_to_nz_Mix_State.
      apply H6. right. assumption. exists j.
      split. lia. apply (@NZ_Mixed_not_Zero (2^(e-s))).
      apply H3. apply H0. lia.    

      assert(f n = Zero \/ (f n) <> Zero). 
      apply Classical_Prop.classic. destruct H5.
      rewrite H5 in *. rewrite Mplus_0_r in *.
      assumption. 
      apply (QExp_eval_sub' F _ _ _ 
       (big_sum f (n)) (f (n))) in H1. 
       intuition.

       eapply WF_qstate_big_sum with (S n).
       intros.  rewrite NZ_Mixed_State_aux_equiv'. pose (H i). destruct o. lia.
       left. apply nz_Mixed_State_aux_to_nz_Mix_State.
       apply H7. right. assumption. exists j.
       split. lia. apply (@NZ_Mixed_not_Zero (2^(e-s))).
       apply H3. apply H0. lia.
       
       pose (H n). destruct o. lia. apply H6.
       rewrite H6 in H5. destruct H5. reflexivity.  
       
        apply H0.
       reflexivity. lia. assumption.   
Qed.



(* seman_find*)
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
Sorted.Sorted (StateMap.Raw.PX.ltk (elt:=qstate s e)) mu->
(WF_dstate_aux mu) -> 
(State_eval_dstate F mu <-> (WF_formula F /\ 
(forall x:cstate, (option_qstate (StateMap.Raw.find x mu) <> Zero) -> (State_eval F 
(x, (option_qstate (StateMap.Raw.find x mu))))))). 
Proof. induction mu; intros.
-simpl. split; intros. split; try apply H1. intros. destruct H2. reflexivity.
  apply H1.
-destruct mu. split; intros. split. eapply State_eval_dstate_WF_formula. apply H1.
 intros. apply seman_find_state_aux; assumption.
 apply seman_find_state_aux; try apply H1. assumption.
  split. destruct a. destruct p. 
  intros.  simpl.
  simpl in *. inversion_clear H1. 
  split. eapply State_eval_WF_formula. apply H2.
  intros. 
  destruct  (Cstate_as_OT.compare x c ).
  simpl in H1. destruct H1. reflexivity.
  unfold Cstate_as_OT.eq in e0.
  rewrite e0. 
  simpl. assumption.
  apply IHmu. inversion_clear H.
  assumption. inversion_clear H0.
  assumption. assumption.
  apply H1.

  destruct a. destruct p. intros.
  simpl.  econstructor.  
  assert(State_eval F
  (c,
   option_qstate
     (StateMap.Raw.find (elt:=qstate s e) c ((c, q) :: (c0, q0) :: mu)))).

 apply H1. 
 simpl. destruct (Cstate_as_OT.compare c c).
 apply Cstate_as_OT.lt_not_eq in l. intuition.
 simpl.  inversion_clear H0.  apply (WF_state_not_Zero _ H2).
 apply Cstate_as_OT.lt_not_eq in l. intuition.
 simpl in H2. 
 destruct (Cstate_as_OT.compare c c).
 apply Cstate_as_OT.lt_not_eq in l. intuition.
 simpl. simpl in H2. assumption.
 apply Cstate_as_OT.lt_not_eq in l. intuition.

 apply IHmu. inversion_clear H. assumption.
  inversion_clear H0.
 assumption.  split. apply H1.  
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


Lemma seman_find{s e}:forall  (mu:dstate s e) (F: State_formula),
sat_State mu F <->
(WF_dstate mu /\ WF_formula F /\
(forall x:cstate, d_find x mu <>Zero -> (State_eval F 
(x, (d_find x mu))))).
Proof. intros. destruct mu as [mu IHmu]. simpl.
split. intros. split.  
inversion_clear H. assumption. 
unfold d_find. unfold StateMap.find. simpl in *.
inversion_clear H. 
split. eapply State_eval_dstate_WF_formula. apply H1.
apply  seman_find_aux. assumption.
 assumption. assumption.
split. apply H. 
simpl in *.  apply seman_find_aux; try apply H.
assumption.
Qed.

Local Open Scope com_scope.
(*big_and_sat*)
Lemma BTrue_true{s e:nat}: forall (mu:dstate s e),
WF_dstate mu ->
sat_State mu <{ true }> .
Proof. intros. econstructor. apply H.  
destruct mu as [mu IHmu]. 
induction mu; simpl in *. auto.  destruct mu. 
econstructor.  auto. econstructor.
econstructor.  auto. 
inversion_clear IHmu. 
simpl in IHmu0. eapply IHmu0 with H0. 
inversion_clear H. assumption. 
Qed.


Lemma State_eval_conj: forall s e (mu:list (cstate * qstate s e)) (F1 F2:State_formula),
State_eval_dstate  (F1 /\s  F2) mu <->
State_eval_dstate   F1 mu /\ State_eval_dstate F2 mu .
Proof. intros. split; intros; 
induction mu; 
simpl in *. assumption. 
-destruct mu; destruct a; inversion_clear H; simpl;
 intuition. assumption. 
-destruct a. destruct mu. simpl. econstructor. 
destruct H. inversion_clear H. inversion_clear H0.
split; intuition. apply Forall_nil.
simpl.  destruct H. inversion_clear H.
inversion_clear H0. intuition.
Qed.


Lemma sat_assert_conj: forall s e (mu:dstate s e) (F1 F2:State_formula),
sat_Assert mu (F1 /\s F2)<->
sat_Assert mu F1/\ sat_Assert mu F2 .
Proof.  split; destruct mu as [mu IHmu]; intros;
repeat rewrite sat_Assert_to_State in *.
inversion_clear H.  apply State_eval_conj in H1.
simpl in *. split; econstructor; intuition.

destruct H. inversion_clear H. inversion_clear H0.
econstructor. intuition.
apply State_eval_conj. split; intuition.   
Qed.


Local Open Scope nat_scope.
Lemma Big_Sand_forall{s e:nat}: forall (mu:dstate s e) (f:nat-> State_formula) n,
(forall i,  sat_Assert mu (f i))->
sat_Assert mu (big_Sand f n).
Proof. induction n; intros. simpl. rewrite sat_Assert_to_State in *.
apply BTrue_true. pose(H 1). 
apply WF_sat_Assert in s0.
assumption.
simpl. apply sat_assert_conj. 
split. 
apply H. apply IHn. assumption.
Qed.



(*big_oplus_sat*)

Lemma Forall_two_big_pOplus{s e:nat}:forall n (p_n:nat-> R) (F_n:nat-> State_formula) (mu_n:nat-> (dstate s e))  (mu:dstate s e),
(forall i : nat,
i < n -> (0 < p_n i)%R -> sat_State (mu_n i) (F_n i) /\ d_trace (mu_n i) = d_trace mu) ->
Forall_two (fun (mu_i : dstate s e) (pF_i : R * State_formula) =>
(0 < fst pF_i)%R -> sat_State mu_i (snd pF_i) /\ d_trace mu_i = d_trace mu)(fun_to_list mu_n n) (big_pOplus p_n F_n n).
Proof. induction n; intros. simpl. econstructor. 
       simpl. apply Forall_two_app. apply IHn. intros. apply H. lia. assumption.
       econstructor. simpl. intros. apply H. lia. assumption.
       econstructor.  
Qed.

Lemma big_pOplus_sat{s e:nat}: forall n (p_n:nat-> R) (F_n:nat-> State_formula) (mu_n:nat-> (dstate s e))  mu mu',
big_dapp' (fun_to_list p_n n) (fun_to_list mu_n n) mu' 
->dstate_eq mu mu' 
-> (forall i, i<n -> (0<(p_n i))%R -> sat_State (mu_n i) (F_n i) /\ d_trace (mu_n i) = d_trace mu) ->
sat_Pro mu (big_pOplus p_n F_n n).
Proof. intros.  
       econstructor. rewrite big_pOplus_get_pro. apply H. assumption.
       apply Forall_two_big_pOplus. assumption. 
Qed.

Lemma fun_to_list_inv{A:Type}: forall(mu_n:list A)  (a: A)  (default: A),
fun_to_list (fun i : nat => match i with
                            | 0 => a
                            | S m => nth m mu_n default
                            end) (Datatypes.length mu_n) ++
[match Datatypes.length mu_n with
 | 0 => a
 | S m => nth m mu_n default
 end] = a :: fun_to_list (fun i : nat => nth i mu_n default) (Datatypes.length mu_n) .
Proof. intros. 
induction (Datatypes.length mu_n). simpl. reflexivity.
simpl. rewrite IHn. reflexivity. 
Qed.


Lemma n_th_fun_to_list_inv{A:Type}: forall (mu_n:list A) (default: A),
(fun_to_list (fun i : nat => nth i mu_n default) (length (mu_n)))=mu_n.
Proof. induction mu_n; intros; simpl in *. reflexivity.
      rewrite <-(IHmu_n default) at 3. apply fun_to_list_inv. 
Qed.


Lemma Forall_two_nth{A B : Type}: forall  (P : A -> B -> Prop) 
(f : list A) (g : list  B) (fdefault:A) (gdefault:B),
Forall_two P f g <-> 
((length f) = (length g) /\ forall i, i< (length f) -> P (nth i f  fdefault) 
(nth i g gdefault)) .
Proof. induction f; destruct g; intros; simpl in *. split; intros. split; lia. econstructor.
       split; intros. inversion_clear H. lia.
       split; intros.   
       inversion_clear H. lia.
       split; intros.  inversion_clear H. split. apply Forall_two_length_eq in H1.
       rewrite H1. reflexivity.   
       intros. destruct i. assumption. apply IHf. assumption. lia.
       destruct H.  econstructor.  apply (H0 0). lia.
       rewrite (IHf _ fdefault gdefault). split. injection H . auto.
       intros. pose( H0 ( S i)). simpl in p.  apply p. lia.      
Qed.


Lemma fst_nth_big_pOplus: forall n p_n F_n i, 
i<n->
fst (nth i (big_pOplus p_n F_n n) ((1%R, SPure (PBexp <{BTrue}>))))%R = p_n i.
Proof. induction n; intros. lia. simpl. 
       assert(i=n \/ i<> n). apply Classical_Prop.classic.
       destruct H0. rewrite H0. 
       rewrite app_nth2; rewrite  big_pOplus_length.  
       rewrite Nat.sub_diag. simpl. reflexivity. lia. 
       rewrite app_nth1; try rewrite  big_pOplus_length.
       apply IHn. lia. lia.    
Qed.


Lemma snd_nth_big_pOplus: forall n p_n F_n i, 
i<n->
snd (nth i (big_pOplus p_n F_n n) ((1%R, SPure (PBexp <{BTrue}>))))%R = F_n i.
Proof. induction n; intros. lia. simpl. 
       assert(i=n \/ i<> n). apply Classical_Prop.classic.
       destruct H0. rewrite H0. 
       rewrite app_nth2; rewrite  big_pOplus_length.  
       rewrite Nat.sub_diag. simpl. reflexivity. lia. 
       rewrite app_nth1; try rewrite  big_pOplus_length.
       apply IHn. lia. lia.    
Qed.

Lemma big_pOplus_sat'{s e:nat}: forall n (p_n:nat-> R) (F_n:nat-> State_formula) (mu_n:nat-> (dstate s e)) mu,
sat_Pro mu (big_pOplus p_n F_n n)->
(exists (mu_n:nat-> (dstate s e)) mu',
 big_dapp' (fun_to_list p_n n) (fun_to_list mu_n n) mu' 
/\ dstate_eq mu mu' 
/\(forall i, i<n -> (0<(p_n i))%R -> sat_State (mu_n i) (F_n i) /\ d_trace (mu_n i) = d_trace mu)).
Proof. intros.  inversion_clear H.  exists (fun i=> nth  i (mu_n0) (d_empty s e)).
      rewrite big_pOplus_get_pro in *.
      assert( n= length mu_n0). 
      rewrite <-(fun_to_list_length  p_n n). eapply big_dapp'_length. apply H0.
      exists mu'.  split. 
      rewrite H.
      rewrite n_th_fun_to_list_inv. rewrite <-H. assumption. 
       split. assumption.
      intros. rewrite H in H3.  
      eapply (Forall_two_nth _ mu_n0  (big_pOplus p_n F_n n) (d_empty s e) ((1%R, SPure (PBexp <{BTrue}>)))) in H2; try apply H3.
      destruct H2. pose(H5 i H3).
      rewrite fst_nth_big_pOplus in a; try lia.  
      rewrite snd_nth_big_pOplus in a;try lia.
      apply a. assumption.
Qed.





(*d_update_cstate a*)

Fixpoint d_update_cstate_list{ s e:nat} i a (mu_n:list (dstate s e)) :=
  match mu_n with 
  | nil => [] 
  |mu::mu_n' => (d_update_cstate i a mu) :: (d_update_cstate_list  i a mu_n')
  end. 

Lemma d_update_cstate_empty{s e:nat}: forall i a, 
dstate_eq  (d_update_cstate i a (d_empty s e)) (d_empty s e).
Proof. unfold dstate_eq. intros. simpl in *. reflexivity.
  
Qed.


Lemma app_fix_2{s e:nat} : forall c (q:qstate s e) i a (mu:list (cstate * qstate s e)),
((fix map2_aux (m' : StateMap.Raw.t (qstate s e)) :
        StateMap.Raw.t (qstate s e) :=
      match m' with
      | [] => [(c_update i (aeval (c, q) a) c, q)]
      | p :: l' =>
          let (k', e') := p in
          match
            Cstate_as_OT.compare (c_update i (aeval (c, q) a) c) k'
          with
          | OrderedType.LT _ =>
              (c_update i (aeval (c, q) a) c, q)
              :: StateMap.Raw.map2_r option_app m'
          | OrderedType.EQ _ =>
              (c_update i (aeval (c, q) a) c, q_plus q e')
              :: StateMap.Raw.map2_r option_app l'
          | OrderedType.GT _ => (k', e') :: map2_aux l'
          end
      end) (d_update_cstate_aux i a mu))=
 StateMap.Raw.map2  option_app  ([(c_update i (aeval (c, q) a) c, q)]) (d_update_cstate_aux i a mu)     .
Proof. intros. reflexivity. 
       
Qed.

Lemma app_fix{s e:nat} : forall c0 (q0:qstate s e) (d d':list (cstate * qstate s e)),
(fix map2_aux (m' : StateMap.Raw.t (qstate s e)) :
                 StateMap.Raw.t (qstate s e) :=
               match m' with
               | [] =>
                   (c0,  q0)
                   :: StateMap.Raw.map2_l option_app d
               | p :: l' =>
                   let (k', e') := p in
                   match Cstate_as_OT.compare c0 k' with
                   | OrderedType.LT _ =>
                       (c0,  q0)
                       :: StateMap.Raw.map2 option_app d  m'
                   | OrderedType.EQ _ =>
                       (c0, q0 .+ e')
                       :: StateMap.Raw.map2 option_app d  l'
                   | OrderedType.GT _ => (k', e') :: map2_aux l'
                   end
               end) d'= StateMap.Raw.map2 option_app ((c0, q0)::d)  d'
               .
Proof. destruct d'. simpl. reflexivity.
   destruct p. 
   destruct (Cstate_as_OT.compare c0 c);
   simpl; MC.elim_comp;  reflexivity.
Qed.

Lemma d_update_cstate_map2_aux{s e:nat}: forall i a (mu1 mu2:list (state s e)), 
 (d_update_cstate_aux i a (StateMap.Raw.map2 option_app mu1  mu2)) =
 ( StateMap.Raw.map2 option_app (d_update_cstate_aux i a mu1 ) 
(d_update_cstate_aux i a mu2 )).
Proof.  induction mu1; intros . simpl in *.
repeat rewrite map2_r_refl. reflexivity. destruct a0.   
induction mu2.  repeat rewrite map2_nil_r.  reflexivity.
destruct a0. simpl. 
destruct (Cstate_as_OT.compare c c0). simpl.
rewrite app_fix_2. rewrite app_fix_2. rewrite app_fix_2.   
rewrite IHmu1.  remember ([(c_update i (aeval (c, q) a) c, q)]).  
remember ((d_update_cstate_aux i a mu1)).
remember ([(c_update i (aeval (c0, q0) a) c0, q0)]). 
simpl. rewrite app_fix_2. rewrite <-Heql2.  
remember ((d_update_cstate_aux i a mu2)).
remember ((StateMap.Raw.map2 option_app l2 l3)).
rewrite map2_assoc. reflexivity.
simpl. rewrite app_fix_2. rewrite app_fix_2. rewrite app_fix_2.
rewrite IHmu1.   rewrite map2_assoc. rewrite map2_assoc.  
remember ((d_update_cstate_aux i a mu1)).
remember ((d_update_cstate_aux i a mu2)). f_equal.  
rewrite <-map2_assoc.  rewrite (map2_comm l ). 
rewrite map2_assoc. f_equal.  
unfold Cstate_as_OT.eq in e0.
rewrite e0.
simpl. rewrite (state_eq_aexp ((c0, q) ) ((c0, q0) )); try reflexivity.
MC.elim_comp. 
rewrite (state_eq_aexp _  ((c0, q0) )); try reflexivity. 
simpl. 
rewrite app_fix_2.  rewrite app_fix_2. rewrite app_fix_2.    
rewrite app_fix. unfold state in IHmu2.  
rewrite IHmu2. simpl d_update_cstate_aux. 
rewrite app_fix_2.   
rewrite map2_assoc. rewrite map2_assoc. 
 rewrite (map2_comm 
([(c_update i (aeval (c0, q0) a) c0, q0)])). 
rewrite <-map2_assoc.  rewrite <-map2_assoc.
rewrite <-map2_assoc.
f_equal.    rewrite map2_assoc. rewrite map2_assoc.
rewrite (map2_comm ([(c_update i (aeval (c0, q0) a) c0, q0)])).
reflexivity. 
Qed.

Lemma d_update_cstate_dapp{s e:nat}: forall i a (mu1 mu2:dstate s e), 
dstate_eq  (d_update_cstate i a (d_app mu1 mu2)) (d_app (d_update_cstate i a mu1 )
(d_update_cstate i a mu2 )).
Proof. intros i a (mu1, IHmu1)  (mu2, IHmu2). unfold dstate_eq. unfold d_app. unfold  StateMap.map2.
simpl StateMap.this. apply d_update_cstate_map2_aux. 
Qed.


Lemma map_update{s e:nat}: forall i a (r:R) (mu1 :list (state s e)),
StateMap.Raw.map (fun x0 : qstate s e => q_scale r x0)
(d_update_cstate_aux i a mu1) = 
d_update_cstate_aux i a (StateMap.Raw.map (fun x0 : qstate s e => q_scale r x0) mu1).
Proof. induction mu1. simpl. reflexivity. destruct a0.  
      simpl.  rewrite app_fix_2. rewrite app_fix_2.   
      pose (@map_map2_distr s e ([(c_update i (aeval (c, q) a) c, q)]) 
      ((d_update_cstate_aux i a mu1)) r).  
      unfold q_scale in *.  unfold qstate in *. 
      rewrite <-e0. simpl StateMap.Raw.map. f_equal. 
      rewrite (state_eq_aexp _  ((c, r.*q) )); try reflexivity. 
      rewrite IHmu1. reflexivity.
Qed.   

Lemma d_scale_not_0_update{s e:nat}: forall i a r (mu1 :dstate s e),
dstate_eq (d_scale_not_0 r (d_update_cstate i a mu1))
  (d_update_cstate i a (d_scale_not_0 r mu1)).
Proof. intros i a r (mu1, IHmu1). unfold dstate_eq. simpl in *.
    apply map_update.
Qed.


Lemma d_scale_update{s e:nat}: forall i a r (mu1 mu2 mu3:dstate s e),
d_scale r mu1 mu2->
d_scale r (d_update_cstate i a mu1) mu3->
dstate_eq mu3 (d_update_cstate i a mu2).
Proof. intros. inversion H; subst. inversion_clear H. inversion_clear H0. 
apply dstate_eq_sym. apply d_update_cstate_empty. lra. lra.
inversion H0; subst. lra.  apply d_scale_not_0_update.
Qed.

  
Lemma big_dapp'_update{s e:nat}: forall p_n (mu_n:list (dstate s e)) mu1 mu2 i a, 
big_dapp' p_n mu_n mu1->
big_dapp' p_n (d_update_cstate_list i a mu_n) mu2->
dstate_eq mu2 (d_update_cstate i a mu1).
Proof. induction p_n; intros. inversion_clear H. inversion_clear H0.
       apply dstate_eq_sym. apply d_update_cstate_empty.
       inversion H; subst. inversion H0; subst.  
       eapply dstate_eq_trans with (d_app (d_update_cstate i a0 r) (d_update_cstate i a0 d)); try  
       apply dstate_eq_sym; try
       apply d_update_cstate_dapp. 
       apply d_app_eq. apply dstate_eq_sym. eapply d_scale_update.
       apply H3. apply H8. 
       apply dstate_eq_sym.
       eapply IHp_n. apply H6. assumption.
Qed.

Lemma d_update_cstate_length{s e:nat}: forall i a (mu_n:list (dstate s e)),
length (d_update_cstate_list i a mu_n) = length mu_n.
Proof. intros. induction mu_n. simpl. reflexivity. simpl. f_equal. auto.
Qed.


Lemma d_update_cstate_eq{s e:nat}: forall i a (mu1 mu2: (dstate s e)),
dstate_eq mu1 mu2->
dstate_eq (d_update_cstate i a mu1) (d_update_cstate i a mu2).
Proof. intros i a (mu1, IHmu1) (mu2, IHmu2). unfold dstate_eq. unfold d_update_cstate. simpl. 
intros. subst.  auto. 
Qed.


Lemma d_trace_update'{s e:nat}: forall  (mu: (dstate s e)) i a,
WWF_dstate mu->
d_trace (d_update_cstate i a mu)=
d_trace mu.
Proof. intros (mu, IHmu). unfold WWF_dstate.  unfold d_trace. unfold d_update_cstate. simpl. intros.
      apply d_trace_update. assumption. 
Qed.


(*eval_odot*)
Lemma State_eval_odot:forall (s e : nat) (mu : list (cstate * qstate s e)) (F1 F2 : State_formula),
State_eval_dstate ((F1 ⊙ F2)) mu <->
State_eval_dstate F1 mu /\ State_eval_dstate F2 mu /\ 
NSet.Equal (NSet.inter (snd (Free_state F1)) (snd (Free_state F2))) NSet.empty  .
Proof.
intros. split; intros; 
       induction mu; 
       simpl in *. assumption. 
       -destruct mu; destruct a; inversion_clear H; simpl;
        intuition. assumption.  
      -destruct a. destruct mu. simpl. econstructor. 
       destruct H. inversion_clear H. inversion_clear H0.
      split; inversion_clear H. intuition. intuition.  apply Forall_nil.
      simpl. econstructor.  destruct H. inversion_clear H.
      destruct H0.
      inversion_clear H. intuition.
      apply IHmu. destruct H. inversion_clear H. destruct H0.
      inversion_clear H. split. 
      intuition. intuition.  
Qed.


Lemma sat_assert_odot: forall s e (mu:dstate s e) (F1 F2:State_formula),
sat_Assert mu (F1 ⊙ F2)<->
sat_Assert mu F1/\ sat_Assert mu F2 /\ NSet.Equal (NSet.inter (snd (Free_state F1)) (snd (Free_state F2))) NSet.empty .
Proof.   split; destruct mu as [mu IHmu]; intros;
repeat rewrite sat_Assert_to_State in *.
inversion_clear H.  apply State_eval_odot in H1.
split. econstructor. assumption. apply H1.
split. econstructor. assumption. apply H1.
apply H1.
inversion_clear H. inversion_clear H0.
econstructor. intuition.
apply State_eval_odot. destruct H1.
inversion_clear H0. split; intuition.  
Qed.





