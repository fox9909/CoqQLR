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
  |QExp_t qs1 qs2=> NSet.Equal (NSet.inter (Free_Qexp qs1) (Free_Qexp qs2)) (NSet.empty)  /\
                               QExp_eval qs1 st /\ QExp_eval qs2 st
                    
end.

Fixpoint State_eval{n:nat} (sf:State_formula) (st:state n): Prop:=
match sf with 
|SPure P => Pure_eval P st
|SQuan s=> QExp_eval s st
|SOdot F1 F2=> 
NSet.Equal (NSet.inter (snd (Free_state F1)) (snd (Free_state F2))) (NSet.empty) /\
State_eval F1 st /\ State_eval F2 st
|SAnd F1 F2 => State_eval F1 st /\ State_eval F2 st
|SNot F => ~(State_eval F st)
|Assn_sub i a F => State_eval F  (s_update_cstate i (aeval st a) st)
end.


Definition  State_eval_dstate{n:nat} (F:State_formula) (mu:list (cstate *(qstate n))): Prop:=
  match mu with 
  |nil => False 
  |_=>
  Forall (fun x=> State_eval F x) mu
  end.

(* Fixpoint State_eval_dstate {n:nat} (F:State_formula) (mu:list (cstate *(qstate n))): Prop:=
  match mu with
  |nil=> False
  |[(sigma,rho)] =>State_eval F (sigma, rho)
  |(sigma,rho)::mu'=>State_eval F (sigma, rho) /\ State_eval_dstate F mu'
  end. *)


(* Fixpoint assert_scale (p:R) (nF: unprobabilistic_formula): probabilistic_formula := 
match nF with
|NState F => PState p F 
|NOplus nF1 nF2=> POplus p F1 (assert_scale p F2)
end.  *)

Local Open Scope R_scope.

Inductive sat_State {n:nat}:(dstate n) -> (State_formula)-> Prop:=
  |sat_F: forall (mu:dstate n) F, WF_dstate mu -> State_eval_dstate F (StateMap.this mu)
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


                   
Fixpoint big_and{n:nat} (f : list (dstate n)) (g: list (State_formula )) (n_0 : nat) : Prop := 
  match n_0 with
  | 0 => True
  | S n' => match f ,g with 
           |[], _ =>False
           | _ ,[]=>False
           | hf:: tf , hg::tg=> (sat_State hf hg) /\ (big_and  tf tg n')
   end
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

Fixpoint big_dapp{n:nat} (g:list R) (f:list (dstate n))  (n_0 : nat) : dstate n := 
  match n_0 with
  | 0 => d_empty n
  | S n' => match g ,f with 
           |[], _ => d_empty n
           | _ ,[]=>  d_empty n 
           | hg::tg, hf:: tf =>d_app (d_scalar hg hf) (big_dapp tg tf n')
            end
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


    (* Lemma  d_scalar_0:
    forall {n : nat} (mu : dstate n), dstate_eq (d_scalar 0 mu) (d_empty n).
    Proof. intros. unfold d_scalar. unfold dstate_eq. 
            simpl.  Admitted. *)
    Lemma  d_scalar_empty:
    forall {n : nat}  p, dstate_eq (d_scalar p (d_empty n)) (d_empty n).
    Proof. intros. unfold d_scalar. unfold dstate_eq. 
            simpl. reflexivity. Qed. 
    
    

    Lemma dstate_eq_trans: forall n (mu mu1 mu2: dstate n),
  dstate_eq mu mu1 -> dstate_eq mu1 mu2
  -> dstate_eq mu mu2.
  Proof. intros n (mu, IHmu) (mu1,IHmu1) (mu2,IHmu2).
    unfold dstate_eq. simpl.
    intros. rewrite H. assumption.
    Qed.

    Lemma  big_dapp_nil{n:nat}: forall n_0 g (f:list (dstate n)),
    g=[]\/f=[]->
     dstate_eq (big_dapp g f n_0) (d_empty n) .
    Proof. intros. destruct H;  induction n_0; 
      simpl. destruct g. simpl. unfold dstate_eq ;try reflexivity.
       simpl. unfold dstate_eq ;try reflexivity. rewrite H.  
       simpl. unfold dstate_eq ;try reflexivity. 
       rewrite H. destruct g. simpl.  unfold dstate_eq ;try reflexivity.
       simpl. unfold dstate_eq ;try reflexivity.
       rewrite H. destruct g. simpl.  unfold dstate_eq ;try reflexivity.
       simpl. unfold dstate_eq ;try reflexivity.
    Qed.
    
Fixpoint pro_to_npro_formula (pF:pro_formula ): npro_formula:=
  match pF with 
  |[] => []
  |(p, F) :: pF'=> F:: (pro_to_npro_formula pF')
  end. 

Inductive sat_Pro {n:nat}: (dstate n)-> (pro_formula)-> Prop:=
|sat_pro: forall (mu:dstate n) pF (mu_n: list (dstate n)), 
length mu_n = length pF->
dstate_eq mu (big_dapp (get_pro_formula pF) mu_n (length pF))
-> (big_and mu_n (pro_to_npro_formula pF) (length pF)) 
-> Forall (fun mu_i => d_trace  mu_i =d_trace mu) mu_n
   -> sat_Pro mu pF.

Fixpoint swap_list {A:Type} (l:list A) (i:nat):=
match l ,i with 
|[], _ =>[]
|h::[], _ => h::[]
|h:: h'::t, 0=> h':: h :: t 
|h:: h'::t, S i' => h:: (swap_list (h'::t) i')
end .

Lemma dstate_eq_sym{n:nat}:forall (mu1 mu2: dstate n),
dstate_eq mu1 mu2-> dstate_eq mu2 mu1 .
Proof. intros  (mu1,IHmu1) (mu2,IHmu2).
unfold dstate_eq. simpl. intuition.
Qed.


Lemma  big_dapp_0{n:nat}: forall (n_0:nat) g (f:list (dstate n)),
(n_0=0)%nat -> big_dapp g f n_0 =d_empty n .
Proof. induction n_0. intros. destruct g.  simpl. reflexivity.
     simpl. reflexivity. intros. lia. 
Qed.

Lemma d_app_assoc': 
forall {n : nat} (mu1 mu2 mu3 : dstate n),
dstate_eq (d_app (d_app mu1 mu2) mu3) (d_app mu1 (d_app mu2 mu3)).
Proof.   unfold dstate_eq. unfold d_app. unfold StateMap.map2.
     simpl. intros n (mu1, IHmu1) (mu2, IHmu2) (mu3, IHmu3).
     simpl.  rewrite map_assoc. reflexivity.
Qed.

Lemma swap_app{n:nat} :forall (g:list R)  (f:(list (dstate n))) (n_0 i:nat),
length g =length f->n_0=length g->
 dstate_eq (big_dapp g f n_0) (big_dapp (swap_list g i) (swap_list f i) n_0).
Proof. induction g. intros.  
       apply dstate_eq_trans with (d_empty n).
       apply big_dapp_nil. left. reflexivity.
       apply dstate_eq_trans with ( (d_empty n)).
       unfold dstate_eq. reflexivity.
       apply dstate_eq_sym. apply big_dapp_nil.
       left. destruct i. reflexivity. simpl. reflexivity.
       induction f. intros.  
       apply dstate_eq_trans with (d_empty n).
       apply big_dapp_nil. right. reflexivity.
       apply dstate_eq_trans with ( (d_empty n)).
       unfold dstate_eq. reflexivity.
       apply dstate_eq_sym. apply big_dapp_nil.
       right. destruct i. reflexivity. simpl. reflexivity.
       
       induction n_0. intros. 
       repeat rewrite big_dapp_0. reflexivity. lia. lia.

        induction i. destruct g. destruct f.   simpl swap_list.
        unfold dstate_eq.
        reflexivity. intros. discriminate H.
        intros.
        simpl swap_list. destruct f. discriminate H.
        simpl. 
        destruct n_0. discriminate H0. 
        apply dstate_eq_trans with 
        ((d_app (d_app (d_scalar a a0)  (d_scalar r d)) (big_dapp g f n_0))).
        apply dstate_eq_sym.
        apply d_app_assoc'.  
        apply dstate_eq_trans with 
        ((d_app (d_app  (d_scalar r d) (d_scalar a a0)) (big_dapp g f n_0))).
        apply d_app_eq. apply d_app_comm.
        unfold dstate_eq. reflexivity.
        apply d_app_assoc'.
        intros. 
       simpl. destruct g; destruct f. 
       simpl. destruct n_0. unfold dstate_eq. reflexivity.
       unfold dstate_eq. reflexivity.
       discriminate H.   discriminate H. 
       apply dstate_eq_trans with (
        (d_app (d_scalar a a0)(big_dapp (swap_list (r :: g) i) (swap_list (d::f) i) n_0))
       ). 
       apply d_app_eq.  unfold dstate_eq. reflexivity.
       apply IHg.  injection H. intuition.
       injection H0. intuition.
      simpl.  unfold dstate_eq. reflexivity.
       
         
  
Qed.



Lemma swap_and{n:nat} :forall    (g:list (State_formula))
(f:(list (dstate n))) (n_0 i:nat),
length g =length f->n_0=length g->
  (big_and  f  g n_0) ->(big_and  (swap_list f i) (swap_list g i) n_0).
Proof. induction g; induction f; intros; try discriminate H.
     simpl. induction i; intuition. 
      induction i.  destruct f; destruct g. induction n_0.
    simpl. intuition. simpl in H1. simpl. apply H1.
    discriminate H. discriminate H. destruct n_0.
    intuition. simpl in H1.

    simpl. destruct n_0. discriminate H0.
  intuition. destruct n_0. simpl.
  destruct f; destruct g. assumption. discriminate H0.
  discriminate H0. discriminate H0. 
  simpl. destruct f; destruct g. assumption.
  discriminate H. discriminate H. 
  simpl in H1.  destruct H1.
  simpl. split. assumption. 
  apply IHg. injection H. intuition.
  injection H0. intuition.
  apply H2. Qed.





Lemma swap_length: forall {A:Type} (pF:list A) i,
length (swap_list pF i)= length pF .
Proof. induction pF; induction i; simpl; try reflexivity.
       destruct pF. simpl. reflexivity.
       simpl. reflexivity. destruct pF. simpl. reflexivity.
       simpl. f_equal. rewrite IHpF. simpl. reflexivity. 
  
  
Qed.




Local Open Scope R_scope.
Inductive sat_Assert {n:nat}: (dstate n)-> (Assertion)-> Prop:=
|sat_APro: forall (mu:dstate n) pF , 
                 WF_dstate mu -> distribution_formula pF -> sat_Pro mu  pF -> 
                 sat_Assert mu (APro pF)
|sat_ANpro: forall (mu:dstate n) nF (p_n:list R), 
                    (nF <> []) -> sat_Assert mu (npro_to_pro_formula nF p_n)
                    ->sat_Assert mu (ANpro nF).







                    Definition assert_implies (P Q : Assertion) : Prop :=
    forall (n:nat) (mu:dstate n), sat_Assert  mu P -> sat_Assert  mu Q.

Lemma  swap_get_pro:  forall pF1 i,
(get_pro_formula (swap_list pF1 i))=
swap_list (get_pro_formula pF1) i.
Proof. induction pF1. intros. destruct i. simpl. reflexivity.
     simpl. reflexivity.
     destruct i.
     intros. destruct a. destruct pF1. simpl.
     reflexivity. destruct p. simpl. reflexivity.
     destruct pF1. destruct a. simpl. reflexivity.
     destruct a.  destruct p.
     simpl. f_equal. apply IHpF1.   
  
Qed.



Lemma  swap_pro_to_npro:  forall pF1 i,
(pro_to_npro_formula (swap_list pF1 i))=
swap_list (pro_to_npro_formula pF1) i.
Proof. induction pF1. intros. destruct i. simpl. reflexivity.
     simpl. reflexivity.
     destruct i.
     intros. destruct a. destruct pF1. simpl.
     reflexivity. destruct p. simpl. reflexivity.
     destruct pF1. destruct a. simpl. reflexivity.
     destruct a.  destruct p.
     simpl. f_equal. apply IHpF1.   
  
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
Proof. induction pF. simpl. reflexivity. intros.
       destruct p_n. discriminate H.
      simpl. f_equal. apply IHpF.
       injection H. intuition.

Qed.

Lemma sum_over_list_swap: forall pF i,
sum_over_list_formula  pF=
sum_over_list_formula  (swap_list pF i) .
Proof.   
        induction pF; intros.  destruct i. simpl in *. reflexivity.
        simpl. reflexivity.
        
        destruct i. destruct pF. simpl. reflexivity. 
         simpl.  repeat rewrite sum_over_list_cons_formula in *.
        repeat rewrite <-Rplus_assoc.  rewrite (Rplus_comm  (fst p) (fst a)).
        reflexivity. 

         destruct pF. simpl.  reflexivity. simpl. 
         repeat rewrite sum_over_list_cons_formula in *. 
         f_equal. apply IHpF.
Qed.

Lemma Forall_swap{G:Type}: forall (pF:list G) (f:G->Prop) i,
Forall f pF  ->
Forall f
  (swap_list pF i).
Proof.  induction pF; intros.  destruct i. simpl in *.  assumption.
simpl. assumption.

destruct i. destruct pF. simpl. assumption. 
 simpl.  inversion_clear H. inversion_clear H1.
 econstructor. assumption. econstructor. assumption.
 assumption. 
 destruct pF. simpl.  assumption. simpl. 
 inversion_clear H.  econstructor. assumption.
 apply IHpF. assumption.
Qed.



Lemma distribution_formula_swap: forall pF i,
distribution_formula  pF ->
distribution_formula  (swap_list pF i) .
Proof. intros. inversion_clear H. econstructor.
       apply Forall_swap. assumption. 
       rewrite <-sum_over_list_swap. assumption.
Qed.

(* Lemma nth_swap_l{n:nat}: forall  (mu_n:list (dstate n)) i,
((i+1)<(length mu_n))%nat ->
(nth i mu_n (d_empty n))=(nth (i + 1) (swap_list mu_n i) (d_empty n)) .
Proof.  induction mu_n; intros. destruct i. simpl. reflexivity.
       simpl. reflexivity.
       destruct i. destruct mu_n. simpl in *. lia. 
       simpl. reflexivity. destruct mu_n.
       simpl. destruct i. simpl in *. lia. 
       simpl in *. lia. simpl.   destruct i.
       simpl. destruct mu_n. simpl in *. lia.  
       simpl. reflexivity. rewrite <-IHmu_n.
       simpl. reflexivity.  simpl in *. lia. 
Qed.


Lemma nth_swap_r{n:nat}: forall  (mu_n:list (dstate n)) i,
((i)>=0)%nat ->
(nth i mu_n (d_empty n))=(nth (i - 1) (swap_list mu_n (i-1)) (d_empty n)) .
Proof.  induction mu_n; intros. destruct i. simpl. reflexivity.
       simpl in *. rewrite sub_0_r in *. destruct i. simpl. reflexivity.
       simpl. reflexivity.
       destruct i. destruct mu_n. simpl in *. reflexivity.
       simpl in *.  
       simpl.  reflexivity. destruct mu_n.
       simpl. destruct i. simpl in *. lia. 
       simpl in *. lia. simpl.   destruct i.
       simpl. destruct mu_n. simpl in *. lia.  
       simpl. reflexivity. rewrite <-IHmu_n.
       simpl. reflexivity.  simpl in *. lia. 
Qed.


Lemma nth_swap_eq{n:nat}: forall  (mu_n:list (dstate n)) i i0,
i<>i0->
(nth i0 mu_n (d_empty n))=(nth i0 (swap_list mu_n i) (d_empty n)) .
Proof.  *)


Notation "P ->> Q" := (assert_implies P Q)
    (at level 90) : assert_scope.
Local Open Scope assert_scope.
Notation "P <<->> Q" :=
    ((P ->> Q) /\ (Q ->> P)) (at level 80) : assert_scope.
Theorem rule_POplusC: forall pF1 i,
APro ( pF1 ) ->>
APro (swap_list pF1 i).
Proof.  intros.  unfold assert_implies. 
intros.
inversion_clear H. inversion_clear H2. 
econstructor. intuition. apply distribution_formula_swap. 
assumption.
econstructor. 
assert(length (swap_list mu_n i)= length (swap_list pF1 i)).
repeat rewrite swap_length. assumption. apply H2. 
rewrite swap_get_pro.
rewrite swap_length. 
apply (dstate_eq_trans _ _ _ _ H3). 
apply swap_app. rewrite H. simpl.
apply get_pro_formula_length. symmetry.
 apply get_pro_formula_length.
 rewrite swap_pro_to_npro.  rewrite swap_length.
 apply swap_and.  rewrite pro_to_npro_formula_length. intuition.
 rewrite pro_to_npro_formula_length. intuition. assumption.
 apply Forall_swap. assumption.
Qed.


Fixpoint big_impiles (g: npro_formula ) (f:npro_formula) : Prop := 
           match g ,f with 
           |[], _ => False
           | _ ,[]=> False
           | hg::tg, hf:: tf =>  and (hg ->> hf)  (big_impiles tg tf) 
            end.

Lemma big_impiles_length:forall nF1 nF2,
big_impiles nF1 nF2 -> length nF1 =length nF2 .
Proof. induction nF1; induction nF2.
     simpl. intuition.
     simpl. intuition.
     simpl. intuition.
     simpl. intros. f_equal.
     destruct H. apply IHnF1 in H0. intuition.

  
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
       simpl. reflexivity.
       destruct p_n.
       simpl. discriminate H.
       simpl. f_equal. apply IHnF.
       injection H. intuition.  
  
Qed.

Lemma WF_dstate_eq{n}: forall (mu mu': dstate n),
dstate_eq mu mu'-> WF_dstate mu -> WF_dstate mu'.
Proof. unfold WF_dstate. unfold dstate_eq. 
      intros (mu,IHmu) (mu', IHmu').
      simpl. intros. rewrite <- H. 
     assumption.
Qed.
Lemma seman_eq: forall n (mu mu':dstate n) (F:State_formula),
dstate_eq mu mu'->
sat_State  mu F-> sat_State  mu' F.
Proof. intros n (mu, IHmu1) (mu', IHmu'). unfold dstate_eq. simpl. intros.
      inversion_clear H0. econstructor.
       apply WF_dstate_eq with (StateMap.Build_slist IHmu1).
       unfold dstate_eq. simpl. assumption. assumption.
      simpl in *. rewrite <-H. assumption.
Qed.

Lemma sat_Assert_to_State: forall n (mu:dstate n) (F:State_formula),
sat_Assert mu F <-> sat_State mu F.
Proof. split; intros. 
inversion_clear H. destruct p_n. inversion_clear H1.
unfold distribution_formula in H2. intuition.
inversion_clear H1. inversion_clear H3.
simpl in *.  destruct mu_n. 
discriminate H1. 
unfold distribution_formula in H2. 
destruct H2. rewrite sum_over_list_cons_formula in H3.
simpl in H3. rewrite sum_over_list_nil_formula in H3.
rewrite Rplus_0_r in H3. rewrite H3 in H4. 
simpl in *.  
assert(dstate_eq mu d). 
apply (dstate_eq_trans _ _ _ _ H4).
apply dstate_eq_trans with ((d_app d (d_empty n))).
apply d_app_eq. apply d_scalar_1_l. 
unfold dstate_eq. reflexivity. 
apply dstate_eq_trans with ((d_app (d_empty n) d)).
apply d_app_comm.  apply d_app_nil_mu.
apply seman_eq with d. apply dstate_eq_sym.
assumption. intuition.

econstructor. 
       discriminate. econstructor.
       inversion_clear H. intuition.
       assert (distribution_formula (npro_to_pro_formula F [1])).
       simpl. unfold distribution_formula. 
       intuition. rewrite sum_over_list_cons_formula.
       simpl. rewrite sum_over_list_nil_formula. lra.
      apply H0.  
      simpl. econstructor. 
      assert(length [mu]= length [(1, F)]).
      simpl. reflexivity. apply H0. simpl.
      apply dstate_eq_trans with ((d_app mu (d_empty n))).
      apply dstate_eq_trans with ((d_app (d_empty n) mu)).
      apply dstate_eq_sym. apply d_app_nil_mu.
      apply d_app_comm. simpl. 
      apply d_app_eq. apply dstate_eq_sym.
      apply d_scalar_1_l. unfold dstate_eq.
      reflexivity.  simpl. intuition. 
      econstructor. reflexivity. apply Forall_nil. 
Qed.

Lemma big_and_impiles{n:nat}: forall nF1 nF2  (mu_n:list (dstate n)),
big_and mu_n nF1 (length nF1) ->
big_impiles nF1 nF2 ->
big_and mu_n nF2 (length nF2).
Proof. induction nF1; destruct nF2;intros .
       simpl. simpl in H. assumption.
       simpl in *. destruct H0.
       simpl in *. destruct H0.
       simpl in *. destruct H0. 
       destruct mu_n. simpl in *.
       destruct H.   
       simpl in H.  destruct H.
       unfold assert_implies in H0.
       simpl. split. 
       assert( sat_Assert  d s).
       apply H0. rewrite sat_Assert_to_State. 
       assumption. rewrite sat_Assert_to_State in H3.
       assumption. 
       apply IHnF1. assumption.
       assumption. 
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


Theorem  rule_OCon: forall (nF1 nF2:npro_formula) (p_n: list R),
length nF1 =length p_n ->
big_impiles nF1 nF2 
->((npro_to_pro_formula nF1 p_n) ->> (npro_to_pro_formula nF2 p_n)).
Proof. intros.    unfold assert_implies. intros. 

inversion_clear H1. inversion_clear H4.
econstructor. intuition. 
apply distribution_formula_npro_to_pro with nF1.
assumption.
rewrite<- (big_impiles_length _ _ H0).
assumption. assumption. 
econstructor. rewrite npro_to_pro_formula_length.
rewrite npro_to_pro_formula_length in H1. 
rewrite<- (big_impiles_length _ _ H0). 
apply H1. assumption. rewrite<- (big_impiles_length _ _ H0).
assumption. rewrite (get_pro_formula_eq  nF1 _  _).
rewrite npro_to_pro_formula_length in H5.
rewrite npro_to_pro_formula_length. 
rewrite<- (big_impiles_length _ _ H0).
assumption.   
rewrite<- (big_impiles_length _ _ H0).
assumption. assumption. assumption.
rewrite<- (big_impiles_length _ _ H0).
assumption.   rewrite pro_npro_inv.
rewrite pro_npro_inv in H6.
rewrite npro_to_pro_formula_length in H6.
 rewrite npro_to_pro_formula_length.
 apply big_and_impiles with nF1. 
 assumption. assumption. 
 rewrite<- (big_impiles_length _ _ H0).
assumption. assumption. assumption.
rewrite<- (big_impiles_length _ _ H0).
assumption.  apply H7.
Qed.


Lemma d_scalar_assoc': forall n (p1 p2:R) (mu:dstate n), 
  dstate_eq (d_scalar p1 (d_scalar p2 mu))
 (d_scalar (Rmult p1  p2) mu).
 Proof.
  intros n p1 p2 (mu, IHmu). 
  induction mu. simpl. reflexivity.
          destruct a.  
          unfold d_scalar. unfold map. simpl.
          unfold d_scalar in IHmu0. unfold map in IHmu0. 
          simpl in IHmu0.
          inversion_clear IHmu.
          unfold dstate_eq. simpl.
          unfold dstate_eq in IHmu0.
          simpl in IHmu0.
          apply IHmu0 in H.
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
          rewrite H1. f_equal.
          intuition.
  Qed.

  

    
Lemma d_scalar_1_l': forall n (mu:dstate n), 
dstate_eq (d_scalar 1 mu)  mu.
Proof. intros n (mu, IHmu). 
        unfold d_scalar; unfold map;
        simpl; induction mu. reflexivity.
        destruct a. inversion_clear IHmu.
        unfold dstate_eq in IHmu0.
        simpl in IHmu0.
        apply IHmu0 in H.
        unfold dstate_eq. simpl.
        f_equal.
         rewrite Mscale_1_l. reflexivity.
        assumption.
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
Lemma WF_d_app{n:nat}: forall (mu mu':dstate n) (p1 p2:R),
(0<p1<=1/\0<p2<=1)-> (p1+p2<=1)->
WF_dstate mu -> WF_dstate mu'-> 
@WF_dstate n (d_app (d_scalar p1 mu) (d_scalar p2 mu')).
Proof. unfold WF_dstate. unfold d_app. unfold d_trace.
 unfold StateMap.map2.
 intros  (mu, IHmu) (mu', IHmu') p1 p2. simpl. 
 intros. 
 apply WF_d_app_aux. 
 apply WF_d_scalar_aux. intuition. intuition.
 apply WF_d_scalar_aux. intuition. intuition.
 rewrite d_trace_app.  repeat rewrite d_trace_scalar_aux.
 apply Rplus_mult_le_1'. intuition. intuition. intuition.
 apply WF_dstate_gt_0_aux. assumption. 
 apply WF_dstate_gt_0_aux. assumption.
 intuition. intuition. 
 apply WF_d_scalar_aux'. intuition. apply WF_dstate_aux'_to_WF_dstate_aux.
  intuition.
 apply WF_d_scalar_aux'. intuition. 
 apply WF_dstate_aux'_to_WF_dstate_aux.
 intuition.
Qed.


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
Proof. induction mu; simpl; intros.  destruct H1. 
       destruct a. inversion_clear H1.
       destruct mu.   
       simpl. econstructor.   assert(State_eval  F (s_scalar p (c, q))).
       apply s_seman_scalar. intuition.
       inversion_clear H0. intuition. intuition.
       unfold s_scalar in H1. simpl in H1.
       intuition. assumption. destruct p0.
       simpl. econstructor. 
       assert(State_eval  F (s_scalar p (c, q))).
       apply s_seman_scalar. intuition.
       inversion_clear H0. intuition. intuition.
       unfold s_scalar in H1. simpl in H1.
       intuition. apply IHmu. intuition. 
      inversion_clear H0. intuition. 
      simpl.  assumption.
Qed.



Local Open Scope R_scope.
Lemma d_seman_scalar: forall n (p:R) (mu:dstate n) (F:State_formula),
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

Lemma seman_find_state_aux{n:nat}:forall  (st: (cstate * qstate n)) (F: State_formula),
( WF_dstate_aux [st]) -> (State_eval_dstate F [st] <->
(forall x:cstate, (option_qstate (StateMap.Raw.find x [st]) <> Zero) -> (State_eval F 
(x, (option_qstate (StateMap.Raw.find x [st])))))).
Proof. intros. 
      split; intros.
      destruct st. simpl in *. inversion_clear H0.
      destruct (Cstate_as_OT.compare x c).
      simpl in *. destruct H1. reflexivity.
      simpl. unfold Cstate_as_OT.eq in e. rewrite e. assumption.
      destruct H1. reflexivity.
      destruct st.
      assert( option_qstate (StateMap.Raw.find (elt:=qstate n) c [(c, q)]) <>
     Zero ->
     State_eval F
       (c,
        option_qstate
          (StateMap.Raw.find (elt:=qstate n) c [(c, q)]))).
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
      
      
      
Lemma seman_find_aux{n}:forall  (mu:list (cstate * qstate n)) (F: State_formula),
Sorted.Sorted
  (StateMap.Raw.PX.ltk (elt:=qstate n)) mu->
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
        unfold Cstate_as_OT.eq in e.
        rewrite e. 
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
           (StateMap.Raw.find (elt:=qstate n) c ((c, q) :: (c0, q0) :: mu)))).

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
          (StateMap.Raw.find (elt:=qstate n) x ((c, q) :: (c0, q0) :: mu)))).
      apply H1.  simpl. 
      destruct (Cstate_as_OT.compare x c);
      try rewrite l in H3; try apply Cstate_as_OT.lt_not_eq in H3; try intuition.
      simpl in H4.    
      destruct (Cstate_as_OT.compare x c);
      try rewrite l in H3; try apply Cstate_as_OT.lt_not_eq in H3; try intuition.
Qed.

Lemma WF_sat_State{n:nat}: forall  (mu:dstate n) (F:State_formula), 
sat_State mu F -> StateMap.this mu <> [] /\ WF_dstate mu.
Proof. intros. 
      inversion_clear H. destruct mu as [mu IHmu].
      destruct mu.
      simpl in H1.  destruct H1.  
      split. discriminate. intuition.
Qed.

Lemma seman_find{n}:forall  (mu:dstate n) (F: State_formula),
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


Lemma State_eval_dstate_Forall{n}:forall (mu:list (cstate *qstate n)) F,
mu<>nil->
(State_eval_dstate F mu <-> Forall (fun x : state n => State_eval F x) mu).
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

Lemma L_trace_scale: forall n l c (M:Square (2^n)) , 
(scale c (@PMlpar_trace' n M l))=
(@PMlpar_trace' n ( scale c  M) l ) .
Proof. intros.   unfold PMlpar_trace'.
assert(forall i:nat, (i< (2^(l)))%nat->
(I (2 ^ (n - l)) ⊗ ⟨ i ∣_ (l) ×  (c.* M)
      × (I (2 ^ (n - l)) ⊗ ∣ i ⟩_ (l)) ) =
(c .* (I (2 ^ (n - l)) ⊗ ⟨ i ∣_ (l) × M
× (I (2 ^ (n - l)) ⊗ ∣ i ⟩_ (l))) )) .
intros. remember (I (2 ^ (n - l)) ⊗ ⟨ i ∣_ (l)) as A.
rewrite (Mscale_mult_dist_r _ _ _ c A M).
rewrite (Mscale_mult_dist_l _ _ _ c (A × M) _).
reflexivity. 
apply big_sum_eq_bounded in H.
rewrite H. 
rewrite <- big_sum_Mscale_l. reflexivity. 
Qed.

Local Open Scope nat_scope.
Lemma R_trace_plus: forall n l   (M N:Square (2^n)) , 
((@PMRpar_trace' n (M .+ N) l ))=
(@PMRpar_trace' n (M) l  ) .+  ((@PMRpar_trace' n (N) l  )).
Proof. intros.   unfold PMRpar_trace'. 
     rewrite (big_sum_eq_bounded 
     (fun i : nat =>
   ⟨ i ∣_ (l) ⊗ I (2 ^ (n - l)) × (M .+ N)
   × (∣ i ⟩_ (l) ⊗ I (2 ^ (n - l))))  
     (fun i : nat =>
     (⟨ i ∣_ (l) ⊗ I (2 ^ (n - l)) × M 
     × (∣ i ⟩_ (l) ⊗ I (2 ^ (n - l))) ) .+ 
     (⟨ i ∣_ (l) ⊗ I (2 ^ (n - l)) × N 
     × (∣ i ⟩_ (l) ⊗ I (2 ^ (n - l))) )
     )). assert(2^(n-l) =1*2^(n-l)).
      rewrite mul_1_l. reflexivity. destruct H.
     apply Msum_plus.  intros.
     assert(2 ^ l * 2 ^ (n - l)= 2 ^ n).
     rewrite <-Nat.pow_add_r. f_equal.
     rewrite Nat.add_comm.
    apply sub_add.  admit.  destruct H0.
    rewrite Mmult_plus_distr_l.
    rewrite Mmult_plus_distr_r. 
    reflexivity. 
Admitted.

Lemma L_trace_plus: forall n l   (M N:Square (2^n)) , 
((@PMlpar_trace' n (M .+ N) l ))=
(@PMlpar_trace' n (M) l  ) .+  ((@PMlpar_trace' n (N) l  )).
Proof. intros.   unfold PMlpar_trace'.
rewrite (big_sum_eq_bounded 
(fun i : nat =>
   I (2 ^ (n - l)) ⊗ ⟨ i ∣_ (l) × (M .+ N)
   × (I (2 ^ (n - l)) ⊗ ∣ i ⟩_ (l)))  
(fun i : nat =>
I (2 ^ (n - l)) ⊗ ⟨ i ∣_ (l) × M
× (I (2 ^ (n - l)) ⊗ ∣ i ⟩_ (l)) .+ 
I (2 ^ (n - l)) ⊗ ⟨ i ∣_ (l) × N
× (I (2 ^ (n - l)) ⊗ ∣ i ⟩_ (l))
)). assert(2^(n-l) =2^(n-l)*1).
 rewrite mul_1_r. reflexivity. destruct H.
apply Msum_plus.  intros.
assert(2 ^ (n-l) * 2 ^ l= 2 ^ n).
rewrite <-Nat.pow_add_r. f_equal.
apply sub_add.  admit.  destruct H0.
rewrite Mmult_plus_distr_l.
rewrite Mmult_plus_distr_r. 
reflexivity. 

Admitted.

Lemma PMtrace_scale: forall n l m c (M:Square (2^n)) , 
(scale c (@PMpar_trace n M l m))=
(@PMpar_trace n ( scale c  M) l m ) .
Proof. intros. unfold PMpar_trace. rewrite R_trace_scale.
rewrite L_trace_scale. reflexivity.
Qed.

Lemma PMtrace_plus: forall n l m  (M N:Square (2^n)) , 
((@PMpar_trace n (M .+ N) l m))=
(@PMpar_trace n (M) l m ) .+  ((@PMpar_trace n (N) l m )).
Proof. intros. unfold PMpar_trace. rewrite L_trace_plus.
rewrite R_trace_plus. reflexivity.
Qed.

Lemma  State_eval_plus{n:nat}: forall F c (q q0: qstate n),
WF_qstate q ->
WF_qstate q0->
State_eval F (c, q)->
State_eval F (c,q0) ->
@State_eval n F (c, q .+ q0) .
Proof.  
       induction F; intros;  intros.
      -apply state_eq_Pure with  (c, q0). 
       reflexivity. intuition.   
      -induction qs. simpl in *.
        rewrite Cdiv_unfold in *.
        rewrite trace_plus_dist.
        rewrite <-PMtrace_scale.
        assert(q= (@trace (2^n) q) .* (((C1 /  (@trace  (2^n) q))%C) .* q) ).
        rewrite Mscale_assoc. 
         rewrite Cdiv_unfold. 
       rewrite Cmult_assoc . 
       rewrite Cmult_comm.  
         rewrite Cmult_assoc . 
         rewrite Cinv_l.  
         rewrite Cmult_1_r . 
         rewrite Mscale_1_l. reflexivity.
          
         admit. 
         assert(q0= (@trace (2^n) q0) .* (((C1 /  (@trace  (2^n) q0))%C) .* q0) ).
        rewrite Mscale_assoc. 
         rewrite Cdiv_unfold. 
       rewrite Cmult_assoc . 
       rewrite Cmult_comm.  
         rewrite Cmult_assoc . 
         rewrite Cinv_l.  
         rewrite Cmult_1_r . 
         rewrite Mscale_1_l. reflexivity. admit.
         rewrite H3. rewrite H4.
          rewrite PMtrace_plus. 
          rewrite <-PMtrace_scale. 
          rewrite Cdiv_unfold in *. rewrite H1.
          rewrite <-PMtrace_scale. 
          rewrite Cdiv_unfold. rewrite H2.
        rewrite <-Mscale_plus_distr_l.
        rewrite Mscale_assoc. 
        rewrite<-H4. rewrite <-H3. 
         rewrite <-Cmult_assoc. rewrite Cinv_l.
         rewrite Cmult_1_l. rewrite Mscale_1_l. reflexivity.
           admit. 
      
        simpl in *. split. intuition.
        destruct H2. destruct H3. 
        destruct H1. destruct H5. 
        apply IHqs1 in H5. apply IHqs2 in H6.
        split. assumption. assumption. assumption.
        assumption.  
      -simpl in *. split. intuition.  split. intuition. intuition. 
      - simpl in *.  split. intuition. intuition. 
      -admit. 
      -admit.
Admitted.



Lemma d_seman_app_aux: forall n  (mu mu':list (cstate * qstate n))  (F:State_formula),
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
       inversion_clear H2. unfold Cstate_as_OT.eq in e.
       rewrite e. assumption.  
       destruct mu. simpl. rewrite map2_r_refl.
       inversion_clear H2. assumption.
       destruct mu'. rewrite map2_nil.  rewrite map2_l_refl.
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
Lemma d_seman_app: forall n (F:State_formula)  (mu mu':dstate n) (p0 p1:R),
(0 < p0 <= 1)->(0 < p1 <= 1)
->(0<(p0+p1)<=1)->
sat_State mu F  -> sat_State  (mu') F
-> sat_State (d_app (d_scalar p0 mu)
   (d_scalar p1 mu')) F.
Proof. intros n F (mu, IHmu) (mu', IHmu'); intros.
       inversion H2; subst. inversion H3; subst.
       apply sat_F. 
       apply WF_d_app.  intuition. intuition.
       assumption. assumption. 
       simpl. apply d_seman_app_aux. 
       apply WF_d_scalar_aux. assumption.
       assumption. 
       apply WF_d_scalar_aux. assumption.
       assumption. 
       apply d_seman_scalar_Qexp. intuition. 
       assumption. assumption. 
       apply d_seman_scalar_Qexp. intuition. 
       assumption. assumption. 
Qed.



Lemma d_trace_app'{n:nat}: forall (mu mu':dstate n),
WF_dstate mu -> WF_dstate mu'->
d_trace (d_app  mu mu') = (d_trace mu) + (d_trace mu').
Proof.  intros  (mu,IHmu) (mu',IHmu'). unfold WF_dstate. unfold d_trace.
    unfold d_app. unfold StateMap.map2. simpl. intros.
     rewrite <-WF_dstate_aux'_to_WF_dstate_aux in *.
     apply d_trace_app. intuition. intuition. 
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

Lemma  d_scalar_app_distr':forall {n : nat} (mu mu' : dstate n) (p : R),
dstate_eq (d_app (d_scalar p mu) (d_scalar p mu'))
  (d_scalar p (d_app mu mu')) .
Proof. unfold dstate_eq. unfold d_app. unfold StateMap.map2.
    unfold d_scalar. unfold StateMap.map.  intros n (mu,IHmu) (mu',IHmu') p.
    simpl. apply d_scalar_app_distr_aux.  
  
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


Theorem rule_OMerg:forall (p0 p1:R) (F:State_formula) (pF:pro_formula),
0< p0<1/\ 0< p1 <1->
 APro ((p0 , F) :: ( p1, F) :: pF)
 ->> APro (((p0+p1), F):: pF).
Proof. intros. unfold assert_implies. intros.

  inversion_clear H. inversion_clear H0.
  inversion_clear H4. 
  econstructor. intuition. unfold distribution_formula in *. 
  destruct H3. inversion_clear H3.  inversion_clear H9.
  split. econstructor. simpl in *. apply Rplus_le_le_0_compat.
  assumption. assumption. assumption. repeat rewrite sum_over_list_cons_formula in *.
  simpl in *. rewrite Rplus_assoc. assumption.
  destruct mu_n. discriminate H0.
  destruct mu_n. discriminate H0.
  simpl in H5 . simpl in H0. simpl in H6.
  econstructor.   
  assert(length (((d_app ((d_scalar (p0 / (p0 + p1)) d))
  (d_scalar (p1 / (p0 + p1)) d0)))::mu_n)= S (length pF) ).
  simpl. f_equal. injection H0. intuition. 
  simpl. apply H4.  
  simpl. apply (dstate_eq_trans _ _ _ _ H5).
  apply dstate_eq_trans with ((d_app (d_app (d_scalar p0 d)
 (d_scalar p1 d0)) (big_dapp (get_pro_formula pF) mu_n (length pF)))).
 apply dstate_eq_sym. apply d_app_assoc'. 
  apply d_app_eq.   
  apply dstate_eq_trans with (d_app (d_scalar (p0 + p1) (d_scalar (p0 / (p0 + p1)) d))
  ((d_scalar (p0 + p1) (d_scalar (p1 / (p0 + p1)) d0)))).
  apply d_app_eq; 
  [apply dstate_eq_trans with ((d_scalar  ((p0 + p1) *(p0 / (p0 + p1))) d))|
  apply dstate_eq_trans with ((d_scalar  ((p0 + p1) *(p1 / (p0 + p1))) d0))];
  [rewrite Rmult_div_assoc| | rewrite Rmult_div_assoc| ];
  [rewrite Rmult_comm| | rewrite Rmult_comm| ];
  [rewrite Rdiv_unfold| | rewrite Rdiv_unfold| ];
  [rewrite Rmult_assoc| | rewrite Rmult_assoc| ];
  [rewrite Rinv_r| | rewrite Rinv_r| ]; 
  try  rewrite Rmult_1_r.  unfold dstate_eq ;  reflexivity. lra.
    apply dstate_eq_sym.  apply d_scalar_assoc'.
   unfold dstate_eq ;  reflexivity.
  lra.  apply dstate_eq_sym.  apply d_scalar_assoc'.
  apply d_scalar_app_distr'.
  unfold dstate_eq ;  reflexivity. 
  simpl.  split.  apply d_seman_app. 
  split. rewrite Rdiv_unfold.
  apply Rmult_gt_0_compat. intuition. 
  apply Rinv_0_lt_compat. lra.
  apply (Rcomplements.Rdiv_le_1 p0 (p0+p1)). lra.
  lra.    split. rewrite Rdiv_unfold.
  apply Rmult_gt_0_compat. intuition. 
  apply Rinv_0_lt_compat. lra.
  apply (Rcomplements.Rdiv_le_1 p1 (p0+p1)). lra.
  lra. repeat rewrite Rdiv_unfold. 
  rewrite <-Rmult_plus_distr_r.
  rewrite Rinv_r. lra. lra. apply H6.
  apply H6. apply H6.  
  inversion_clear H7. inversion_clear H8.
  econstructor.  rewrite d_trace_app'.
  repeat rewrite d_trace_scalar.
  rewrite H4. rewrite H7.  rewrite <-Rmult_plus_distr_r.
  repeat rewrite Rdiv_unfold. rewrite <-Rmult_plus_distr_r.
  rewrite Rinv_r. rewrite Rmult_1_l. reflexivity.
  apply tech_Rplus. intuition. intuition.
  rewrite Rplus_comm. apply Rdiv_in01. intuition. intuition.
  apply Rdiv_in01. intuition. intuition.
   apply WF_d_scalar_aux.    apply Rdiv_in01. intuition. intuition.
  destruct H6.  apply WF_sat_State with F. assumption.
  apply WF_d_scalar_aux. rewrite Rplus_comm.
     apply Rdiv_in01. intuition. intuition.
     destruct H6. destruct H8. 
     apply WF_sat_State with F. assumption.
assumption. 
Qed.








Lemma  sat_State_dstate_eq: forall n (D:State_formula) (mu mu': dstate n),
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

Lemma d_trace_eq{n:nat}: forall (mu mu':dstate n),
dstate_eq mu mu' ->
d_trace mu = d_trace mu'.
Proof. unfold d_trace; unfold dstate_eq. intros.
        rewrite H. reflexivity.
        
Qed.


Lemma  sat_Pro_dstate_eq: forall n (D:pro_formula) (mu mu': dstate n),
dstate_eq mu mu'->
sat_Assert mu D-> sat_Assert mu' D.
Proof.  induction D; intros.  
        inversion_clear H0.
        unfold distribution_formula in H2.
        destruct H2. rewrite sum_over_list_nil_formula in H2.
        lra.
        inversion_clear H0. inversion_clear H3.
        destruct mu_n. discriminate H0. 
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


Lemma  sat_Npro_dstate_eq: forall n (D:npro_formula) (mu mu': dstate n),
dstate_eq mu mu'->
sat_Assert mu D-> sat_Assert mu' D.
Proof. intros. induction D. 
        inversion_clear H0. destruct H1. reflexivity. 
        inversion_clear H0.
        econstructor. assumption.
        apply sat_Pro_dstate_eq with mu. 
        assumption. apply H2.
Qed.



Lemma  sat_Assert_dstate_eq: forall n (D:Assertion) (mu mu': dstate n),
dstate_eq mu mu'->
sat_Assert mu D-> sat_Assert mu' D.
Proof. intros. induction D;   
        [apply sat_Pro_dstate_eq with mu|
        apply sat_Npro_dstate_eq with mu]; 
        intuition; intuition.
Qed.

Lemma d_app_not_nil:
forall {n : nat} (mu mu' : dstate n),
StateMap.this mu <> [] \/ StateMap.this mu' <> [] ->
StateMap.this (d_app mu mu') <> [] .
Proof. intros n (mu,IHmu) (mu',IHmu'). 
       simpl. intros. destruct H. apply map2_app_not_nil_l.
       intuition. 
       rewrite map2_comm.  
       apply map2_app_not_nil_l.
       intuition. 
  
Qed.


       
Lemma WF_sat_Pro{n:nat}: forall   (pF:pro_formula) (mu:dstate n), 
sat_Assert mu pF-> StateMap.this mu <> [] /\ WF_dstate mu.
Proof.  induction pF; intros.
      inversion_clear H.   unfold distribution_formula in H1.
      destruct H1. rewrite sum_over_list_nil_formula in H1.
      lra.  inversion_clear H. 
      inversion_clear H2. 
      destruct mu_n. discriminate H.
      destruct a.
      simpl in H3. simpl in H4. 
      destruct H4. 
      split. unfold dstate_eq in H3.
      rewrite H3. apply d_app_not_nil.
      left. apply d_scalar_not_nil.  admit. 
      apply WF_sat_State with s. assumption.
      assumption.
Admitted.
       
Lemma WF_sat_Npro{n:nat}: forall (nF:npro_formula)  (mu:dstate n) , 
sat_Assert mu nF-> StateMap.this mu <> [] /\ WF_dstate mu.
Proof.  intros.  inversion_clear H. apply (WF_sat_Pro _ _ H1) .
Qed.


Lemma WF_sat_Assert{n:nat}: forall (mu:dstate n) (D:Assertion), 
sat_Assert  mu D-> StateMap.this mu <> [] /\ WF_dstate mu.
Proof. intros. induction D. 
       apply (WF_sat_Pro _ _ H).
       apply (WF_sat_Npro _ _ H).
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




