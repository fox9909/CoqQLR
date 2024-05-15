Require Import Reals.
Require Import Coquelicot.Complex.
Require Import Strings.String.
Require Import Lists.List.
Require Import
  Coq.FSets.FMapList
  Coq.Structures.OrderedTypeEx.


(* From Quan Require Import QMatrix.
From Quan Require Import QVector.
From Quan Require Import PVector1. *)
From Quan Require Import Matrix.
From Quan Require Import Quantum.
From Quan Require Import QState.
From Quan Require Import Basic_Supplement.

Delimit Scope C_scope with C.
Local Open Scope C_scope.

(*-------------------------Syntax-----------------------------------*)
Inductive aexp : Type :=
  | ANum (n : nat)
  | AId (i : nat)            
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).

Definition X0 : nat := 0.
Definition X1 : nat := 1.
Definition X2 : nat := 3.

Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BNeq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BGt (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).

Coercion AId : nat >-> aexp.

Declare Custom Entry com.
Declare Scope com_scope.
Local Open Scope com_scope.
Notation "<{ e }>" := e (at level 0, e custom com at level 99) : com_scope.
Notation "( x )" := x (in custom com, x at level 99) : com_scope.
Notation "x" := x (in custom com at level 0, x constr at level 0) : com_scope.
Notation "f x .. y" := (.. (f x) .. y)
                  (in custom com at level 0, only parsing,
                  f constr at level 0, x constr at level 9,
                  y constr at level 9) : com_scope.
Notation "x + y"   := (APlus x y) (in custom com at level 50, left associativity).
Notation "x - y"   := (AMinus x y) (in custom com at level 50, left associativity).
Notation "x * y"   := (AMult x y) (in custom com at level 40, left associativity).
(*Notation "'true'"  := true (at level 1).*)
Notation "'true'"  := BTrue (in custom com at level 0).
(*Notation "'false'" := false (at level 1).*)
Notation "'false'" := BFalse (in custom com at level 0).
Notation "x <= y"  := (BLe x y) (in custom com at level 70, no associativity).
Notation "x > y"   := (BGt x y) (in custom com at level 70, no associativity).
Notation "x = y"   := (BEq x y) (in custom com at level 70, no associativity).
Notation "x <> y"  := (BNeq x y) (in custom com at level 70, no associativity).
Notation "x && y"  := (BAnd x y) (in custom com at level 80, left associativity).
Notation "'~' b"   := (BNot b) (in custom com at level 75, right associativity).

Inductive com : Type :=
  | CSkip
  | CAbort
  | CAsgn (i:nat) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com)
  | QInit (s e: nat) 
  | QUnit_One (s e:nat) (U: Square (2^(e-s)))
  | QUnit_Ctrl (s0 e0 s1 e1:nat) (U: Square (2^(e1-s1)))
  | QMeas (i : nat) (s e:nat).


Notation "'skip'"  :=
         CSkip (in custom com at level 0) : com_scope.
Notation "'abort'"  :=
         CAbort(in custom com at level 0) : com_scope.
Notation "x := y"  :=
         (CAsgn x y)
            (in custom com at level 0, x constr at level 0,
             y at level 85, no associativity) : com_scope.
Notation "x ; y" :=
         (CSeq x y)
           (in custom com at level 90,
            right associativity) : com_scope.
Notation "'if' x 'then' y 'else' z 'end'" :=
         (CIf x y z)
           (in custom com at level 89, x at level 99,
            y at level 99, z at level 99) : com_scope.
Notation "'while' x 'do' y 'end'" :=
         (CWhile x y)
           (in custom com at level 89, x at level 99,
            y at level 99) : com_scope.

Notation "( s e ) :Q= 0 "  :=
         (QInit s e)
            (in custom com at level 0, s  constr at level 0,
            e  constr at level 0,
              no associativity) : com_scope.
 
Notation " U  '[[' s e ']]' " :=
         (QUnit_One e U)
            (in custom com at level 0,  s at level 0,
            e at level 0,
              no associativity) : com_scope.

Notation " U  '[[' s0 e0 ']]' '[[' s1 e1 ']]' " :=
(QUnit_Ctrl s0 e0 s1 e1 U)
(in custom com at level 1,  s0 at level 0,
e0 at level 0,
no associativity) : com_scope.

Notation " x :=M '[[' s e ']]' " :=
         (QMeas x s e )
            (in custom com at level 1, s constr at level 0,
              no associativity) : com_scope.

Local Open Scope nat_scope.
Definition fact_in_coq : com :=
  <{ 1 := X0;
     X1 := 1;
     while 1 <> 0 do
       X1 := X0 * 1;
       1 := 1 - 1
     end }>.


(*-----------------------Semantics------------------------------------*)

Fixpoint aeval{n:nat} (st: state n) 
               (a : aexp) : nat :=
  match a with
  | ANum n => n
  | AId x => c_find x (fst st)                               
  | <{a1 + a2}> => (aeval st a1) + (aeval st a2)
  | <{a1 - a2}> => (aeval st a1) - (aeval st a2)
  | <{a1 * a2}> => (aeval st a1) * (aeval st a2)
  end.


Fixpoint beval{n: nat} (st : state n) 
               (b : bexp) : bool :=
  match b with
  | <{true}>      => true
  | <{false}>     => false
  | <{a1 = a2}>   => (aeval st a1) =? (aeval st a2)
  | <{a1 <> a2}>  => negb ((aeval st a1) =? (aeval st a2))
  | <{a1 <= a2}>  => (aeval st a1) <=? (aeval st a2)
  | <{a1 > a2}>   => negb ((aeval st a1) <=? (aeval st a2))
  | <{~ b1}>      => negb (beval st b1)
  | <{b1 && b2}>  => andb (beval st b1) (beval st b2)
  end.

Notation "∣ i ⟩_ n " := (Vec (2^n) i) (at level 0) :matrix_scope.
Notation "⟨ i ∣_ n " := (adjoint (Vec (2^n) i)) (at level 0) :matrix_scope.
Check ∣ 2 ⟩_ 4.

Fixpoint exp_U{n:nat} (U:Square (2^n)) (i:nat):(Square (2^n)):=
    match i with
    |0=> I (2^n)
    |S i'=> U × (exp_U U i')
    end.
Notation "U ^ i":=(exp_U U i).


Fixpoint big_app{n:nat} (f : nat -> list (cstate * qstate n)) (n_0 : nat) : list (cstate * qstate n) := 
  match n_0 with
  | 0 => nil
  | S n' =>StateMap.Raw.map2 option_app (big_app f n')  (f n')
  end.


  

Declare Scope state_scope.
Notation "mu1 +l mu2" :=
  (StateMap.Raw.map2 option_app mu1 mu2)
  (at level 70, no associativity)
  : state_scope.
Local Open Scope state_scope.


Local Open Scope com_scope.


Definition QInit_fun{n:nat} (s e:nat) (rho:(qstate n)):=
  big_sum (fun i:nat=>  (((I (2^(s))) ⊗ ((Vec (2^(e-s)) 0) × (Vec (2^(e-s)) i )†) ⊗ (I (2^(n-e))))) × rho
                         × (((I (2^(s))) ⊗ ((Vec (2^(e-s)) 0) × (Vec (2^(e-s)) i)†) ⊗ (I (2^(n-e))))† )) (2^(e-s)) .

  Inductive ceval_single{n:nat}: com-> list (cstate * (qstate n)) -> list (cstate * (qstate n)) -> Prop:=
  |E_nil:  forall  c, ceval_single c nil nil
  |E_Skip sigma rho mu:  ceval_single <{skip}> ((sigma,rho)::mu) ((sigma,rho)::mu)
  |E_Abort sigma rho mu: ceval_single <{abort}> ((sigma,rho)::mu) nil
  |E_Asgn sigma rho mu: forall x a mu', 
                   ceval_single (CAsgn x a) mu mu'
                -> ceval_single (CAsgn x a) ((sigma,rho)::mu) 
                    (StateMap.Raw.map2 option_app 
                    [((c_update x (aeval (sigma, rho) a) sigma), rho)] 
                    mu')
  |E_Qinit sigma rho mu: forall mu'(s e:nat),
                   ceval_single (QInit s e) mu mu'
                   -> ceval_single (QInit s e) ((sigma,rho)::mu) 
                   (StateMap.Raw.map2 option_app [(sigma, (QInit_fun s e rho))] mu')
  |E_Qunit_One sigma rho mu: forall mu' (s e:nat) (U: Square (2^(e-s))), 
                   (0<=s/\e<=n)
                 ->(WF_Unitary U)
                 -> ceval_single (QUnit_One s e U) mu mu'
                -> ceval_single (QUnit_One s e U) ((sigma,rho)::mu) 
                (StateMap.Raw.map2 option_app [(sigma, q_update ((I (2^(s)) ⊗ U ⊗ (I (2^(n-e))))) rho )] mu')
  |E_QUnit_Ctrl sigma rho mu: forall mu' (s0 e0 s1 e1:nat) (U: Square (2^(e1-s1))), 
                    (0<=s0)/\ (e0<=s1) /\ (e1<n)
                   ->(WF_Unitary U)
                   -> ceval_single (QUnit_Ctrl s0 e0 s1 e1 U) mu mu'
                   -> ceval_single (QUnit_Ctrl s0 e0 s1 e1 U) ((sigma,rho)::mu) 
                (StateMap.Raw.map2 option_app [(sigma, q_update 
                ((big_sum (fun i:nat =>@Mmult (2^(n)) (2^(n)) (2^(n))
                (I (2^(s0)) ⊗ (∣ i ⟩_ (e0-s0) × ⟨ i ∣_ (e0-s0) ) ⊗ (I (2^(n-e0)))) 
                 (I (2^(s1)) ⊗ (U ^ i) ⊗ (I (2^(n-e1))))) (2^(n)))) rho )] mu')
  |E_Meas sigma rho mu: forall mu' (i:nat) (s e:nat),
                  ceval_single (QMeas i s e) mu mu'
                  -> ceval_single (QMeas i s e) ((sigma,rho)::mu)
                  (StateMap.Raw.map2 option_app 
                  (big_app (fun j:nat=> 
                  [((c_update i j sigma), (q_update (((I (2^(s))) ⊗ ((Vec j (2^(e-s))) × (Vec j (2^(e-s)))†) ⊗ (I (2^(n-e))))) rho))] ) (2^(e-s))) mu' )               
  |E_Seq sigma rho mu : forall c1 c2 (mu1 mu2:list (cstate * (qstate n))),  
                  ceval_single c1 ((sigma,rho)::mu) mu1 
                  ->ceval_single c2 mu1 mu2
                  ->ceval_single (<{c1;c2}>) ((sigma,rho)::mu) mu2
  |E_IF_true sigma rho mu: forall (mu' mu'':list (cstate * (qstate n))) c1 c2 b, 
                        (beval (sigma, rho) b)=true
                        ->ceval_single (CIf b c1 c2) mu mu''
                        ->ceval_single c1 ([(sigma,rho)]) mu'
                        ->ceval_single (CIf b c1 c2) ((sigma,rho)::mu)  
                           (StateMap.Raw.map2 option_app mu' mu'')
  |E_IF_false sigma rho mu: forall (mu' mu'':list (cstate * (qstate n))) c1 c2 b, 
                      (beval (sigma, rho) b)=false
                      ->ceval_single (CIf b c1 c2) mu mu''
                      ->ceval_single c2 ([(sigma,rho)]) mu'
                      ->ceval_single (CIf b c1 c2) ((sigma,rho)::mu)  
                        (StateMap.Raw.map2 option_app mu' mu'')
  |E_While_true sigma rho mu: forall (mu' mu'' mu1:list (cstate * (qstate n))) c b, 
                        (beval (sigma, rho) b)=true
                        ->ceval_single (CWhile b c) mu mu''
                        ->ceval_single c [(sigma,rho)] mu1 
                        ->ceval_single (CWhile b c) mu1 mu'
                        ->ceval_single (CWhile b c) ((sigma,rho)::mu)  
                           (StateMap.Raw.map2 option_app mu' mu'')
  |E_While_false sigma rho mu: forall (mu':list (cstate * (qstate n))) c b, 
                      (beval (sigma, rho) b)=false
                      ->ceval_single (CWhile b c) mu mu'
                      ->ceval_single (CWhile b c) ((sigma,rho)::mu)  
                       (StateMap.Raw.map2 option_app [(sigma,rho)] mu').

(*------------------------------FV-----------------------------------------*)
Definition CSet:=NSet.t.
Fixpoint Free_aexp (a:aexp) : CSet :=
  match a with
  | ANum n => NSet.empty 
  | AId x => NSet.add x (NSet.empty)                      
  | <{a1 + a2}> => NSet.union (Free_aexp a1)  (Free_aexp a2)
  | <{a1 - a2}> => NSet.union (Free_aexp a1)  (Free_aexp a2)
  | <{a1 * a2}> => NSet.union (Free_aexp a1)  (Free_aexp a2)
  end.

Fixpoint Free_bexp (b:bexp):CSet:=
  match b with
    | <{a1 = a2}>   => NSet.union (Free_aexp a1)  (Free_aexp a2)
    | <{a1 <> a2}>  => NSet.union (Free_aexp a1)  (Free_aexp a2)
    | <{a1 <= a2}>  => NSet.union (Free_aexp a1)  (Free_aexp a2)
    | <{a1 > a2}>   => NSet.union (Free_aexp a1)  (Free_aexp a2)
    | <{~ b}>      => (Free_bexp b) 
    | <{b1 && b2}>  => NSet.union (Free_bexp b1)  (Free_bexp b2)
    |_=>NSet.empty
    end.

 Fixpoint Var (c:com): (CSet * QSet) :=
  match c with
    |<{ x:=a }> => (NSet.add x (Free_aexp a), NSet.empty)
    |<{ c1;c2 }> => (NSet.union (fst (Var c1)) (fst (Var c2)), NSet.union (snd (Var c1)) (snd (Var c2))) 
    |<{ if b then c1 else c2 end }>
         => (NSet.union (Free_bexp b) (NSet.union (fst (Var c1)) (fst (Var c2))), 
             (NSet.union (snd (Var c1)) (snd (Var c2))))
    |<{while b do c end}>
         => (NSet.union (Free_bexp b) (fst (Var c)), (snd (Var c)))
    |<{ ( s e):Q=0 }>
         => (NSet.empty, Qsys_to_Set s e)
    | QUnit_One s e U  
         =>(NSet.empty, Qsys_to_Set  s e)
    | QUnit_Ctrl s0 e0 s1 e1 U  
         =>(NSet.empty, NSet.union (Qsys_to_Set s0 e0) (Qsys_to_Set s1 e1))
    |<{ x :=M [[s e]] }>
         => (NSet.empty, Qsys_to_Set  s e )
    |_=>(NSet.empty, NSet.empty)
  end.  

Local Open Scope com_scope.
Fixpoint MVar (c:com): (CSet * QSet) :=
  match c with
    |<{ x:=a }> => (NSet.add x (Free_aexp a), NSet.empty)
    |<{ c1;c2 }> => (NSet.union (fst (MVar c1)) (fst (MVar c2)), NSet.union (snd (MVar c1)) (snd (MVar c2))) 
    |<{ if b then c1 else c2 end }>
         => ((NSet.union (fst (MVar c1)) (fst (MVar c2))), 
             (NSet.union (snd (MVar c1)) (snd (MVar c2))))
    |<{while b do c end}>
         => MVar c
    |<{ ( s e ):Q=0 }>
         => (NSet.empty, Qsys_to_Set  s e)
    | QUnit_One s e U  
         =>(NSet.empty, Qsys_to_Set s e)
    | QUnit_Ctrl s0 e0 s1 e1 U  
         =>(NSet.empty, NSet.union (Qsys_to_Set s0 e0) (Qsys_to_Set s1 e1))
    |<{ x :=M [[ s e]] }>
         => (NSet.empty, Qsys_to_Set s e  )
    |_=>(NSet.empty, NSet.empty)
  end.




  (*-----------------------------------Properties-----------------------------------------------*)
(*linear combination*)


(* Definition strong_ind{ n:nat} (P : list (cstate * qstate n) ->Prop) : Prop :=
  P [] /\ 
  (forall (a:(cstate * qstate n)) (l':list (cstate * qstate n)),
  P l' -> P (StateMap.Raw.map2 option_app [a] l')).


  Lemma dstate_ind{n}: forall (P: list (cstate * qstate n)->Prop) 
  (mu:list (cstate * qstate n)), 
  Sorted.Sorted (StateMap.Raw.PX.ltk (elt:=qstate n)) mu ->
  strong_ind P -> ( P mu).
  (* Proof.  intros. unfold strong_ind in H. destruct H.
         -induction mu. intuition.
         - inversion_clear H0. assert(a::mu= StateMap.Raw.map2 option_app [a] mu).
           destruct a. induction mu. simpl. reflexivity.
           destruct a.
           simpl. destruct (Cstate_as_OT.compare c c0).
           rewrite map2_r_refl. reflexivity.
          inversion_clear H3.
          apply Cstate_as_OT.lt_not_eq in H0.
          simpl in H0. intuition. 
          inversion_clear H3. 
          unfold StateMap.Raw.PX.ltk in H0.
           rewrite H0 in l. simpl in l.
           apply Cstate_as_OT.lt_not_eq in l. 
           intuition. 
           rewrite H0. apply H1. apply IHmu.
           intuition.  *)
  Admitted. *)

  (* Lemma dstate_ind': forall (n:nat ) (P: list (cstate * qstate n)->Prop), 
  strong_ind P -> (forall (mu:list (cstate * qstate n)), P mu).
  Proof. Admitted. *)




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

(* Definition list_ind2 :
  forall {n : nat} (P : list(cstate * qstate n) -> Prop),
  P [] ->
  (forall (a: (cstate *qstate n)) (l':list (cstate * qstate n)),
    P l' -> P (StateMap.Raw.map2 option_app [a] l')) ->
  forall (mu:list(cstate * qstate n)),  Sorted.Sorted (StateMap.Raw.PX.ltk (elt:=qstate n)) mu
  -> P mu.
Proof. Admitted. *)
  Ltac discrim' H c q:=
    apply (map2_app_not_nil_l [(c, q)]) in H; 
    try match goal with 
    H1: False |- _ => destruct H1
    end; discriminate.

Lemma ceval_nil{n:nat}: forall (mu:list (cstate *qstate n)) c,
ceval_single c [] mu-> mu=nil.
Proof. intros. inversion H ;subst; try reflexivity.
Qed.

Lemma ceval_skip_1{n:nat}: forall (mu mu':list (cstate *qstate n)),
ceval_single <{skip}> mu mu'->mu=mu'.
Proof.   induction mu; intros; inversion H; subst; try
        reflexivity. Qed.



(* Lemma app_cons{n:nat}: forall (a: (state n)) (mu:list (cstate *qstate n)),
Sorted.Sorted (StateMap.Raw.PX.ltk (elt:=qstate n)) (a :: mu)->
a::mu = StateMap.Raw.map2 option_app [a] mu  .
Proof. intros. destruct a as [c q]; induction mu. reflexivity.
 destruct a. simpl; destruct (Cstate_as_OT.compare c c0); try rewrite map2_r_refl ;
 try reflexivity; inversion_clear H; inversion_clear H1. 
 apply Cstate_as_OT.lt_not_eq in H; simpl in H.
 rewrite e0 in H. intuition. unfold StateMap.Raw.PX.ltk in H. rewrite H in l.
 simpl in l.
  apply Cstate_as_OT.lt_not_eq in l. 
  intuition. 
Qed. *)


(* Ltac app_sovle:=
  match goal with 
  H : Sorted.Sorted (StateMap.Raw.PX.ltk (elt:=qstate ?s ?e)) (?a :: ?mu)
  |- _ => 
   assert(a::mu = StateMap.Raw.map2 option_app [a] mu)
  end; try apply app_cons; try intuition; 
  match goal with 
  H0: ?a :: ?mu = ([?a] +l ?mu) |- _ => rewrite H0 end. *)

  (* destruct (Cstate_as_OT.compare c c0).
  rewrite map2_r_refl. reflexivity.
 inversion_clear H3.
 apply Cstate_as_OT.lt_not_eq in H0.
 simpl in H0. intuition. 
 inversion_clear H3. 
 unfold StateMap.Raw.PX.ltk in H0.
  rewrite H0 in l. simpl in l.
  apply Cstate_as_OT.lt_not_eq in l. 
  intuition. 
  rewrite H0. *)


Lemma ceval_skip{n:nat}: forall (mu:list (cstate *qstate n)),
ceval_single <{skip}> mu mu.
Proof. induction mu; intros. apply E_nil.
 destruct a.
apply E_Skip.
Qed.


Lemma ceval_abort{n:nat}: forall (mu:list (cstate *qstate n)),
ceval_single <{abort}> mu [].
Proof. induction mu; intros.  apply E_nil.
destruct a.
apply E_Abort.
Qed.



Lemma ceval_abort_1{n:nat}: forall (mu mu':list (cstate *qstate n)),
ceval_single <{abort}> mu mu'->mu'= [].
Proof. induction mu; intros; inversion H;subst;
reflexivity.
Qed.

Lemma ceval_seq{n:nat}: forall c1 c2 (mu mu' mu'':list (cstate *qstate n)),
ceval_single c1 mu mu'->
ceval_single c2 mu' mu''->
ceval_single <{c1;c2}> mu mu''.
Proof. induction mu. intros. inversion H;subst.
inversion H0;subst.
apply E_nil.
intros.  destruct a. apply E_Seq with mu'.
intuition. intuition. 
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

Import Sorted.

(* Lemma app_nil{  n : nat}: forall sigma (rho: qstate n),
[(sigma, rho)] = ([(sigma, rho)] +l nil).
Proof. simpl. intuition.
Qed.

Lemma map_assoc: forall n (x y z: list (cstate *qstate n)),
(x +l (y +l z))=(x +l y +l z).
Proof. Admitted. *)


(* Lemma ceval_3{n:nat}:  forall c  (y x  mu mu1: list (cstate *qstate n)),
Sorted.Sorted (StateMap.Raw.PX.ltk (elt:=qstate n)) y->
ceval_single c (StateMap.Raw.map2 option_app x y) mu ->
ceval_single c x mu1 ->
exists mu2 , ceval_single c y mu2.
Proof. induction y; intros. intros. exists nil.
     apply E_nil. rewrite app_cons in H0.  rewrite map_assoc in H0.
     inversion_clear H. 
     assert( exists mu2 : list (cstate * qstate n), ceval_single c y mu2).
     assert(exists ceval_single c (x +l [a]) )
     apply (IHy _ _ _ H2 H0 _). *)




(* Lemma ceval_4{n:nat}:  forall c sigma (rho: qstate n) (mu mu': list (cstate *qstate n)),
Sorted.Sorted (StateMap.Raw.PX.ltk (elt:=qstate n)) mu->
ceval_single c ([(sigma, rho)] +l mu) mu' ->
exists mu1 mu2 , (ceval_single c [(sigma,rho)] mu1
/\ ceval_single c mu mu2 /\
mu'=StateMap.Raw.map2 option_app mu1 mu2).
Proof. induction c; intros. inversion H0; subst.
      - symmetry in H3. try discrim' H3 sigma rho.
        exists ([(sigma, rho)]). exists  mu. 
        split. apply ceval_skip. apply Sorted_cons.
        apply Sorted_nil. apply HdRel_nil.
        split. apply ceval_skip. intuition. 
        apply H1.
      -exists nil. exists nil. split. apply ceval_abort.
      apply Sorted_cons. apply Sorted_nil. apply HdRel_nil.
      split. apply ceval_abort. intuition. inversion H0 ;subst.
      symmetry in H3. try discrim' H3 sigma rho. simpl. reflexivity.
      -inversion H0; subst. symmetry in H3. try discrim' H3 sigma rho.
      exists ([(c_update i (aeval (sigma, rho) a) sigma, rho)]).
      exists mu'0. split. rewrite app_nil. rewrite (app_nil (c_update i (aeval (sigma, rho) a) sigma)).
      apply E_Asgn. apply E_nil. split. 
      simpl in H0. rewrite<- H4 in H0.  *)
      Lemma ceval_3'{n:nat}: 
       forall b c,
      (forall  x y mu : list (cstate * qstate n),
      ceval_single c (x +l y) mu ->
      exists mu1 mu2 : list (cstate * qstate n),
        ceval_single c x mu1 /\
        ceval_single c y mu2 /\ mu = (mu1 +l mu2))->

       (forall (mu mu' : list (cstate *qstate n)),
      ceval_single <{ while b do c end }> mu mu' ->
      (forall x y ,  mu=(StateMap.Raw.map2 option_app x y)->
      exists mu1 mu2 , (ceval_single <{ while b do c end }> x mu1
      /\ceval_single <{ while b do c end }> y mu2 
      /\mu'=StateMap.Raw.map2 option_app mu1 mu2))).
      Proof. intros b c Hc mu mu' H.

      remember <{while b do c end}> as original_command eqn:Horig. 
      induction H;  try inversion Horig; subst.
       intros. admit.

       
       destruct x; destruct y;
       intros. discriminate H3.
       destruct p.
       simpl in H3. 
       rewrite map2_r_refl in H3.
      
       exists []. exists ((mu' +l mu'')).
       split. apply E_nil. split. 
       admit. simpl. rewrite map2_r_refl. reflexivity.

       destruct p.
       simpl in H3. 
       rewrite map2_l_refl in H3.

       exists ((mu' +l mu'')). exists nil.
       split.  admit.
       split. apply E_nil. 
       admit.

       destruct p. destruct p0.
       simpl in H3.
       destruct (Cstate_as_OT.compare c0 c1).
       injection H3. intros. 
 

       assert( exists mu1 mu2 : list (cstate * qstate n),
       ceval_single <{ while b do c end }> x mu1 /\
       ceval_single <{ while b do c end }> ((c1, q0) :: y) mu2 /\
       mu'' = (mu1 +l mu2)).

       apply IHceval_single1.
        reflexivity. apply H4.
        destruct H7. destruct H7.
        exists (mu' +l x0).
        exists x1.
        split. rewrite<-H6. rewrite <-H5.
        apply E_While_true with mu1.
        assumption. intuition. intuition. 
        intuition. 
        split. intuition. admit.

        injection H3. intros.


        assert(exists mu2 mu3 : list (cstate * qstate n),
        ceval_single c [(c0,q)] mu2 /\ ceval_single c [(c0,q0)] mu3 /\ mu1 = (mu2 +l mu3)).
        apply (Hc [(c0, q)] [(c0, q0)] mu1).

        rewrite <-H6. 
        simpl.  
        destruct (Cstate_as_OT.compare sigma sigma).
        admit. rewrite <-H5.
          assumption.
          
          admit.
  

          destruct H7. destruct H7.
 assert(exists mu1 mu2 : list (cstate * qstate n),
 ceval_single <{ while b do c end }> x mu1 /\
 ceval_single <{ while b do c end }> y mu2 /\ mu'' = (mu1 +l mu2)).

 apply IHceval_single1. reflexivity. assumption.
 destruct H8. destruct H8. 


 destruct H7. destruct H9. 

 assert(exists mu1 mu2 : list (cstate * qstate n),
 ceval_single <{ while b do c end }> x0 mu1 /\
 ceval_single <{ while b do c end }> x1 mu2 /\ mu' = (mu1 +l mu2)).
 apply IHceval_single3.
 reflexivity. assumption. destruct H11. destruct H11.

          exists (x4 +l x2). 
          exists (x5 +l x3).
          split. 
          apply E_While_true with x0.
          rewrite <-H6. admit.
          intuition. assumption.
          intuition. split.
          apply E_While_true with x1.
          admit.

          intuition. 
      unfold Cstate_as_OT.eq in e.
      rewrite <-e.
          intuition. intuition.
          admit.
    
          injection H3. intros.


        assert( exists mu1 mu2 : list (cstate * qstate n),
        ceval_single <{ while b do c end }> ((c0,q)::x) mu1 /\
        ceval_single <{ while b do c end }> y mu2 /\ mu'' = (mu1 +l mu2)).
        apply IHceval_single1.
        reflexivity. simpl.
        apply H4. destruct H7. 
        destruct H7. 
        exists (x0).
        exists (mu' +l x1).
        split. intuition.
        split. apply E_While_true with mu1.
        admit.
        intuition. admit.
        intuition. 
        admit. 


       admit.

         



       Admitted. 
      




      
      




      (* Lemma ceval_3{n:nat}:  forall c (mu mu' : list (cstate *qstate n)),
      ceval_single c mu mu' ->
      (forall x y ,  mu=(StateMap.Raw.map2 option_app x y)->
      exists mu1 mu2 , (ceval_single c x mu1
      /\ceval_single c y mu2 
      /\mu'=StateMap.Raw.map2 option_app mu1 mu2)).
      Proof. 
            induction c. 
           - intros. exists x. exists y.
             split. apply ceval_skip. 
             split. apply ceval_skip.
             apply ceval_skip_1 in H0.
             rewrite <-H0.
             intuition. 
           - intros. exists nil. exists nil. 
            split. apply ceval_abort. 
            split. apply ceval_abort.
            simpl. apply ceval_abort_1 in H0.
            intuition.
           -intros. revert x. induction x; induction y; intros.
             exists nil. exists nil.
             split. apply E_nil. split. apply E_nil.
             simpl. simpl in H. rewrite H in H0.
             inversion_clear H0. reflexivity. 
             destruct a0. simpl in H. rewrite map2_r_refl in H.
             rewrite H in H0.
             inversion H;subst. 
             exists nil. exists mu'.
             split. apply E_nil. split. intuition.
             rewrite map2_nil_l. rewrite map2_r_refl. reflexivity.
             destruct a0. simpl in H. rewrite map2_l_refl in H.
             rewrite H in H0.
             inversion H;subst. 
             exists (mu').
             exists nil.
             split.  intuition. split.  apply E_nil.
             rewrite map2_nil. rewrite map2_l_refl. reflexivity.
             rewrite H in H0. 
             destruct a0. destruct a1. simpl in H0.
             destruct (Cstate_as_OT.compare c c0).
             inversion H0;subst.
             apply (IHx ((c0, q0) :: y) _ _ )in H7.
            destruct H7. destruct H0.
            destruct H0. destruct H1. 
            remember (StateMap.Raw.map2 option_app
            [(c_update i (aeval (c, q) a) c, q)] x0).
            exists t. exists x1.
            split. rewrite Heqt. apply E_Asgn.
            intuition. split. intuition. 
            rewrite H2. rewrite Heqt. admit.
            inversion H;subst.
            apply IHx in H6. destruct H6. destruct H0.
            destruct H0. destruct H1.
            remember (StateMap.Raw.map2 option_app
            [(c_update i (aeval (c, q) a) c, q)] x0).
            remember (StateMap.Raw.map2 option_app
            [(c_update i (aeval (c0, (q0)) a) c0, q0)] x1).
            exists t. exists t0.
            split. rewrite Heqt. 
            apply E_Asgn. intuition. 
            split. rewrite Heqt0. apply E_Asgn. intuition.
            rewrite H2. rewrite Heqt. rewrite Heqt0.
            admit. inversion H;subst.
            apply IHy in H6. 
            destruct H6. destruct H0.
            destruct H0. destruct H1.
            exists x0. 
            remember (StateMap.Raw.map2 option_app [(c_update i (aeval (c0, q0) a) c0, q0)] x1).
            exists t. 
            rewrite Heqt. split. intuition.
            split. apply E_Asgn. intuition.
            rewrite H2. admit.
     
          -intros. inversion H; subst.
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
     -- induction x; induction y; intros.
        simpl in H. inversion_clear H.
        exists nil. exists nil.
        split. apply E_nil. split. apply E_nil.
        simpl. reflexivity.
        destruct a. simpl in H. rewrite map2_r_refl in H.
        exists nil. exists (mu).
        split. apply E_nil. split. intuition.
        rewrite map2_nil_l. rewrite map2_r_refl. reflexivity.
        destruct a. simpl in H. rewrite map2_l_refl in H.
        exists (mu).
        exists nil.
        split.  intuition. split.  apply E_nil.
        rewrite map2_nil. rewrite map2_l_refl. reflexivity.
        destruct a. destruct a0. simpl in H.
        destruct (Cstate_as_OT.compare c c0).
        inversion H;subst.
        apply IHx in H8. destruct H8. destruct H0.
        destruct H0. destruct H1. 
        exists (StateMap.Raw.map2 option_app mu' x0). exists x1.
        split.  apply E_IF_true. intuition. intuition.
        intuition. split. intuition. 
        rewrite H2.  admit.
        apply IHx in H8. destruct H8. destruct H0.
        destruct H0. destruct H1. 
        exists (StateMap.Raw.map2 option_app mu' x0). exists x1.
        split.  apply E_IF_false. intuition. intuition.
        intuition. split. intuition. 
        rewrite H2.  admit.
        
        inversion_clear H.
        apply IHx in H1. destruct H1. destruct H.
        destruct H. destruct H1.
        assert(exists mu1 mu2 : list (cstate * qstate n),
        ceval_single c1 [(c,q)] mu1 /\
        ceval_single c1 [(c, q0)] mu2 /\
        mu' = StateMap.Raw.map2 option_app mu1 mu2).
        apply IHc1. simpl.  destruct (Cstate_as_OT.compare c c).
        apply Cstate_as_OT.lt_not_eq in l. intuition.
        intuition.  apply Cstate_as_OT.lt_not_eq in l. intuition.
        destruct H4. destruct H4. destruct H4. destruct H5. 
        exists (StateMap.Raw.map2 option_app x2 x0). 
        exists ((StateMap.Raw.map2 option_app x3 x1)).
        split.  apply E_IF_true. rewrite (state_eq_bexp _ (c, q .+ q0)).
        intuition. intuition.
        intuition.  intuition.   split.  apply E_IF_true. rewrite (state_eq_bexp _ (c, q .+ q0)).
        intuition. intuition. 
        intuition.  unfold Cstate_as_OT.eq in e. rewrite <-e. intuition.
        rewrite H6. rewrite H3.  admit.
        
        apply IHx in H1. destruct H1. destruct H.
        destruct H. destruct H1.
        assert(exists mu1 mu2 : list (cstate * qstate n),
        ceval_single c2 [(c,q)] mu1 /\
        ceval_single c2 [(c, q0)] mu2 /\
        mu' = StateMap.Raw.map2 option_app mu1 mu2).
        apply IHc2. simpl.  destruct (Cstate_as_OT.compare c c).
        apply Cstate_as_OT.lt_not_eq in l. intuition.
        intuition.  apply Cstate_as_OT.lt_not_eq in l. intuition.
        destruct H4. destruct H4. destruct H4. destruct H5. 
        exists (StateMap.Raw.map2 option_app x2 x0). 
        exists ((StateMap.Raw.map2 option_app x3 x1)).
        split.  apply E_IF_false. rewrite (state_eq_bexp _ (c, q .+ q0)).
        intuition. intuition.
        intuition.  intuition.   split.  apply E_IF_false. rewrite (state_eq_bexp _ (c, q .+ q0)).
        intuition. intuition. 
        intuition.  unfold Cstate_as_OT.eq in e. rewrite <-e. intuition.
        rewrite H6. rewrite H3.  admit.
        
        inversion H;subst.
        apply IHy in H8. destruct H8. destruct H0.
        destruct H0. destruct H1. 
        exists x0. exists (StateMap.Raw.map2 option_app mu' x1).
        split. intuition.  split.
        apply E_IF_true. intuition. intuition.
        intuition.  
        rewrite H2.  admit.
        apply IHy in H8. destruct H8. destruct H0.
        destruct H0. destruct H1. 
        exists x0. exists (StateMap.Raw.map2 option_app mu' x1).
        split. intuition.  split.
        apply E_IF_false. intuition. intuition.
        intuition.  
        rewrite H2.  admit.
        
    --intros.   remember <{while b do c end}> as original_command eqn:Horig. 

    induction H;try inversion_clear Horig. 
    admit. 

    
    
    
    
    
    
    
    
    
    
    induction x; induction y; intros.
    simpl in H. inversion_clear H.
    exists nil. exists nil.
    split. apply E_nil. split. apply E_nil.
    simpl. reflexivity.
    destruct a. simpl in H. rewrite map2_r_refl in H.
    exists nil. exists (mu).
    split. apply E_nil. split. intuition.
    rewrite map2_nil_l. rewrite map2_r_refl. reflexivity.
    destruct a. simpl in H. rewrite map2_l_refl in H.
    exists (mu).
    exists nil.
    split.  intuition. split.  apply E_nil.
    rewrite map2_nil. rewrite map2_l_refl. reflexivity.
    destruct a. destruct a0. simpl in H.
    destruct (Cstate_as_OT.compare c0 c1).
    inversion H;subst.
    apply IHx in H7. destruct H7. destruct H0.
    destruct H0. destruct H1. 
    exists (StateMap.Raw.map2 option_app mu' x0). exists x1.
    split.  apply E_While_true with mu1. intuition. intuition.
    intuition. intuition. split. intuition. 
    rewrite H2.  admit.
    apply IHx in H7. destruct H7. destruct H0.
    destruct H0. destruct H1. 
    exists (StateMap.Raw.map2 option_app [(c0,q)] x0). exists x1.
    split.  apply E_While_false. intuition. intuition.
     split. intuition. 
    rewrite H2.  admit.
    
    inversion_clear H.
    apply IHx in H1. destruct H1. destruct H.
    destruct H. destruct H1.
    inversion_clear H2. 
    assert(exists mu1' mu2 : list (cstate * qstate n),
    ceval_single (c) [(c0,q)] mu1' /\
    ceval_single (c) [(c1, q0)] mu2 /\
    mu1 = StateMap.Raw.map2 option_app mu1' mu2).
    apply IHc. simpl. unfold Cstate_as_OT.eq in e.
    subst. destruct (Cstate_as_OT.compare c1 c1).
    apply Cstate_as_OT.lt_not_eq in l.  intuition.
    (* intuition.
     apply Cstate_as_OT.lt_not_eq in l. intuition.
    destruct H2. destruct H2. destruct H2. destruct H6. 
    rewrite H7 in H5.
    exists (StateMap.Raw.map2 option_app x2 x0). 
    exists ((StateMap.Raw.map2 option_app x3 x1)).
    split.  apply E_IF_true. rewrite (state_eq_bexp _ (c, q .+ q0)).
    intuition. intuition.
    intuition.  intuition.   split.  apply E_IF_true. rewrite (state_eq_bexp _ (c, q .+ q0)).
    intuition. intuition. 
    intuition.  unfold Cstate_as_OT.eq in e0. rewrite <-e0. intuition.
    rewrite H6. rewrite H3.  admit. *)
    
    
     Admitted. *)


  Lemma ceval_3''{n:nat}:  forall c  ( x y mu: list (cstate *qstate n)),
  ceval_single c (StateMap.Raw.map2 option_app x y) mu ->
  exists mu1 mu2 , (ceval_single c x mu1
  /\ceval_single c y mu2 
  /\mu=StateMap.Raw.map2 option_app mu1 mu2).
  Proof. 
  
  
  
        induction c. 
       - intros. exists x. exists y.
         split. apply ceval_skip. 
         split. apply ceval_skip.
         apply ceval_skip_1 in H. intuition. 
       - intros. exists nil. exists nil. 
        split. apply ceval_abort. 
        split. apply ceval_abort.
        simpl. apply ceval_abort_1 in H.
        intuition.
       - induction x; induction y; intros.
         exists nil. exists nil.
         split. apply E_nil. split. apply E_nil.
         simpl. simpl in H. inversion_clear H. reflexivity. 
         destruct a0. simpl in H. rewrite map2_r_refl in H.
         inversion H;subst. 
         exists nil. exists ((StateMap.Raw.map2 option_app
         [(c_update i (aeval (c, q) a) c, q)] mu')).
         split. apply E_nil. split. intuition.
         rewrite map2_nil_l. rewrite map2_r_refl. reflexivity.
         destruct a0. simpl in H. rewrite map2_l_refl in H.
         inversion H;subst. 
         exists ((StateMap.Raw.map2 option_app
         [(c_update i (aeval (c, q) a) c, q)] mu')).
         exists nil.
         split.  intuition. split.  apply E_nil.
         rewrite map2_nil. rewrite map2_l_refl. reflexivity.
         destruct a0. destruct a1. simpl in H.
         destruct (Cstate_as_OT.compare c c0).
         inversion H;subst.
        apply IHx in H6. destruct H6. destruct H0.
        destruct H0. destruct H1. 
        remember (StateMap.Raw.map2 option_app
        [(c_update i (aeval (c, q) a) c, q)] x0).
        exists t. exists x1.
        split. rewrite Heqt. apply E_Asgn.
        intuition. split. intuition. 
        rewrite H2. rewrite Heqt. admit.
        inversion H;subst.
        apply IHx in H6. destruct H6. destruct H0.
        destruct H0. destruct H1.
        remember (StateMap.Raw.map2 option_app
        [(c_update i (aeval (c, q) a) c, q)] x0).
        remember (StateMap.Raw.map2 option_app
        [(c_update i (aeval (c0, (q0)) a) c0, q0)] x1).
        exists t. exists t0.
        split. rewrite Heqt. 
        apply E_Asgn. intuition. 
        split. rewrite Heqt0. apply E_Asgn. intuition.
        rewrite H2. rewrite Heqt. rewrite Heqt0.
        admit. inversion H;subst.
        apply IHy in H6. 
        destruct H6. destruct H0.
        destruct H0. destruct H1.
        exists x0. 
        remember (StateMap.Raw.map2 option_app [(c_update i (aeval (c0, q0) a) c0, q0)] x1).
        exists t. 
        rewrite Heqt. split. intuition.
        split. apply E_Asgn. intuition.
        rewrite H2. admit.
 
      -intros. inversion H; subst.
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
 -- induction x; induction y; intros.
    simpl in H. inversion_clear H.
    exists nil. exists nil.
    split. apply E_nil. split. apply E_nil.
    simpl. reflexivity.
    destruct a. simpl in H. rewrite map2_r_refl in H.
    exists nil. exists (mu).
    split. apply E_nil. split. intuition.
    rewrite map2_nil_l. rewrite map2_r_refl. reflexivity.
    destruct a. simpl in H. rewrite map2_l_refl in H.
    exists (mu).
    exists nil.
    split.  intuition. split.  apply E_nil.
    rewrite map2_nil. rewrite map2_l_refl. reflexivity.
    destruct a. destruct a0. simpl in H.
    destruct (Cstate_as_OT.compare c c0).
    inversion H;subst.
    apply IHx in H8. destruct H8. destruct H0.
    destruct H0. destruct H1. 
    exists (StateMap.Raw.map2 option_app mu' x0). exists x1.
    split.  apply E_IF_true. intuition. intuition.
    intuition. split. intuition. 
    rewrite H2.  admit.
    apply IHx in H8. destruct H8. destruct H0.
    destruct H0. destruct H1. 
    exists (StateMap.Raw.map2 option_app mu' x0). exists x1.
    split.  apply E_IF_false. intuition. intuition.
    intuition. split. intuition. 
    rewrite H2.  admit.
    
    inversion_clear H.
    apply IHx in H1. destruct H1. destruct H.
    destruct H. destruct H1.
    assert(exists mu1 mu2 : list (cstate * qstate n),
    ceval_single c1 [(c,q)] mu1 /\
    ceval_single c1 [(c, q0)] mu2 /\
    mu' = StateMap.Raw.map2 option_app mu1 mu2).
    apply IHc1. simpl.  destruct (Cstate_as_OT.compare c c).
    apply Cstate_as_OT.lt_not_eq in l. intuition.
    intuition.  apply Cstate_as_OT.lt_not_eq in l. intuition.
    destruct H4. destruct H4. destruct H4. destruct H5. 
    exists (StateMap.Raw.map2 option_app x2 x0). 
    exists ((StateMap.Raw.map2 option_app x3 x1)).
    split.  apply E_IF_true. rewrite (state_eq_bexp _ (c, q .+ q0)).
    intuition. intuition.
    intuition.  intuition.   split.  apply E_IF_true. rewrite (state_eq_bexp _ (c, q .+ q0)).
    intuition. intuition. 
    intuition.  unfold Cstate_as_OT.eq in e. rewrite <-e. intuition.
    rewrite H6. rewrite H3.  admit.
    
    apply IHx in H1. destruct H1. destruct H.
    destruct H. destruct H1.
    assert(exists mu1 mu2 : list (cstate * qstate n),
    ceval_single c2 [(c,q)] mu1 /\
    ceval_single c2 [(c, q0)] mu2 /\
    mu' = StateMap.Raw.map2 option_app mu1 mu2).
    apply IHc2. simpl.  destruct (Cstate_as_OT.compare c c).
    apply Cstate_as_OT.lt_not_eq in l. intuition.
    intuition.  apply Cstate_as_OT.lt_not_eq in l. intuition.
    destruct H4. destruct H4. destruct H4. destruct H5. 
    exists (StateMap.Raw.map2 option_app x2 x0). 
    exists ((StateMap.Raw.map2 option_app x3 x1)).
    split.  apply E_IF_false. rewrite (state_eq_bexp _ (c, q .+ q0)).
    intuition. intuition.
    intuition.  intuition.   split.  apply E_IF_false. rewrite (state_eq_bexp _ (c, q .+ q0)).
    intuition. intuition. 
    intuition.  unfold Cstate_as_OT.eq in e. rewrite <-e. intuition.
    rewrite H6. rewrite H3.  admit.
    
    inversion H;subst.
    apply IHy in H8. destruct H8. destruct H0.
    destruct H0. destruct H1. 
    exists x0. exists (StateMap.Raw.map2 option_app mu' x1).
    split. intuition.  split.
    apply E_IF_true. intuition. intuition.
    intuition.  
    rewrite H2.  admit.
    apply IHy in H8. destruct H8. destruct H0.
    destruct H0. destruct H1. 
    exists x0. exists (StateMap.Raw.map2 option_app mu' x1).
    split. intuition.  split.
    apply E_IF_false. intuition. intuition.
    intuition.  
    rewrite H2.  admit.

    intros.  


  apply ceval_3' with ((x +l y)).
  intros. apply IHc. assumption. assumption.
 reflexivity. 

    


 Admitted.
 






Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Arith.Peano_dec.


Lemma ceval_4{n:nat}:  forall c sigma (rho: qstate n) (mu mu': list (cstate *qstate n)),
ceval_single c ((sigma, rho)::mu) mu' ->
exists mu1 mu2 , (ceval_single c [(sigma,rho)] mu1
/\ ceval_single c mu mu2 /\
mu'=StateMap.Raw.map2 option_app mu1 mu2).
Proof. induction c. 
- intros. simpl. inversion H;subst.  exists [(sigma,rho)].
    exists mu. split. apply E_Skip. 
    split. apply ceval_skip. admit.
-intros.  inversion H;subst. exists nil. exists nil.
split. apply E_Abort. split. apply ceval_abort.
admit. 
-intros. inversion H;subst. exists  [(c_update i
 (aeval  (sigma, rho)
   a) sigma, rho)]. exists mu'0. split; intuition. 
    admit.
-intros. inversion H;subst. 
 apply IHc1 in H6. destruct H6. destruct H0.
 destruct H0. destruct H1. rewrite H2 in H7.
 apply ceval_3'' in H7. destruct H7.
 destruct H3. destruct H3. destruct H4.
 exists x1. exists x2. 
 split. apply E_Seq with x. intuition. intuition.
 split. apply ceval_seq with x0. intuition. intuition.
 intuition.
-intros.  inversion H;subst. 
 exists mu'0. exists mu''. 
 split. assert(mu'0=StateMap.Raw.map2 option_app mu'0 []).
 rewrite map2_nil. rewrite map2_l_refl. reflexivity.
 rewrite H0.
   apply E_IF_true. intuition.
   apply E_nil. intuition.
   split. intuition. reflexivity.
intros.  
exists mu'0. exists mu''. 
split. assert(mu'0=StateMap.Raw.map2 option_app mu'0 []).
rewrite map2_nil. rewrite map2_l_refl. reflexivity.
rewrite H0.
  apply E_IF_false. intuition.
  apply E_nil. intuition.
  split. intuition. reflexivity.

  -intros.  inversion H;subst. 
  exists mu'0. exists mu''. 
  split. assert(mu'0=StateMap.Raw.map2 option_app mu'0 []).
  rewrite map2_nil. rewrite map2_l_refl. reflexivity.
  rewrite H0.
    apply E_While_true with mu1. intuition.
    apply E_nil. intuition. intuition.
    split. intuition. reflexivity.
 exists [(sigma, rho)]. exists mu'0. 
 split. assert([(sigma, rho)]=StateMap.Raw.map2 option_app [(sigma, rho)] []).
 rewrite map2_nil. rewrite map2_l_refl. reflexivity.
 rewrite H0.
   apply E_While_false. intuition. 
   apply E_nil. intuition.
admit.
-intros. inversion H;subst.   
apply inj_pair2_eq_dec in H2. destruct H2.
 remember ([(sigma,
q_update
  (I (2 ^ (s )) ⊗ U1
   ⊗ I
       (2 ^ (n- e))) rho)]).
exists l. exists mu'0.  split.
rewrite Heql. admit.
split. intuition. intuition.
 apply Nat.eq_dec. 
Admitted.

Require Import Sorted.
Lemma big_app_sorted{n:nat}: forall (f : nat -> list (cstate * qstate n)) (n_0:nat),
(forall i, Sorted (StateMap.Raw.PX.ltk (elt:=qstate n)) (f i))->
Sorted (StateMap.Raw.PX.ltk (elt:=qstate n)) (big_app f n_0).
Proof. intros. induction n_0. 
-simpl. apply Sorted_nil.
-simpl. apply StateMap.Raw.map2_sorted. 
        apply IHn_0. apply H.
Qed.      


Lemma ceval_sorted{ n:nat}: forall c (mu mu':list (cstate *qstate n)) 
 (Hm: Sorted (StateMap.Raw.PX.ltk (elt:=qstate n)) mu)
(H:ceval_single c mu mu'),
Sorted (StateMap.Raw.PX.ltk (elt:=qstate n)) mu'.
Proof.  induction c. 
-intros. inversion H;subst. intuition. intuition.
- intros. inversion H;subst. intuition. intuition.
-induction mu; intros; inversion H;subst. intuition. 
  apply StateMap.Raw.map2_sorted. 
  apply Sorted_cons. 
  apply Sorted_nil.  apply HdRel_nil. apply IHmu.
  inversion_clear Hm.  intuition. intuition.
-intros. inversion H;subst. intuition.
  apply IHc2 with mu1. apply IHc1 with ((sigma, rho) :: mu0).
  intuition. intuition. intuition.
-induction mu; intros; inversion H;subst. intuition. 
apply StateMap.Raw.map2_sorted.  
apply IHc1 with [(sigma, rho)]. 
apply Sorted_cons. 
apply Sorted_nil.  apply HdRel_nil. intuition.
 apply IHmu. 
inversion_clear Hm.  intuition. intuition.
apply StateMap.Raw.map2_sorted.  
apply IHc2 with [(sigma, rho)]. 
apply Sorted_cons. 
apply Sorted_nil.  apply HdRel_nil. intuition.
 apply IHmu. 
inversion_clear Hm.  intuition. intuition.
-induction mu; intros; inversion H;subst.  intuition.
 admit.  
 apply StateMap.Raw.map2_sorted. apply Sorted_cons. 
 apply Sorted_nil.  apply HdRel_nil.
 apply IHmu. inversion Hm. subst. intuition. intuition.
-admit.
-induction mu; intros; inversion H;subst. intuition. 
apply StateMap.Raw.map2_sorted. 
apply Sorted_cons. 
apply Sorted_nil.  apply HdRel_nil. apply IHmu.
inversion_clear Hm.  intuition.
apply inj_pair2_eq_dec in H2. 
apply inj_pair2_eq_dec in H2.  destruct H2. 
intuition. apply Nat.eq_dec. apply Nat.eq_dec. admit.
-induction mu; intros; inversion H;subst. intuition. 
apply (StateMap.Raw.map2_sorted ). 
apply big_app_sorted. intros. 
apply Sorted_cons. apply Sorted_nil.  apply HdRel_nil.
apply IHmu.
inversion_clear Hm.  intuition.
intuition.
Admitted.


Inductive ceval{n:nat}: com -> dstate n-> dstate n->Prop:=
|E_com:  forall c (mu mu':dstate n), 
        WF_dstate mu-> WF_dstate mu'->
       (ceval_single c (StateMap.this mu) (StateMap.this mu'))->
        ceval c mu mu'.


Lemma ceval_2{n:nat}: forall b c1 c2 (mu mu': list (cstate *qstate n)),
(forall x:cstate, option_qstate 
(StateMap.Raw.find x mu) <> Zero -> (beval (x, (option_qstate (StateMap.Raw.find x mu))) b)=true)
->ceval_single c1 mu mu'
-> ceval_single (CIf b c1 c2) mu mu'.
Proof. induction mu.
-intros. inversion H0; apply E_nil.
-intros. destruct a. apply ceval_4 in H0.
destruct H0. destruct H0. destruct H0.
destruct H1. rewrite H2.
apply E_IF_true. 
admit. apply IHmu. admit.
intuition. intuition.
Admitted. 

Lemma WF_ceval{n:nat} : forall c (mu mu':list (cstate *qstate n)), 
WF_dstate_aux mu->
ceval_single c mu mu'->
WF_dstate_aux mu'. 
Proof. induction c.
--intros. apply ceval_skip_1 in H0. rewrite <- H0. intuition.
--intros. apply ceval_abort_1 in H0. rewrite H0. apply WF_nil.
-- induction mu; intros; inversion H0;subst. apply WF_nil.
   inversion_clear H. 
Admitted. 


Require Import Coq.Arith.PeanoNat.

Lemma pred_sub_1:forall n:nat, pred n=n-1 .
Proof. lia.
Qed.

Lemma S_add_1:forall n:nat, S n=n+1 .
Proof. lia.
Qed.

Lemma add_sub_assoc: forall (a b c:nat), (b<=c) -> a+(b-c)=a+b-c .
Proof.  induction a. intros. lia.
                   intros. simpl plus. 
                   rewrite IHa. 
                   (* rewrite Nat.sub_succ_r.
                   simpl.  rewrite pred_sub_1. 
                   rewrite S_add_1.
                 
                   assert((b-c-1)+1=b-c).
                   rewrite Nat.sub_add. reflexivity.

                   
                  f_equal. *)
Admitted.

Local Open Scope R_scope.
Lemma pow_1: forall a:nat, 1^a=1.
Proof. Admitted.

Lemma Npow_mult: forall a b c, (a^b)^c= a^(b*c). 
Proof. induction b; induction c. intuition. 
simpl.
      intuition.
Admitted. 

Lemma inner_product_qubit0: ⟨0∣ × ∣0⟩=I 1 .
Proof. Admitted.

Lemma qubit01_I: ∣0⟩⟨0∣ .+ ∣1⟩⟨1∣ = I 2.
Proof. Admitted.