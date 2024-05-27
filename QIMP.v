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
                  [((c_update i j sigma), 
                  (q_update (((I (2^(s))) ⊗ ((Vec (2^(e-s)) j ) × (Vec (2^(e-s)) j )†) ⊗ (I (2^(n-e))))) rho))]) 
                  (2^(e-s))) mu' )               
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
Qed. *)

Lemma map_assoc: forall n (x y z: list (cstate *qstate n)),
(x +l (y +l z)) = (x +l y +l z).
Proof. induction x. simpl; intros. 
       -repeat rewrite map2_r_refl.
        reflexivity. 
      - destruct a.
             induction y; intros. rewrite map2_nil_l. rewrite map2_nil.
               rewrite map2_r_refl.  rewrite map2_l_refl. reflexivity.
           induction z. repeat rewrite map2_nil.
          repeat  rewrite map2_l_refl. reflexivity.
          destruct a. destruct a0. 
          simpl.   
          destruct (Cstate_as_OT.compare c0 c1).
          destruct (Cstate_as_OT.compare c c0).
          remember ((x +l (c0, q0) :: y) +l (c1, q1) :: z).
          simpl. destruct (Cstate_as_OT.compare c c1). 
          f_equal. rewrite <-(IHx ((c0, q0) :: y) ((c1, q1) :: z)).
          simpl. destruct (Cstate_as_OT.compare c0 c1).
          reflexivity. rewrite e in l. apply Cstate_as_OT.lt_not_eq in l.
          intuition. rewrite l2 in l. 
          apply Cstate_as_OT.lt_not_eq in l.
          intuition.  rewrite e in l0. rewrite l0 in l. 
          apply Cstate_as_OT.lt_not_eq in l.
          intuition. assert(Cstate_as_OT.lt c c1).
          apply Cstate_as_OT.lt_trans with c0. assumption. assumption.
          rewrite H in l1. apply Cstate_as_OT.lt_not_eq in l1. intuition.
          
          rewrite IHx.  simpl. 
          destruct (Cstate_as_OT.compare c c1). reflexivity.
          rewrite e in e0. rewrite e0 in l.  
          apply Cstate_as_OT.lt_not_eq in l.
          intuition.  rewrite e in l0. rewrite l0 in l. 
          apply Cstate_as_OT.lt_not_eq in l.
          intuition. simpl. 
          
          
          destruct (Cstate_as_OT.compare c0 c1).  
          f_equal. apply IHy. 
           rewrite e in l.   apply Cstate_as_OT.lt_not_eq in l.
           intuition. rewrite l1 in l. 
           apply Cstate_as_OT.lt_not_eq in l.
           intuition.   

        destruct (Cstate_as_OT.compare c c0).  simpl.
         destruct (Cstate_as_OT.compare c c1). f_equal.
         rewrite <-IHx.  simpl. 
         destruct (Cstate_as_OT.compare c0 c1). 
         rewrite e in l1. 
         apply Cstate_as_OT.lt_not_eq in l1.
           intuition. reflexivity. 
           rewrite e in l1. apply Cstate_as_OT.lt_not_eq in l1.
           intuition.
           
           rewrite e0 in l. rewrite e in  l. 
           apply Cstate_as_OT.lt_not_eq in l.
           intuition. rewrite e in l. rewrite l in l0.
           apply Cstate_as_OT.lt_not_eq in l0.
           intuition.  

           simpl. destruct (Cstate_as_OT.compare c c1).
            rewrite e0 in l. rewrite e in l. 
            apply Cstate_as_OT.lt_not_eq in l.
           intuition.  f_equal. rewrite Mplus_assoc. reflexivity.
           apply IHx. rewrite e in e0. rewrite e0 in l. 
           apply Cstate_as_OT.lt_not_eq in l.
           intuition. 

           simpl. destruct (Cstate_as_OT.compare c0 c1).
           rewrite e in l0.  apply Cstate_as_OT.lt_not_eq in l0.
           intuition.  f_equal.  apply IHy.
           
           rewrite e in l0.  apply Cstate_as_OT.lt_not_eq in l0.
           intuition.
           
           

  destruct (Cstate_as_OT.compare c c1). 
destruct (Cstate_as_OT.compare c c0).
simpl. destruct (Cstate_as_OT.compare c c1). 
f_equal.  rewrite<- IHx. f_equal.  simpl.
destruct (Cstate_as_OT.compare c0 c1).  
rewrite l3 in l. apply Cstate_as_OT.lt_not_eq in l.
intuition.  rewrite e in l. apply Cstate_as_OT.lt_not_eq in l.
intuition. reflexivity.   rewrite e in l0. 
apply Cstate_as_OT.lt_not_eq in l0.
           intuition. rewrite l2 in l0.
           apply Cstate_as_OT.lt_not_eq in l0.
           intuition.                
rewrite e in l0. rewrite l0 in l. 
apply Cstate_as_OT.lt_not_eq in l.
intuition.    assert(Cstate_as_OT.lt c c0).
apply Cstate_as_OT.lt_trans with c1. assumption. assumption.
rewrite H in l1.   apply Cstate_as_OT.lt_not_eq in l1.
intuition. 
destruct (Cstate_as_OT.compare c c0).  
simpl. destruct (Cstate_as_OT.compare c c1). 
rewrite e in l1.  apply Cstate_as_OT.lt_not_eq in l1.
intuition. f_equal. rewrite<- IHx. reflexivity. 

rewrite e in l1.  apply Cstate_as_OT.lt_not_eq in l1.
intuition.  rewrite e in e0. rewrite e0 in l. 
apply Cstate_as_OT.lt_not_eq in l.
intuition. rewrite e in l0. rewrite l0 in l. 
apply Cstate_as_OT.lt_not_eq in l.
intuition. 

destruct (Cstate_as_OT.compare c c0). 
simpl. destruct (Cstate_as_OT.compare c c1). 
rewrite l2 in l0. apply Cstate_as_OT.lt_not_eq in l0.
intuition.  rewrite e in l0. apply Cstate_as_OT.lt_not_eq in l0.
intuition. f_equal. simpl in IHz. rewrite IHz.


destruct (Cstate_as_OT.compare c c0).  reflexivity.
rewrite e in l1. apply Cstate_as_OT.lt_not_eq in l1.
intuition. rewrite l3 in l1. apply Cstate_as_OT.lt_not_eq in l1.
intuition. 
simpl. destruct (Cstate_as_OT.compare c c1). 
rewrite l1 in l0. apply Cstate_as_OT.lt_not_eq in l0.
intuition. rewrite e0 in l0. apply Cstate_as_OT.lt_not_eq in l0.
intuition. f_equal. simpl in IHz. rewrite IHz.
rewrite e. destruct (Cstate_as_OT.compare c0 c0).
apply Cstate_as_OT.lt_not_eq in l2. intuition.
reflexivity. apply Cstate_as_OT.lt_not_eq in l2. intuition.

simpl in IHz.
rewrite IHz.  destruct ( Cstate_as_OT.compare c c0 ).
rewrite l2 in l1. apply Cstate_as_OT.lt_not_eq in l1.
intuition. rewrite e in l1. apply Cstate_as_OT.lt_not_eq in l1.
intuition.

simpl.
destruct (Cstate_as_OT.compare c0 c1).
rewrite l3 in l. apply Cstate_as_OT.lt_not_eq in l.
intuition. rewrite e in l. apply Cstate_as_OT.lt_not_eq in l.
intuition.  f_equal. 
Qed.





         






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
       intros. apply map2_app_nil in H0. destruct H0. 
       exists []. exists []. rewrite H0. rewrite H1. 
       split; try split; try apply E_nil. intuition. 

       destruct x; destruct y;
       intros. discriminate H3.
       destruct p.
       simpl in H3. 
       rewrite map2_r_refl in H3.
      
       exists []. exists ((mu' +l mu'')).
       split. apply E_nil. split.
       
       inversion H3.  rewrite <-H5. rewrite <-H6.
       rewrite <-H7. apply E_While_true with mu1.
       assumption. assumption. assumption. assumption.
      rewrite map2_nil_l. rewrite map2_r_refl. reflexivity.

       destruct p.
       simpl in H3. 
       rewrite map2_l_refl in H3.

       exists ((mu' +l mu'')). exists nil.
       split.   inversion H3.  rewrite <-H5. rewrite <-H6.
       rewrite <-H7. apply E_While_true with mu1.
       assumption. assumption. assumption. assumption.
       split. apply E_nil. simpl. 
      rewrite map2_nil. rewrite map2_l_refl. reflexivity.

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
        split. intuition. rewrite <-map_assoc. 
        destruct H7. destruct H8. rewrite <-H9.
        reflexivity. 

        injection H3. intros.
        assert(exists mu2 mu3 : list (cstate * qstate n),
        ceval_single c [(c0,q)] mu2 /\ ceval_single c [(c0,q0)] mu3 /\ mu1 = (mu2 +l mu3)).
        apply (Hc [(c0, q)] [(c0, q0)] mu1).

        rewrite <-H6. 
        simpl.  
        destruct (Cstate_as_OT.compare sigma sigma).
        apply Cstate_as_OT.lt_not_eq in l. intuition. rewrite <-H5.
          assumption.
          
          apply Cstate_as_OT.lt_not_eq in l. intuition.
  

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
          rewrite <-H6.
         rewrite (state_eq_bexp  _ (sigma, rho) _ ). assumption.
          reflexivity.
          intuition. assumption.
          intuition. split.
          apply E_While_true with x1.
          unfold Cstate_as_OT.eq in e.
          rewrite <-e. rewrite <-H6. 
          rewrite (state_eq_bexp  _ (sigma, rho) _ ). assumption.
          reflexivity. 
          intuition. 
      unfold Cstate_as_OT.eq in e.
      rewrite <-e.
          intuition. intuition. rewrite (map2_comm x4 x2).
         rewrite map_assoc.  rewrite <-(map_assoc _ x2 _ _).
          destruct H11. destruct H12. rewrite H13. 
          destruct H8. destruct H14. rewrite H15.
          rewrite (map2_comm x2  ((x4 +l x5))). 
          rewrite map_assoc. reflexivity. 

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
        rewrite <-H6. rewrite (state_eq_bexp  _ (sigma, rho) _ ).
        assumption. reflexivity.
        intuition. rewrite <-H6. rewrite<-H5. assumption. 
        intuition. rewrite (map2_comm mu' x1). 
        rewrite map_assoc. destruct H7. destruct H8. rewrite H9.
        apply map2_comm. 
     
        intros.   destruct x; destruct y; simpl  in H1;
        try discriminate H1; try destruct p. rewrite map2_r_refl in H1.

        exists []. exists ([(sigma, rho)] +l mu'). 
        split. apply E_nil. split. inversion H1; subst. 
        apply E_While_false. assumption. assumption.
        rewrite map2_nil_l. rewrite map2_r_refl. reflexivity.
        
        rewrite map2_l_refl in H1. 
        exists ([(sigma, rho)] +l mu'). exists []. split. 
        inversion H1; subst. 
        apply E_While_false. assumption. assumption.
        split. apply E_nil.
        rewrite map2_nil. rewrite map2_l_refl. reflexivity. 

        destruct p0.    
        destruct (Cstate_as_OT.compare c0 c1).
      injection H1. intros; subst.
      assert( exists mu1 mu2 : list (cstate * qstate n),
      ceval_single <{ while b do c end }> x mu1 /\
      ceval_single <{ while b do c end }> ((c1, q0) :: y) mu2 /\
      mu' = (mu1 +l mu2)).     apply IHceval_single.
      reflexivity. 
        reflexivity. 
        destruct H2. destruct H2.
        exists ( [(c0, q)] +l x0).
        exists x1.
        split. 
        apply E_While_false.
        assumption. intuition. split. intuition. 
        rewrite <-map_assoc. destruct H2. destruct H3.
        rewrite H4. reflexivity.
        
 assert(exists mu1 mu2 : list (cstate * qstate n),
 ceval_single <{ while b do c end }> x mu1 /\
 ceval_single <{ while b do c end }> y mu2 /\ mu' = (mu1 +l mu2)).

 apply IHceval_single. reflexivity. injection H1. intros; subst.
 reflexivity. 
 destruct H2. destruct H2.  destruct H2. destruct H3.

 exists ( [(c0, q)] +l x0). exists ( [(c1, q0)] +l x1).
 split. apply E_While_false. unfold Cstate_as_OT.eq in e.
 subst. injection H1; intros. subst. 
 rewrite (state_eq_bexp  _ (c1, q .+ q0) _ ). assumption.
 reflexivity. assumption. split. 
 apply E_While_false. unfold Cstate_as_OT.eq in e.
 subst. injection H1; intros. subst. 
 rewrite (state_eq_bexp  _ (c1, q .+ q0) _ ). assumption.
 reflexivity. assumption. injection H1; intros. subst.
 remember ((@cons (prod cstate (qstate n))
 (@pair cstate (qstate n) c0
    (@Mplus (Nat.pow (S (S O)) n) (Nat.pow (S (S O)) n) q q0))
 (@nil (prod cstate (qstate n))))).  
remember ([(c0, @Mplus (2^n) (2^n) q  q0)]). 
assert(l=l0). rewrite Heql. rewrite Heql0. reflexivity. 
rewrite H4. rewrite Heql0. 
 assert([(c0, @Mplus (2^n) (2^n) q  q0)] = ([(c0, q )] +l  [(c1, q0)])).
 simpl. destruct (Cstate_as_OT.compare c0 c1). 
 rewrite e in l1. apply Cstate_as_OT.lt_not_eq in l1. intuition.
 reflexivity. rewrite e in l1. apply Cstate_as_OT.lt_not_eq in l1. 
 intuition.    rewrite H5.  rewrite map_assoc. 
 rewrite (map2_comm ([(c0, q)]) ([(c1, q0)])).
 rewrite<- (map_assoc _ ([(c1, q0)]) ).
  rewrite (map2_comm ([(c1, q0)]) _). 
 rewrite map_assoc. reflexivity. 


 injection H1. intros. subst.
 assert(exists mu1 mu2 : list (cstate * qstate n),
 ceval_single <{ while b do c end }> ((c0,q)::x) mu1 /\
 ceval_single <{ while b do c end }> y mu2 /\ mu' = (mu1 +l mu2)).
 apply IHceval_single.
 reflexivity. reflexivity.  destruct H2. destruct H2.
 destruct H2. destruct H3. 

          exists (x0). 
          exists ( [(c1, q0)] +l x1).
          split. assumption. split. 
          apply E_While_false.
          assumption. intuition. rewrite (map2_comm _ x1). 
          rewrite map_assoc. rewrite map2_comm. rewrite H4.  reflexivity.
Qed.


Require Import ParDensityO.
Lemma WF_state_dstate_aux{n:nat}: forall (st:state (2^n)), 
WF_state st <-> WF_dstate_aux [st] .
Proof. split; unfold WF_dstate;
       destruct st; simpl; intros. 
    
       apply WF_cons. intuition. apply WF_nil. 
       unfold WF_state in H.  unfold WF_qstate in H. simpl in H.
       unfold d_trace_aux. unfold s_trace. simpl. rewrite Rplus_0_r.
       apply mixed_state_Cmod_1. intuition.

       inversion_clear H. intuition. 
Qed.


      



Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Arith.Peano_dec.

      
      




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
        rewrite H2. rewrite Heqt. apply map_assoc.
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
        admit.
        
        
         inversion H;subst.
        apply IHy in H6. 
        destruct H6. destruct H0.
        destruct H0. destruct H1.
        exists x0. 
        remember (StateMap.Raw.map2 option_app [(c_update i (aeval (c0, q0) a) c0, q0)] x1).
        exists t. 
        rewrite Heqt. split. intuition.
        split. apply E_Asgn. intuition.
        rewrite H2. rewrite (map2_comm ([(c_update i (aeval (c0, q0) a) c0, q0)]) x1).
        rewrite (map_assoc _ x0). apply map2_comm.  

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
    rewrite H2. apply map_assoc.
    apply IHx in H8. destruct H8. destruct H0.
    destruct H0. destruct H1. 
    exists (StateMap.Raw.map2 option_app mu' x0). exists x1.
    split.  apply E_IF_false. intuition. intuition.
    intuition. split. intuition. 
    rewrite H2.  apply map_assoc.
    
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
    rewrite H6. rewrite H3. 
    rewrite (map2_comm x2 _).  rewrite map_assoc.
    rewrite<-(map_assoc _ x3 x2 x0). rewrite (map2_comm x3 _).
    rewrite <-map_assoc. reflexivity.

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
    rewrite H6. rewrite H3. rewrite (map2_comm x2 _).  rewrite map_assoc.
    rewrite<-(map_assoc _ x3 x2 x0). rewrite (map2_comm x3 _).
    rewrite <-map_assoc. reflexivity.
    inversion H;subst.
    apply IHy in H8. destruct H8. destruct H0.
    destruct H0. destruct H1. 
    exists x0. exists (StateMap.Raw.map2 option_app mu' x1).
    split. intuition.  split.
    apply E_IF_true. intuition. intuition.
    intuition.  
    rewrite H2. rewrite map_assoc. rewrite (map2_comm mu' _).
    rewrite <-map_assoc. reflexivity.

    apply IHy in H8. destruct H8. destruct H0.
    destruct H0. destruct H1. 
    exists x0. exists (StateMap.Raw.map2 option_app mu' x1).
    split. intuition.  split.
    apply E_IF_false. intuition. intuition.
    intuition.  
    rewrite H2.  rewrite map_assoc. rewrite (map2_comm mu' _).
    rewrite <-map_assoc. reflexivity.

    intros.  


  apply ceval_3' with ((x +l y)).
  intros. apply IHc. assumption. assumption.
 reflexivity.
 
 -- induction x; induction y; intros.
 exists nil. exists nil.
 split. apply E_nil. split. apply E_nil.
 simpl. simpl in H. inversion_clear H. reflexivity. 
 destruct a. simpl in H. rewrite map2_r_refl in H.
 inversion H;subst. 
 exists nil. exists ((StateMap.Raw.map2 option_app
 [(c, QInit_fun s e q)] mu')).
 split. apply E_nil. split. intuition.
 rewrite map2_nil_l. rewrite map2_r_refl. reflexivity.
 destruct a. simpl in H. rewrite map2_l_refl in H.
 inversion H;subst. 
 exists ((StateMap.Raw.map2 option_app
 [(c, QInit_fun s e q)] mu')).
 exists nil.
 split.  intuition. split.  apply E_nil.
 rewrite map2_nil. rewrite map2_l_refl. reflexivity.
 destruct a0. destruct a. simpl in H.
 destruct (Cstate_as_OT.compare c0 c).
 inversion H;subst.
apply IHx in H6. destruct H6. destruct H0.
destruct H0. destruct H1. 
remember (StateMap.Raw.map2 option_app
[(c0, QInit_fun s e q0)] x0).
exists t. exists x1.
split. rewrite Heqt. apply E_Qinit.
intuition. split. intuition. 
rewrite H2. rewrite Heqt. apply map_assoc.
inversion H;subst.
apply IHx in H6. destruct H6. destruct H0.
destruct H0. destruct H1.
remember (StateMap.Raw.map2 option_app
[(c0, QInit_fun s e q0)] x0).
remember (StateMap.Raw.map2 option_app
[(c, QInit_fun s e q)] x1).
exists t. exists t0.
split. rewrite Heqt. 
apply E_Qinit. intuition. 
split. rewrite Heqt0. apply E_Qinit. intuition.
rewrite H2. rewrite Heqt. rewrite Heqt0.
admit.


 inversion H;subst.
apply IHy in H6. 
destruct H6. destruct H0.
destruct H0. destruct H1.
exists x0. 
remember (StateMap.Raw.map2 option_app [(c, QInit_fun s e q)] x1).
exists t. 
rewrite Heqt. split. intuition.
split. apply E_Qinit. intuition.
rewrite H2. rewrite (map2_comm ([(c, QInit_fun s e q)]) x1).
rewrite (map_assoc _ x0). apply map2_comm.

induction x; induction y; intros.
 exists nil. exists nil.
 split. apply E_nil. split. apply E_nil.
 simpl. simpl in H. inversion_clear H. reflexivity. 
 destruct a. simpl in H. rewrite map2_r_refl in H.
 inversion H;subst. apply inj_pair2_eq_dec in H2. 
 apply inj_pair2_eq_dec in H2. destruct H2.
 exists nil. exists ((StateMap.Raw.map2 option_app
 [(c, q_update (I (2 ^ s) ⊗ U1 ⊗ I (2 ^ (n - e))) q)] mu')).
 split. apply E_nil. split. intuition.
 rewrite map2_nil_l. rewrite map2_r_refl. reflexivity.
 apply Nat.eq_dec. apply Nat.eq_dec.
 destruct a. simpl in H. rewrite map2_l_refl in H.
 inversion H;subst.  apply inj_pair2_eq_dec in H2. 
 apply inj_pair2_eq_dec in H2. destruct H2.
 exists ((StateMap.Raw.map2 option_app
 [(c, q_update (I (2 ^ s) ⊗ U1 ⊗ I (2 ^ (n - e))) q)] mu')).
 exists nil. 
 split.  intuition. split.  apply E_nil.
 rewrite map2_nil. rewrite map2_l_refl. reflexivity.
 apply Nat.eq_dec. apply Nat.eq_dec.
 destruct a0. destruct a. simpl in H.
 destruct (Cstate_as_OT.compare c0 c).
 inversion H;subst. 
 apply inj_pair2_eq_dec in H2. 
 apply inj_pair2_eq_dec in H2. destruct H2.
apply IHx in H9. destruct H9. destruct H0.
destruct H0. destruct H1. 
remember (StateMap.Raw.map2 option_app
[(c0, q_update (I (2 ^ s) ⊗ U1 ⊗ I (2 ^ (n - e))) q0)] x0).
exists t. exists x1.
split. rewrite Heqt. apply E_Qunit_One.
intuition. intuition.  intuition. split. intuition. 
rewrite H2. rewrite Heqt. apply map_assoc.
apply Nat.eq_dec. apply Nat.eq_dec.
inversion H;subst. 
apply inj_pair2_eq_dec in H2. 
apply inj_pair2_eq_dec in H2. destruct H2.
apply IHx in H9. destruct H9. destruct H0.
destruct H0. destruct H1.
remember (StateMap.Raw.map2 option_app
[(c0, q_update (I (2 ^ s) ⊗ U1 ⊗ I (2 ^ (n - e))) (q0 ))] x0).
remember (StateMap.Raw.map2 option_app
[(c, q_update (I (2 ^ s) ⊗ U1 ⊗ I (2 ^ (n - e))) ( q))] x1).
exists t. exists t0.
split. rewrite Heqt. 
apply E_Qunit_One. intuition. intuition. intuition. 
split. rewrite Heqt0. apply E_Qunit_One. intuition. intuition.
intuition. 
rewrite H2. rewrite Heqt. rewrite Heqt0.
admit. apply Nat.eq_dec. apply Nat.eq_dec.

 inversion H;subst. apply inj_pair2_eq_dec in H2. 
 apply inj_pair2_eq_dec in H2. destruct H2.
apply IHy in H9. 
destruct H9. destruct H0.
destruct H0. destruct H1.
exists x0. 
remember (StateMap.Raw.map2 option_app [(c, q_update (I (2 ^ s) ⊗ U1 ⊗ I (2 ^ (n - e))) q)] x1).
exists t. 
rewrite Heqt. split. intuition.
split. apply E_Qunit_One. intuition. intuition. intuition.
rewrite H2. rewrite (map2_comm ([(c, q_update (I (2 ^ s) ⊗ U1 ⊗ I (2 ^ (n - e))) q)]) x1).
rewrite (map_assoc _ x0). apply map2_comm. 
apply Nat.eq_dec. apply Nat.eq_dec.

admit.


induction x; induction y; intros.
 exists nil. exists nil.
 split. apply E_nil. split. apply E_nil.
 simpl. simpl in H. inversion_clear H. reflexivity. 
 destruct a. simpl in H. rewrite map2_r_refl in H.
 inversion H;subst. 
 exists nil. exists ((StateMap.Raw.map2 option_app
 (big_app
     (fun j : nat =>
      [(c_update i j c,
        q_update
          (I (2 ^ s) ⊗ (∣ j ⟩_ (e - s) × ⟨ j ∣_ (e - s)) ⊗ I (2 ^ (n - e)))
          q)]) (2 ^ (e - s))) mu')).
 split. apply E_nil. split. intuition.
 rewrite map2_nil_l. rewrite map2_r_refl. reflexivity.
 destruct a. simpl in H. rewrite map2_l_refl in H.
 inversion H;subst.  
 exists ((StateMap.Raw.map2 option_app
 (big_app
     (fun j : nat =>
      [(c_update i j c,
        q_update
          (I (2 ^ s) ⊗ (∣ j ⟩_ (e - s) × ⟨ j ∣_ (e - s)) ⊗ I (2 ^ (n - e)))
          q)]) (2 ^ (e - s))) mu')).
 exists nil.
 split.  intuition. split.  apply E_nil.
 rewrite map2_nil. rewrite map2_l_refl. reflexivity.
 destruct a0. destruct a. simpl in H.
 destruct (Cstate_as_OT.compare c0 c).
 inversion H;subst. 
apply IHx in H7. destruct H7. destruct H0.
destruct H0. destruct H1. 
remember (StateMap.Raw.map2 option_app
 (big_app
 (fun j : nat =>
  [(c_update i j c0,
    q_update
      (I (2 ^ s) ⊗ (∣ j ⟩_ (e - s) × ⟨ j ∣_ (e - s)) ⊗ I (2 ^ (n - e)))
      q0)]) (2 ^ (e - s)) ) x0).
exists t. exists x1.
split. rewrite Heqt. apply E_Meas.
intuition. split. intuition. 
rewrite H2. rewrite Heqt. apply map_assoc.
inversion H;subst.
apply IHx in H7. destruct H7. destruct H0.
destruct H0. destruct H1.
remember (StateMap.Raw.map2 option_app
(big_app
     (fun j : nat =>
      [(c_update i j c0,
        q_update
          (I (2 ^ s) ⊗ (∣ j ⟩_ (e - s) × ⟨ j ∣_ (e - s)) ⊗ I (2 ^ (n - e)))
          q0)]) (2 ^ (e - s))) x0).
remember (StateMap.Raw.map2 option_app
(big_app
(fun j : nat =>
 [(c_update i j c,
   q_update
     (I (2 ^ s) ⊗ (∣ j ⟩_ (e - s) × ⟨ j ∣_ (e - s)) ⊗ I (2 ^ (n - e)))
     q)]) (2 ^ (e - s))) x1).
exists t. exists t0.
split. rewrite Heqt. 
apply E_Meas. intuition. 
split. rewrite Heqt0. apply E_Meas. intuition.
rewrite H2. rewrite Heqt. rewrite Heqt0.
admit.


 inversion H;subst.
apply IHy in H7. 
destruct H7. destruct H0.
destruct H0. destruct H1.
exists x0. 
remember (StateMap.Raw.map2 option_app (big_app
(fun j : nat =>
 [(c_update i j c,
   q_update
     (I (2 ^ s) ⊗ (∣ j ⟩_ (e - s) × ⟨ j ∣_ (e - s)) ⊗ I (2 ^ (n - e)))
     q)]) (2 ^ (e - s))) x1).
exists t. 
rewrite Heqt. split. intuition.
split. apply E_Meas. intuition.
rewrite H2. rewrite (map2_comm (big_app
(fun j : nat =>
 [(c_update i j c,
   q_update
     (I (2 ^ s) ⊗ (∣ j ⟩_ (e - s) × ⟨ j ∣_ (e - s)) ⊗ I (2 ^ (n - e)))
     q)]) (2 ^ (e - s))) x1).
rewrite (map_assoc _ x0). apply map2_comm.

 Admitted.
 


 Lemma ceval_4{n:nat}:  forall c sigma (rho: qstate n) 
(mu mu': list (cstate *qstate n)),
Sorted (StateMap.Raw.PX.ltk (elt:=qstate n)) ((sigma, rho)::mu)->
ceval_single c ((sigma, rho)::mu) mu' ->
exists mu1 mu2 , (ceval_single c [(sigma,rho)] mu1
/\ ceval_single c mu mu2 /\
mu'=StateMap.Raw.map2 option_app mu1 mu2).
Proof. intros. assert((sigma, rho) :: mu= ([(sigma, rho)] +l mu)).
       destruct mu. simpl. reflexivity. destruct p.
       inversion_clear H. inversion_clear H2. simpl in *.
       destruct (Cstate_as_OT.compare sigma c0). 
       rewrite map2_r_refl. reflexivity.  unfold Cstate_as_OT.eq in e.
       rewrite e in H. apply Cstate_as_OT.lt_not_eq  in H. simpl in *. intuition.
       unfold StateMap.Raw.PX.ltk in H. simpl in H.
       rewrite <-H in l. apply Cstate_as_OT.lt_not_eq  in l. intuition.
       rewrite H1 in H0. apply ceval_3'' in H0. 
       destruct H0. destruct H0. destruct H0. 
       exists x. exists x0. intuition.
Qed. 


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
Proof. 
induction c. 
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
- intros. remember <{while b do c end}> as original_command eqn:Horig. 
induction H;  try inversion Horig; subst. apply Sorted_nil.
apply StateMap.Raw.map2_sorted. apply IHceval_single3.
apply IHc with [(sigma, rho)].  apply Sorted_cons. 
apply Sorted_nil.  apply HdRel_nil. assumption. reflexivity. 
apply IHceval_single1. inversion_clear Hm. intuition. reflexivity.
 apply StateMap.Raw.map2_sorted. apply Sorted_cons. 
 apply Sorted_nil.  apply HdRel_nil. apply IHceval_single. 
 inversion Hm. subst. intuition. intuition.
-induction mu; intros; inversion H;subst. intuition. 
apply StateMap.Raw.map2_sorted. 
apply Sorted_cons. 
apply Sorted_nil.  apply HdRel_nil. apply IHmu.
inversion_clear Hm.  intuition. intuition.
-induction mu; intros; inversion H;subst. intuition. 
apply StateMap.Raw.map2_sorted. 
apply Sorted_cons. 
apply Sorted_nil.  apply HdRel_nil. apply IHmu.
inversion_clear Hm.  intuition.
apply inj_pair2_eq_dec in H2. 
apply inj_pair2_eq_dec in H2.  destruct H2. 
intuition. apply Nat.eq_dec. apply Nat.eq_dec. 
-induction mu; intros; inversion H;subst. intuition. 
apply StateMap.Raw.map2_sorted. 
apply Sorted_cons. 
apply Sorted_nil.  apply HdRel_nil. apply IHmu.
inversion_clear Hm.  intuition.
apply inj_pair2_eq_dec in H5. 
apply inj_pair2_eq_dec in H5.  destruct H5. 
intuition. apply Nat.eq_dec. apply Nat.eq_dec. 
-induction mu; intros; inversion H;subst. intuition. 
apply (StateMap.Raw.map2_sorted ). 
apply big_app_sorted. intros. 
apply Sorted_cons. apply Sorted_nil.  apply HdRel_nil.
apply IHmu.
inversion_clear Hm.  intuition.
intuition.
Qed.


Inductive ceval{n:nat}: com -> dstate n-> dstate n->Prop:=
|E_com:  forall c (mu mu':dstate n), 
        WF_dstate mu-> WF_dstate mu'->
       (ceval_single c (StateMap.this mu) (StateMap.this mu'))->
        ceval c mu mu'.


(* Lemma ceval_2{n:nat}: forall b c1 c2 (mu mu': list (cstate *qstate n)),
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
Admitted.  *)



Require Import Coq.Arith.PeanoNat.
Local Open Scope nat_scope.
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

Definition WF_qstate_aux{n:nat} (rho : qstate n ):=
    @Mixed_State_aux (2^(n)) rho.

Definition WF_state_aux{n:nat} (st:state n): Prop:=
      WF_qstate_aux (snd st).

Inductive WF_dstate_aux'{n:nat}: list(cstate * (qstate n)) -> Prop:=
|WF_nil': WF_dstate_aux' nil
|WF_cons' st mu': WF_state_aux st -> WF_dstate_aux' mu' 
                        -> WF_dstate_aux' (st::mu').

Lemma Mixed_State_scale_aux: forall n (ρ : Square n) p, Mixed_State_aux ρ ->
0 < p->
Mixed_State_aux (p .* ρ).
Proof. intros.
        induction H.
        - rewrite Mscale_assoc.  
        rewrite RtoC_mult. apply Pure_S_aux.
        apply Rmult_lt_0_compat. intuition. intuition.
        intuition.
      --rewrite Mscale_plus_distr_r. 
        apply Mix_S_aux; intuition.
Qed.

Lemma WF_d_scalar_aux'{n}: forall (mu:list (cstate *qstate n)) p, 
(0<p)
->WF_dstate_aux' mu 
->@WF_dstate_aux' n
((StateMap.Raw.map (fun x : qstate n => p .* x) mu)).
Proof. intros. induction mu. 
        --simpl. intuition.
        --inversion_clear H0. destruct a. 
        simpl.  apply (@WF_cons' n). unfold WF_state_aux in *.
        unfold WF_qstate_aux in *.   apply Mixed_State_scale_aux.
        simpl in H1. assumption. assumption.
        apply IHmu. intuition.
Qed.

Lemma WF_s_plus_aux{n}:forall (c c0:cstate) (q q0:qstate n ) ,
WF_state_aux (c, q)-> WF_state_aux ( c0, q0)->
@WF_state_aux n (c, q .+ q0).
Proof. unfold WF_state.  unfold s_trace. unfold WF_qstate. simpl. 
       intros. apply Mix_S_aux; intuition. 
Qed.

  Lemma WF_d_app_aux'{n:nat}: forall (mu mu':list (cstate*qstate n)),
  WF_dstate_aux' mu -> WF_dstate_aux' mu'-> @WF_dstate_aux' n
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
        --apply WF_cons'.  apply WF_s_plus_aux with c.
          intuition. intuition. 
          apply IHmu. intuition. intuition. 
      --apply WF_cons'.   intuition.
          apply IHmu'.
          assumption.
Qed.


Lemma d_trace_app{n:nat}: forall (mu mu':list (cstate *qstate n)),
WF_dstate_aux' mu -> WF_dstate_aux' mu'->
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



Lemma WF_state_gt_0'{n:nat}: forall (st:state n), 
WF_state_aux st -> s_trace st>0.
Proof. unfold WF_state_aux. unfold WF_qstate_aux. unfold s_trace. intros.
       apply mixed_state_Cmod_1_aux. intuition. 
Qed.

Lemma WF_dstate_gt_0_aux'{n:nat}: forall (mu:list( cstate*qstate n)),
WF_dstate_aux' mu-> 0 <= ((d_trace_aux mu)).
Proof. intros. induction mu.
--simpl.  intuition.
--inversion_clear H. apply IHmu in H1. 
 simpl. apply Rplus_le_le_0_compat. 
apply WF_state_gt_0' in H0. simpl in H0. 
intuition. intuition. 
Qed.


Lemma WF_dstate_aux'_to_WF_dstate_aux{n}: forall (mu: list (cstate *qstate n)),
WF_dstate_aux' mu /\ d_trace_aux mu <=1 <-> WF_dstate_aux mu.
Proof.  intros. split; intros. induction mu. apply WF_nil. 
        destruct H. inversion_clear H. simpl in H0.
        apply WF_cons. unfold WF_state. unfold WF_state_aux in H1.
        destruct a. simpl in *.  unfold WF_qstate. unfold WF_qstate_aux in H1.
        apply Mixed_State_aux_to_Mix_State. split.  assumption.
        unfold s_trace in H0. simpl in H0.
        apply Rplus_le_reg_pos_r with (d_trace_aux mu).
        apply WF_dstate_gt_0_aux'. assumption. assumption.
        apply IHmu.  split. intuition.  
        apply Rplus_le_1 with (s_trace a).
        apply WF_state_gt_0'. assumption. assumption.
        simpl. assumption.
        induction mu.   split. apply WF_nil'. simpl. 
        lra. inversion_clear H. split. apply WF_cons'.
        unfold WF_state_aux. unfold WF_state in H0.
          unfold WF_qstate in H0. unfold WF_qstate_aux.
        apply Mixed_State_aux_to_Mix_State. assumption.
         apply IHmu. assumption. assumption.  
Qed.



Lemma WF_d_app_aux{n:nat}: forall (mu mu':list (cstate*qstate n)), 
WF_dstate_aux mu -> WF_dstate_aux mu'-> (d_trace_aux (mu +l mu')<=1)
->
WF_dstate_aux (mu +l mu').
Proof. intros. apply WF_dstate_aux'_to_WF_dstate_aux. 
        apply WF_dstate_aux'_to_WF_dstate_aux in H.
       apply WF_dstate_aux'_to_WF_dstate_aux in H0.
       split. apply WF_d_app_aux'. intuition. intuition. 
       assumption.
Qed.


Lemma WF_d_app{n:nat}: forall (mu mu':dstate n),
WF_dstate mu -> WF_dstate mu'-> (d_trace (d_app mu mu')<=1)->
WF_dstate  (d_app mu mu').
Proof. unfold WF_dstate. unfold d_app. unfold d_trace. unfold StateMap.map2. 
 intros  (mu, IHmu) (mu', IHmu') p1 p2. simpl.
 apply WF_d_app_aux. assumption. assumption. 
Qed.

Local Open Scope nat_scope.
Lemma pow_gt_0: forall n ,
2^ n >0 .
Proof. induction n. simpl. lia.
      simpl. rewrite Nat.add_0_r. 
      lia.
Qed.

Lemma Vector_State_snd_0: forall n (x: Vector (2 ^ n)),
WF_Matrix x->
snd (((x) † × x) 0 0)= 0%R.
 Proof.  intros.  simpl. unfold adjoint. unfold Mmult. 
 apply big_sum_snd_0.  intros.  rewrite  Cmult_comm.
 apply Cmult_conj_real.  
Qed.
         
Lemma matrix_0_0_rev:forall (x: Vector 1), 
WF_Matrix x->
(x  0 0) .* I 1= x.
Proof. intros.   assert(WF_Matrix (x 0 0 .* I 1)).
apply WF_scale. apply WF_I.   prep_matrix_equality. bdestruct (x0=?0).
bdestruct (y=?0). rewrite H2. rewrite H1. unfold scale.
unfold I.  simpl. rewrite Cmult_1_r. reflexivity.
rewrite H1. unfold WF_Matrix in *.   
  rewrite (H _ y).   rewrite (H0 _ y). reflexivity.
  right. lia. right. lia.  unfold WF_Matrix in *.    
  rewrite (H _ y).   rewrite (H0 _ y). reflexivity.
  left. lia. left. lia.
  
  
  Qed.         


Lemma inner_eq: forall n (x: Vector (2 ^ n)),
WF_Matrix x->
((x) † × x) = ((norm x) * (norm x))%R .* I 1
 .
Proof. intros. unfold norm. rewrite sqrt_sqrt. unfold inner_product.
     rewrite <-(matrix_0_0_rev ((x) † × x)) at 1.
      unfold RtoC.  f_equal. 
      destruct (((x) † × x) 0 0)  eqn:E. 
      simpl.  f_equal. assert(r0= snd (((x) † × x) 0 0)).
      rewrite E. simpl. reflexivity. rewrite H0.
     apply Vector_State_snd_0. assumption. apply WF_mult.
     apply WF_adjoint. assumption. assumption.   
      apply inner_product_ge_0.
       
  
Qed.


Local Open Scope R_scope.
Lemma Vector_Mix_State{n:nat} : forall (x: Vector (2^n)),
WF_Matrix x-> x <> Zero->
Mixed_State_aux (x × (x) †).
Proof. intros. assert(x= ( (norm x))%R .* ( (R1 / ( (norm x)))%R .* x )).
          rewrite Mscale_assoc. rewrite Rdiv_unfold.
          rewrite Rmult_1_l. rewrite Cmult_comm. 
          rewrite RtoC_mult. 
          rewrite Rinv_l.
          rewrite Mscale_1_l. reflexivity.
          unfold not. intros.
          apply norm_zero_iff_zero in H1. rewrite H1 in H0.
          destruct H0. reflexivity. assumption.
          rewrite H1. rewrite Mscale_mult_dist_l.
          rewrite Mscale_adj.   rewrite Mscale_mult_dist_r.
          remember ( (norm x)). rewrite Mscale_assoc.
          rewrite Cconj_R. 
          rewrite RtoC_mult. 
          apply Pure_S_aux. 
          assert(0<=r). rewrite Heqr.
          apply norm_ge_0 . assert(0<r).   destruct H2.  
          assumption. rewrite Heqr in H2. 
          symmetry in H2.
          apply norm_zero_iff_zero in H2. rewrite H2 in H0.
          destruct H0. reflexivity.  
          assumption. apply Rmult_gt_0_compat.
          assumption. assumption.    
          unfold Pure_State. exists (((R1 / r)%R .* x)).
          split. unfold Pure_State_Vector. split. apply WF_scale.
          assumption.
           rewrite Mscale_adj. rewrite Mscale_mult_dist_r.
          rewrite Cconj_R. rewrite Mscale_mult_dist_l.
          rewrite inner_eq. 
          rewrite Heqr.  
          rewrite Rdiv_unfold. rewrite Rmult_1_l.
          repeat rewrite Mscale_assoc. 
          repeat rewrite RtoC_mult. 
          rewrite <-Rmult_assoc . 
          rewrite (Rmult_assoc  _ (/ norm x) _).
          assert((norm x<> 0)%R). 
          unfold not. intros.
          apply norm_zero_iff_zero in H2. rewrite H2 in H0.
          destruct H0. reflexivity. assumption.  
          rewrite Rinv_l. rewrite Rmult_1_r. 
          rewrite  Rinv_l. rewrite Mscale_1_l. reflexivity.
          assumption. assumption. assumption. reflexivity.
Qed.
          


Local Open Scope nat_scope.
Lemma WF_dstate_init: forall s e i j n (rho:qstate n),
WF_qstate_aux rho->
@WF_qstate_aux n ((I (2 ^ s) ⊗ (∣ i ⟩_ (e - s) × ⟨ j ∣_ (e - s))
       ⊗ I (2 ^ (n - e))) × rho
       × (I (2 ^ s) ⊗ (∣ i ⟩_ (e - s) × ⟨ j ∣_ (e - s))
          ⊗ I (2 ^ (n - e))) †).
Proof. intros. unfold WF_qstate_aux in *.
       assert( (2 ^ s * 2 ^ (e - s) * 2 ^ (n - e))%nat= (Nat.pow (S (S O)) n) ) .
        admit. destruct H0.

       induction H.
       remember ((I (2 ^ s) ⊗ (∣ i ⟩_ (e - s) × ⟨ j ∣_ (e - s))
        ⊗ I (2 ^ (n - e)))). 
       rewrite (Mscale_mult_dist_r _ _ _ p m ρ). 
       rewrite Mscale_mult_dist_l. 
        destruct H0. destruct H0.
        rewrite H1.  destruct H0.   

       
       apply Mixed_State_scale_aux. 
       repeat rewrite Mmult_assoc. 
        rewrite <-(Mmult_adjoint m x). 
        repeat rewrite<- Mmult_assoc.
        remember (m × x).

        assert( (Nat.pow (S (S O)) n)%nat= (2 ^ s * 2 ^ (e - s) * 2 ^ (n - e))%nat ) .
        admit. destruct H3.
        apply Vector_Mix_State.   rewrite Heqm0.
         apply WF_mult. rewrite Heqm.
        apply WF_kron.  admit. admit.
        apply WF_kron. reflexivity. reflexivity.
        apply WF_I. apply WF_mult. apply WF_vec.
        admit.   apply WF_adjoint. apply WF_vec.
         admit.
        apply WF_I. apply H0. rewrite Heqm0. 
       
     
        admit. 
        
        
        assumption.
       remember (I (2 ^ s) ⊗ (∣ i ⟩_ (e - s) × ⟨ j ∣_ (e - s)) ⊗ I (2 ^ (n - e))).
       rewrite Mmult_plus_distr_l.  rewrite Mmult_plus_distr_r.
       apply Mix_S_aux; intuition.
  
Admitted.

Lemma WF_qstate_big_sum: forall n (f:nat -> Square (2^n)) n_0,
n_0>0->
(forall i:nat, i< n_0 -> WF_qstate_aux (f i))->
WF_qstate_aux (big_sum (fun i:nat=> f  i) n_0).
Proof. intros. induction n_0. 
         simpl. lia. 
         simpl. unfold WF_qstate_aux.
         destruct n_0. simpl in *. rewrite Mplus_0_l.
         apply H0. lia. 
         apply Mix_S_aux. 
         apply IHn_0. lia. 
         intros. apply H0. lia.
         apply H0. lia. 
  
Qed.


Lemma WF_dstate_big_app: forall n (f:nat -> list (state n)) n_0,
(forall i:nat, i< n_0 -> WF_dstate_aux' (f i))->
WF_dstate_aux' (big_app (fun i:nat=> f  i) n_0).
Proof. intros. induction n_0. 
         simpl. apply WF_nil'.
         simpl. apply WF_d_app_aux'. 
         apply IHn_0.  intros. apply H. lia. 
         apply H. lia. 
  
Qed.




Lemma WF_ceval'{n:nat} : forall c (mu mu':list (cstate *qstate n)), 
WF_dstate_aux' mu->
ceval_single c mu mu'->
WF_dstate_aux' mu'. 
Proof. induction c.
--intros. apply ceval_skip_1 in H0. rewrite <- H0. intuition.
--intros. apply ceval_abort_1 in H0. rewrite H0. apply WF_nil'.
-- induction mu; intros; inversion H0;subst. apply WF_nil'. 
   apply WF_d_app_aux'. apply WF_cons'. inversion_clear H.
   unfold WF_state_aux in *. unfold WF_qstate_aux  in *.
   simpl in *. assumption.  apply WF_nil'.
   apply IHmu. inversion_clear H. assumption.  intuition.
--intros. inversion H0; subst. assumption.   apply IHc2 with mu1.
   apply IHc1 with  ((sigma, rho) :: mu0). assumption.
   assumption. assumption.
--induction mu; intros; inversion H0;subst. assumption.
  apply WF_d_app_aux'. apply IHc1 with [(sigma, rho)]. 
  apply WF_cons'. inversion_clear H.
   unfold WF_state_aux in *. unfold WF_qstate_aux  in *.
   simpl in *. assumption.  apply WF_nil'. 
   assumption. apply IHmu.  inversion_clear H. assumption.  intuition.

   apply WF_d_app_aux'. apply IHc2 with [(sigma, rho)]. 
  apply WF_cons'. inversion_clear H.
   unfold WF_state_aux in *. unfold WF_qstate_aux  in *.
   simpl in *. assumption.  apply WF_nil'. 
   assumption. apply IHmu.  inversion_clear H. assumption.  intuition.
  
-intros. remember <{while b do c end}> as original_command eqn:Horig. 
 induction H0;  try inversion Horig; subst. assumption.
 apply WF_d_app_aux'.  apply IHceval_single3. 
 apply IHc with [(sigma, rho)].  apply WF_cons'. inversion_clear H.
 unfold WF_state_aux in *. unfold WF_qstate_aux  in *.
 simpl in *. assumption.  apply WF_nil'.
 assumption. reflexivity.  apply IHceval_single1.  
 inversion_clear H. assumption.  intuition. 
 
 apply WF_d_app_aux'. apply WF_cons'. inversion_clear H.
 unfold WF_state_aux in *. unfold WF_qstate_aux  in *.
 simpl in *. assumption.  apply WF_nil'.
 apply IHceval_single. inversion_clear H. assumption.  intuition. 

-induction mu; intros; inversion H0;subst.  apply WF_nil'. 
apply WF_d_app_aux'. unfold QInit_fun. apply WF_cons'.
unfold WF_state_aux. simpl.  apply WF_qstate_big_sum.
apply pow_gt_0. intros. apply WF_dstate_init. inversion_clear H.
unfold WF_state_aux in H2. simpl in *. assumption. 
assert( (Nat.pow (S (S O)) n) =(2 ^ s * 2 ^ (e - s) * 2 ^ (n - e))%nat  ) .
admit. destruct H1. 
assert(@WF_dstate_aux' n (@nil (prod cstate  (Matrix (Nat.pow (S (S O)) n)
 (Nat.pow (S (S O)) n))))<-> @WF_dstate_aux' n (@nil  (prod cstate (qstate n)))). intuition. apply H1.
apply WF_nil'.
apply IHmu.  inversion_clear H. assumption.  intuition.
-induction mu; intros; inversion H0;subst. apply WF_nil'. 
apply WF_d_app_aux'. apply WF_cons'.
unfold WF_state_aux. unfold WF_qstate_aux.  simpl.
 apply mixed_unitary_aux. 
 assert( (2 ^ s * 2 ^ (e - s) * 2 ^ (n - e))%nat = (Nat.pow (S (S O)) n) ) .
admit. destruct H1.
 apply kron_unitary. apply kron_unitary. apply id_unitary. 
 assumption. apply id_unitary.  inversion_clear H.
 unfold WF_state_aux in H1. simpl in *. assumption.
 apply WF_nil'.  
apply IHmu.  inversion_clear H. assumption.
apply inj_pair2_eq_dec in H3. apply inj_pair2_eq_dec in H3.
destruct H3.
intuition.  apply Nat.eq_dec. apply Nat.eq_dec.
-induction mu; intros; inversion H0;subst. apply WF_nil'. 
apply WF_d_app_aux'. apply WF_cons'.
unfold WF_state_aux. unfold WF_qstate_aux.  simpl.
 apply mixed_unitary_aux.  admit.
  inversion_clear H.
 unfold WF_state_aux in H1. simpl in *. assumption.
 apply WF_nil'.  
apply IHmu.  inversion_clear H. assumption.
apply inj_pair2_eq_dec in H6. apply inj_pair2_eq_dec in H6.
destruct H6.
intuition.  apply Nat.eq_dec. apply Nat.eq_dec.
-induction mu; intros; inversion H0;subst. apply WF_nil'. 
apply WF_d_app_aux'. apply WF_dstate_big_app. intros.
apply WF_cons'.
unfold WF_state_aux. simpl.  unfold q_update.
unfold super. 
assert( (2 ^ s * 2 ^ (e - s) * 2 ^ (n - e))%nat = (Nat.pow (S (S O)) n) ) .
admit. destruct H2.
apply (WF_dstate_init s e i0 i0 n rho). 
inversion_clear H.
unfold WF_state_aux in H1. simpl in *. assumption.
apply WF_nil'. 
apply IHmu.  inversion_clear H. assumption.
intuition.  
Admitted. 



Lemma ceval_trace_assgn: forall n (mu mu':list (cstate * qstate n)) i a,
WF_dstate_aux' mu->
ceval_single <{ i := a }> mu mu'-> (d_trace_aux mu = d_trace_aux mu').
Proof. 
      induction mu; intros.
      
      -inversion_clear H0. reflexivity.
      -inversion H0;subst. rewrite d_trace_app.
       simpl. rewrite Rplus_0_r.  f_equal.  apply IHmu with i a0.
       inversion_clear H. assumption. assumption. 
       admit.
       apply WF_ceval' with  (<{ i := a0 }>) mu. 
       inversion_clear H. assumption. assumption.
Admitted.



Lemma ceval_trace_Qinit: forall n (mu mu':list (cstate * qstate n)) s e,
WF_dstate_aux' mu->
ceval_single <{ QInit s e }> mu mu'-> (d_trace_aux mu = d_trace_aux mu').
Proof. 
      induction mu; intros.
      
      -inversion_clear H0. reflexivity.
      -inversion H0;subst. rewrite d_trace_app.
       simpl. rewrite Rplus_0_r.  f_equal. admit.
       apply IHmu with s e. 
       inversion_clear H. assumption. assumption. 
       apply WF_ceval' with (<{ (s e) :Q= 0 }>) [(sigma, rho)].
       apply WF_cons'. inversion_clear H. assumption. apply WF_nil'.
       assert(([(sigma, QInit_fun s e rho)]) = StateMap.Raw.map2 (@option_app n) ([(sigma, QInit_fun s e rho)]) ([])).
       symmetry. apply map2_nil. rewrite H1. apply E_Qinit. apply E_nil.  
       apply WF_ceval' with  (<{ (s e) :Q= 0 }>) mu. 
       inversion_clear H. assumption. assumption.
Admitted.


Lemma ceval_trace_QUnit_one: forall n (mu mu':list (cstate * qstate n)) s e (U: Square (2 ^ (e - s))),
WF_dstate_aux' mu->
ceval_single <{ QUnit_One s e U }> mu mu'-> (d_trace_aux mu = d_trace_aux mu').
Proof. 
      induction mu; intros.
      
      -inversion_clear H0. reflexivity.
      -inversion H0;subst. rewrite d_trace_app.
       simpl. rewrite Rplus_0_r.  f_equal. admit.
       apply IHmu with s e U. 
       inversion_clear H. assumption. apply inj_pair2_eq_dec in H3.
       apply inj_pair2_eq_dec in H3. destruct H3.
       assumption. apply Nat.eq_dec. apply Nat.eq_dec. 
       apply WF_ceval' with (QUnit_One s e U1) [(sigma, rho)].
       apply WF_cons'. inversion_clear H. assumption. apply WF_nil'.
       remember ((sigma, q_update (I (2 ^ s) ⊗ U1 ⊗ I (2 ^ (n - e))) rho)).
       assert(([p]) =  (([p]) +l ([]))). 
       symmetry. rewrite map2_nil. rewrite map2_l_refl. reflexivity.  
       rewrite H1. rewrite Heqp. apply E_Qunit_One. assumption. assumption.
        apply E_nil.  
       apply WF_ceval' with  (<{ QUnit_One s e U1 }>) mu. 
       inversion_clear H. assumption. assumption.
Admitted.


Lemma ceval_trace_QUnit_ctrl: forall n (mu mu':list (cstate * qstate n)) s0 e0  s1 e1 (U: Square (2 ^ (e1 - s1))),
WF_dstate_aux' mu->
ceval_single <{ QUnit_Ctrl s0 e0 s1 e1 U }> mu mu'-> (d_trace_aux mu = d_trace_aux mu').
Proof. 
      induction mu; intros.
      
      -inversion_clear H0. reflexivity.
      -inversion H0;subst. rewrite d_trace_app.
       simpl. rewrite Rplus_0_r.  f_equal. admit.
       apply IHmu with s0 e0 s1 e1 U. 
       inversion_clear H. assumption. apply inj_pair2_eq_dec in H6.
       apply inj_pair2_eq_dec in H6. destruct H6.
       assumption. apply Nat.eq_dec. apply Nat.eq_dec. 
       apply WF_ceval' with (QUnit_Ctrl s0 e0 s1 e1 U1) [(sigma, rho)].
       apply WF_cons'. inversion_clear H. assumption. apply WF_nil'.
       admit.
       apply WF_ceval' with  (<{ QUnit_Ctrl s0 e0 s1 e1 U1 }>) mu. 
       inversion_clear H. assumption. assumption.
Admitted.


Lemma ceval_trace_QMeas: forall n (mu mu':list (cstate * qstate n)) s e i,
WF_dstate_aux' mu->
ceval_single <{ i :=M [[s e]] }> mu mu'-> (d_trace_aux mu = d_trace_aux mu').
Proof. 
      induction mu; intros.
      
      -inversion_clear H0. reflexivity.
      -inversion H0;subst. rewrite d_trace_app.
       simpl.   f_equal.  admit.
       apply IHmu with s e i. 
       inversion_clear H. assumption. assumption.
       apply WF_ceval' with (<{ i :=M [[s e]] }>) [(sigma, rho)].
       apply WF_cons'. inversion_clear H. assumption. apply WF_nil'.
       admit.
       apply WF_ceval' with  (<{ i :=M [[s e]] }>) mu. 
       inversion_clear H. assumption. assumption.
Admitted.


Lemma ceval_trace_le: forall c n  (mu mu':list (cstate * qstate n)),
WF_dstate_aux' mu->
ceval_single c mu mu'-> ((d_trace_aux mu' <= d_trace_aux mu)%R).
Proof. induction c. 
-- --intros. apply ceval_skip_1 in H0. rewrite <- H0. intuition.
--intros.  apply ceval_abort_1 in H0. rewrite H0. simpl.  apply WF_dstate_gt_0_aux'.
  assumption.
-- intros. rewrite <-(ceval_trace_assgn _ mu _ i a). lra. assumption. assumption.
-- intros. inversion H0; subst. simpl. lra. apply Rle_trans with (d_trace_aux mu1).
   apply IHc2. apply WF_ceval' with c1 ((sigma, rho) :: mu0). assumption.
   assumption. assumption. apply IHc1. assumption. assumption.
--induction mu; intros; inversion H0; subst; try simpl; try lra;  
  inversion H;subst;  rewrite d_trace_app; 
  try simpl; try apply Rplus_le_compat;
  assert(s_trace (sigma, rho)= d_trace_aux [ (sigma, rho)]); try simpl;
  try rewrite Rplus_0_r; try reflexivity; try rewrite H1. 
   apply IHc1.  apply WF_cons'. assumption.  apply WF_nil'. assumption.
  apply IHmu. assumption. assumption.
   apply WF_ceval' with c1 ([(sigma, rho)]).   apply WF_cons'. assumption. 
  apply WF_nil'. assumption. 
 apply WF_ceval' with (<{ if b then c1 else c2 end }>) (mu).  assumption.
    assumption. 
    apply IHc2.  apply WF_cons'. assumption.  apply WF_nil'. assumption.
    apply IHmu. assumption. assumption.
     apply WF_ceval' with c2 ([(sigma, rho)]).   apply WF_cons'. assumption. 
    apply WF_nil'. assumption. 
   apply WF_ceval' with (<{ if b then c1 else c2 end }>) (mu).  assumption.
      assumption.

--intros. remember <{while b do c end}> as original_command eqn:Horig. 
induction H0;  try inversion Horig; subst. try simpl; try lra.  
inversion H;subst.  rewrite d_trace_app; 
try simpl; try apply Rplus_le_compat;
assert(s_trace (sigma, rho)= d_trace_aux [ (sigma, rho)]); try simpl;
try rewrite Rplus_0_r; try reflexivity; try rewrite H1. 
apply Rle_trans with (d_trace_aux mu1). apply IHceval_single3.
apply WF_ceval' with c ([(sigma, rho)]).  apply WF_cons'. assumption.
  apply WF_nil'. assumption. reflexivity.
  apply IHc. apply WF_cons'. assumption. apply WF_nil'. assumption.
  apply IHceval_single1. assumption. reflexivity. 
  apply WF_ceval' with (<{ while b do c end }>) (mu1). 
  apply WF_ceval' with c ([(sigma, rho)]).  apply WF_cons'. assumption.
  apply WF_nil'. assumption. assumption. 
 apply WF_ceval' with (<{ while b do c end }>) (mu).  assumption.
    assumption. 

    inversion H;subst.  rewrite d_trace_app. simpl.  rewrite Rplus_0_r.
    apply Rplus_le_compat_l. apply IHceval_single. assumption. reflexivity.
    apply WF_cons'. assumption. apply WF_nil'.
    apply WF_ceval' with (<{ while b do c end }>) (mu).  assumption.
    assumption.
    
--intros. rewrite <-(ceval_trace_Qinit _ mu _ s e ). lra. assumption. assumption.
--intros. rewrite <-(ceval_trace_QUnit_one _ mu _ s e  U). lra. assumption. assumption.
--intros. rewrite <-(ceval_trace_QUnit_ctrl _ mu _ s0 e0 s1 e1  U). lra. assumption. assumption.
-- intros. rewrite <-(ceval_trace_QMeas _ mu _ s e i). lra. assumption. assumption.
Qed.


Lemma WF_ceval{n:nat} : forall c (mu mu':list (cstate *qstate n)), 
WF_dstate_aux mu->
ceval_single c mu mu'->
WF_dstate_aux mu'. 
Proof. intros.   apply WF_dstate_aux'_to_WF_dstate_aux. 
 apply WF_dstate_aux'_to_WF_dstate_aux in H. 
 split. apply WF_ceval' with (c) mu . intuition. 
 assumption.   apply Rle_trans with (d_trace_aux  mu).
 apply ceval_trace_le with (c). intuition.
 assumption. intuition.
Qed. 

