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
From Quan Require Import QState_L.
From Quan Require Import Par_trace.

Delimit Scope C_scope with C.
Local Open Scope C_scope.

(*-------------------------Syntax-----------------------------------*)
Inductive aexp : Type :=
  | ANum (n : nat)
  | AId (i : nat)            
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp)
  | AGcd (a1 a2:aexp)
  | AMod (a1 a2:aexp)
  | APow (a1 a2: aexp)
  | ADiv (a1 a2:aexp).

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
  | BAnd (b1 b2 : bexp)
  | BOr (b1 b2 :bexp).

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
  | Clet (i a:nat)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com)
  | QInit (s e : nat) 
  | QUnit_One (s e:nat) (U: Square (2^(e-s)))
  | QUnit_Ctrl (s0 e0 s1 e1:nat) (U: nat->Square (2^(e1-s1)))
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

Fixpoint ord' n a N :=
  match n with
  | O => O
  | S n' => match (ord' n' a N) with
           | O => (if (a ^ n mod N =? 1) then n else O)
           | _ => ord' n' a N
           end
  end.

Require Import Coq.ZArith.Znumtheory.
Definition ϕ (n : nat) :=
big_sum (fun x => if rel_prime_dec x n then 1%nat else 0%nat) n.
Definition ord a N := ord' (ϕ N) a N. 

Require Import Psatz ZArith Znumtheory.
Local Open Scope nat_scope.
Fixpoint aeval{s e:nat} (st: state s e) 
               (a : aexp) : nat :=
  match a with
  | ANum n => n
  | AId x => c_find x (fst st)                               
  | <{a1 + a2}> => (aeval st a1) + (aeval st a2)
  | <{a1 - a2}> => (aeval st a1) - (aeval st a2)
  | <{a1 * a2}> => (aeval st a1) * (aeval st a2)
  | AGcd a1 a2 => Nat.gcd (aeval st a1) (aeval st a2)
  | APow a1 a2 => Nat.pow (aeval st a1) (aeval st a2)
  | ADiv a1 a2 => (Nat.div (aeval st a1) (aeval st a2))
  | AMod a1 a2 => (Nat.modulo (aeval st a1) (aeval st a2))
  end.


Fixpoint beval{s e: nat} (st : state s e) 
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
  | BOr b1 b2 => orb  (beval st b1) (beval st b2)
  end.


Fixpoint exp_U{n:nat} (U:Square (2^n)) (i:nat):(Square (2^n)):=
    match i with
    |0=> I (2^n)
    |S i'=> U × (exp_U U i')
    end.
Notation "U ^ i":=(exp_U U i).
Lemma  pow_U_unitary: forall s e (U: Square (2^(e-s))) i,
WF_Unitary U ->
WF_Unitary (U^i).
Proof. induction i; simpl; intros. apply id_unitary.
      apply Mmult_unitary. assumption. intuition.  
Qed.

Local Open Scope state_scope.
Fixpoint big_app{s e:nat} (f : nat -> list (cstate * qstate s e)) (n_0 : nat) : list (cstate * qstate s e) := 
  match n_0 with
  | 0 => nil
  | S n' =>  (big_app f n') +l (f n')
  end.


Inductive big_app'{s e:nat}: (nat -> (cstate * qstate s e)) -> nat-> list (cstate * qstate s e)-> Prop := 
|big_app_0: forall f, big_app' f 0 nil 
|big_app_cons_Zero: forall (f: nat -> (cstate * qstate s e)) n l, 
               snd (f n) = Zero -> big_app' f n l-> big_app' f (S n) l
|big_app_cons: forall (f: nat -> (cstate * qstate s e)) n l, 
snd (f n) <> Zero -> big_app' f n l-> big_app' f (S n) (l +l [(f n)]).

          

Local Open Scope com_scope.



Lemma d_par_trace_app{ s e :nat}: forall n l r(f: nat -> list (cstate *qstate s e)),
(d_par_trace
        (big_app
           (fun j : nat => f j) n) l r)=
big_app (fun j :nat => d_par_trace (f j) l r) n. 
Proof. induction n; intros;
       simpl; try reflexivity.
       rewrite d_par_trace_map2.
       rewrite IHn. reflexivity.
Qed.

Lemma d_par_trace_app'{ s e :nat}: forall n l r (f: nat ->  (cstate *qstate s e)) mu,
(big_app' (fun j : nat => f j) n) mu ->
(exists mu', (big_app' (fun j :nat => (fst (f j), (PMpar_trace (snd (f j)) l r))) n mu')
/\ (d_par_trace mu l r)= mu'). 
Proof. induction n; intros. inversion_clear H.
       exists nil. simpl. split. econstructor.
       reflexivity. 
       inversion_clear H.
       apply (IHn l r) in H1. destruct H1. 
       exists x. split. 
       econstructor. simpl. rewrite H0. admit.
       apply H. apply H.
       rewrite d_par_trace_map2.
       apply (IHn l r) in H1. destruct H1.
       exists (x +l (d_par_trace [f n] l r)).
       assert(d_par_trace [f n] l r=
       [(fun j : nat =>
       (fst (f j), PMpar_trace (snd (f j)) l r)) n]).
       destruct (f n).
       simpl. reflexivity. rewrite H1. 
       split. apply (big_app_cons ((fun j : nat =>
       (fst (f j), PMpar_trace (snd (f j)) l r)))).
        simpl. 
       admit.
       apply H. f_equal. apply H.
Admitted.



Definition QInit_fun{s0 e0:nat} (s e:nat) (rho:(qstate s0 e0)):=
  big_sum (fun i:nat=>  
  q_update (((I (2^(s-s0))) ⊗ ((Vec (2^(e-s)) 0) × (Vec (2^(e-s)) i )†) ⊗ (I (2^(e0-e)))))  rho) (2^(e-s)) .

Definition QUnit_One_fun{s0 e0:nat} (s e:nat)(U: Square (2^(e-s)))  (rho:qstate s0 e0):= 
  q_update ((I (2^(s-s0)) ⊗ U ⊗ (I (2^(e0-e))))) rho .

Definition QUnit_Ctrl_fun{s' e':nat} (s0 e0 s1 e1:nat) (U: nat->Square (2^(e1-s1))) (rho:qstate s' e') :=
  q_update  ((big_sum (fun i:nat => @Mmult (2^(e'-s')) (2^(e'-s')) (2^(e'-s'))
                (I (2^(s0-s')) ⊗ (∣ i ⟩_ (e0-s0) × ⟨ i ∣_ (e0-s0) ) ⊗ (I (2^(e'-e0)))) 
                 (I (2^(s1-s')) ⊗ (U i) ⊗ (I (2^(e'-e1))))) (2^(e0 -s0)))) rho.

Local Open Scope nat_scope.



Definition  QMeas_fun{s' e':nat} (s e j:nat) (rho: qstate s' e'):= 
(q_update (((I (2^(s-s'))) ⊗ ((Vec (2^(e-s)) j) × (Vec (2^(e-s)) j )†) ⊗ (I (2^(e'-e))))) rho).


Fixpoint Zero_list{ s e:nat} (mu:list (cstate * qstate s e) ):= 
  match mu with 
  |nil => True
  |(c,q) :: mu'=> q= Zero /\ Zero_list mu' 
  end. 




(* Lemma big_app_not_0{s e:nat}: forall n0 (f: nat -> list(cstate * qstate s e)), 
(forall i : nat,
i < n0 -> Zero_list (f i) )->
  (Zero_list (big_app f n0).
  Proof. Admitted. *)



  Inductive ceval_single{s' e':nat}: com-> list (cstate * (qstate s' e' )) -> list (cstate * (qstate s' e')) -> Prop:=
  |E_nil:  forall  c, ceval_single c nil nil
  |E_Skip sigma rho mu:  ceval_single <{skip}> ((sigma,rho)::mu) ((sigma,rho)::mu)
  |E_Abort sigma rho mu: ceval_single <{abort}> ((sigma,rho)::mu) nil
  |E_Asgn sigma rho mu: forall x a mu', 
                   ceval_single (CAsgn x a) mu mu'
                -> ceval_single (CAsgn x a) ((sigma,rho)::mu) 
                    (StateMap.Raw.map2 option_app 
                    [((c_update x (aeval (sigma, rho) a) sigma), rho)] 
                    mu')
  |Elet sigma rho mu : forall (x a:nat) ,  let x:= a in 
                   ceval_single (Clet x a) ((sigma,rho)::mu) ((sigma,rho)::mu)
  |E_Qinit sigma rho mu: forall mu'(s e:nat), s'<=s/\ s<e /\ e<=e'->
                   ceval_single (QInit s e) mu mu'
                   -> ceval_single (QInit s e) ((sigma,rho)::mu) 
                   (StateMap.Raw.map2 option_app [(sigma, (QInit_fun s e rho))] mu')
  |E_Qunit_One sigma rho mu: forall mu' (s e:nat) (U: Square (2^(e-s))), 
                   (s'<=s/\s<e /\ e<=e')
                 ->(WF_Unitary U)
                 -> ceval_single (QUnit_One s e U) mu mu'
                -> ceval_single (QUnit_One s e U) ((sigma,rho)::mu) 
                (StateMap.Raw.map2 option_app [(sigma, QUnit_One_fun s e U rho)] mu')
  |E_QUnit_Ctrl sigma rho mu: forall mu' (s0 e0 s1 e1:nat) (U: nat->Square (2^(e1-s1))), 
                  (s'<=s0) /\ (s0<e0)/\ (e0<=s1) /\ (s1<e1) /\ (e1<=e')
                   ->(forall i,WF_Unitary (U i))
                   -> ceval_single (QUnit_Ctrl s0 e0 s1 e1 U) mu mu'
                   -> ceval_single (QUnit_Ctrl s0 e0 s1 e1 U) ((sigma,rho)::mu) 
                (StateMap.Raw.map2 option_app [(sigma, (QUnit_Ctrl_fun s0 e0 s1 e1 U rho))] mu')
  |E_Meas sigma rho mu: forall mu' mu'' (i:nat) (s e:nat),
                (s'<=s/\s<e /\ e<=e') ->
                  ceval_single (QMeas i s e) mu mu'->
                  (big_app' (fun j:nat=> 
                  ((c_update i j sigma), (QMeas_fun s e j rho)) ) 
                  (2^(e-s)) mu'')->
                   ceval_single (QMeas i s e) ((sigma,rho)::mu)
                  (StateMap.Raw.map2 option_app 
                  mu'' mu' )               
  |E_Seq sigma rho mu : forall c1 c2 (mu1 mu2:list (cstate * (qstate s' e'))),  
                  ceval_single c1 ((sigma,rho)::mu) mu1 
                  ->ceval_single c2 mu1 mu2
                  ->ceval_single (<{c1;c2}>) ((sigma,rho)::mu) mu2
  |E_IF_true sigma rho mu: forall (mu' mu'':list (cstate * (qstate s' e'))) c1 c2 b, 
                        (beval (sigma, rho) b)=true
                        ->ceval_single (CIf b c1 c2) mu mu''
                        ->ceval_single c1 ([(sigma,rho)]) mu'
                        ->ceval_single (CIf b c1 c2) ((sigma,rho)::mu)  
                           (StateMap.Raw.map2 option_app mu' mu'')
  |E_IF_false sigma rho mu: forall (mu' mu'':list (cstate * (qstate s' e'))) c1 c2 b, 
                      (beval (sigma, rho) b)=false
                      ->ceval_single (CIf b c1 c2) mu mu''
                      ->ceval_single c2 ([(sigma,rho)]) mu'
                      ->ceval_single (CIf b c1 c2) ((sigma,rho)::mu)  
                        (StateMap.Raw.map2 option_app mu' mu'')
  |E_While_true sigma rho mu: forall (mu' mu'' mu1:list (cstate * (qstate s' e'))) c b, 
                        (beval (sigma, rho) b)=true
                        ->ceval_single (CWhile b c) mu mu''
                        ->ceval_single c [(sigma,rho)] mu1 
                        ->ceval_single (CWhile b c) mu1 mu'
                        ->ceval_single (CWhile b c) ((sigma,rho)::mu)  
                           (StateMap.Raw.map2 option_app mu' mu'')
  |E_While_false sigma rho mu: forall (mu':list (cstate * (qstate s' e'))) c b, 
                      (beval (sigma, rho) b)=false
                      ->ceval_single (CWhile b c) mu mu'
                      ->ceval_single (CWhile b c) ((sigma,rho)::mu)  
                       (StateMap.Raw.map2 option_app [(sigma,rho)] mu').

  Inductive ceval{s e:nat}: com -> dstate s e-> dstate s e->Prop:=
  |E_com:  forall c (mu mu':dstate s e), 
          WF_dstate mu-> WF_dstate mu'->
        (ceval_single c (StateMap.this mu) (StateMap.this mu'))->
          ceval c mu mu'.
(*------------------------------FV-----------------------------------------*)
Definition CSet:=NSet.t.
Fixpoint Free_aexp (a:aexp) : CSet :=
  match a with
  | ANum n => NSet.empty 
  | AId x => NSet.add x (NSet.empty)                      
  | <{a1 + a2}> => NSet.union (Free_aexp a1)  (Free_aexp a2)
  | <{a1 - a2}> => NSet.union (Free_aexp a1)  (Free_aexp a2)
  | <{a1 * a2}> => NSet.union (Free_aexp a1)  (Free_aexp a2)
  | AGcd a1 a2 => NSet.union (Free_aexp a1)  (Free_aexp a2)
  | APow a1 a2 => NSet.union (Free_aexp a1)  (Free_aexp a2)
  |ADiv a1 a2 => NSet.union (Free_aexp a1)  (Free_aexp a2)
  |AMod a1 a2 => NSet.union (Free_aexp a1)  (Free_aexp a2)
  end.

Fixpoint Free_bexp (b:bexp):CSet:=
  match b with
    | <{a1 = a2}>   => NSet.union (Free_aexp a1)  (Free_aexp a2)
    | <{a1 <> a2}>  => NSet.union (Free_aexp a1)  (Free_aexp a2)
    | <{a1 <= a2}>  => NSet.union (Free_aexp a1)  (Free_aexp a2)
    | <{a1 > a2}>   => NSet.union (Free_aexp a1)  (Free_aexp a2)
    | <{~ b}>       => (Free_bexp b) 
    | <{b1 && b2}>  => NSet.union (Free_bexp b1)  (Free_bexp b2)
    | BOr b1 b2  => NSet.union (Free_bexp b1)  (Free_bexp b2)
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
         => (NSet.add x (NSet.empty), Qsys_to_Set  s e )
    |_=>(NSet.empty, NSet.empty)
  end.  

Local Open Scope com_scope.
Fixpoint MVar (c:com): (CSet * QSet) :=
  match c with
    |<{ x:=a }> => (NSet.add x NSet.empty, NSet.empty)
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
         => (NSet.add x (NSet.empty), Qsys_to_Set s e  )
    |_=>(NSet.empty, NSet.empty)
  end.


(*-----------------------------------Ceval-----------------------------------------------*)


Lemma QInit_fun_plus{s' e':nat}: forall s e (q q0: qstate s' e'), 
s'<=s/\s<=e/\e<=e'->
@Mplus (2^(e'-s')) (2^(e'-s')) (QInit_fun s e q) (QInit_fun s e q0)=
@QInit_fun s' e' s e (q .+ q0) .
Proof. unfold QInit_fun. unfold q_update.
unfold super.   intros. unfold qstate.
assert(2^(s-s') * 2^(e-s) * 2^(e'-e)= 2^(e'-s'))%nat.
type_sovle'. destruct H0. 
rewrite <-(@Msum_plus (2 ^ (e - s)) 
((2 ^ (s - s') * 2 ^ (e - s) * 2 ^ (e' - e)))
((2 ^ (s - s') * 2 ^ (e - s) * 2 ^ (e' - e)))).
apply big_sum_eq_bounded. intros.
rewrite Mmult_plus_distr_l. 
rewrite Mmult_plus_distr_r. reflexivity.
Qed.

Lemma QInit_fun_scale{s' e':nat}: forall s e p (q : qstate s' e'), 
s'<=s/\s<=e/\e<=e'->
@QInit_fun s' e' s e (p .* q) =
p .* (QInit_fun s e q) .
Proof. unfold QInit_fun. unfold q_update. unfold super.  intros.
assert(2^(s-s') * 2^(e-s) * 2^(e'-e)= 2^(e'-s'))%nat.
type_sovle'. destruct H0.
rewrite <-(@Mscale_Msum_distr_r 
((2 ^ (s - s') * 2 ^ (e - s) * 2 ^ (e' - e)))
((2 ^ (s - s') * 2 ^ (e - s) * 2 ^ (e' - e))) (2 ^ (e - s)) ). 
apply big_sum_eq_bounded. intros.

rewrite Mscale_mult_dist_r.
rewrite Mscale_mult_dist_l. reflexivity.
Qed.


Lemma QInit_fun_kron{s0 x e0:nat}: forall s e (p : qstate s0 x)
(q: qstate x e0), 
@WF_Matrix (2^(e0-x)) (2^(e0-x)) q->
s0<=s/\s<=e/\e<=x/\x<=e0->
@QInit_fun s0 e0  s e (@kron (2^(x-s0)) (2^(x-s0)) (2^(e0-x))
(2^(e0-x)) p q) =
@kron  (2^(x-s0)) (2^(x-s0)) (2^(e0-x))
(2^(e0-x)) (QInit_fun s e p) q.
Proof. unfold QInit_fun. unfold q_update. unfold super.  intros.
assert(2 ^ (s - s0) * 2 ^ (e - s) * 2 ^ (x - e)= 2^(x-s0))%nat.
type_sovle'. destruct H1.
rewrite (@kron_Msum_distr_r 
(2 ^ (s - s0) * 2 ^ (e - s) * 2 ^ (x - e))
(2 ^ (s - s0) * 2 ^ (e - s) * 2 ^ (x - e))
(2^(e0-x)) (2^(e0-x))). apply big_sum_eq_bounded.
intros. repeat rewrite kron_adjoint.
repeat rewrite id_adjoint_eq. 
rewrite Mmult_adjoint. rewrite adjoint_involutive.
apply Logic.eq_trans with (((I (2 ^ (s - s0))
⊗ (∣ 0 ⟩_ (e - s) × ⟨ x0 ∣_ (e - s))
⊗ I (2 ^ (x - e))) ⊗ I (2 ^ (e0 - x))) × (p ⊗ q)
× ((I (2 ^ (s - s0))
   ⊗ (∣ x0 ⟩_ (e - s) × ⟨ 0 ∣_ (e - s))
   ⊗ I (2 ^ (x - e))) ⊗ I (2 ^ (e0 - x))) ).
f_equal; type_sovle'. f_equal; type_sovle'.
repeat rewrite kron_assoc; auto_wf. f_equal; type_sovle'.
repeat rewrite kron_assoc; auto_wf. f_equal; type_sovle'.
rewrite id_kron. f_equal; type_sovle'.
apply WF_mult. apply WF_vec. apply pow_gt_0.
auto_wf. apply WF_kron; type_sovle'. auto_wf.
apply WF_mult. apply WF_vec. apply pow_gt_0.
auto_wf. apply WF_mult. apply WF_vec. apply pow_gt_0.
auto_wf.
assert(2 ^ (s - s0) * 2 ^ (e - s) * 2 ^ (e0 - e)= 2^(e0-s0))%nat.
type_sovle'. destruct H2.
repeat rewrite kron_adjoint. repeat rewrite id_adjoint_eq.
rewrite Mmult_adjoint. rewrite adjoint_involutive.
repeat rewrite kron_assoc; auto_wf.
f_equal; type_sovle'.
rewrite id_kron. f_equal; type_sovle'. f_equal; type_sovle'.
apply WF_mult. auto_wf. apply WF_adjoint. apply WF_vec.
apply pow_gt_0. apply WF_kron; type_sovle'. auto_wf.
apply WF_mult. auto_wf. apply WF_adjoint. apply WF_vec.
apply pow_gt_0. apply WF_mult. auto_wf. apply WF_adjoint. apply WF_vec.
apply pow_gt_0. 
repeat rewrite kron_mixed_product.
 rewrite Mmult_1_r; auto_wf.  rewrite Mmult_1_l; auto_wf.
reflexivity.
Qed. 

Lemma QUnit_One_fun_kron{s0 x e0:nat}: forall s e U (p : qstate s0 x)
(q: qstate x e0), 
WF_Matrix U->
@WF_Matrix (2^(e0-x)) (2^(e0-x)) q->
s0<=s/\s<=e/\e<=x/\x<=e0->
@QUnit_One_fun s0 e0  s e U (@kron (2^(x-s0)) (2^(x-s0)) (2^(e0-x))
(2^(e0-x)) p q) =
@kron  (2^(x-s0)) (2^(x-s0)) (2^(e0-x))
(2^(e0-x)) (QUnit_One_fun s e U p) q.
Proof. unfold QUnit_One_fun.  intros. unfold q_update.
unfold super. 
assert(2 ^ (s - s0) * 2 ^ (e - s) * 2 ^ (x - e)= 2^(x-s0))%nat.
type_sovle'. destruct H2.
assert(2 ^ (s - s0) * 2 ^ (e - s) * 2 ^ (e0 - e)= 2^(e0-s0))%nat.
type_sovle'. destruct H2.
repeat rewrite kron_adjoint.
repeat rewrite id_adjoint_eq. 
apply Logic.eq_trans with ((I (2 ^ (s - s0)) ⊗ U ⊗ I (2 ^ (x - e))
 ⊗ I (2 ^ (e0 - x))) × (p ⊗ q)
× ((I (2 ^ (s - s0)) ⊗ (U) † ⊗ I (2 ^ (x - e))) ⊗ I (2 ^ (e0 - x))) ).
f_equal; type_sovle'. f_equal; type_sovle'.
repeat rewrite kron_assoc; auto_wf. f_equal; type_sovle'.
f_equal; type_sovle'.
rewrite id_kron. f_equal; type_sovle'.
repeat rewrite kron_assoc; auto_wf. f_equal; type_sovle'.
rewrite id_kron. f_equal; type_sovle'. f_equal; type_sovle'.
repeat rewrite kron_mixed_product.
 rewrite Mmult_1_r; auto_wf.  rewrite Mmult_1_l; auto_wf.
reflexivity.
Qed.



Lemma QUnit_One_fun_plus{s' e':nat}: forall s e (q q0: qstate s' e') (U:Square (2^(e-s))), 
s'<=s/\s<=e/\e<=e'->
@Mplus (2^(e'-s')) (2^(e'-s')) (QUnit_One_fun s e U q0) (QUnit_One_fun s e U q)=
@QUnit_One_fun s' e' s e U (q0 .+ q).
Proof. unfold QUnit_One_fun.  intros. 
unfold q_update. unfold super.
assert(2^(e'-s')=2^(s-s') * 2^(e-s) * 2^(e'-e))%nat.
type_sovle'. destruct H0.
rewrite Mmult_plus_distr_l. 
rewrite Mmult_plus_distr_r. reflexivity.
Qed.


Lemma QUnit_One_fun_scale{s' e':nat}: forall s e p (q : qstate s' e') (U:Square (2^(e-s))), 
s'<=s/\s<=e/\e<=e'->
@scale (2^(e'-s')) (2^(e'-s')) p (QUnit_One_fun s e U q)=
@QUnit_One_fun s' e' s e U (p .*  q).
Proof. unfold QUnit_One_fun.  intros. 
unfold q_update. unfold super.
assert(2^(e'-s')=2^(s-s') * 2^(e-s) * 2^(e'-e))%nat.
type_sovle'. destruct H0.
rewrite Mscale_mult_dist_r. 
rewrite Mscale_mult_dist_l. reflexivity.
Qed.

Lemma QUnit_Ctrl_fun_plus{s' e':nat}: forall s0 e0 s1 e1 (q q0: qstate s' e') (U: nat-> Square (2^(e1-s1))), 
s'<=s0/\s0<=e0 /\ e0<=s1/\s1<=e1/\e1<=e'->
@Mplus (2^(e'-s')) (2^(e'-s')) (QUnit_Ctrl_fun s0 e0 s1 e1 U q0) (QUnit_Ctrl_fun s0  e0 s1 e1 U q)=
@QUnit_Ctrl_fun s' e' s0 e0 s1 e1 U (q0 .+ q).
Proof. unfold QUnit_Ctrl_fun.  intros. 
unfold q_update. unfold super.
assert(2^(e'-s')=2^(s1-s') * 2^(e1-s1) * 2^(e'-e1))%nat.
type_sovle'. destruct H0.
rewrite Mmult_plus_distr_l. 
rewrite Mmult_plus_distr_r. reflexivity.
Qed.

Lemma QUnit_Ctrl_fun_scale{s e:nat}: forall s0 e0 s1 e1 p (q: qstate s e) (U: nat-> Square (2^(e1-s1))), 
s<=s0/\s0<=e0 /\ e0<=s1/\s1<=e1/\e1<=e->
@scale (2^(e-s)) (2^(e-s)) p (QUnit_Ctrl_fun s0  e0 s1 e1 U q)=
@QUnit_Ctrl_fun s e s0 e0 s1 e1 U (p .* q).
Proof. unfold QUnit_Ctrl_fun.  intros. 
unfold q_update. unfold super.
assert(2^(e-s)=2^(s1-s) * 2^(e1-s1) * 2^(e-e1))%nat.
type_sovle'. destruct H0.
rewrite Mscale_mult_dist_r. 
rewrite Mscale_mult_dist_l. reflexivity. 
Qed.

Lemma QUnit_Ctrl_fun_kron{s x e:nat}: forall s0 e0 s1 e1 (U:nat-> Square (2^(e1-s1))) (p : qstate s x)
(q: qstate x e), 
(forall j, WF_Matrix (U j))->
@WF_Matrix (2^(e-x)) (2^(e-x)) q->
s<=s0/\s0<=e0 /\ e0<=s1/\s1<=e1/\e1<=x /\ x<=e->
@QUnit_Ctrl_fun s e  s0 e0 s1 e1 U (@kron (2^(x-s)) (2^(x-s)) (2^(e-x))
(2^(e-x)) p q) =
@kron  (2^(x-s)) (2^(x-s)) (2^(e-x))
(2^(e-x)) (QUnit_Ctrl_fun s0 e0 s1 e1 U p) q.
Proof. unfold QUnit_Ctrl_fun.  intros. unfold q_update.
unfold super.  repeat rewrite Msum_adjoint.
assert(2^(e-s)=2^(s1-s) * 2^(e1-s1) * 2^(e-e1))%nat.
type_sovle'. destruct H2.
assert(2^(e-s)=2^(s0-s) * 2^(e0-s0) * 2^(e-e0))%nat.
type_sovle'. destruct H2.
Admitted.


Lemma QUnit_Ctrl_unitary{s e:nat}: forall (s0 e0 s1 e1:nat) (U: nat -> Square (2^(e1-s1))) ,
s<=s0/\s0<=e0/\ e0<=s1->s1<=e1/\ e1<=e->
(forall i, WF_Unitary (U i))->
WF_Unitary (big_sum (fun i:nat =>@Mmult (2^(e-s)) (2^(e-s)) (2^(e-s))
                (I (2^(s0-s)) ⊗ (∣ i ⟩_ (e0-s0) × ⟨ i ∣_ (e0-s0) ) ⊗ (I (2^(e-e0)))) 
                 (I (2^(s1-s)) ⊗ (U i) ⊗ (I (2^(e-e1))))) (2^(e0-s0))).
Proof. intros. unfold WF_Unitary in *. split. 
        apply WF_Msum. intros. apply WF_mult. 
        auto_wf. apply WF_kron;   type_sovle'. apply WF_kron; try reflexivity; 
        try auto_wf. apply H1. auto_wf.
        rewrite Msum_adjoint.
         rewrite Mmult_Msum_distr_l.
         rewrite (big_sum_eq_bounded _  
         (fun i : nat =>
         big_sum  (fun i0 : nat =>
           (I (2 ^ (s0-s)) ⊗ ((∣ i0 ⟩_ (e0 - s0) × ⟨ i0 ∣_ (e0 - s0))
                              × (∣ i ⟩_ (e0 - s0) × ⟨ i ∣_ (e0 - s0)))
           ⊗ I (2 ^ (s1 - e0)) ⊗ (((U i0)†) × (U i)) ⊗ I (2 ^ (e - e1)) ) )
           (2 ^ (e0 - s0)))). 
         rewrite (big_sum_eq_bounded _  
         (fun i : nat =>
          (I (2 ^ (s0-s)) ⊗ (∣ i ⟩_ (e0 - s0) × ⟨ i ∣_ (e0 - s0))
      ⊗ I (2 ^ (s1 - e0)) ⊗ I (2 ^ (e1 - s1)) ⊗ I (2 ^ (e - e1)) )) ).
        repeat rewrite <-kron_Msum_distr_r.
       rewrite <-kron_Msum_distr_l. 
        rewrite big_sum_I.    
        repeat rewrite id_kron; auto_wf.
        f_equal; type_sovle'. 
      intros. 
       apply big_sum_unique. exists x.
        split.  assumption. 
        split.  f_equal. f_equal. f_equal.
        f_equal. rewrite Mmult_assoc. 
        rewrite <-(Mmult_assoc (⟨ x ∣_ (e0 - s0))).
        rewrite Vec_inner_1. rewrite Mmult_1_l; auto_wf. reflexivity.
        assumption. apply H1.
        intros. rewrite Mmult_assoc. 
        rewrite <-(Mmult_assoc (⟨ x' ∣_ (e0 - s0))).
        rewrite Vec_inner_0. rewrite Mscale_0_l.
        rewrite Mmult_0_l. rewrite Mmult_0_r.
        rewrite kron_0_r. repeat rewrite kron_0_l. reflexivity.
        intuition. assumption. assumption.
        intros. rewrite Mmult_Msum_distr_r.  apply big_sum_eq_bounded.
        intros. 
        apply Logic.eq_trans with ((I (2 ^ (s0-s))
        ⊗ (∣ x0 ⟩_ (e0 - s0) × ⟨ x0 ∣_ (e0 - s0))
        ⊗ I (2^ (s1-e0)) ⊗ I (2^ (e1-s1)) ⊗ I (2 ^ (e - e1))
        × (I (2^ (s0-s)) ⊗ I (2^ (e0-s0)) ⊗ I (2 ^ (s1 - e0)) ⊗ U x0 ⊗ I (2 ^ (e - e1)))) †
       × (I (2 ^ (s0-s))
          ⊗ (∣ x ⟩_ (e0 - s0) × ⟨ x ∣_ (e0 - s0))
          ⊗ I (2^ (s1-e0)) ⊗ I (2^ (e1-s1)) ⊗ I (2 ^ (e - e1))
          × (I (2^ (s0-s)) ⊗ I (2^ (e0-s0)) ⊗ I (2 ^ (s1 - e0)) ⊗ U x ⊗ I (2 ^ (e - e1))))).
        f_equal; type_sovle';  repeat rewrite id_kron; auto_wf; f_equal; type_sovle'.
         f_equal; type_sovle'. repeat rewrite kron_assoc; auto_wf; f_equal; type_sovle'.
         f_equal; type_sovle'. repeat rewrite id_kron; auto_wf. f_equal; type_sovle'.
         repeat rewrite id_kron; auto_wf.
         f_equal; type_sovle'; f_equal; type_sovle'. f_equal; type_sovle'.
         repeat rewrite kron_assoc; auto_wf; f_equal; type_sovle'.
         f_equal; type_sovle'.  repeat rewrite id_kron; auto_wf. f_equal; type_sovle'.
         f_equal; type_sovle'; f_equal; type_sovle'. f_equal; type_sovle'.
           rewrite Mmult_adjoint.
        repeat rewrite kron_adjoint.  rewrite Mmult_adjoint.
        repeat rewrite id_adjoint_eq. rewrite adjoint_involutive.
        repeat rewrite kron_mixed_product. repeat rewrite Mmult_1_r; auto_wf. 
        repeat rewrite Mmult_1_l; auto_wf. reflexivity. apply H1.
        apply WF_adjoint. apply H1.
Qed.  

Lemma  big_sum_trace{n:nat}: forall (f: nat-> Square n) n0,
trace (big_sum f n0)= big_sum (fun x=> (trace (f x))) n0 .
Proof. induction n0. simpl. rewrite Zero_trace. reflexivity.
      simpl. rewrite trace_plus_dist. f_equal. intuition.
  
Qed.

Lemma QMeas_fun_plus{s' e':nat}: forall s e  x (q q0: qstate s' e') , 
s'<=s/\s<=e/\e<=e'->
@Mplus (2^(e'-s')) (2^(e'-s')) (QMeas_fun s e x q0) (QMeas_fun s e x q)=
@QMeas_fun s' e' s e x (q0 .+ q).
Proof. unfold QMeas_fun.  intros. 
unfold q_update. unfold super.
assert(2^(e'-s')=2^(s-s') * 2^(e-s) * 2^(e'-e))%nat.
type_sovle'. destruct H0.
rewrite Mmult_plus_distr_l. 
rewrite Mmult_plus_distr_r. reflexivity.
Qed.


Lemma QMeas_fun_scale{s' e':nat}: forall s e  x p (q: qstate s' e') , 
s'<=s/\s<=e/\e<=e'->
@scale (2^(e'-s')) (2^(e'-s')) p (QMeas_fun s e x q)=
@QMeas_fun s' e' s e x (p .*  q).
Proof. unfold QMeas_fun.  intros. 
unfold q_update. unfold super.
assert(2^(e'-s')=2^(s-s') * 2^(e-s) * 2^(e'-e))%nat.
type_sovle'. destruct H0.
rewrite Mscale_mult_dist_r. 
rewrite Mscale_mult_dist_l. reflexivity.
Qed.





Lemma QMeas_fun_kron{s0 x e0:nat}: forall s e i (p : qstate s0 x)
(q: qstate x e0), 
i<(2^(e-s))%nat->
@WF_Matrix (2^(e0-x)) (2^(e0-x)) q->
s0<=s/\s<=e/\e<=x/\x<=e0->
@QMeas_fun s0 e0 s e i (@kron (2^(x-s0)) (2^(x-s0)) (2^(e0-x))
(2^(e0-x)) p q) =
@kron  (2^(x-s0)) (2^(x-s0)) (2^(e0-x))
(2^(e0-x)) (QMeas_fun s e i p) q.
Proof. unfold QMeas_fun.  intros. unfold q_update.
unfold super. 
assert(2 ^ (s - s0) * 2 ^ (e - s) * 2 ^ (x - e)= 2^(x-s0))%nat.
type_sovle'. destruct H2.
assert(2 ^ (s - s0) * 2 ^ (e - s) * 2 ^ (e0 - e)= 2^(e0-s0))%nat.
type_sovle'. destruct H2.
repeat rewrite kron_adjoint.
repeat rewrite id_adjoint_eq. 
apply Logic.eq_trans with ((I (2 ^ (s - s0)) ⊗ (∣ i ⟩_ (e - s) × ⟨ i ∣_ (e - s)) ⊗ I (2 ^ (x - e))
 ⊗ I (2 ^ (e0 - x))) × (p ⊗ q)
× ((I (2 ^ (s - s0)) ⊗ ((∣ i ⟩_ (e - s) × ⟨ i ∣_ (e - s))) † ⊗ I (2 ^ (x - e))) ⊗ I (2 ^ (e0 - x))) ).
f_equal; type_sovle'. f_equal; type_sovle'.
repeat rewrite kron_assoc; auto_wf. f_equal; type_sovle'.
f_equal; type_sovle'.
rewrite id_kron. f_equal; type_sovle'.
repeat rewrite kron_assoc; auto_wf. f_equal; type_sovle'.
rewrite id_kron. f_equal; type_sovle'. f_equal; type_sovle'.
repeat rewrite kron_mixed_product.
 rewrite Mmult_1_r; auto_wf.  rewrite Mmult_1_l; auto_wf.
reflexivity.
Qed.




Lemma QInit_trace{s' e':nat}: forall (s e:nat) (rho:Square (2^(e'-s'))),
s'<=s/\s<=e/\ e<=e'-> WF_Matrix rho->
@trace  (2^(e'-s')) (QInit_fun s e rho) = @trace  (2^(e'-s')) rho.
Proof. 
      unfold QInit_fun.  unfold q_update. unfold super. intros. 
      assert( (2 ^ (s-s') * 2 ^ (e - s) * 2 ^ (e' - e))%nat=  (Nat.pow (S (S O)) (e'-s'))% nat).
      type_sovle'. destruct H1. 
      rewrite (@big_sum_trace ((2 ^ (s - s') *
      2 ^ (e - s) * 2 ^ (e' - e)))). 
      rewrite (big_sum_eq_bounded  _
      (fun x : nat =>
      trace ((I (2 ^ (s-s')) ⊗ (∣ x ⟩_ (e - s) × ⟨ x ∣_ (e - s))
      ⊗ I (2 ^ (e' - e)))  × rho))).
      rewrite <-big_sum_trace. 
      f_equal. type_sovle'.
      rewrite <-Mmult_Msum_distr_r.
      rewrite <-kron_Msum_distr_r .
      rewrite <-kron_Msum_distr_l.
      rewrite big_sum_I. rewrite id_kron. rewrite id_kron.
      rewrite Mmult_1_l. reflexivity. 
      assert(2 ^ (s-s') * 2 ^ (e - s) * 2 ^ (e' - e) = (2 ^ (e'-s'))%nat).
      type_sovle'. destruct H1. assumption.
      intros. rewrite trace_mult.   
      repeat rewrite kron_adjoint. repeat rewrite id_adjoint_eq.
      rewrite Mmult_adjoint. rewrite adjoint_involutive.
      rewrite <-Mmult_assoc. 
      repeat  rewrite kron_mixed_product.  repeat rewrite Mmult_1_r.
      rewrite <-Mmult_assoc.  rewrite (Mmult_assoc _ (⟨ 0 ∣_ (e - s)) _).
      assert((⟨ 0 ∣_ (e - s) × ∣ 0 ⟩_ (e - s)) = I 1). 
      apply Vec_inner_1. apply pow_gt_0. rewrite H2.  rewrite Mmult_1_r. reflexivity.
      auto_wf. auto_wf. auto_wf.
Qed.


Lemma QUnit_One_trace
{s' e':nat}:forall (s e:nat)(U: Square (2^(e-s)))  (rho:qstate s' e'),
s'<=s/\s<=e/\ e<=e'-> @WF_Matrix (2^(e'-s')) (2^(e'-s')) rho->
WF_Unitary U-> 
@trace (2^(e'-s')) (QUnit_One_fun s e U rho) = @trace (2^(e'-s')) rho.
Proof. 
intros.  unfold QUnit_One_fun. unfold q_update.
unfold super. rewrite <-trace_mult_Unitary. reflexivity.
assert(2 ^ (s-s') * 2 ^ (e - s) * 2 ^ (e' - e) = (2 ^ (e'-s'))%nat).
 type_sovle'. destruct H2.  
apply kron_unitary. apply kron_unitary. apply id_unitary. 
assumption. apply id_unitary. auto_wf.
Qed.


Lemma QUnit_Ctrl_trace{s e:nat}: forall (s0 e0 s1 e1:nat) (U: nat-> Square (2^(e1-s1))) (rho:qstate s e),
s<=s0/\s0<=e0/\ e0<=s1->s1<=e1/\ e1<=e->
@WF_Matrix (2^(e-s)) (2^(e-s)) rho->
(forall i, WF_Unitary (U i))-> @trace (2^(e-s)) (QUnit_Ctrl_fun s0 e0 s1 e1 U rho) = @trace (2^(e-s)) rho.
Proof. intros. unfold QUnit_Ctrl_fun. unfold q_update. unfold super. 
rewrite <-trace_mult_Unitary; try auto. 
apply QUnit_Ctrl_unitary; try assumption.
Qed.


Lemma WWF_dstate_big_app: forall s e (f:nat -> list (state s e)) n_0,
(forall i:nat, i< n_0 -> WWF_dstate_aux (f i) )->
WWF_dstate_aux (big_app (fun i:nat=> f  i) n_0).
Proof. intros. induction n_0. 
         simpl. apply WF_nil'.

         simpl. apply WWF_d_app_aux. 
         apply IHn_0.  intros. apply H. lia.
         apply H. lia. 
Qed.


Lemma big_app_trace{s e:nat}: forall (f:nat-> list (cstate * qstate s e)) n0,
(forall i : nat, i < n0 -> WWF_dstate_aux (f i) )->
d_trace_aux (big_app f n0) = big_sum (fun i=> d_trace_aux (f i)) n0 .
Proof. intros. induction n0.
      simpl. reflexivity.

      simpl. rewrite d_trace_app_aux. 
      f_equal. intuition. 
      apply WWF_dstate_big_app. intros.
      apply H. lia. apply H. lia.   
Qed.

Lemma WWF_dstate_big_app': forall s e  n (f:nat ->  (state s e))  mu,
(forall i : nat, i < n -> WWF_state (f i) \/ (snd (f i) = Zero) )->
(big_app' (fun i:nat=> f  i) n mu)->
WWF_dstate_aux mu.
Proof.   induction n; intros. 
         inversion H0; subst.
         apply WF_nil'.
         
         inversion H0; subst.
         apply IHn with f. intros. apply H. lia.
         assumption.

         apply WWF_d_app_aux.  
         apply IHn with f.  intros. apply H. lia.
         assumption. econstructor.
         pose (H n). destruct o. lia. assumption.
         rewrite H1 in H2. destruct H2. reflexivity.
         econstructor.
Qed.


Lemma big_app'_out_nil{ s e:nat}: forall n (f:nat-> (cstate * qstate s e)) l,
n>0 -> big_app' f n l-> 
l = [] ->(forall i, i < n ->snd (f i) = Zero).
Proof. induction n; intros. lia.
       inversion H0; subst.  
       destruct (Nat.eq_dec i n). rewrite e0.
       apply H4. apply IHn with []. lia. assumption.
       reflexivity. 
       lia. rewrite map2_comm in H7.
       apply map2_app_not_nil_l in H7. destruct H7.  
       discriminate.
Qed.


Lemma big_app'_trace{s e:nat}: forall n (f:nat-> (cstate * qstate s e))  mu,
(forall i : nat, i < n -> WWF_state (f i) \/ (snd (f i) = Zero) )->
big_app' f n mu -> 
d_trace_aux mu = big_sum (fun i=> s_trace (f i)) n.
Proof. induction n; intros.
       inversion_clear H0. simpl.
       reflexivity.

      inversion H0; subst. simpl. apply IHn in H4.
      rewrite H4. unfold s_trace.
      rewrite H2. rewrite Zero_trace. rewrite Cmod_0.
      rewrite Rplus_0_r. reflexivity. intros.
      apply H. lia.  

      rewrite d_trace_app_aux. simpl. 
      f_equal. intuition. rewrite Rplus_0_r. reflexivity.
      apply WWF_dstate_big_app' with n f. intros.
      apply H. lia. apply H4. econstructor.
      pose (H n). destruct o. lia. assumption.
      rewrite H1 in H2. destruct H2. reflexivity.
      econstructor.
Qed.

Require Import ParDensityO.
Lemma  big_sum_Cmod{n:nat}: forall (f:nat-> Square n) n0,
(forall i:nat, (i<n0)%nat-> Mixed_State_aux (f i)\/ f i =Zero)->
Cmod (trace (big_sum f n0)) = 
big_sum (fun i=> Cmod (trace (f i))) n0 .
Proof. induction n0.
    { simpl. intros. rewrite Zero_trace. 
     rewrite Cmod_0.  reflexivity. }

    { intros.
    assert((forall i : nat,
    (i < S n0)%nat -> f i = Zero) \/ ~(forall i : nat,
    (i < S n0)%nat ->
    f i = Zero)).
     apply Classical_Prop.classic. destruct H0.
     rewrite big_sum_0_bounded.  rewrite big_sum_0_bounded.
     rewrite Zero_trace. rewrite Cmod_0. reflexivity.
     intros. rewrite H0. rewrite Zero_trace. rewrite Cmod_0. reflexivity.
     lia. apply H0. simpl. 
     bdestruct (n0=?0).

     rewrite H1. simpl. rewrite Mplus_0_l.
     rewrite Rplus_0_l. reflexivity.

     assert((forall i : nat,
     (i <  n0)%nat -> f i = Zero) \/ ~(forall i : nat,
     (i <  n0)%nat ->
     f i = Zero)).
     apply Classical_Prop.classic. destruct H2.
     rewrite big_sum_0_bounded.  rewrite big_sum_0_bounded.
     rewrite Mplus_0_l.
     rewrite Rplus_0_l. reflexivity.
     intros. rewrite H2. rewrite Zero_trace.
     rewrite Cmod_0. reflexivity. lia.
     intros. rewrite H2. reflexivity. lia. 
     assert(f n0 = Zero \/ f n0 <> Zero).
     apply Classical_Prop.classic. 
     destruct H3.

     rewrite H3. 
     rewrite Mplus_0_r. rewrite Zero_trace.
     rewrite Cmod_0. rewrite Rplus_0_r.
     apply IHn0. intros. apply H. lia.     
     rewrite mixed_state_Cmod_plus_aux. f_equal. apply IHn0.
     intros. apply H. lia.
     apply Mixed_State_aux_big_sum. lia. intros. apply H.
     lia. unfold not.  
     apply Classical_Pred_Type.not_all_ex_not in H2.
     destruct H2. exists x. 
     apply Classical_Prop.imply_to_and.
     assumption.

     assert(Mixed_State_aux (f n0) \/ f n0 = Zero).
     apply H. lia. intuition.   }
Qed.

Lemma WF_Mixed_aux : forall {n} (ρ : Density n), 
Mixed_State_aux ρ -> WF_Matrix ρ.
Proof.  induction 1; auto with wf_db. Qed.
#[export] Hint Resolve WF_Mixed : wf_db.

Require Import ParDensityO.


Lemma  Mixed_State_aux_eq{n:nat}: forall (q1 q2: Square (2^n)),
q1 = q2 -> Mixed_State_aux q1 -> Mixed_State_aux q2 .
Proof. intros. rewrite <-H. assumption.
Qed.

Local Open Scope nat_scope.
Lemma  QMeas_trace{s' e':nat}:  forall (s e i j:nat) sigma (rho: qstate s' e'),
s'<=s/\s<=e/\ e<=e'-> WWF_qstate rho->
@d_trace_aux s' e' ((big_app (fun j:nat=> 
[((c_update i j sigma), (QMeas_fun s e j rho)) ]) 
(2^(e-s)))) = @s_trace s' e' (sigma, rho).
Proof. 
        intros. unfold QMeas_fun.  
        assert( (2 ^ (e'-s'))%nat= (2 ^ (s-s') * 2 ^ (e - s) * 2 ^ (e' - e))%nat).
        type_sovle'. destruct H1.
        rewrite (big_app_trace _ (2 ^ (e - s))).
        simpl. unfold s_trace. simpl.  
        rewrite (big_sum_eq_bounded _  (fun i0 : nat =>
        (Cmod (@trace (2 ^ (e'-s'))   ((q_update  (I (2 ^ (s - s'))
        ⊗ (∣ i0 ⟩_ (e - s) × ⟨ i0 ∣_ (e - s)) ⊗ I (2 ^ (e' - e))) rho)))))).
        rewrite <-big_sum_Cmod. f_equal.  rewrite big_sum_trace.
        rewrite (big_sum_eq_bounded _ (fun x : nat =>
        trace (I (2 ^ (s-s')) ⊗ (∣ x ⟩_ (e - s) × ⟨ x ∣_ (e - s)) ⊗ I (2 ^ (e' - e))
        × rho)) _ ). rewrite <-big_sum_trace. 
        f_equal. type_sovle'.  
        rewrite <-Mmult_Msum_distr_r.
        rewrite <-kron_Msum_distr_r .
        rewrite <-kron_Msum_distr_l.
        rewrite big_sum_I. rewrite id_kron. rewrite id_kron.
        rewrite Mmult_1_l. reflexivity. 
        unfold WF_qstate in *. apply WF_Mixed_aux.
        unfold WWF_qstate in H0. assert(2 ^ (s-s') * 2 ^ (e - s) * 2 ^ (e' - e) = (2 ^ (e'-s'))%nat).
        type_sovle'. destruct H1.  
        assumption.  unfold q_update. unfold super.
        intros.  rewrite trace_mult. 
        assert(  (2 ^ (s-s') * 2 ^ (e - s) * 2 ^ (e' - e))%nat= (2 ^ (e'-s'))%nat).
        type_sovle'. destruct H2. 
        repeat rewrite kron_adjoint. repeat rewrite id_adjoint_eq.
        rewrite Mmult_adjoint. rewrite adjoint_involutive.
        rewrite <-Mmult_assoc. 
        repeat  rewrite kron_mixed_product.  repeat rewrite Mmult_1_r.
        rewrite <-Mmult_assoc.  rewrite (Mmult_assoc _ (⟨ x ∣_ (e - s)) _).
        assert((⟨ x ∣_ (e - s) × ∣ x ⟩_ (e - s)) = I 1). 
        apply Vec_inner_1. assumption. rewrite H2.  rewrite Mmult_1_r. reflexivity.
        auto_wf. auto_wf. auto_wf. assert(2 ^ (e - s) > 0). apply pow_gt_0.
        intros. 
        assert(2^(e'-s')=2 ^ (s-s') * 2 ^ (e - s) * 2 ^ (e' - e)). type_sovle'.
        destruct H3.  
        assert(q_update
        (I (2 ^ (s - s'))
        ⊗ (∣ i0 ⟩_ (e - s) × ⟨ i0 ∣_ (e - s))
        ⊗ I (2 ^ (e' - e))) rho = Zero \/ q_update
        (I (2 ^ (s - s'))
        ⊗ (∣ i0 ⟩_ (e - s) × ⟨ i0 ∣_ (e - s))
        ⊗ I (2 ^ (e' - e))) rho <> Zero).
        apply Classical_Prop.classic. destruct H3.
        right. assumption. left. unfold q_update.
        apply mixed_super_aux. auto_wf.
        assumption.  assumption.
        intros.  rewrite Rplus_0_r. f_equal.  
        intros. econstructor.  unfold WWF_state. simpl.
        assert(2^(e'-s')=2 ^ (s-s') * 2 ^ (e - s) * 2 ^ (e' - e)). 
        type_sovle'. destruct H2.
        split. apply mixed_super_aux. auto_wf. 
        assumption. admit. lia. econstructor.
Admitted.


Lemma WWF_qstate_QMeas{s' e'}: forall s e (rho:qstate s' e') j,
s'<=s/\s<=e/\ e<=e'-> 
QMeas_fun s e j rho <> Zero ->
(j<2^(e-s))->
WWF_qstate rho-> 
WWF_qstate (QMeas_fun s e j rho).
Proof. intros.
unfold WWF_qstate. unfold QMeas_fun in *. unfold q_update in *.
apply mixed_super_aux. auto_wf. assumption. assumption.
Qed.

Lemma QMeas_fun_ge_0{s' e':nat}:forall j s e (rho : qstate s' e'), 
s' <= s /\ s <= e <= e'->
j<2 ^ (e - s)->
@Mixed_State_aux (2^(e'-s')) rho ->
@Mixed_State_aux (2^(e'-s')) (QMeas_fun s e j rho)\/ (QMeas_fun s e j rho)= Zero.
Proof. intros.
assert (QMeas_fun s e j rho = Zero \/ QMeas_fun s e j rho <> Zero).
apply Classical_Prop.classic. destruct H2.
right. assumption. left.
apply WWF_qstate_QMeas; try lia. 
assumption. apply H1.
Qed.


Lemma  QMeas_trace'{s' e':nat}:  forall (s e i j:nat) sigma (rho: qstate s' e') mu,
s'<=s/\s<=e/\ e<=e'-> WWF_qstate rho->
((big_app' (fun j:nat=> 
((c_update i j sigma), (QMeas_fun s e j rho))) 
(2^(e-s))) mu ) ->
@d_trace_aux s' e' mu = @s_trace s' e' (sigma, rho).
Proof. 
        intros. unfold QMeas_fun.  
        assert( (2 ^ (e'-s'))%nat= (2 ^ (s-s') * 2 ^ (e - s) * 2 ^ (e' - e))%nat).
        type_sovle'. destruct H2.
        rewrite (big_app'_trace  (2 ^ (e - s)) (fun j : nat =>
        (c_update i j sigma,
         QMeas_fun s e j rho)) ); try assumption.
        simpl. unfold s_trace. simpl.  
        rewrite (big_sum_eq_bounded _  (fun i0 : nat =>
        (Cmod (@trace (2 ^ (e'-s'))   ((q_update  (I (2 ^ (s - s'))
        ⊗ (∣ i0 ⟩_ (e - s) × ⟨ i0 ∣_ (e - s)) ⊗ I (2 ^ (e' - e))) rho)))))).
        rewrite <-big_sum_Cmod. f_equal.  rewrite big_sum_trace.
        rewrite (big_sum_eq_bounded _ (fun x : nat =>
        trace (I (2 ^ (s-s')) ⊗ (∣ x ⟩_ (e - s) × ⟨ x ∣_ (e - s)) ⊗ I (2 ^ (e' - e))
        × rho)) _ ). rewrite <-big_sum_trace. 
        f_equal. type_sovle'.  
        rewrite <-Mmult_Msum_distr_r.
        rewrite <-kron_Msum_distr_r .
        rewrite <-kron_Msum_distr_l.
        rewrite big_sum_I. rewrite id_kron. rewrite id_kron.
        rewrite Mmult_1_l. reflexivity. 
        unfold WF_qstate in *. apply WF_Mixed_aux.
        unfold WWF_qstate in H0. assert(2 ^ (s-s') * 2 ^ (e - s) * 2 ^ (e' - e) = (2 ^ (e'-s'))%nat).
        type_sovle'. destruct H2.  
        assumption.  unfold q_update. unfold super.
        intros.  rewrite trace_mult. 
        assert(  (2 ^ (s-s') * 2 ^ (e - s) * 2 ^ (e' - e))%nat= (2 ^ (e'-s'))%nat).
        type_sovle'. destruct H3. 
        repeat rewrite kron_adjoint. repeat rewrite id_adjoint_eq.
        rewrite Mmult_adjoint. rewrite adjoint_involutive.
        rewrite <-Mmult_assoc. 
        repeat  rewrite kron_mixed_product.  repeat rewrite Mmult_1_r; auto_wf.
        rewrite <-Mmult_assoc.  rewrite (Mmult_assoc _ (⟨ x ∣_ (e - s)) _).
        assert((⟨ x ∣_ (e - s) × ∣ x ⟩_ (e - s)) = I 1). 
        apply Vec_inner_1. assumption. rewrite H3.  rewrite Mmult_1_r; auto_wf. reflexivity.
        intros. apply (@QMeas_fun_ge_0 s' e'); try assumption.  
        intros. reflexivity. intros. unfold WWF_state.
        simpl. pose (@QMeas_fun_ge_0 s' e' _ _ _ rho H H2 H0).
        destruct o. left. split; try lia. assumption.
        right. assumption.  
Qed.





Lemma ceval_nil{s e:nat}: forall (mu:list (cstate * qstate s e)) c,
ceval_single c [] mu-> mu=nil.
Proof. intros. inversion H ;subst; try reflexivity.
Qed.

Lemma ceval_skip_1{s e:nat}: forall (mu mu':list (cstate *qstate s e)),
ceval_single <{skip}> mu mu'->mu=mu'.
Proof.   induction mu; intros; inversion H; subst; try
        reflexivity. Qed.

Lemma ceval_skip{s e:nat}: forall (mu:list (cstate *qstate s e)),
ceval_single <{skip}> mu mu.
Proof. induction mu; intros. apply E_nil.
 destruct a.
apply E_Skip.
Qed.


Lemma ceval_abort{s e:nat}: forall (mu:list (cstate *qstate s e)),
ceval_single <{abort}> mu [].
Proof. induction mu; intros.  apply E_nil.
destruct a.
apply E_Abort.
Qed.

Lemma ceval_abort_1{s e:nat}: forall (mu mu':list (cstate *qstate s e)),
ceval_single <{abort}> mu mu'->mu'= [].
Proof. induction mu; intros; inversion H;subst;
reflexivity.
Qed.

Lemma ceval_seq{s e:nat}: forall c1 c2 (mu mu' mu'':list (cstate *qstate s e)),
ceval_single c1 mu mu'->
ceval_single c2 mu' mu''->
ceval_single <{c1;c2}> mu mu''.
Proof. induction mu. intros. inversion H;subst.
inversion H0;subst.
apply E_nil.
intros.  destruct a. apply E_Seq with mu'.
intuition. intuition. 
Qed.

Lemma ceval_seq_1{s e: nat }: forall 
(mu mu': list (cstate *qstate s e)) c1 c2,
ceval_single <{ c1; c2 }> mu mu' ->
exists mu1,
and (ceval_single c1 mu mu1)
(ceval_single c2 mu1 mu').
Proof. induction mu; intros; inversion H; subst.
       exists nil. split. econstructor. econstructor.
       exists mu1. intuition. 
Qed.


Lemma  ceval_Qinit{s' e':nat}: forall c (q:qstate s' e') s e, 
s' <= s /\ s < e <= e' ->
ceval_single (QInit s e) ([(c,q)]) 
   ([(c, (QInit_fun s e q))]).
Proof. 
intros. apply  (@E_Qinit s' e' c q nil nil).  lia. econstructor.
Qed.


Lemma  ceval_QUnit_One{s' e':nat}: forall c (q:qstate s' e') s e (U:Square (2^(e-s))), 
s' <= s /\ s < e <= e' ->
WF_Unitary U->
ceval_single (QUnit_One s e U) ([(c,q)]) 
   ([(c, (QUnit_One_fun s e U q))]).
Proof. 
intros. apply  (@E_Qunit_One s' e' c q nil nil).  lia.
assumption. econstructor.
Qed.


Lemma  ceval_QUnit_Ctrl{s' e':nat}: forall c (s0 e0 s1 e1:nat) (q:qstate s' e') (U: nat->Square (2^(e1-s1))), 
(s'<=s0) /\ (s0<e0)/\ (e0<=s1) /\ (s1<e1) /\ (e1<=e')
 ->(forall i,WF_Unitary (U i))
 -> ceval_single (QUnit_Ctrl s0 e0 s1 e1 U) ([(c,q)]) 
 ([(c, (QUnit_Ctrl_fun s0 e0 s1 e1 U q))]).
Proof. 
intros. apply  (@E_QUnit_Ctrl s' e' c q nil nil).  lia.
assumption. econstructor.
Qed.

Lemma ceval_QMeas{s' e':nat}: forall c (q:qstate s' e') s e j mu, 
s' <= s /\ s < e <= e' ->
(big_app'
(fun j0 : nat =>
 (c_update j j0 c, QMeas_fun  s e j0 q)) (2 ^ (e - s)) mu)->
 ceval_single (QMeas j s e ) ([(c,q)])  mu.
Proof. 
intros. rewrite<-map2_nil_r.
apply  (@E_Meas s' e' c q nil nil ).  lia. econstructor.
assumption.
Qed.



Lemma state_eq_aexp{s e:nat}: forall (st st':state s e )  (a:aexp),
(fst st) = (fst st')-> (aeval st a) = aeval st' a.
Proof. intros. induction a.
      --reflexivity. 
      --simpl. rewrite H. reflexivity.
      --simpl.  rewrite IHa1. rewrite IHa2. reflexivity.
      --simpl.  rewrite IHa1. rewrite IHa2. reflexivity.
      --simpl.  rewrite IHa1. rewrite IHa2. reflexivity.
      --simpl.  rewrite IHa1. rewrite IHa2. reflexivity.
      --simpl.  rewrite IHa1. rewrite IHa2. reflexivity.
      --simpl.  rewrite IHa1. rewrite IHa2. reflexivity.
      --simpl.  rewrite IHa1. rewrite IHa2. reflexivity.
      
Qed.

Lemma state_eq_bexp{s e:nat}: forall (st st':state s e) (b:bexp),
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
      --simpl. rewrite IHb1.
      rewrite IHb2. reflexivity.
Qed.

Import Sorted.

Lemma ceval_app_while{s e:nat}: 
forall b c,
(forall  x y mu : list (cstate * qstate s e),
ceval_single c (x +l y) mu ->
exists mu1 mu2 : list (cstate * qstate s e),
ceval_single c x mu1 /\
ceval_single c y mu2 /\ mu = (mu1 +l mu2))->

(forall (mu mu' : list (cstate *qstate s e)),
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
      rewrite map2_nil_l.  reflexivity.

      destruct p.
      simpl in H3. 
      rewrite map2_l_refl in H3.

      exists ((mu' +l mu'')). exists nil.
      split.   inversion H3.  rewrite <-H5. rewrite <-H6.
      rewrite <-H7. apply E_While_true with mu1.
      assumption. assumption. assumption. assumption.
      split. apply E_nil. simpl. 
      rewrite map2_nil_r.  reflexivity.

      destruct p. destruct p0.
      simpl in H3.
      destruct (Cstate_as_OT.compare c0 c1).
      injection H3. intros. 


      assert( exists mu1 mu2 : list (cstate * qstate s e),
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
      assert(exists mu2 mu3 : list (cstate * qstate s e),
      ceval_single c [(c0,q)] mu2 /\ ceval_single c [(c0,q0)] mu3 /\ mu1 = (mu2 +l mu3)).
      apply (Hc [(c0, q)] [(c0, q0)] mu1).

      rewrite <-H6. 
      simpl.  
      destruct (Cstate_as_OT.compare sigma sigma).
      apply Cstate_as_OT.lt_not_eq in l. intuition. rewrite <-H5.
      assumption.

      apply Cstate_as_OT.lt_not_eq in l. intuition.


      destruct H7. destruct H7.
      assert(exists mu1 mu2 : list (cstate * qstate s e),
      ceval_single <{ while b do c end }> x mu1 /\
      ceval_single <{ while b do c end }> y mu2 /\ mu'' = (mu1 +l mu2)).

      apply IHceval_single1. reflexivity. assumption.
      destruct H8. destruct H8. 


      destruct H7. destruct H9. 

      assert(exists mu1 mu2 : list (cstate * qstate s e),
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
      unfold Cstate_as_OT.eq in e0.
      rewrite <-e0. rewrite <-H6. 
      rewrite (state_eq_bexp  _ (sigma, rho) _ ). assumption.
      reflexivity. 
      intuition. 
      unfold Cstate_as_OT.eq in e0.
      rewrite <-e0.
      intuition. intuition. rewrite (map2_comm x4 x2).
      rewrite map_assoc.  rewrite <-(map_assoc _ _ x2 _ _).
      destruct H11. destruct H12. rewrite H13. 
      destruct H8. destruct H14. rewrite H15.
      rewrite (map2_comm x2  ((x4 +l x5))). 
      rewrite map_assoc. reflexivity. 

      injection H3. intros.


      assert( exists mu1 mu2 : list (cstate * qstate s e),
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
      rewrite map2_nil_l.  reflexivity.

      rewrite map2_l_refl in H1. 
      exists ([(sigma, rho)] +l mu'). exists []. split. 
      inversion H1; subst. 
      apply E_While_false. assumption. assumption.
      split. apply E_nil.
      rewrite map2_nil_r.  reflexivity. 

      destruct p0.    
      destruct (Cstate_as_OT.compare c0 c1).
      injection H1. intros; subst.
      assert( exists mu1 mu2 : list (cstate * qstate s e),
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

      assert(exists mu1 mu2 : list (cstate * qstate s e),
      ceval_single <{ while b do c end }> x mu1 /\
      ceval_single <{ while b do c end }> y mu2 /\ mu' = (mu1 +l mu2)).

      apply IHceval_single. reflexivity. injection H1. intros; subst.
      reflexivity. 
      destruct H2. destruct H2.  destruct H2. destruct H3.

      exists ( [(c0, q)] +l x0). exists ( [(c1, q0)] +l x1).
      split. apply E_While_false. unfold Cstate_as_OT.eq in e0.
      subst. injection H1; intros. subst. 
      rewrite (state_eq_bexp  _ (c1, q .+ q0) _ ). assumption.
      reflexivity. assumption. split. 
      apply E_While_false. unfold Cstate_as_OT.eq in e0.
      subst. injection H1; intros. subst. 
      rewrite (state_eq_bexp  _ (c1, q .+ q0) _ ). assumption.
      reflexivity. assumption. injection H1; intros. subst.
      remember ((@cons (prod cstate (qstate s e))
      (@pair cstate (qstate s e) c0
      (@Mplus (Nat.pow (S (S O)) (e-s)) (Nat.pow (S (S O)) (e-s)) q q0))
      (@nil (prod cstate (qstate s e))))).  
      remember ([(c0, @Mplus (2^(e-s)) (2^(e-s)) q  q0)]). 
      assert(l=l0). rewrite Heql. rewrite Heql0. reflexivity. 
      rewrite H4. rewrite Heql0. 
      assert([(c0, @Mplus (2^(e-s)) (2^(e-s)) q  q0)] = ([(c0, q )] +l  [(c1, q0)])).
      simpl. destruct (Cstate_as_OT.compare c0 c1). 
      rewrite e0 in l1. apply Cstate_as_OT.lt_not_eq in l1. intuition.
      reflexivity. rewrite e0 in l1. apply Cstate_as_OT.lt_not_eq in l1. 
      intuition.    rewrite H5.  rewrite map_assoc. 
      rewrite (map2_comm ([(c0, q)]) ([(c1, q0)])).
      rewrite<- (map_assoc _ _ ([(c1, q0)]) ).
      rewrite (map2_comm ([(c1, q0)]) _). 
      rewrite map_assoc. reflexivity. 


      injection H1. intros. subst.
      assert(exists mu1 mu2 : list (cstate * qstate s e),
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

Lemma  map_nil:forall (s e : nat) (p: R) (x : list (cstate * qstate s e)),
([] = StateMap.Raw.map (fun i: Square (2 ^ (e-s)) => @scale (2^(e-s)) (2^(e-s)) p i) x)
-> x = [].
Proof. destruct x. simpl. intuition. destruct p0. simpl.
intros. discriminate H. 
Qed.


Lemma ceval_scale_while{s e:nat}: 
forall b c,
(forall  (p:R) (x  mu : list (cstate * qstate s e)),
ceval_single c (StateMap.Raw.map (fun i => p .* i) x) mu ->
exists mu1 : list (cstate * qstate s e),
ceval_single c x mu1  /\ mu = (StateMap.Raw.map (fun i => p .* i)mu1))->

(forall (mu mu' : list (cstate *qstate s e)),
ceval_single <{ while b do c end }> mu mu' ->
(forall (p:R) x,  mu=(StateMap.Raw.map (fun i => p .* i) x )->
exists mu1, (ceval_single <{ while b do c end }> x mu1
/\mu'=StateMap.Raw.map (fun i => p .* i) mu1))).
Proof.  intros b c Hc mu mu' H.

      remember <{while b do c end}> as original_command eqn:Horig. 
      induction H;  try inversion Horig; subst.
      intros.   apply map_nil in H0. rewrite H0.
      exists []. split.   try apply E_nil. intuition. 

      destruct x; intros. discriminate H3.
      destruct p0. simpl in H3.  
      inversion H3. 
      assert( exists mu1 : list (cstate * qstate s e),
      ceval_single <{ while b do c end }> x mu1 /\
      mu''= StateMap.Raw.map
      (fun i : Square (2 ^ (e-s)) => p .* i) mu1).
      apply IHceval_single1. reflexivity. assumption.
      destruct H4.  
      assert(exists mu2 : list (cstate * qstate s e),
      ceval_single c [(c0,m)] mu2 /\ mu1 = StateMap.Raw.map
      (fun i : Square (2 ^ (e-s)) => p .* i) mu2 ).
      apply (Hc p [(c0, m)] mu1). simpl. 
      rewrite <-H5. rewrite <-H6. assumption.
      destruct H8.   
      assert(exists mu1 : list (cstate * qstate s e),
      ceval_single <{ while b do c end }> x1
        mu1 /\ mu' =
      StateMap.Raw.map
        (fun i : Square (2 ^ (e-s)) => p .* i)
        mu1). apply IHceval_single3. reflexivity.
        intuition. destruct H9.
      exists (x2 +l x0) .  split.
      apply E_While_true with x1. 
      rewrite <-H5. rewrite (state_eq_bexp _ (sigma, rho)).
      assumption. reflexivity. intuition. intuition. intuition.
      rewrite <-d_scalar_app_distr_aux.
      f_equal. intuition. intuition.

      destruct x; intros. discriminate H1.
      destruct p0. simpl in H1.  
      inversion H1. 
      assert( exists mu1 : list (cstate * qstate s e),
      ceval_single <{ while b do c end }> x mu1 /\
      mu'= StateMap.Raw.map
      (fun i : Square (2 ^ (e-s)) => p .* i) mu1).
      apply IHceval_single. reflexivity. assumption.
      destruct H2.  
      exists (([(c0 , m)]) +l x0) .  split.
      pose (@E_While_false s e). unfold qstate in c1.
      apply c1. rewrite <-H3. rewrite (state_eq_bexp _ (sigma, rho)).
      assumption. reflexivity. intuition. 
      rewrite <-d_scalar_app_distr_aux.
      f_equal. intuition.

Qed.



Fixpoint dstate_fst_eq{s e:nat} (mu1 mu2:list(cstate * qstate s e)) :=
  match mu1, mu2 with
  |[], [] => True
  |(c0,q0)::mu1', (c1,q1)::mu2' => c0= c1 /\ dstate_fst_eq mu1' mu2'
  |_, _ =>False
  end.


Lemma big_app_plus{s e:nat}: forall n0 (f g: nat -> list(cstate * qstate s e)), 
(big_app f n0) +l (big_app g n0) =
big_app (fun j:nat => (f j) +l (g j)) n0.
Proof. induction n0; intros. 
      simpl. reflexivity.

      simpl.  repeat rewrite map_assoc. 
      repeat rewrite <-(map_assoc _ _ _ (f n0)).
     rewrite (map2_comm (f n0) ).
      rewrite map_assoc. 
      rewrite <-(map_assoc _ _ ((big_app f n0 +l big_app g n0))).
      f_equal. apply IHn0.
Qed.

Lemma big_app'_plus{s e:nat}: forall n0 (f g: nat -> (cstate * qstate s e)) mu mu1 mu2, 
(forall i, i < n0 -> WWF_qstate ( snd ( f i))\/ ( snd ( f i))= Zero)->
(forall i, i < n0 -> WWF_qstate ( snd ( g i))\/ ( snd ( g i))= Zero)->
(forall i,  fst (f i) = fst ( g i))->
(big_app' f n0 mu1) ->
(big_app' g n0 mu2) ->
big_app' (fun j:nat =>(fst (f j), snd (f j) .+ snd (g j))) n0 mu->
mu1 +l mu2 = mu.
Proof. induction n0; intros f g mu mu1 mu2 Hf Hg; intros. 
      simpl. inversion_clear H0. inversion_clear H1.
      inversion_clear H2. reflexivity.

      inversion_clear H0. inversion_clear H1.
      inversion_clear  H2. 
      apply IHn0 with f g;  auto.
      rewrite H3 in *. rewrite H0 in *.
      simpl in H1. rewrite Mplus_0_r in H1.
      destruct H1.  reflexivity.

      inversion_clear H2. rewrite H3 in *.
      simpl in H1. rewrite Mplus_0_l in H1.
      rewrite H1 in H0. destruct H0. reflexivity.

      rewrite H3 in *. simpl in *. rewrite Mplus_0_l in *.
      rewrite map_assoc. f_equal. apply IHn0 with f g; auto.
      rewrite H. destruct (g n0). reflexivity.
      
      inversion_clear H1.  inversion_clear H2.
      rewrite H0 in *.
      simpl in H1. rewrite Mplus_0_r in H1.
      rewrite H1 in H3. destruct H3. reflexivity.

      rewrite H0 in *. simpl in *. rewrite Mplus_0_r in *.
      rewrite <-map_assoc.  rewrite (map2_comm [f n0] ).
      rewrite map_assoc.  f_equal. apply IHn0 with f g; auto.
       destruct (f n0). reflexivity.

       inversion_clear H2. simpl in *. admit.  

      
      repeat rewrite map_assoc. 
      repeat rewrite <-(map_assoc _ _ _ [f n0]).
     rewrite (map2_comm [f n0] ).
      rewrite map_assoc. 
      rewrite <-(map_assoc _ _ (l +l l0)).
      f_equal. apply IHn0 with f g; auto.
      assert(fst (f n0) = fst (g n0)). apply H.
      destruct (f n0). destruct ( g n0). 
      simpl in *. rewrite H2. MC.elim_comp. 
      reflexivity.
Admitted.

Lemma big_app_scale{s e:nat}: forall n0 (p:R) (f: nat -> list(cstate * qstate s e)), 
StateMap.Raw.map (fun x0 : qstate s e =>@scale (2^(e-s)) (2^(e-s)) p  x0) (big_app f n0)=
big_app (fun j:nat => StateMap.Raw.map (fun x0 : qstate s e => @scale (2^(e-s)) (2^(e-s))  p  x0) (f j)) n0.
Proof. induction n0; intros.
     simpl. reflexivity.

     simpl . unfold qstate.
     apply Logic.eq_trans with  (StateMap.Raw.map (fun x0 : Square (2 ^ (e-s)) => p .* x0)
    ((big_app f n0) +l f n0)). f_equal. 
      rewrite <-(d_scalar_app_distr_aux).
      f_equal.  apply IHn0.
Qed.


Lemma big_app'_scale{s e:nat}: forall n0 (p:R) (f: nat -> (cstate * qstate s e)) mu mu', 
(p<>0)%R->
(big_app' f n0 mu)-> 
big_app' (fun j:nat =>s_scale p (f j)) n0 mu'->
StateMap.Raw.map (fun x0 : qstate s e =>@scale (2^(e-s)) (2^(e-s)) p  x0) mu = mu'.
Proof. induction n0; intros.
      inversion_clear H0. inversion_clear H1.
     simpl. reflexivity.

     inversion_clear H0. inversion_clear H1.
     apply IHn0 with f; auto.
     unfold s_scale in *.
     rewrite H2 in *. rewrite Mscale_0_r in *.
     simpl in H0. destruct H0. reflexivity.

     inversion_clear H1.  
     unfold s_scale in *. simpl in *.
     assert((p,0%R)<> C0)%C. apply C0_fst_neq. apply H.
     pose (scale_Zero _ _ H0 H1). rewrite e0 in H2.
     destruct H2. reflexivity.

     rewrite <-(d_scalar_app_distr_aux). f_equal.
     apply IHn0 with f; auto.
     unfold s_scale. simpl. destruct (f n0).
     reflexivity.
Qed.

Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Arith.Peano_dec.
Require Import
  Coq.FSets.FMapList
  Coq.Structures.OrderedTypeEx.
Require Import OrderedType.
Module Import MC := OrderedTypeFacts(Cstate_as_OT).

Lemma big_app'_exsist{ s e:nat}: forall n ( f:nat-> (cstate * qstate s e)) ,
exists mu, big_app' f n mu.
Proof. induction n; intros.
        exists []. econstructor.
        pose (IHn f). destruct e0.
        assert (snd (f n) = Zero \/ snd (f n)<> Zero).
        apply Classical_Prop.classic. 
        destruct H0. 
        exists x. econstructor; try assumption.
        exists (x+l [f n]). apply big_app_cons; try assumption.
Qed.


Lemma ceval_app_aux{s e:nat}:  forall c  ( x y mu: list (cstate *qstate s e)),
ceval_single c (StateMap.Raw.map2 option_app x y) mu ->
exists mu1 mu2 , (ceval_single c x mu1
/\ceval_single c y mu2 
/\mu=StateMap.Raw.map2 option_app mu1 mu2).
Proof.  induction c. 
    -{ intros. exists x. exists y.
      split. apply ceval_skip. 
      split. apply ceval_skip.
      apply ceval_skip_1 in H. intuition. } 
    -{ intros. exists nil. exists nil. 
      split. apply ceval_abort. 
      split. apply ceval_abort.
      simpl. apply ceval_abort_1 in H.
      intuition. }
    -{ induction x; induction y; intros.
      exists nil. exists nil.
      split. apply E_nil. split. apply E_nil.
      simpl. simpl in H. inversion_clear H. reflexivity. 
      destruct a0. simpl in H. rewrite map2_r_refl in H.
      inversion H;subst. 
      exists nil. exists ((StateMap.Raw.map2 option_app
      [(c_update i (aeval (c, q) a) c, q)] mu')).
      split. apply E_nil. split. intuition.
      rewrite map2_nil_l.  reflexivity.
      destruct a0. simpl in H. rewrite map2_l_refl in H.
      inversion H;subst. 
      exists ((StateMap.Raw.map2 option_app
      [(c_update i (aeval (c, q) a) c, q)] mu')).
      exists nil.
      split.  intuition. split.  apply E_nil.
      rewrite map2_nil_r.  reflexivity.
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
      repeat rewrite map_assoc. repeat rewrite <-(map_assoc _ _ _ x0).
      rewrite (map2_comm x0 ([(c_update i (aeval (c0, q0) a) c0, q0)])).
      rewrite <-map_assoc. rewrite <-map_assoc.
      rewrite (map_assoc _ _ _ _ ((x0 +l x1))).
      f_equal. simpl. unfold Cstate_as_OT.eq in e0.
      rewrite e0. rewrite (state_eq_aexp (c0, q) (c0, q0) a ).
      MC.elim_comp.  
      rewrite (state_eq_aexp  (c0, q0) (c0, q.+ q0) a ).
      f_equal. reflexivity. reflexivity. reflexivity.

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
      rewrite (map_assoc _ _ x0). apply map2_comm. }
      - admit.  

    -{intros. inversion H; subst.
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
      intuition. intuition. intuition. }
      -{induction x; induction y; intros.
      simpl in H. inversion_clear H.
      exists nil. exists nil.
      split. apply E_nil. split. apply E_nil.
      simpl. reflexivity.
      destruct a. simpl in H. rewrite map2_r_refl in H.
      exists nil. exists (mu).
      split. apply E_nil. split. intuition.
      rewrite map2_nil_l.  reflexivity.
      destruct a. simpl in H. rewrite map2_l_refl in H.
      exists (mu).
      exists nil.
      split.  intuition. split.  apply E_nil.
      rewrite map2_nil_r.  reflexivity.
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
      assert(exists mu1 mu2 : list (cstate * qstate s e),
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
      intuition.  unfold Cstate_as_OT.eq in e0. rewrite <-e0. intuition.
      rewrite H6. rewrite H3. 
      rewrite (map2_comm x2 _).  rewrite map_assoc.
      rewrite<-(map_assoc _ _ x3 x2 x0). rewrite (map2_comm x3 _).
      rewrite <-map_assoc. reflexivity.

      apply IHx in H1. destruct H1. destruct H.
      destruct H. destruct H1.
      assert(exists mu1 mu2 : list (cstate * qstate s e),
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
      intuition.  unfold Cstate_as_OT.eq in e0. rewrite <-e0. intuition.
      rewrite H6. rewrite H3. rewrite (map2_comm x2 _).  rewrite map_assoc.
      rewrite<-(map_assoc _ _ x3 x2 x0). rewrite (map2_comm x3 _).
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
      rewrite <-map_assoc. reflexivity. }

    -{intros.  apply ceval_app_while with ((x +l y)).
      intros. apply IHc. assumption. assumption.
      reflexivity. }

    -{ induction x; induction y; intros.
      exists nil. exists nil.
      split. apply E_nil. split. apply E_nil.
      simpl. simpl in H. inversion_clear H. reflexivity. 
      destruct a. simpl in H. rewrite map2_r_refl in H.
      inversion H;subst. 
      exists nil. exists ((StateMap.Raw.map2 option_app
      [(c, QInit_fun s0 e0 q)] mu')).
      split. apply E_nil. split. apply H.  rewrite map2_nil_l.  reflexivity.
      destruct a. simpl in H. rewrite map2_l_refl in H.
      inversion H;subst. 
      exists ((StateMap.Raw.map2 option_app
      [(c, QInit_fun s0 e0 q)] mu')).
      exists nil.
      split.  intuition. split.  apply E_nil.
      rewrite map2_nil_r.  reflexivity.
      destruct a0. destruct a. simpl in H.
      destruct (Cstate_as_OT.compare c0 c).
      inversion H;subst.
      apply IHx in H7. destruct H7. destruct H0.
      destruct H0. destruct H1. 
      remember (StateMap.Raw.map2 option_app
      [(c0, QInit_fun s0 e0 q0)] x0).
      exists t. exists x1.
      split. rewrite Heqt. apply E_Qinit. intuition.
      intuition. split. intuition. 
      rewrite H2. rewrite Heqt. apply map_assoc.
      inversion H;subst.
      apply IHx in H7. destruct H7. destruct H0.
      destruct H0. destruct H1.
      remember (StateMap.Raw.map2 option_app
      [(c0, QInit_fun s0 e0 q0)] x0).
      remember (StateMap.Raw.map2 option_app
      [(c, QInit_fun s0 e0 q)] x1).
      exists t. exists t0.
      split. rewrite Heqt. 
      apply E_Qinit. intuition. intuition.  
      split. rewrite Heqt0. apply E_Qinit. intuition.
      intuition.
      rewrite H2. rewrite Heqt. rewrite Heqt0.
      repeat rewrite map_assoc. repeat rewrite <-(map_assoc _ _ _ x0).
      rewrite (map2_comm x0 ([(c, QInit_fun s0 e0 q)])).
      rewrite <-map_assoc. rewrite <-map_assoc.
      rewrite (map_assoc _ _ _ _ ((x0 +l x1))).
      f_equal. simpl. unfold Cstate_as_OT.eq in e1.
      rewrite e1.  MC.elim_comp.
      rewrite <-QInit_fun_plus. reflexivity. lia.  

      inversion H;subst.
      apply IHy in H7. 
      destruct H7. destruct H0.
      destruct H0. destruct H1.
      exists x0. 
      remember (StateMap.Raw.map2 option_app [(c, QInit_fun s0 e0 q)] x1).
      exists t. 
      rewrite Heqt. split. intuition.
      split. apply E_Qinit. intuition. intuition.
      rewrite H2. rewrite (map2_comm ([(c, QInit_fun s0 e0 q)]) x1).
      rewrite (map_assoc _ _ x0). apply map2_comm. } 

    -{induction x; induction y; intros.
      exists nil. exists nil.
      split. apply E_nil. split. apply E_nil.
      simpl. simpl in H. inversion_clear H. reflexivity. 
      destruct a. simpl in H. rewrite map2_r_refl in H.
      inversion H;subst. apply inj_pair2_eq_dec in H2. 
      apply inj_pair2_eq_dec in H2. destruct H2.
      exists nil. exists ((StateMap.Raw.map2 option_app
      [(c, QUnit_One_fun s0 e0 U1 q)] mu')).
      split. apply E_nil. split. intuition.
      rewrite map2_nil_l.  reflexivity.
      apply Nat.eq_dec. apply Nat.eq_dec.
      destruct a. simpl in H. rewrite map2_l_refl in H.
      inversion H;subst.  apply inj_pair2_eq_dec in H2. 
      apply inj_pair2_eq_dec in H2. destruct H2.
      exists ((StateMap.Raw.map2 option_app
      [(c, QUnit_One_fun s0 e0 U1 q)] mu')).
      exists nil. 
      split.  intuition. split.  apply E_nil.
      rewrite map2_nil_r.  reflexivity.
      apply Nat.eq_dec. apply Nat.eq_dec.
      destruct a0. destruct a. simpl in H.
      destruct (Cstate_as_OT.compare c0 c).
      inversion H;subst. 
      apply inj_pair2_eq_dec in H2. 
      apply inj_pair2_eq_dec in H2. destruct H2.
      apply IHx in H9. destruct H9. destruct H0.
      destruct H0. destruct H1. 
      remember (StateMap.Raw.map2 option_app
      [(c0, QUnit_One_fun s0 e0 U1 q0)] x0).
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
      [(c0, QUnit_One_fun s0 e0 U1 (q0))] x0).
      remember (StateMap.Raw.map2 option_app
      [(c, QUnit_One_fun s0 e0 U1 (q))] x1).
      exists t. exists t0.
      split. rewrite Heqt. 
      apply E_Qunit_One. intuition. intuition. intuition. 
      split. rewrite Heqt0. apply E_Qunit_One. intuition. intuition.
      intuition. 
      rewrite H2. rewrite Heqt. rewrite Heqt0.
      repeat rewrite map_assoc. repeat rewrite <-(map_assoc _ _ _ x0).
      rewrite (map2_comm x0 ([(c, QUnit_One_fun s0 e0 U1 q)])).
      rewrite <-map_assoc. rewrite <-map_assoc.
      rewrite (map_assoc _ _ _  _ ((x0 +l x1))).
      f_equal. simpl. unfold Cstate_as_OT.eq in e1.
      rewrite e1.  MC.elim_comp.
      rewrite QUnit_One_fun_plus. reflexivity. lia.  
      apply Nat.eq_dec. apply Nat.eq_dec.

      inversion H;subst. apply inj_pair2_eq_dec in H2. 
      apply inj_pair2_eq_dec in H2. destruct H2.
      apply IHy in H9. 
      destruct H9. destruct H0.
      destruct H0. destruct H1.
      exists x0. 
      remember (StateMap.Raw.map2 option_app [(c, QUnit_One_fun s0 e0 U1 ( q))] x1).
      exists t. 
      rewrite Heqt. split. intuition.
      split. apply E_Qunit_One. intuition. intuition. intuition.
      rewrite H2. rewrite (map2_comm ([(c, QUnit_One_fun s0 e0 U1 (q))]) x1).
      rewrite (map_assoc _ _ x0). apply map2_comm. 
      apply Nat.eq_dec. apply Nat.eq_dec. } 

    -{induction x; induction y; intros.
      exists nil. exists nil.
      split. apply E_nil. split. apply E_nil.
      simpl. simpl in H. inversion_clear H. reflexivity. 
      destruct a. simpl in H. rewrite map2_r_refl in H.
      inversion H;subst. apply inj_pair2_eq_dec in H5. 
      apply inj_pair2_eq_dec in H5. destruct H5.
      exists nil. exists ((StateMap.Raw.map2 option_app
      [(c, QUnit_Ctrl_fun s0 e0 s1 e1 U1 q)] mu')).
      split. apply E_nil. split. intuition.
      rewrite map2_nil_l.  reflexivity.
      apply Nat.eq_dec. apply Nat.eq_dec.
      destruct a. simpl in H. rewrite map2_l_refl in H.
      inversion H;subst.  apply inj_pair2_eq_dec in H5. 
      apply inj_pair2_eq_dec in H5. destruct H5.
      exists ((StateMap.Raw.map2 option_app
      [(c, QUnit_Ctrl_fun s0 e0 s1 e1 U1 q)] mu')).
      exists nil. 
      split.  intuition. split.  apply E_nil.
      rewrite map2_nil_r.  reflexivity.
      apply Nat.eq_dec. apply Nat.eq_dec.
      destruct a0. destruct a. simpl in H.
      destruct (Cstate_as_OT.compare c0 c).
      inversion H;subst. 
      apply inj_pair2_eq_dec in H5. 
      apply inj_pair2_eq_dec in H5. destruct H5.
      apply IHx in H11. destruct H11. destruct H0.
      destruct H0. destruct H1. 
      remember (StateMap.Raw.map2 option_app
      [(c0, QUnit_Ctrl_fun s0 e0 s1 e1 U1 q0)] x0).
      exists t. exists x1.
      split. rewrite Heqt. apply E_QUnit_Ctrl.
      intuition. intuition.  intuition. split. intuition. 
      rewrite H2. rewrite Heqt. apply map_assoc.
      apply Nat.eq_dec. apply Nat.eq_dec.
      inversion H;subst. 
      apply inj_pair2_eq_dec in H5. 
      apply inj_pair2_eq_dec in H5. destruct H5.
      apply IHx in H11. destruct H11. destruct H0.
      destruct H0. destruct H1.
      remember (StateMap.Raw.map2 option_app
      [(c0, QUnit_Ctrl_fun s0 e0 s1 e1 U1 q0)] x0).
      remember (StateMap.Raw.map2 option_app
      [(c, QUnit_Ctrl_fun s0 e0 s1 e1 U1 q)] x1).
      exists t. exists t0.
      split. rewrite Heqt. 
      apply E_QUnit_Ctrl. intuition. intuition. intuition. 
      split. rewrite Heqt0. apply E_QUnit_Ctrl. intuition. intuition.
      intuition. 
      rewrite H2. rewrite Heqt. rewrite Heqt0.
      repeat rewrite map_assoc. repeat rewrite <-(map_assoc _ _ _ x0).
      rewrite (map2_comm x0 ([(c, QUnit_Ctrl_fun s0 e0 s1 e1 U1 q)])).
      rewrite <-map_assoc. rewrite <-map_assoc.
      rewrite (map_assoc _ _ _ _((x0 +l x1))).
      f_equal. simpl. unfold Cstate_as_OT.eq in e2.
      rewrite e2.  MC.elim_comp.
      rewrite QUnit_Ctrl_fun_plus. reflexivity. lia.  
      apply Nat.eq_dec. apply Nat.eq_dec.

      inversion H;subst. apply inj_pair2_eq_dec in H5. 
      apply inj_pair2_eq_dec in H5. destruct H5.
      apply IHy in H11. 
      destruct H11. destruct H0.
      destruct H0. destruct H1.
      exists x0. 
      remember (StateMap.Raw.map2 option_app [(c, QUnit_Ctrl_fun s0 e0 s1 e1 U1 q)] x1).
      exists t. 
      rewrite Heqt. split. intuition.
      split. apply E_QUnit_Ctrl. intuition. intuition. intuition.
      rewrite H2. rewrite (map2_comm ([(c, QUnit_Ctrl_fun s0 e0 s1 e1 U1 q)]) x1).
      rewrite (map_assoc _ _ x0). apply map2_comm. 
      apply Nat.eq_dec. apply Nat.eq_dec. }


      -{induction x; induction y; intros.
      exists nil. exists nil.
      split. apply E_nil. split. apply E_nil.
      simpl. simpl in H. inversion_clear H. reflexivity. 
      destruct a. simpl in H. rewrite map2_r_refl in H.
      inversion H;subst. 
      exists nil. exists ((
       mu'' +l mu')).
      split. apply E_nil. split. intuition.
      rewrite map2_nil_l.  reflexivity.
      destruct a. simpl in H. rewrite map2_l_refl in H.
      inversion H;subst.  
      exists (mu'' +l mu').
      exists nil.
      split.  intuition. split.  apply E_nil.
      rewrite map2_nil_r.  reflexivity.
      destruct a0. destruct a. simpl in H.
      destruct (Cstate_as_OT.compare c0 c).
      inversion H;subst. 
      apply IHx in H8. destruct H8. destruct H0.
      destruct H0. destruct H1. 
      remember (mu'' +l x0).
      exists t. exists x1.
      split. rewrite Heqt. apply E_Meas.
      intuition. intuition. assumption. split. intuition. 
      rewrite H2. rewrite Heqt. apply map_assoc.
      inversion H;subst.
      apply IHx in H8. destruct H8. destruct H0.
      destruct H0. destruct H1.
      pose (big_app'_exsist (2 ^ (e0 - s0)) (fun j : nat =>
      (c_update i j c0, QMeas_fun s0 e0 j (q0 )))).
      pose (big_app'_exsist (2 ^ (e0 - s0)) (fun j : nat =>
      (c_update i j c, QMeas_fun s0 e0 j (q)))).
      destruct e2. destruct e3.
      remember (x2+l x0).
      remember (x3+l x1).
      exists t. exists t0.
      split. rewrite Heqt. 
      apply E_Meas. intuition. intuition. assumption. 
      split. rewrite Heqt0. apply E_Meas. intuition.
      intuition.  assumption.
      rewrite H2. rewrite Heqt. rewrite Heqt0.
      repeat rewrite map_assoc. repeat rewrite <-(map_assoc _ _ _ x0).
      rewrite (map2_comm x0 x3).
      rewrite <-map_assoc. rewrite <-map_assoc.
      rewrite (map_assoc _ _ _ _ ((x0 +l x1))).
      f_equal.  symmetry.
       apply big_app'_plus with ((2 ^ (e0 - s0))) 
       ((fun j : nat =>
       (c_update i j c0, QMeas_fun s0 e0 j q0))) 
       ((fun j : nat =>
       (c_update i j c, QMeas_fun s0 e0 j q))).
      simpl. intros. apply QMeas_fun_ge_0; try lia.
      admit. intros. apply QMeas_fun_ge_0; try lia.
      admit. intros. simpl.  unfold Cstate_as_OT.eq in e1. rewrite e1.
      reflexivity.
      f_equal. assumption. assumption. simpl.
      admit.

      inversion H;subst.
      apply IHy in H8. 
      destruct H8. destruct H0.
      destruct H0. destruct H1.
      exists x0. 
      remember (mu'' +l x1).
      exists t. 
      rewrite Heqt. split. intuition.
      split. apply E_Meas. intuition. intuition.
      assumption.
      rewrite H2. rewrite (map2_comm mu''  x1).
      rewrite (map_assoc _ _ x0). apply map2_comm. }
Admitted.

 
 Lemma ceval_dscale_aux{s' e':nat}:  forall c  (y mu: list (cstate *qstate s' e')) (p:R),
ceval_single c (StateMap.Raw.map (fun x: qstate s' e' => p .* x) y) mu ->
exists mu', (and (ceval_single c y mu')
(mu=StateMap.Raw.map (fun x: qstate s' e' => p .* x) mu')).
Proof. induction c.
  -{intros. apply ceval_skip_1 in H. exists y. 
    split. apply ceval_skip. intuition. }
  -{admit. } 
  -{induction y; intros. exists []. split. apply E_nil.
    inversion_clear H. reflexivity. destruct a0. inversion H; subst.
    assert(exists y' : list (cstate * qstate s' e'),
    ceval_single <{ i := a }> y y' /\
    mu' =
    StateMap.Raw.map (fun x : qstate s' e' => p .* x)
    y'). apply IHy. assumption.
    destruct H0. destruct H0.
    exists  ([(c_update i (@aeval s' e' (c, q) a) c,  q)] +l x).
    split.  apply E_Asgn. intuition.
    rewrite H1. rewrite <-d_scalar_app_distr_aux.
     simpl StateMap.Raw.map.  
     rewrite (state_eq_aexp (c, p .* q)  (c, q)).
    reflexivity. reflexivity. }
    -{ admit. }
    -{ destruct y; intros. inversion H; subst.
    exists []. split. apply E_nil. reflexivity.
    destruct p. inversion H; subst. 
    assert((@cons (prod cstate (qstate s' e'))
    (@pair cstate (qstate s' e') c
    (@scale (Nat.pow (S (S O)) (e'-s'))
    (Nat.pow (S (S O)) (e'-s')) 
    (RtoC p0) q))
    (@StateMap.Raw.map (qstate s' e')
    (Matrix (Nat.pow (S (S O)) (e'-s'))
    (Nat.pow (S (S O)) (e'-s')))
    (fun x : qstate s' e' =>
    @scale (Nat.pow (S (S O)) (e'-s'))
    (Nat.pow (S (S O)) (e'-s')) 
    (RtoC p0) x) y))=
    StateMap.Raw.map
          (fun x : qstate s' e' => p0 .* x) ((c,q)::y)).
    reflexivity.  
    rewrite H0 in H6. 
    assert( exists mu' : list (cstate * qstate s' e'),
    ceval_single c1 ((c, q) :: y) mu' /\
    mu1 =
    StateMap.Raw.map
    (fun x : qstate s' e' => p0 .* x) mu'). apply IHc1.
    assumption. destruct H1.  destruct H1. 
    rewrite H2 in H7. 
    assert( exists mu' : list (cstate * qstate s' e'),
    ceval_single c2 x mu' /\
    mu =
    StateMap.Raw.map
    (fun x : qstate s' e' => p0 .* x) mu'). apply IHc2.
    assumption. destruct H3.  destruct H3.
    exists (x0). split. apply E_Seq with x.
    assumption. assumption. apply H4. }

  -{induction y; intros. inversion H; subst.
      exists []. split. apply E_nil. reflexivity.
      destruct a. inversion H; subst.

      assert(exists y' : list (cstate * qstate s' e'),
      ceval_single <{ if b then c1 else c2 end }> y y' /\
      mu'' =
      StateMap.Raw.map (fun x : qstate s' e' => p .* x)
      y'). apply IHy. assumption.
      destruct H0. destruct H0.
      assert( exists q' : list (cstate * qstate s' e'),
      ceval_single c1 [(c,q)] q' /\
      mu' =
      StateMap.Raw.map
      (fun x : qstate s' e' => p .* x) q'). 
      apply IHc1. simpl. assumption. 
      destruct H2. destruct H2. 
      exists  (x0 +l x).
      split.  apply E_IF_true.
      rewrite (state_eq_bexp _ (c, p .* q)). intuition.
      reflexivity. assumption. assumption.
      rewrite H1. rewrite H3.   apply d_scalar_app_distr_aux.

      assert(exists y' : list (cstate * qstate s' e'),
      ceval_single <{ if b then c1 else c2 end }> y y' /\
      mu'' =
      StateMap.Raw.map (fun x : qstate s' e' => p .* x)
      y'). apply IHy. assumption.
      destruct H0. destruct H0.
      assert( exists q' : list (cstate * qstate s' e'),
      ceval_single c2 [(c,q)] q' /\
      mu' =
      StateMap.Raw.map
      (fun x : qstate s' e' => p .* x) q'). 
      apply IHc2. simpl. assumption. 
      destruct H2. destruct H2. 
      exists  (x0 +l x).
      split.  apply E_IF_false.
      rewrite (state_eq_bexp _ (c, p .* q)). intuition.
      reflexivity. assumption. assumption.
      rewrite H1. rewrite H3.   apply d_scalar_app_distr_aux. }

    -{intros. apply ceval_scale_while with ((StateMap.Raw.map
    (fun x : qstate s' e' => p .* x) y)). intros.
    apply IHc. assumption. assumption. reflexivity. }

    -{induction y; intros. exists []. split. apply E_nil.
    inversion_clear H. reflexivity. destruct a. inversion H; subst.
    assert(exists y' : list (cstate * qstate s' e'),
    ceval_single <{ (s e) :Q= 0 }> y y' /\
    mu' =
    StateMap.Raw.map (fun x : qstate s' e' => p .* x)
    y'). apply IHy. assumption.
    destruct H0. destruct H0.
    exists  ([(c, QInit_fun s e  q)] +l x).
    split.  apply E_Qinit. intuition. intuition.
    rewrite H1.  
    assert ([(c, @QInit_fun s' e' s e (p .* q))]=  StateMap.Raw.map (fun x0 : qstate s' e' => p .* x0) [(c, QInit_fun s e q)]).
    simpl. rewrite QInit_fun_scale. reflexivity. lia.
    rewrite H2. apply d_scalar_app_distr_aux. }

  -{induction y; intros. exists []. split. apply E_nil.
    inversion_clear H. reflexivity. destruct a. inversion H; subst.
    apply inj_pair2_eq_dec in H2. apply inj_pair2_eq_dec in H2.
    destruct H2.
    assert(exists y' : list (cstate * qstate s' e'),
    ceval_single (QUnit_One s e U1) y y' /\
    mu' =
    StateMap.Raw.map (fun x : qstate s' e' => p .* x)
      y'). apply IHy. assumption.
    destruct H0. destruct H0.
    exists  ([(c, QUnit_One_fun s e U1 ( q))] +l x).
    split.  apply E_Qunit_One. intuition.
    assumption. assumption. 
    rewrite H1.  
    assert ([(c, @QUnit_One_fun s' e' s e U1 (p .* q))]=  
    StateMap.Raw.map (fun x0 : qstate s' e' => p .* x0) 
    [(c, QUnit_One_fun s e U1 ( q))]).
    simpl. rewrite QUnit_One_fun_scale. reflexivity. lia.
    rewrite H2. apply d_scalar_app_distr_aux.
    apply Nat.eq_dec. apply Nat.eq_dec. }

  -{induction y; intros. exists []. split. apply E_nil.
    inversion_clear H. reflexivity. destruct a. inversion H; subst.
    apply inj_pair2_eq_dec in H5. apply inj_pair2_eq_dec in H5.
    destruct H5.
    assert(exists y' : list (cstate * qstate s' e'),
    ceval_single (QUnit_Ctrl s0 e0 s1 e1 U1) y y' /\
    mu' =
    StateMap.Raw.map (fun x : qstate s' e' => p .* x)
    y'). apply IHy. assumption.
    destruct H0. destruct H0.
    exists  ([(c, QUnit_Ctrl_fun s0 e0 s1 e1 U1 (q))] +l x).
    split.  apply E_QUnit_Ctrl. intuition.
    assumption. assumption. 
    rewrite H1. 
    assert ([(c, @QUnit_Ctrl_fun s' e' s0 e0 s1 e1 U1 (p .* q))]=  
    StateMap.Raw.map (fun x0 : qstate s' e' => p .* x0) 
    [(c, QUnit_Ctrl_fun s0 e0 s1 e1 U1 q)]).
    simpl. rewrite QUnit_Ctrl_fun_scale . reflexivity.
    lia. rewrite H2. apply  d_scalar_app_distr_aux.
    apply Nat.eq_dec. apply Nat.eq_dec. }


  -{induction y; intros. exists []. split. apply E_nil.
    inversion_clear H. reflexivity. destruct a. inversion H; subst.
    assert(exists y' : list (cstate * qstate s' e'),
    ceval_single <{ i :=M [[s e]] }> y y' /\
    mu' =
    StateMap.Raw.map (fun x : qstate s' e' => p .* x)
    y'). apply IHy. assumption.
    destruct H0. destruct H0.
    pose (big_app'_exsist (2 ^ (e - s)) (fun j : nat =>
    (c_update i j c, QMeas_fun s e j (q)))).
    destruct e0.
    exists  (x0 +l x).
    split.  apply E_Meas. intuition. intuition.
    assumption.
    rewrite H1.  
    rewrite <-d_scalar_app_distr_aux.
    f_equal. symmetry.
    apply (@big_app'_scale s' e') with ((2 ^ (e - s)))
    (fun j : nat =>
        (c_update i j c, QMeas_fun s e j q)).
    admit. assumption. unfold s_scale.
    simpl.  admit. } 
    
   
Admitted.
 


 Lemma ceval_4{s' e':nat}:  forall c sigma (rho: qstate s' e') 
(mu mu': list (cstate *qstate s' e')),
Sorted (StateMap.Raw.PX.ltk (elt:=qstate s' e')) ((sigma, rho)::mu)->
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
       rewrite H1 in H0. apply ceval_app_aux in H0. 
       destruct H0. destruct H0. destruct H0. 
       exists x. exists x0. intuition.
Qed. 


Require Import Sorted.
Lemma big_app_sorted{s e:nat}: forall (f : nat -> list (cstate * qstate s e)) (n_0:nat),
(forall i, Sorted (StateMap.Raw.PX.ltk (elt:=qstate s e)) (f i))->
Sorted (StateMap.Raw.PX.ltk (elt:=qstate s e)) (big_app f n_0).
Proof. intros. induction n_0. 
-simpl. apply Sorted_nil.
-simpl. apply StateMap.Raw.map2_sorted. 
        apply IHn_0. apply H.
Qed.      

Lemma big_app'_sorted{s e:nat}: forall (f : nat ->  (cstate * qstate s e)) (n_0:nat) mu,
big_app' f n_0 mu->
Sorted (StateMap.Raw.PX.ltk (elt:=qstate s e)) mu.
Proof. induction n_0; intros. 
-inversion_clear H.  apply Sorted_nil.
-inversion_clear H. apply IHn_0. assumption.
 apply StateMap.Raw.map2_sorted.  
        apply IHn_0. assumption.
  apply Sorted.Sorted_cons. apply Sorted.Sorted_nil.
  apply Sorted.HdRel_nil. 
Qed.    


Lemma ceval_sorted{ s e:nat}: forall c (mu mu':list (cstate *qstate s e)) 
 (Hm: Sorted (StateMap.Raw.PX.ltk (elt:=qstate s e)) mu)
(H:ceval_single c mu mu'),
Sorted (StateMap.Raw.PX.ltk (elt:=qstate s e)) mu'.
Proof. 
induction c. 
-intros. inversion H;subst. intuition. intuition.
- intros. inversion H;subst. intuition. intuition.
-induction mu; intros; inversion H;subst. intuition. 
  apply StateMap.Raw.map2_sorted. 
  apply Sorted_cons. 
  apply Sorted_nil.  apply HdRel_nil. apply IHmu.
  inversion_clear Hm.  intuition. intuition.
-admit.
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
apply big_app'_sorted with 
(fun j : nat =>
        (c_update i j sigma, QMeas_fun s0 e0 j rho))  (2 ^ (e0 - s0)).
assumption.
apply IHmu.
inversion_clear Hm.  intuition.
intuition.
Admitted.


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

Lemma Mixed_aux_not_Zero{n:nat}:forall (M: Square n),
Mixed_State_aux M -> M<>Zero .
Proof. intros.  intro.  
      assert(@trace n Zero= trace (M)).
      rewrite H0. reflexivity.
      rewrite Zero_trace in H1.
      symmetry in H1. pose H.
        apply mixed_state_trace_gt0_aux in m.
        apply mixed_state_trace_real_aux in H.
      destruct (trace M). simpl in *.
      injection H1. intros. rewrite H3 in m.
      lra. 
Qed.


Lemma WWF_qstate_init{s' e'}: forall s e (rho:qstate s' e'),
s'<=s/\s<=e/\ e<=e'-> 
WWF_qstate rho-> 
WWF_qstate (QInit_fun s e rho).
Proof. intros.
    assert(@trace (2^(e'-s')) (QInit_fun s e rho)= @trace (2^(e'-s')) rho).
    apply QInit_trace. lia.  
    apply WF_Mixed_aux. assumption.
   
    apply (@Mixed_State_aux_big_sum (2^(e'-s'))).
    apply Nat.pow_nonzero. lia. 
    intros. 
    remember (I (2 ^ (s - s'))
    ⊗ (∣ 0 ⟩_ (e - s) × ⟨ i ∣_ (e - s))
    ⊗ I (2 ^ (e' - e))).
    assert(q_update m rho = Zero \/ q_update m rho <> Zero).
    apply Classical_Prop.classic. destruct H3.
    right. assumption.
    left. apply mixed_super_aux. rewrite Heqm.
    apply WF_kron; type_sovle'; auto_wf.
     apply WF_kron; type_sovle';
     auto_wf. apply WF_mult. apply WF_vec. apply pow_gt_0.
     auto_wf. assumption. assumption.
    apply big_sum_not_0. 
    intro. apply mixed_state_trace_gt0_aux  in H0.
    remember ((fun i : nat =>
    q_update (I (2 ^ (s - s'))
       ⊗ (∣ 0 ⟩_ (e - s)
          × ⟨ i ∣_ (e - s))
       ⊗ I (2 ^ (e' - e))) rho)).
    assert ((@big_sum
    (Matrix (Nat.pow (S (S O)) (Init.Nat.sub e' s'))
       (Nat.pow (S (S O)) (Init.Nat.sub e' s')))
    (M_is_monoid (Nat.pow (S (S O)) (Init.Nat.sub e' s'))
       (Nat.pow (S (S O)) (Init.Nat.sub e' s')))
    q (2 ^ (e - s)) )=QInit_fun s e rho). rewrite Heqq.
    unfold QInit_fun. reflexivity.
    rewrite H3 in H2. rewrite H2 in H1.
    rewrite Zero_trace in H1. destruct  (trace rho).
    injection H1. intros. simpl in H0. rewrite H5 in H0. lra.
Qed.


Lemma WF_qstate_init{s' e'}: forall s e (rho:qstate s' e'),
s'<=s/\s<=e/\ e<=e'-> 
WF_qstate rho-> 
WF_qstate (QInit_fun s e rho).
Proof. intros. destruct H0. split.  
rewrite<- Mixed_State_aux_to_Mix_State in *. 
split. apply WWF_qstate_init. lia. intuition. 
 rewrite QInit_trace. intuition. lia. 
 apply WF_Mixed_aux. intuition. lia.
Qed. 


Lemma WWF_qstate_QUnit_One{s' e'}: forall s e (rho:qstate s' e') (U:Square (2^(e-s))),
s'<=s/\s<=e/\ e<=e'-> 
WF_Unitary U->
WWF_qstate rho-> 
WWF_qstate (QUnit_One_fun s e U rho).
Proof. intros.
unfold WWF_qstate.  
 apply mixed_unitary_aux. 
 assert( (2 ^ (s-s') * 2 ^ (e - s) * 2 ^ (e' - e))%nat = (2^ (e'-s')) ) .
type_sovle'. destruct H2.
 apply kron_unitary. apply kron_unitary. apply id_unitary. 
 assumption. apply id_unitary. assumption.
Qed.


Lemma WF_qstate_QUnit_One{s' e'}: forall s e (rho:qstate s' e') (U:Square (2^(e-s))),
s'<=s/\s<=e/\ e<=e'-> 
WF_Unitary U->
WF_qstate rho-> 
WF_qstate (QUnit_One_fun s e U rho).
Proof. 

intros. destruct H1. split.  
rewrite<- Mixed_State_aux_to_Mix_State in *. 
split. apply WWF_qstate_QUnit_One. lia. intuition. intuition. 
 rewrite QUnit_One_trace. intuition. lia. 
 apply WF_Mixed_aux. intuition. assumption. lia.
Qed.

Lemma WWF_qstate_QUnit_Ctrl{s' e'}: forall s0 e0 s1 e1  (rho:qstate s' e') (U:nat ->Square (2^(e1-s1))),
s'<=s0/\s0<=e0/\ e0<=s1/\ s1<=e1 /\ e1<= e'-> 
(forall j, WF_Unitary (U j))->
WWF_qstate rho-> 
WWF_qstate (QUnit_Ctrl_fun s0 e0 s1 e1 U rho).
Proof. intros.
unfold WWF_qstate.  
 apply mixed_unitary_aux. 
 apply QUnit_Ctrl_unitary. intuition.
 intuition.   assumption.
 assumption. 
Qed.


Lemma WF_qstate_QUnit_Ctrl{s' e'}: forall s0 e0 s1 e1  (rho:qstate s' e') (U:nat ->Square (2^(e1-s1))),
s'<=s0/\s0<=e0/\ e0<=s1/\ s1<=e1 /\ e1<= e'-> 
(forall j, WF_Unitary (U j))->
WF_qstate rho-> 
WF_qstate (QUnit_Ctrl_fun s0 e0 s1 e1 U rho).
Proof. 
intros. destruct H1. split.  
rewrite<- Mixed_State_aux_to_Mix_State in *. 
split. apply WWF_qstate_QUnit_Ctrl. lia. intuition. intuition. 
 rewrite QUnit_Ctrl_trace. intuition. lia. lia.  
 apply WF_Mixed_aux. intuition. assumption. lia.
Qed.


Lemma big_sum_ge_0_bound : forall (f: nat-> R) n, 
(forall x, x<n ->(0 <=  (f x))%R) 
-> (0 <=  (big_sum f n))%R.
Proof.
  intros f n H.
  induction n.
  - simpl. lra. 
  - simpl in *.
    rewrite <- Rplus_0_r at 1.
    apply Rplus_le_compat. apply IHn. intros.
    apply H. lia. apply H. lia.  
Qed.


Lemma big_sum_member_le_bound : forall (f : nat -> R) (n : nat), 
(forall x, x<n -> (0 <=  (f x))%R) ->
(forall x, (x < n)%nat -> ( (f x) <=  (big_sum f n))%R).
Proof.
  intros f.
  induction n.
  - intros H x Lt. inversion Lt.
  - intros H x Lt.
    bdestruct (Nat.ltb x n).
    + simpl.
      rewrite <- Rplus_0_r at 1.
      apply Rplus_le_compat.
      apply IHn. intros. apply H. lia. assumption.  
      apply H. lia. 
    + assert (E: x = n) by lia.
      rewrite E.
      simpl.
      rewrite <- Rplus_0_l at 1.
      apply Rplus_le_compat.
      apply big_sum_ge_0_bound. intros. apply H. lia.
      lra.
Qed.  

Lemma big_sum_le: forall m n (f:nat -> R), 
(forall x:nat, x< n -> (0<=  (f x))%R )->
m<=n ->
( (big_sum f m) <=  (big_sum f n))%R.
Proof. intros.  assert(n= m+ (n-m)). lia.
       rewrite H1. rewrite big_sum_sum.
       rewrite<- Rplus_0_r at 1.
       apply Rplus_le_compat_l.
       apply big_sum_ge_0_bound. intros. apply H. lia. 
Qed. 


Lemma Cmod_fst_eq{n:nat}:forall (q:Square n),
Mixed_State_aux q \/ q=Zero->
Cmod (trace q)= fst (trace q).
Proof. intros. destruct H. apply Cmod_snd_0.
       apply mixed_state_trace_gt0_aux. assumption.
       apply mixed_state_trace_real_aux. assumption.
       rewrite H. rewrite Zero_trace.
       simpl. rewrite Cmod_0. reflexivity.
  
Qed.

Lemma big_sum_fst : forall f n,
  fst (big_sum f n) = big_sum (fun i => fst (f i)) n.
Proof. induction n as [| n'].
       - simpl. reflexivity.
       - simpl. f_equal.  auto.
Qed.



Lemma WF_qstate_QMeas{s' e'}: forall s e (rho:qstate s' e') (c:cstate) (i:nat) j,
s'<=s/\s<=e/\ e<=e'-> 
QMeas_fun s e j rho <> Zero ->
(j<2^(e-s))->
WF_qstate rho-> 
WF_qstate (QMeas_fun s e j rho).
Proof.
intros. destruct H2. split.  
rewrite<- Mixed_State_aux_to_Mix_State in *. 
split. apply WWF_qstate_QMeas. lia. intuition. intuition.
intuition.
pose (big_app'_exsist  (2 ^ (e - s)) (fun j0 : nat => (c_update i j0 c, QMeas_fun s e j0 rho))).
destruct e0.
apply Rle_trans with (d_trace_aux x).
rewrite (big_app'_trace ((2 ^ (e - s))) (fun j0 : nat =>
(c_update i j0 c, QMeas_fun s e j0 rho))); try assumption.
unfold s_trace. simpl.
rewrite Cmod_fst_eq; auto.  
rewrite (big_sum_eq_bounded _ (fun i0 : nat =>
fst (@trace (2^(e'-s'))  (QMeas_fun s e i0 rho)))). 
apply (big_sum_member_le_bound ((fun i0 : nat =>
fst (trace (QMeas_fun s e i0 rho))) )); try lia. 
intros. rewrite <-Cmod_fst_eq; auto. apply Cmod_ge_0.
apply (@QMeas_fun_ge_0 s' e'); try lia. apply H2.
intros. rewrite Cmod_fst_eq; auto.
apply (@QMeas_fun_ge_0 s' e'); try lia. apply H2.
apply (@QMeas_fun_ge_0 s' e'); try lia. apply H2.
intros. pose ((@QMeas_fun_ge_0 s' e' _ _ _ rho H H5)).
destruct o. apply H2. econstructor. unfold WWF_state.
simpl. split. assumption. lia. right. assumption. 
 rewrite (QMeas_trace' s e i j c rho) . unfold s_trace. simpl.  intuition.
 intuition. apply H2. assumption. lia. 
Qed.

Lemma WF_qstate_QMeas_app{s' e'}: forall s e (rho:qstate s' e') (c:cstate) (i:nat) n mu,
s'<=s/\s<=e/\ e<=e'-> 
(n<=2^(e-s))->
WF_qstate rho-> 
(big_app' (fun j0 : nat => (c_update i j0 c, QMeas_fun s e j0 rho))
n mu)->
WF_dstate_aux mu.
Proof. intros. apply WWF_dstate_aux_to_WF_dstate_aux.
destruct H1.
rewrite <-Mixed_State_aux_to_Mix_State in H1. 
split. apply WWF_dstate_big_app' with n
(fun j0 : nat =>  (c_update i j0 c, QMeas_fun s e j0 rho)).
intros. pose ((@QMeas_fun_ge_0 s' e' i0 _ _ rho H)).
destruct o. lia. apply H1. econstructor. unfold WWF_state.
simpl. split. assumption. lia. right. assumption.
assumption.
pose (big_app'_exsist  (2 ^ (e - s)) (fun j0 : nat => (c_update i j0 c, QMeas_fun s e j0 rho))).
destruct e0.
apply Rle_trans with (d_trace_aux x).
rewrite (big_app'_trace n (fun j0 : nat =>
(c_update i j0 c, QMeas_fun s e j0 rho))); try assumption.
rewrite (big_app'_trace ((2 ^ (e - s)) ) (fun j0 : nat =>
(c_update i j0 c, QMeas_fun s e j0 rho))); try assumption.
unfold s_trace. simpl.
apply big_sum_le; auto. intros. apply Cmod_ge_0.  
intros. pose ((@QMeas_fun_ge_0 s' e' _ _ _ rho H H5)).
destruct o; try lia.  apply H1. econstructor. unfold WWF_state.
simpl. split. assumption. lia. right. assumption.
intros. pose ((@QMeas_fun_ge_0 s' e' i0 _ _ rho H )).
destruct o; try lia.  apply H1. econstructor. unfold WWF_state.
simpl. split. assumption. lia. right. assumption.  
rewrite (QMeas_trace' s e i n c rho) . unfold s_trace. simpl.  intuition.
intuition. apply H1. assumption. 
Qed.



Lemma WF_ceval'{s e:nat} : forall c (mu mu':list (cstate *qstate s e)), 
WWF_dstate_aux mu->
ceval_single c mu mu'->
WWF_dstate_aux mu'. 
Proof. induction c.
--intros. apply ceval_skip_1 in H0. rewrite <- H0. intuition.
--intros. apply ceval_abort_1 in H0. rewrite H0. apply WF_nil'.
-- induction mu; intros; inversion H0;subst. apply WF_nil'. 
   apply WWF_d_app_aux. apply WF_cons'. inversion_clear H.
   unfold WWF_state in *. unfold WWF_qstate  in *.
   simpl in *. assumption.  apply WF_nil'.
   apply IHmu. inversion_clear H. assumption.  intuition.
-- admit.
--intros. inversion H0; subst. assumption.   apply IHc2 with mu1.
   apply IHc1 with  ((sigma, rho) :: mu0). assumption.
   assumption. assumption.
--induction mu; intros; inversion H0;subst. assumption.
  apply WWF_d_app_aux. apply IHc1 with [(sigma, rho)]. 
  apply WF_cons'. inversion_clear H.
   unfold WWF_state in *. unfold WWF_qstate  in *.
   simpl in *. assumption.  apply WF_nil'. 
   assumption. apply IHmu.  inversion_clear H. assumption.  intuition.

   apply WWF_d_app_aux. apply IHc2 with [(sigma, rho)]. 
  apply WF_cons'. inversion_clear H.
   unfold WWF_state in *. unfold WWF_qstate  in *.
   simpl in *. assumption.  apply WF_nil'. 
   assumption. apply IHmu.  inversion_clear H. assumption.  intuition.
  
-intros. remember <{while b do c end}> as original_command eqn:Horig. 
 induction H0;  try inversion Horig; subst. assumption.
 apply WWF_d_app_aux.  apply IHceval_single3. 
 apply IHc with [(sigma, rho)].  apply WF_cons'. inversion_clear H.
 unfold WWF_state in *. unfold WWF_qstate  in *.
 simpl in *. assumption.  apply WF_nil'.
 assumption. reflexivity.  apply IHceval_single1.  
 inversion_clear H. assumption.  intuition. 
 
 apply WWF_d_app_aux. apply WF_cons'. inversion_clear H.
 unfold WWF_state in *. unfold WWF_qstate  in *.
 simpl in *. assumption.  apply WF_nil'.
 apply IHceval_single. inversion_clear H. assumption.  intuition. 

-induction mu; intros; inversion H0;subst.  apply WF_nil'. 
apply WWF_d_app_aux. unfold QInit_fun. apply WF_cons'.
unfold WWF_state. simpl. split.
apply WWF_qstate_init.  intuition.  inversion_clear H.
unfold WWF_state in H1. simpl in *. intuition. lia.
econstructor.  
apply IHmu.  inversion_clear H. assumption.  intuition.
-induction mu; intros; inversion H0;subst. apply WF_nil'. 
apply WWF_d_app_aux. apply WF_cons'.
unfold WWF_state. unfold WWF_qstate.  simpl.
split. apply WWF_qstate_QUnit_One; try assumption. lia.  
 inversion_clear H.  apply H1. intuition. apply WF_nil'.  
apply IHmu.  inversion_clear H. assumption.
apply inj_pair2_eq_dec in H3. apply inj_pair2_eq_dec in H3.
destruct H3. intuition.  apply Nat.eq_dec. apply Nat.eq_dec.
-induction mu; intros; inversion H0;subst. apply WF_nil'. 
apply WWF_d_app_aux. apply WF_cons'.
unfold WWF_state. unfold WWF_qstate.  simpl.
split. apply WWF_qstate_QUnit_Ctrl ; try assumption. lia. 
  inversion_clear H. apply H1. lia. econstructor. 
apply IHmu.  inversion_clear H. assumption.
apply inj_pair2_eq_dec in H6. apply inj_pair2_eq_dec in H6.
destruct H6.
intuition.  apply Nat.eq_dec. apply Nat.eq_dec.
-induction mu; intros; inversion H0;subst. apply WF_nil'. 
apply WWF_d_app_aux.
 apply WWF_dstate_big_app' with (2 ^ (e0 - s0)) ((fun j : nat =>
 (c_update i j sigma, QMeas_fun s0 e0 j rho))).
intros. pose ((@QMeas_fun_ge_0 s e i0 s0 e0 rho  )).
destruct o; try lia. inversion_clear H.   apply H2.
econstructor. unfold WWF_state.
simpl. split. assumption. lia. right. assumption.
assumption. 
apply IHmu.  inversion_clear H. assumption.
intuition.  
Admitted. 



Lemma ceval_trace_assgn{s e}: forall  (mu mu':list (cstate * qstate s e)) i a,
WWF_dstate_aux mu->
ceval_single <{ i := a }> mu mu'-> (d_trace_aux mu = d_trace_aux mu').
Proof. 
      induction mu; intros.
      
      -inversion_clear H0. reflexivity.
      -inversion H0;subst. rewrite d_trace_app_aux.
       simpl. rewrite Rplus_0_r.  f_equal.  apply IHmu with i a0.
       inversion_clear H. assumption. assumption.
       econstructor. unfold WWF_state. simpl. inversion_clear H. assumption.
       apply WF_nil'.
       apply WF_ceval' with  (<{ i := a0 }>) mu. 
       inversion_clear H. assumption. assumption.
Qed.



Lemma ceval_trace_Qinit{s' e'}: forall  (mu mu':list (cstate * qstate s' e')) s e,
WWF_dstate_aux mu->
ceval_single <{ QInit s e }> mu mu'-> (d_trace_aux mu = d_trace_aux mu').
Proof. 
      induction mu; intros.
      
      -inversion_clear H0. reflexivity.
      -inversion H0;subst. rewrite d_trace_app_aux.
       simpl. rewrite Rplus_0_r.  f_equal. unfold s_trace. simpl.
       f_equal. symmetry.  apply QInit_trace. lia. 
       apply WF_Mixed_aux.    
      inversion_clear H. apply H1.
       apply IHmu with s e. 
       inversion_clear H. assumption. assumption.
       apply WF_ceval' with (<{ (s e) :Q= 0 }>) [(sigma, rho)].
       apply WF_cons'. inversion_clear H.  intuition. apply WF_nil'.
       assert(([(sigma, QInit_fun s e rho)]) = StateMap.Raw.map2 (@option_app s' e') ([(sigma, QInit_fun s e rho)]) ([])).
       symmetry. apply map2_nil_r. rewrite H1. apply E_Qinit. intuition.
        apply E_nil.  
       apply WF_ceval' with  (<{ (s e) :Q= 0 }>) mu. 
       inversion_clear H.  assumption. assumption.
Qed.


Lemma ceval_trace_QUnit_one{s' e'}: forall  (mu mu':list (cstate * qstate s' e')) s e (U: Square (2 ^ (e - s))),
WWF_dstate_aux mu->
ceval_single <{ QUnit_One s e U }> mu mu'-> (d_trace_aux mu = d_trace_aux mu').
Proof. 
      induction mu; intros.
      
      -inversion_clear H0. reflexivity.
      -inversion H0;subst. rewrite d_trace_app_aux.
       simpl. rewrite Rplus_0_r.  f_equal. unfold s_trace. simpl.
       f_equal. symmetry.  apply QUnit_One_trace. lia. 
       apply WF_Mixed_aux.    
       inversion_clear H. apply H1. assumption.
       apply IHmu with s e U. 
       inversion_clear H. assumption. apply inj_pair2_eq_dec in H3.
       apply inj_pair2_eq_dec in H3. destruct H3.
       assumption. apply Nat.eq_dec. apply Nat.eq_dec. 
       apply WF_ceval' with (QUnit_One s e U1) [(sigma, rho)].
       apply WF_cons'. inversion_clear H. assumption. apply WF_nil'.
       remember ((sigma, QUnit_One_fun s e U1 rho)).
       assert(([p]) =  (([p]) +l ([]))). 
       symmetry. rewrite map2_nil_r. reflexivity.  
       rewrite H1. rewrite Heqp. apply E_Qunit_One. assumption. assumption.
        apply E_nil.  
       apply WF_ceval' with  (<{ QUnit_One s e U1 }>) mu. 
       inversion_clear H. assumption. assumption.
Qed.


Lemma ceval_trace_QUnit_ctrl{s' e'}: forall (mu mu':list (cstate * qstate s' e')) s0 e0  s1 e1 (U: nat-> Square (2 ^ (e1 - s1))),
WWF_dstate_aux mu->
ceval_single <{ QUnit_Ctrl s0 e0 s1 e1 U }> mu mu'-> (d_trace_aux mu = d_trace_aux mu').
Proof. 
      induction mu; intros.
      
      -inversion_clear H0. reflexivity.
      -inversion H0;subst. rewrite d_trace_app_aux.
       simpl. rewrite Rplus_0_r.  f_equal. unfold s_trace. simpl.
       f_equal. symmetry.  apply QUnit_Ctrl_trace. intuition. intuition. 
       apply WF_Mixed_aux.    
       inversion_clear H. apply H1. assumption.
       apply IHmu with s0 e0 s1 e1 U. 
       inversion_clear H. assumption. apply inj_pair2_eq_dec in H6.
       apply inj_pair2_eq_dec in H6. destruct H6.
       assumption. apply Nat.eq_dec. apply Nat.eq_dec. 
       apply WF_ceval' with (QUnit_Ctrl s0 e0 s1 e1 U1) [(sigma, rho)].
       apply WF_cons'. inversion_clear H. assumption. apply WF_nil'.
       remember ((sigma, QUnit_Ctrl_fun s0 e0 s1 e1 U1 rho)).
       assert(([p]) =  (([p]) +l ([]))). 
       symmetry. rewrite map2_nil_r. reflexivity.  
       rewrite H1. rewrite Heqp. apply E_QUnit_Ctrl. assumption. assumption.
        apply E_nil.  
       apply WF_ceval' with  (<{ QUnit_Ctrl s0 e0 s1 e1 U1 }>) mu. 
       inversion_clear H. assumption. assumption.
Qed.


Lemma ceval_trace_QMeas{s' e'}: forall  (mu mu':list (cstate * qstate s' e')) s e i,
WWF_dstate_aux mu->
ceval_single <{ i :=M [[s e]] }> mu mu'-> (d_trace_aux mu = d_trace_aux mu').
Proof. 
      induction mu; intros.
      
      -inversion_clear H0. reflexivity.
      -inversion H0;subst. rewrite d_trace_app_aux.
       simpl.   f_equal.  symmetry.
       eapply (@QMeas_trace' s' e' s e). intuition.
       lia.  inversion_clear H. apply H1. apply H9.
       apply IHmu with s e i. 
       inversion_clear H. assumption. assumption.
       apply WF_ceval' with (<{ i :=M [[s e]] }>) [(sigma, rho)].
       apply WF_cons'. inversion_clear H. assumption. apply WF_nil'.
       
        apply ceval_QMeas. lia. assumption. 
       apply WF_ceval' with  (<{ i :=M [[s e]] }>) mu. 
       inversion_clear H. assumption. assumption.
Qed.


Lemma ceval_trace_eq{s' e'}: forall c  (mu mu':list (cstate * qstate s' e')),
WWF_dstate_aux mu->
ceval_single c mu mu'-> ((d_trace_aux mu' = d_trace_aux mu)%R).
Proof. induction c. 
-- --intros. apply ceval_skip_1 in H0. rewrite <- H0. intuition.
--admit.
-- intros. rewrite <-(ceval_trace_assgn mu _ i a). lra. assumption. assumption.
-- admit.
-- intros. inversion H0; subst. simpl. lra. apply eq_trans with (d_trace_aux mu1).
   apply IHc2. apply WF_ceval' with c1 ((sigma, rho) :: mu0). assumption.
   assumption. assumption. apply IHc1. assumption. assumption.
--induction mu; intros; inversion H0; subst; try simpl; try lra;  
  inversion H;subst;  rewrite d_trace_app_aux; 
  try simpl; try f_equal;
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
inversion H;subst.  rewrite d_trace_app_aux; 
try simpl; try f_equal;
assert(s_trace (sigma, rho)= d_trace_aux [ (sigma, rho)]); try simpl;
try rewrite Rplus_0_r; try reflexivity; try rewrite H1. 
apply eq_trans with (d_trace_aux mu1). apply IHceval_single3.
apply WF_ceval' with c ([(sigma, rho)]).  apply WF_cons'. assumption.
  apply WF_nil'. assumption. reflexivity.
  apply IHc. apply WF_cons'. assumption. apply WF_nil'. assumption.
  apply IHceval_single1. assumption. reflexivity. 
  apply WF_ceval' with (<{ while b do c end }>) (mu1). 
  apply WF_ceval' with c ([(sigma, rho)]).  apply WF_cons'. assumption.
  apply WF_nil'. assumption. assumption. 
 apply WF_ceval' with (<{ while b do c end }>) (mu).  assumption.
    assumption. 

    inversion H;subst.  rewrite d_trace_app_aux. simpl.  rewrite Rplus_0_r.
    f_equal . apply IHceval_single. assumption. reflexivity.
    apply WF_cons'. assumption. apply WF_nil'.
    apply WF_ceval' with (<{ while b do c end }>) (mu).  assumption.
    assumption.
    
--intros. rewrite <-(ceval_trace_Qinit mu _ s e ). lra. assumption. assumption.
--intros. rewrite <-(ceval_trace_QUnit_one mu _ s e  U). lra. assumption. assumption.
--intros. rewrite <-(ceval_trace_QUnit_ctrl mu _ s0 e0 s1 e1  U). lra. assumption. assumption.
-- intros. rewrite <-(ceval_trace_QMeas mu _ s e i). lra. assumption. assumption.
Admitted.


Lemma WF_ceval{s' e':nat} : forall c (mu mu':list (cstate *qstate s' e')), 
WF_dstate_aux mu->
ceval_single c mu mu'->
WF_dstate_aux mu'. 
Proof. intros.   apply WWF_dstate_aux_to_WF_dstate_aux. 
 apply WWF_dstate_aux_to_WF_dstate_aux in H. 
 split. apply WF_ceval' with (c) mu . intuition. 
 assumption.   
 rewrite (ceval_trace_eq  c  mu _); intuition.
Qed. 