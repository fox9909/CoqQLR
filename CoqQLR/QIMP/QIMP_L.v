Require Import Reals.
Require Import Coquelicot.Complex.
Require Import Strings.String.
Require Import Lists.List.
Require Import
  Coq.FSets.FMapList
  Coq.Structures.OrderedTypeEx.

From Quan Require Import Matrix.
From Quan Require Import Quantum.
From Quan Require Import Mixed_State.
From Quan Require Import QState_L.
From Quan Require Import Reduced.
From Quan Require Import Basic.

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
  | ADiv (a1 a2:aexp)
  | Afun (f:nat->nat->nat->nat) (a1:aexp) (a2:aexp) (a3:aexp).

Definition X0 : nat := 0.
Definition X1 : nat := 1.
Definition X2 : nat := 3.

Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BNeq (a1 a2 : aexp)
  | BLt (a1 a2 : aexp)
  | BGt (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).

Coercion ANum : nat >-> aexp.

Declare Custom Entry com.
Declare Scope com_scope.
Local Open Scope com_scope.
Notation "<{ e }>" := e (at level 0, e custom com at level 99) : com_scope.
Notation "x" := x (in custom com at level 0, x constr at level 0) : com_scope.
Notation "x + y"   := (APlus x y) (in custom com at level 50, left associativity).
Notation "x - y"   := (AMinus x y) (in custom com at level 50, left associativity).
Notation "x * y"   := (AMult x y) (in custom com at level 40, left associativity).
Notation "x / y"   := (ADiv x y) (in custom com at level 40, left associativity).
Notation "x % y"   := (AMod x y) (in custom com at level 40, left associativity).
Notation "x ^ y"   := (APow x y) (in custom com at level 30, left associativity).

Notation "'true'"  := BTrue (in custom com at level 0).
Notation "'false'" := BFalse (in custom com at level 0).
Notation "x < y"  := (BLt x y) (in custom com at level 70, no associativity).
Notation "x > y"   := (BGt x y) (in custom com at level 70, no associativity).
Notation "x = y"   := (BEq x y) (in custom com at level 70, no associativity).
Notation "x <> y"  := (BNeq x y) (in custom com at level 70, no associativity).
Notation "x && y"  := (BAnd x y) (in custom com at level 80, left associativity).
Notation "'~' b"   := (BNot b) (in custom com at level 75, right associativity).


Inductive com : Type :=
  | CSkip
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

            Notation "[[ s e ]] :Q= 0 "  :=
              (QInit s e)
                 (in custom com at level 0, s  constr at level 0,
                 e  constr at level 0,
                   no associativity) : com_scope.
 
Notation " U  '[[' s e ']]' " :=
         (QUnit_One s e U)
            (in custom com at level 1,  s at level 0,
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
  |Afun f1  a1 a2 a3 =>NSet.union (NSet.union (Free_aexp a1)  (Free_aexp a2)) (Free_aexp a3)
  end.

Fixpoint Free_bexp (b:bexp):CSet:=
  match b with
    | <{a1 = a2}>   => NSet.union (Free_aexp a1)  (Free_aexp a2)
    | <{a1 <> a2}>  => NSet.union (Free_aexp a1)  (Free_aexp a2)
    | <{a1 < a2}>  => NSet.union (Free_aexp a1)  (Free_aexp a2)
    | <{a1 > a2}>   => NSet.union (Free_aexp a1)  (Free_aexp a2)
    | <{~ b}>       => (Free_bexp b) 
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
    |<{ [[ s e ]] :Q= 0 }>
         => (NSet.empty, Qsys_to_Set s e)
    | <{ U [[s e ]] }>  
         =>(NSet.empty, Qsys_to_Set  s e)
    | <{ U [[ s0 e0 ]] [[ s1 e1 ]] }> 
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
    |<{ [[ s e ]]:Q=0 }>
         => (NSet.empty, Qsys_to_Set  s e)
    | QUnit_One s e U  
         =>(NSet.empty, Qsys_to_Set s e)
    | QUnit_Ctrl s0 e0 s1 e1 U  
         =>(NSet.empty, NSet.union (Qsys_to_Set s0 e0) (Qsys_to_Set s1 e1))
    |<{ x :=M [[ s e]] }>
         => (NSet.add x (NSet.empty), Qsys_to_Set s e  )
    |_=>(NSet.empty, NSet.empty)
  end.



(*-----------------------Semantics------------------------------------*)
Local Open Scope nat_scope.

Fixpoint aeval{s e:nat} (st: state s e) 
               (a : aexp) : nat :=
  match a with
  | ANum n =>   n
  | AId x =>  (c_find x (fst st))                         
  | <{a1 + a2}> => (aeval st a1) + (aeval st a2)
  | <{a1 - a2}> => (aeval st a1) - (aeval st a2)
  | <{a1 * a2}> => (aeval st a1) * (aeval st a2)
  | AGcd a1 a2 => Nat.gcd (aeval st a1) (aeval st a2)
  |  <{a1 ^ a2}> => Nat.pow (aeval st a1) (aeval st a2)
  |  <{a1 / a2}> => (Nat.div (aeval st a1) (aeval st a2))
  |  <{a1 % a2}> => (Nat.modulo (aeval st a1) (aeval st a2))
  | Afun f1 a1 a2 a3 => f1  (aeval st a1) (aeval st a2) (aeval st a3) 
  end.



  Fixpoint beval{s e: nat} (st : state s e) 
  (b : bexp) : bool :=
match b with
| <{true}>      => true
| <{false}>     => false
| <{a1 = a2}>   => (aeval st a1) =? (aeval st a2)
| <{a1 <> a2}>  => negb ((aeval st a1) =? (aeval st a2))
| <{a1 < a2}>  => (aeval st a1) <? (aeval st a2)
| <{a1 > a2}>   => negb ((aeval st a1) <=? (aeval st a2))
| <{~ b1}>      => negb (beval st b1)
| <{b1 && b2}>  => andb (beval st b1) (beval st b2)
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

Lemma WF_NZ_Mixed_aux : forall {n} (ρ : Density n), 
NZ_Mixed_State_aux ρ -> WF_Matrix ρ.
Proof.  induction 1; auto with wf_db. Qed.
#[export] Hint Resolve WF_NZ_Mixed_aux : wf_db.

Lemma WF_Mixed_aux : forall {n} (ρ : Density n), 
Mixed_State_aux ρ -> WF_Matrix ρ.
Proof.  induction 1; auto with wf_db. Qed.
#[export] Hint Resolve WF_Mixed_aux : wf_db.


Lemma d_reduced_app{ s e :nat}: forall n l r(f: nat -> list (cstate *qstate s e)),
(d_reduced  (big_app
           (fun j : nat => f j) n) l r)=
big_app (fun j :nat => d_reduced (f j) l r) n. 
Proof. induction n; intros;
       simpl; try reflexivity.
       rewrite d_reduced_map2.
       rewrite IHn. reflexivity.
Qed.

Local Open Scope nat_scope.
Lemma d_reduced_app'{ s e :nat}: forall n l r (f: nat ->  (cstate *qstate s e)) mu,
s <= l /\ l <= r <= e  ->
(forall i, i<n->@Mixed_State_aux (2^(e-s)) (snd (f i)))->
(big_app' (fun j : nat => f j) n) mu ->
(exists mu', (big_app' (fun j :nat => (fst (f j), (Reduced (snd (f j)) l r))) n mu')
/\ (d_reduced mu l r)= mu'). 
Proof. induction n; intros. inversion_clear H1.
       exists nil. simpl. split. econstructor.
       reflexivity. 
       inversion_clear H1.
       apply (IHn l r) in H3. destruct H3. 
       exists x. split. 
       econstructor. simpl. rewrite H2. rewrite Reduced_Zero.
       reflexivity. 
       apply H1. apply H1. lia. intros. 
       apply H0; try lia. 
       rewrite d_reduced_map2.
       apply (IHn l r) in H3. destruct H3.
       exists (x +l (d_reduced [f n] l r)).
       assert(d_reduced [f n] l r=
       [(fun j : nat =>
       (fst (f j), Reduced (snd (f j)) l r)) n]).
       destruct (f n).
       simpl. reflexivity. rewrite H3. 
       split. apply (big_app_cons ((fun j : nat =>
       (fst (f j), Reduced (snd (f j)) l r)))).
        simpl. intro. 
        assert(@trace (2^(r-l))(Reduced (snd (f n)) l r)= C0).
        rewrite H4. rewrite Zero_trace. reflexivity.
        rewrite Reduced_trace in H5; try lia; try auto_wf.
        pose ( H0 n). 
        rewrite NZ_Mixed_State_aux_equiv' in m. 
        destruct m. lia.
         apply nz_mixed_state_trace_gt0_aux in H6.
        rewrite H5 in H6. simpl in H6. lra.
        rewrite H6 in H2.  destruct H2. reflexivity.  
        pose ( H0 n). destruct m. lia.  auto_wf.   

       apply H1. apply H1. f_equal. apply H1. lia. 
       intros. apply H0; try lia.
Qed.

Definition QInit_fun{s0 e0:nat} (s e:nat) (rho:(qstate s0 e0)):=
  @big_sum (Matrix (2^(e0-s0)) (2^(e0-s0))) _ (fun i:nat=>  
  q_update (((I (2^(s-s0))) ⊗ ((∣ 0 ⟩_ (2^(e-s))) × (⟨ i ∣_ (2^(e-s)))) ⊗ (I (2^(e0-e)))))  rho) (2^(e-s)) .

Definition QUnit_One_fun{s0 e0:nat} (s e:nat)(U: Square (2^(e-s)))  (rho:qstate s0 e0):= 
  q_update ((I (2^(s-s0)) ⊗ U ⊗ (I (2^(e0-e))))) rho .

Definition QUnit_Ctrl_fun{s' e':nat} (s0 e0 s1 e1:nat) (U: nat->Square (2^(e1-s1))) (rho:qstate s' e') :=
  q_update  ((@big_sum (Matrix (2^(e'-s')) (2^(e'-s'))) _ (fun i:nat => @Mmult (2^(e'-s')) (2^(e'-s')) (2^(e'-s'))
                (I (2^(s0-s')) ⊗ (∣ i ⟩_ (2^(e0-s0)) × ⟨ i ∣_ (2^(e0-s0)) ) ⊗ (I (2^(e'-e0)))) 
                 (I (2^(s1-s')) ⊗ (U i) ⊗ (I (2^(e'-e1))))) (2^(e0 -s0)))) rho.

Local Open Scope nat_scope.



Definition  QMeas_fun{s' e':nat} (s e j:nat) (rho: qstate s' e'):= 
(q_update (((I (2^(s-s'))) ⊗ (∣ j ⟩_ (2^(e-s)) × (⟨ j ∣_ (2^(e-s)))) ⊗ (I (2^(e'-e))))) rho).


  Definition option_nat (n:option nat):nat :=
  match n with 
  |None => 0
  |Some x => x
   end .

  Inductive ceval_single{s' e':nat}: com-> list (cstate * (qstate s' e' )) -> list (cstate * (qstate s' e')) -> Prop:=
  |E_nil:  forall  c, ceval_single c nil nil
  |E_Skip sigma rho mu:  ceval_single <{skip}> ((sigma,rho)::mu) ((sigma,rho)::mu)
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
                        -> NSet.Subset (snd (MVar c2)) (Qsys_to_Set s' e')
                        ->ceval_single (CIf b c1 c2) mu mu''
                        ->ceval_single c1 ([(sigma,rho)]) mu'
                        ->ceval_single (CIf b c1 c2) ((sigma,rho)::mu)  
                           (StateMap.Raw.map2 option_app mu' mu'')
  |E_IF_false sigma rho mu: forall (mu' mu'':list (cstate * (qstate s' e'))) c1 c2 b, 
                      (beval (sigma, rho) b)=false
                      -> NSet.Subset (snd (MVar c1)) (Qsys_to_Set s' e')
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
                      -> NSet.Subset (snd (MVar c)) (Qsys_to_Set s' e') 
                      ->ceval_single (CWhile b c) mu mu'
                      ->ceval_single (CWhile b c) ((sigma,rho)::mu)  
                       (StateMap.Raw.map2 option_app [(sigma,rho)] mu').

Inductive ceval{s e:nat}: com -> dstate s e-> dstate s e->Prop:=
  |E_com:  forall c (mu mu':dstate s e), 
          WF_dstate mu-> 
        (ceval_single c (StateMap.this mu) (StateMap.this mu'))->
          ceval c mu mu'.


(*-----------------------------------Ceval-----------------------------------------------*)
Lemma super_0{ m n:nat}: forall (M:Matrix m n),
super M Zero = Zero .
Proof. intros. unfold super. Msimpl. reflexivity.
Qed.

Lemma WF_Mixed_Zero{s e:nat}:forall (q: Square (2^(e-s))),
WF_qstate q \/ q= Zero ->
WF_Matrix q .
Proof. intros. destruct H. destruct H. auto_wf. 
rewrite H. auto_wf.
Qed.
#[export] Hint Resolve WF_Mixed WF_Mixed_Zero : wf_db.

Lemma WF_QInit{s' e'}: forall s e (rho:qstate s' e'),
s'<=s/\s<=e/\ e<=e'-> 
@WF_Matrix (2^(e'-s'))  (2^(e'-s')) rho-> 
@WF_Matrix (2^(e'-s'))  (2^(e'-s')) (QInit_fun s e rho).
Proof. intros. unfold QInit_fun. unfold q_update. 
apply WF_Msum.  intros. apply WF_super. 
apply WF_kron; type_sovle'. apply WF_kron; type_sovle'.
auto_wf. apply WF_mult. apply WF_base. apply pow_gt_0.
apply WF_adjoint. apply WF_base. assumption. 
 auto_wf. auto_wf. 
Qed. 


Lemma WF_QUnit_One{s' e'}: forall s e (rho:qstate s' e') (U:Square (2^(e-s))),
s'<=s/\s<=e/\ e<=e'-> 
WF_Unitary U->
@WF_Matrix (2^(e'-s'))  (2^(e'-s')) rho-> 
@WF_Matrix (2^(e'-s')) ((2^(e'-s'))) (QUnit_One_fun s e U rho).
Proof. intros. unfold QUnit_One_fun. unfold q_update. destruct H0.
auto_wf.
Qed.


Lemma WF_QUnit_Ctrl{s' e'}: forall s0 e0 s1 e1  (rho:qstate s' e') (U:nat ->Square (2^(e1-s1))),
s'<=s0/\s0<=e0/\ e0<=s1/\ s1<=e1 /\ e1<= e'-> 
(forall j, WF_Unitary (U j))->
@WF_Matrix (2^(e'-s'))  (2^(e'-s')) rho-> 
@WF_Matrix (2^(e'-s'))  (2^(e'-s')) (QUnit_Ctrl_fun s0 e0 s1 e1 U rho).
Proof. 
intros. unfold QUnit_Ctrl_fun. unfold q_update.
apply WF_super. apply WF_Msum.
intros. pose (H0 i). destruct w. auto_wf. assumption.
Qed.

Lemma WF_QMeas{s' e'}: forall s e (rho:qstate s' e') j,
s'<=s/\s<=e/\ e<=e'-> 
QMeas_fun s e j rho <> Zero ->
(j<2^(e-s))->
@WF_Matrix (2^(e'-s'))  (2^(e'-s')) rho-> 
@WF_Matrix (2^(e'-s'))  (2^(e'-s')) (QMeas_fun s e j rho).
Proof. intros.
intros. unfold QMeas_fun. unfold q_update. auto_wf. 
Qed.
#[export] Hint Resolve WF_QInit WF_QUnit_One WF_QUnit_Ctrl WF_QMeas : wf_db.


Lemma QInit_Zero{ s' e':nat}: forall s e ,
(@QInit_fun s' e' s e Zero) = @Zero s' e'.
Proof.  intros.  unfold QInit_fun. unfold q_update. 
apply (@big_sum_0_bounded (Matrix (2^(e'-s')) (2^(e'-s')))).
intros. apply super_0. 
Qed. 


Lemma QUnit_One_Zero{s' e'}: forall s e (U:Square (2^(e'-s'))),
 (@QUnit_One_fun s' e' s e U Zero) = Zero.
Proof. intros. unfold QUnit_One_fun. unfold q_update. 
apply (@super_0 (2^(e'-s'))). 
Qed.


Lemma QUnit_Ctrl_Zero{s' e'}: forall s0 e0 s1 e1  (U:nat ->Square (2^(e1-s1))),
(@QUnit_Ctrl_fun s' e' s0 e0 s1 e1 U Zero= Zero).
Proof. 
intros. unfold QUnit_Ctrl_fun. unfold q_update.
apply (@super_0 (2^(e'-s'))).
Qed.

Lemma QMeas_Zero{s' e'}: forall s e  j,
@QMeas_fun s' e' s e j Zero = Zero.
Proof. intros. unfold QMeas_fun. unfold q_update.
apply (@super_0 (2^(e'-s'))).
Qed.


Lemma super_plus{m n}: forall (A:Matrix m n)(M N:Square n),
super A (M.+ N) = super A M .+ (super A N) .
Proof. intros. unfold super. rewrite Mmult_plus_distr_l. 
       rewrite Mmult_plus_distr_r. reflexivity.
Qed.


Lemma super_sum{m n}: forall (A:Matrix m n) (f: nat->Square n) n',
super A (big_sum f n') = big_sum (fun i=> super A (f i)) n'. 
Proof. intros.  unfold super. rewrite Mmult_Msum_distr_l. 
       rewrite Mmult_Msum_distr_r. reflexivity.
Qed.


Lemma QInit_fun_plus{s' e':nat}: forall s e (q q0: qstate s' e'), 
@Mplus (2^(e'-s')) (2^(e'-s')) (QInit_fun s e q) (QInit_fun s e q0)=
@QInit_fun s' e' s e (q .+ q0) .
Proof. unfold QInit_fun. unfold q_update.
intros. rewrite <-Msum_plus. 
apply big_sum_eq_bounded. intros. 
rewrite super_plus. reflexivity.  
Qed.


Lemma  super_scale: forall {m n:nat} (M : Matrix m n) (A :Matrix n n) r,
super M (r .* A) =r.* (super M A) .
Proof. unfold super. intros. rewrite Mscale_mult_dist_r.
        rewrite Mscale_mult_dist_l. reflexivity.   
Qed.

Lemma QInit_fun_scale{s' e':nat}: forall s e p (q : qstate s' e'), 
@QInit_fun s' e' s e (p .* q) =
p .* (QInit_fun s e q) .
Proof. unfold QInit_fun. unfold q_update.  intros.
rewrite <-(@Mscale_Msum_distr_r ). 
apply big_sum_eq_bounded. intros.
rewrite super_scale. reflexivity.
Qed.

Lemma  super_kron_r{s0 e0 s e x:nat}: forall (A: Square (2^(e-s))) (p: qstate s0 x ) (q:qstate x e0),
s0 <= s /\ s <= e /\ e <= x <= e0 -> WF_Matrix A-> 
@WF_Matrix (2^(e0-x)) (2^(e0-x)) q->
@super (2^(e0-s0)) (2^(e0-s0)) (I (2 ^ (s - s0)) ⊗ A  ⊗ I (2 ^ (e0 - e))) 
(@kron (2^(x-s0)) (2^(x-s0)) (2^(e0-x))(2^(e0-x)) p q) =
@kron  (2^(x-s0)) (2^(x-s0)) (2^(e0-x))
(2^(e0-x)) (@super (2^(x-s0)) (2^(x-s0)) (I (2 ^ (s - s0)) ⊗ A  ⊗ I (2 ^ (x - e))) p) q.
Proof. intros. unfold super.
assert(2 ^ (s - s0) * 2 ^ (e - s) * 2 ^ (x - e)= 2^(x-s0))%nat.
type_sovle'. destruct H2.
assert(2 ^ (s - s0) * 2 ^ (e - s) * 2 ^ (e0 - e)= 2^(e0-s0))%nat.
type_sovle'. destruct H2.
repeat rewrite kron_adjoint.
repeat rewrite id_adjoint_eq. 
apply Logic.eq_trans with ((I (2 ^ (s - s0)) ⊗ A ⊗ I (2 ^ (x - e))
 ⊗ I (2 ^ (e0 - x))) × (p ⊗ q)
× ((I (2 ^ (s - s0)) ⊗ (A) † ⊗ I (2 ^ (x - e))) ⊗ I (2 ^ (e0 - x))) ).
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


Lemma  super_kron_l{s0 e0 s e x:nat}: forall (A: Square (2^(e-s))) (p: qstate s0 x ) (q:qstate x e0),
s0 <= x /\ x <= s /\ s <= e <= e0 -> WF_Matrix A-> 
@WF_Matrix (2^(x-s0)) (2^(x-s0)) p->
@super (2^(e0-s0)) (2^(e0-s0)) (I (2 ^ (s - s0)) ⊗ A  ⊗ I (2 ^ (e0 - e))) 
(@kron (2^(x-s0)) (2^(x-s0)) (2^(e0-x))(2^(e0-x)) p q) =
@kron  (2^(x-s0)) (2^(x-s0)) (2^(e0-x))
(2^(e0-x))  p (@super (2^(e0-x)) (2^(e0-x)) (I (2 ^ (s - x)) ⊗ A  ⊗ I (2 ^ (e0- e))) q).
Proof. intros. unfold super. 
assert(2 ^ (s - x) * 2 ^ (e - s) * 2 ^ (e0 - e)= 2^(e0-x))%nat.
type_sovle'. destruct H2.
assert(2 ^ (s - s0) * 2 ^ (e - s) * 2 ^ (e0 - e)= 2^(e0-s0))%nat.
type_sovle'. destruct H2.
repeat rewrite kron_adjoint.
repeat rewrite id_adjoint_eq. 
apply Logic.eq_trans with ((I (2 ^ (x - s0)) ⊗ (I (2 ^ (s - x)) ⊗ A ⊗ I (2 ^ (e0-e)))) × (p ⊗ q)
× (( I (2 ^ (x - s0)) ⊗ (I (2 ^ (s - x)) ⊗ (A) † ⊗ I (2 ^ (e0 - e))))) ).

f_equal; type_sovle'. f_equal; type_sovle'. 
repeat rewrite <-kron_assoc; auto_wf.  f_equal; type_sovle'. 
f_equal; type_sovle'.
rewrite id_kron. f_equal; type_sovle'.
repeat rewrite <-kron_assoc; auto_wf. 
f_equal; type_sovle'. 
rewrite id_kron. f_equal; type_sovle'. f_equal; type_sovle'.
repeat rewrite kron_mixed_product.
 rewrite Mmult_1_l; auto_wf.  rewrite Mmult_1_r; auto_wf.  
reflexivity. 
Qed.


Lemma QInit_fun_kron_r{s0 x e0:nat}: forall s e (p : qstate s0 x)
(q: qstate x e0), 
@WF_Matrix (2^(e0-x)) (2^(e0-x)) q->
s0<=s/\s<=e/\e<=x/\x<=e0->
@QInit_fun s0 e0  s e (@kron (2^(x-s0)) (2^(x-s0)) (2^(e0-x)) (2^(e0-x)) p q) =
@kron  (2^(x-s0)) (2^(x-s0)) (2^(e0-x)) (2^(e0-x)) (QInit_fun s e p) q.
Proof. unfold QInit_fun. unfold q_update.  intros.
rewrite (@kron_Msum_distr_r 
_ _ (2^(e0-x)) (2^(e0-x))). apply big_sum_eq_bounded.
intros.  
rewrite (@super_kron_r s0 e0 s  e x); try lia; auto_wf.
reflexivity. pose(pow_gt_0 (e-s)) . auto_wf.

Qed. 

Lemma QUnit_One_fun_kron_r{s0 x e0:nat}: forall s e U (p : qstate s0 x)
(q: qstate x e0), 
WF_Matrix U->
@WF_Matrix (2^(e0-x)) (2^(e0-x)) q->
s0<=s/\s<=e/\e<=x/\x<=e0->
@QUnit_One_fun s0 e0  s e U (@kron (2^(x-s0)) (2^(x-s0)) (2^(e0-x))
(2^(e0-x)) p q) =
@kron  (2^(x-s0)) (2^(x-s0)) (2^(e0-x))
(2^(e0-x)) (QUnit_One_fun s e U p) q.
Proof. unfold QUnit_One_fun.  intros. unfold q_update.
apply super_kron_r; try assumption.
Qed.

Lemma QInit_fun_kron_l{s0 x e0:nat}: forall s e (p : qstate s0 x)
(q: qstate x e0), 
@WF_Matrix (2^(x-s0)) (2^(x-s0)) p->
s0<=x/\x<=s/\s<=e/\e<=e0->
@QInit_fun s0 e0 s e (@kron (2^(x-s0)) (2^(x-s0)) (2^(e0-x))
(2^(e0-x)) p q) =
@kron  (2^(x-s0)) (2^(x-s0)) (2^(e0-x))
(2^(e0-x))  p (QInit_fun s e q).
Proof. unfold QInit_fun. unfold q_update.  intros.
rewrite (@kron_Msum_distr_l  (2^(e0-x))
(2^(e0-x)) (2^(x-s0)) (2^(x-s0))). apply big_sum_eq_bounded.
intros.  
rewrite (@super_kron_l s0 e0 s  e x); try lia; auto_wf.
reflexivity.  pose(pow_gt_0 (e-s)) . auto_wf.
Qed. 

Lemma QUnit_One_fun_kron_l{s0 x e0:nat}: forall s e U (p : qstate s0 x)
(q: qstate x e0), 
WF_Matrix U->
@WF_Matrix (2^(x-s0)) (2^(x-s0)) p->
s0<=x/\x<=s/\s<=e/\e<=e0->
@QUnit_One_fun s0 e0  s e U (@kron (2^(x-s0)) (2^(x-s0)) (2^(e0-x))
(2^(e0-x)) p q) =
@kron  (2^(x-s0)) (2^(x-s0)) (2^(e0-x))
(2^(e0-x)) p (QUnit_One_fun s e U q) .
Proof. unfold QUnit_One_fun.  intros. unfold q_update.
apply super_kron_l; try assumption.
Qed.



Lemma QUnit_One_fun_plus{s' e':nat}: forall s e (q q0: qstate s' e') (U:Square (2^(e-s))), 
@Mplus (2^(e'-s')) (2^(e'-s')) (QUnit_One_fun s e U q0) (QUnit_One_fun s e U q)=
@QUnit_One_fun s' e' s e U (q0 .+ q).
Proof. unfold QUnit_One_fun.  intros. 
unfold q_update.  rewrite super_plus. reflexivity.
Qed.


Lemma QUnit_One_fun_scale{s' e':nat}: forall s e p (q : qstate s' e') (U:Square (2^(e-s))), 
@scale (2^(e'-s')) (2^(e'-s')) p (QUnit_One_fun s e U q)=
@QUnit_One_fun s' e' s e U (p .*  q).
Proof. unfold QUnit_One_fun.  intros. 
unfold q_update. rewrite super_scale.  reflexivity.
Qed.

Lemma QUnit_Ctrl_fun_plus{s' e':nat}: forall s0 e0 s1 e1 (q q0: qstate s' e') (U: nat-> Square (2^(e1-s1))), 
@Mplus (2^(e'-s')) (2^(e'-s')) (QUnit_Ctrl_fun s0 e0 s1 e1 U q0) (QUnit_Ctrl_fun s0  e0 s1 e1 U q)=
@QUnit_Ctrl_fun s' e' s0 e0 s1 e1 U (q0 .+ q).
Proof. unfold QUnit_Ctrl_fun.  intros. 
unfold q_update. rewrite super_plus.  reflexivity.
Qed.

Lemma QUnit_Ctrl_fun_scale{s e:nat}: forall s0 e0 s1 e1 p (q: qstate s e) (U: nat-> Square (2^(e1-s1))), 
@scale (2^(e-s)) (2^(e-s)) p (QUnit_Ctrl_fun s0  e0 s1 e1 U q)=
@QUnit_Ctrl_fun s e s0 e0 s1 e1 U (p .* q).
Proof. unfold QUnit_Ctrl_fun.  intros. 
unfold q_update.  rewrite super_scale. reflexivity. 
Qed.

Lemma QUnit_Ctrl_fun_kron_r{s x e:nat}: forall s0 e0 s1 e1 (U:nat-> Square (2^(e1-s1))) (p : qstate s x)
(q: qstate x e), 
(forall j, WF_Matrix (U j))->
@WF_Matrix (2^(e-x)) (2^(e-x)) q->
s<=s0/\s0<=e0 /\ e0<=s1/\s1<=e1/\e1<=x /\ x<=e->
@QUnit_Ctrl_fun s e  s0 e0 s1 e1 U (@kron (2^(x-s)) (2^(x-s)) (2^(e-x))
(2^(e-x)) p q) =
@kron  (2^(x-s)) (2^(x-s)) (2^(e-x))
(2^(e-x)) (QUnit_Ctrl_fun s0 e0 s1 e1 U p) q.
Proof. unfold QUnit_Ctrl_fun.  intros. unfold q_update.
rewrite (@big_sum_eq_bounded (Matrix (2^(e-s)) (2^(e-s))) _ _ 
((fun i:nat=>(I (2^(s0-s)))  ⊗ ((∣ i ⟩_ (2^(e0 - s0)) × ⟨ i ∣_ (2^(e0 - s0))) ⊗ I (2 ^ (s1 - e0)) ⊗ U i) ⊗ (I (2^(e-e1))) ) )) at 1.
rewrite <-kron_Msum_distr_r. 
rewrite <-kron_Msum_distr_l. 
 assert(2^(e1-s0)= 2 ^ (e0 - s0) * 2 ^ (s1 - e0) * 2 ^ (e1 - s1)).
 type_sovle'. destruct H2.  
rewrite (@super_kron_r s e s0 e1 x ); try lia; try auto_wf.
f_equal. f_equal. 
rewrite kron_Msum_distr_l. 
rewrite kron_Msum_distr_r. apply  big_sum_eq_bounded.
intros.
apply Logic.eq_trans with 
(I (2 ^ (s0 - s)) ⊗ (∣ x0 ⟩_ (2^(e0 - s0)) × ⟨ x0 ∣_ (2^(e0 - s0))) ⊗ I (2 ^ (s1 - e0)) ⊗ I (2 ^ (e1- s1)) ⊗ I (2 ^ (x - e1))
× (I (2 ^ (s0 - s)) ⊗ I (2 ^ (e0 - s0)) ⊗I (2 ^ (s1 - e0)) ⊗ U x0 ⊗ I (2 ^ (x - e1)))).
repeat rewrite kron_mixed_product. repeat rewrite Mmult_1_r; auto_wf.
rewrite Mmult_1_l; auto_wf. f_equal; type_sovle'.  repeat rewrite kron_assoc; auto_wf.
f_equal; type_sovle'. repeat rewrite id_kron. repeat rewrite kron_assoc; auto_wf.
repeat rewrite id_kron; auto_wf. f_equal; type_sovle'. f_equal; type_sovle'.
f_equal; type_sovle'. f_equal; type_sovle'. f_equal; type_sovle'.
f_equal; type_sovle'. 
intros.
apply Logic.eq_trans with 
(I (2 ^ (s0 - s)) ⊗ (∣ x0 ⟩_ (2^(e0 - s0)) × ⟨ x0 ∣_ (2^(e0 - s0))) ⊗ I (2 ^ (s1 - e0)) ⊗ I (2 ^ (e1- s1)) ⊗ I (2 ^ (e - e1))
× (I (2 ^ (s0 - s)) ⊗ I (2 ^ (e0 - s0)) ⊗I (2 ^ (s1 - e0)) ⊗ U x0 ⊗ I (2 ^ (e - e1)))).
repeat rewrite id_kron. repeat rewrite kron_assoc; auto_wf.
repeat rewrite id_kron; auto_wf. f_equal; type_sovle'. f_equal; type_sovle'.
f_equal; type_sovle'. f_equal; type_sovle'. f_equal; type_sovle'.
f_equal; type_sovle'. 
repeat rewrite kron_mixed_product. repeat rewrite Mmult_1_r; auto_wf.
rewrite Mmult_1_l; auto_wf. f_equal; type_sovle'.  repeat rewrite kron_assoc; auto_wf.
f_equal; type_sovle'. 
Qed.

Lemma QUnit_Ctrl_fun_kron_l{s x e:nat}: forall s0 e0 s1 e1 (U:nat-> Square (2^(e1-s1))) (p : qstate s x)
(q: qstate x e), 
(forall j, WF_Matrix (U j))->
@WF_Matrix (2^(x-s)) (2^(x-s)) p->
s<=x/\x<=s0 /\s0<=e0 /\ e0<=s1/\s1<=e1/\e1<=e->
@QUnit_Ctrl_fun s e  s0 e0 s1 e1 U (@kron (2^(x-s)) (2^(x-s)) (2^(e-x))
(2^(e-x)) p q) =
@kron  (2^(x-s)) (2^(x-s)) (2^(e-x))
(2^(e-x)) p (QUnit_Ctrl_fun s0 e0 s1 e1 U q).
Proof. unfold QUnit_Ctrl_fun.  intros. unfold q_update.
rewrite (@big_sum_eq_bounded (Matrix (2^(e-s)) (2^(e-s))) _ _ 
((fun i:nat=>(I (2^(s0-s)))  ⊗ ((∣ i ⟩_ (2^(e0 - s0)) × ⟨ i ∣_ (2^(e0 - s0))) ⊗ I (2 ^ (s1 - e0)) ⊗ U i) ⊗ (I (2^(e-e1))) ) )) at 1.
rewrite <-kron_Msum_distr_r. 
rewrite <-kron_Msum_distr_l. 
assert(2^(e1-s0)= 2 ^ (e0 - s0) * 2 ^ (s1 - e0) * 2 ^ (e1 - s1)).
type_sovle'. destruct H2.  
rewrite (@super_kron_l s e s0 e1 x ); try lia; try auto_wf.
f_equal. f_equal. 
rewrite kron_Msum_distr_l. 
rewrite kron_Msum_distr_r. apply  big_sum_eq_bounded.
intros.
apply Logic.eq_trans with 
(I (2 ^ (s0 - x)) ⊗ (∣ x0 ⟩_ (2^(e0 - s0)) × ⟨ x0 ∣_ (2^(e0 - s0))) ⊗ I (2 ^ (s1 - e0)) ⊗ I (2 ^ (e1- s1)) ⊗ I (2 ^ (e - e1))
× (I (2 ^ (s0 -x)) ⊗ I (2 ^ (e0 - s0)) ⊗I (2 ^ (s1 - e0)) ⊗ U x0 ⊗ I (2 ^ (e - e1)))).
repeat rewrite kron_mixed_product. repeat rewrite Mmult_1_r; auto_wf.
rewrite Mmult_1_l; auto_wf. f_equal; type_sovle'.  repeat rewrite kron_assoc; auto_wf.
f_equal; type_sovle'. repeat rewrite id_kron. repeat rewrite kron_assoc; auto_wf.
repeat rewrite id_kron; auto_wf. f_equal; type_sovle'. f_equal; type_sovle'.
f_equal; type_sovle'. f_equal; type_sovle'. f_equal; type_sovle'.
f_equal; type_sovle'. 
intros.
apply Logic.eq_trans with 
(I (2 ^ (s0 - s)) ⊗ (∣ x0 ⟩_ (2^(e0 - s0)) × ⟨ x0 ∣_ (2^(e0 - s0))) ⊗ I (2 ^ (s1 - e0)) ⊗ I (2 ^ (e1- s1)) ⊗ I (2 ^ (e - e1))
× (I (2 ^ (s0 - s)) ⊗ I (2 ^ (e0 - s0)) ⊗I (2 ^ (s1 - e0)) ⊗ U x0 ⊗ I (2 ^ (e - e1)))).
repeat rewrite id_kron. repeat rewrite kron_assoc; auto_wf.
repeat rewrite id_kron; auto_wf. f_equal; type_sovle'. f_equal; type_sovle'.
f_equal; type_sovle'. f_equal; type_sovle'. f_equal; type_sovle'.
f_equal; type_sovle'. 
repeat rewrite kron_mixed_product. repeat rewrite Mmult_1_r; auto_wf.
rewrite Mmult_1_l; auto_wf. f_equal; type_sovle'.  repeat rewrite kron_assoc; auto_wf.
f_equal; type_sovle'. 
Qed.

Lemma QUnit_Ctrl_unitary{s e:nat}: forall (s0 e0 s1 e1:nat) (U: nat -> Square (2^(e1-s1))) ,
s<=s0/\s0<=e0/\ e0<=s1->s1<=e1/\ e1<=e->
(forall i, WF_Unitary (U i))->
WF_Unitary (big_sum (fun i:nat =>@Mmult (2^(e-s)) (2^(e-s)) (2^(e-s))
                (I (2^(s0-s)) ⊗ (∣ i ⟩_ (2^(e0-s0)) × ⟨ i ∣_ (2^(e0-s0)) ) ⊗ (I (2^(e-e0)))) 
                 (I (2^(s1-s)) ⊗ (U i) ⊗ (I (2^(e-e1))))) (2^(e0-s0))).
Proof. intros. unfold WF_Unitary in *. split. 
      {  apply WF_Msum. intros. apply WF_mult. 
        auto_wf. apply WF_kron;   type_sovle'. apply WF_kron; try reflexivity; 
        try auto_wf. apply H1. auto_wf. }
      { rewrite Msum_adjoint.  rewrite Mmult_Msum_distr_l.
        rewrite (big_sum_eq_bounded _  
        (fun i : nat =>
        big_sum  (fun i0 : nat =>
        (I (2 ^ (s0-s)) ⊗ ((∣ i0 ⟩_ (2^(e0 - s0)) × ⟨ i0 ∣_ (2^(e0 - s0)))
                          × (∣ i ⟩_ (2^(e0 - s0)) × ⟨ i ∣_ (2^(e0 - s0))))
        ⊗ I (2 ^ (s1 - e0)) ⊗ (((U i0)†) × (U i)) ⊗ I (2 ^ (e - e1)) ) )
        (2 ^ (e0 - s0)))). 
        rewrite (big_sum_eq_bounded _  
        (fun i : nat =>
        (I (2 ^ (s0-s)) ⊗ (∣ i ⟩_ (2^(e0 - s0)) × ⟨ i ∣_ (2^(e0 - s0)))
        ⊗ I (2 ^ (s1 - e0)) ⊗ I (2 ^ (e1 - s1)) ⊗ I (2 ^ (e - e1)) )) ).
        repeat rewrite <-kron_Msum_distr_r. rewrite <-kron_Msum_distr_l. 
        rewrite big_sum_I. repeat rewrite id_kron; auto_wf. f_equal; type_sovle'.

        intros. 
        apply big_sum_unique. exists x.
        split.  assumption. 
        split.  f_equal. f_equal. f_equal.
        f_equal. rewrite Mmult_assoc. 
        rewrite <-(Mmult_assoc (⟨ x ∣_ (2^(e0 - s0)))).
        rewrite base_inner_1. unfold c_to_Vector1.
        Msimpl.  reflexivity.
        assumption. apply H1.
        intros. rewrite Mmult_assoc. 
        rewrite <-(Mmult_assoc (⟨ x' ∣_ (2^(e0 - s0)))).
        rewrite base_inner_0. unfold c_to_Vector1.
        Msimpl. reflexivity. 
        intuition. assumption. assumption.

        intros. rewrite Mmult_Msum_distr_r.  apply big_sum_eq_bounded.
        intros. 
        apply Logic.eq_trans with ((I (2 ^ (s0-s))
        ⊗ (∣ x0 ⟩_ (2^(e0 - s0)) × ⟨ x0 ∣_ (2^(e0 - s0)))
        ⊗ I (2^ (s1-e0)) ⊗ I (2^ (e1-s1)) ⊗ I (2 ^ (e - e1))
        × (I (2^ (s0-s)) ⊗ I (2^ (e0-s0)) ⊗ I (2 ^ (s1 - e0)) ⊗ U x0 ⊗ I (2 ^ (e - e1)))) †
        × (I (2 ^ (s0-s))
        ⊗ (∣ x ⟩_ (2^(e0 - s0)) × ⟨ x ∣_ (2^(e0 - s0)))
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
        apply WF_adjoint. apply H1. }
Qed.  


Lemma QMeas_fun_plus{s' e':nat}: forall s e  x (q q0: qstate s' e') , 
@Mplus (2^(e'-s')) (2^(e'-s')) (QMeas_fun s e x q0) (QMeas_fun s e x q)=
@QMeas_fun s' e' s e x (q0 .+ q).
Proof. unfold QMeas_fun.  intros. 
unfold q_update. rewrite super_plus.   reflexivity.
Qed.


Lemma QMeas_fun_scale{s' e':nat}: forall s e  x p (q: qstate s' e') , 
@scale (2^(e'-s')) (2^(e'-s')) p (QMeas_fun s e x q)=
@QMeas_fun s' e' s e x (p .*  q).
Proof. unfold QMeas_fun.  intros. 
unfold q_update. rewrite super_scale. 
reflexivity.
Qed.



Lemma QMeas_fun_kron_r{s0 x e0:nat}: forall s e i (p : qstate s0 x)
(q: qstate x e0), 
i<(2^(e-s))%nat->
@WF_Matrix (2^(e0-x)) (2^(e0-x)) q->
s0<=s/\s<=e/\e<=x/\x<=e0->
@QMeas_fun s0 e0 s e i (@kron (2^(x-s0)) (2^(x-s0)) (2^(e0-x))
(2^(e0-x)) p q) =
@kron  (2^(x-s0)) (2^(x-s0)) (2^(e0-x))
(2^(e0-x)) (QMeas_fun s e i p) q.
Proof. unfold QMeas_fun.  intros. unfold q_update.
apply super_kron_r; try assumption; auto_wf.
Qed.


Lemma QMeas_fun_kron_l{s0 x e0:nat}: forall s e i (p : qstate s0 x)
(q: qstate x e0), 
i<(2^(e-s))%nat->
@WF_Matrix (2^(x-s0)) (2^(x-s0)) p->
s0<=x/\ x<= s/\s<=e/\e<=e0->
@QMeas_fun s0 e0 s e i (@kron (2^(x-s0)) (2^(x-s0)) (2^(e0-x))
(2^(e0-x)) p q) =
@kron  (2^(x-s0)) (2^(x-s0)) (2^(e0-x))
(2^(e0-x))  p (QMeas_fun s e i q).
Proof. unfold QMeas_fun.  intros. unfold q_update.
apply super_kron_l; try assumption; auto_wf.
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
      trace ((I (2 ^ (s-s')) ⊗ (∣ x ⟩_ (2^(e - s)) × ⟨ x ∣_ (2^(e - s)))
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
      repeat  rewrite kron_mixed_product.  repeat rewrite Mmult_1_r; auto_wf.
      rewrite <-Mmult_assoc.  rewrite (Mmult_assoc _ (⟨ 0 ∣_ (2^(e - s))) _).
      rewrite base_inner_1. unfold c_to_Vector1. Msimpl.  reflexivity.
      apply pow_gt_0.
Qed.

Lemma trace_mult_Unitary{n:nat}: forall (A B:Square n) ,
 WF_Unitary A -> WF_Matrix B-> trace B=trace (A × B ×  A†).
Proof. intros. rewrite trace_mult. rewrite<-Mmult_assoc. 
destruct H. rewrite H1. rewrite Mmult_1_l. reflexivity.
assumption. 
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
Proof. intros.  unfold QUnit_Ctrl_fun. unfold q_update. unfold super. 
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
       apply map2_app_not_nil in H7. destruct H7.
       left.  
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
      rewrite H2. unfold q_trace. rewrite Zero_trace. rewrite Cmod_0.
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




Lemma WWF_qstate_super{s' e'}: forall (A:Square (2^(e'-s'))) (rho:qstate s' e') ,
super A rho <> Zero ->
WF_Matrix A->
WWF_qstate rho-> 
WWF_qstate (super A rho).
Proof. intros.
unfold WWF_qstate. 
split; try apply H1. apply nz_mixed_super_aux; try assumption; apply H1.  
Qed.

Lemma mixed_super_ge_0{s' e':nat}:forall (A:Square (2^(e'-s'))) (rho : qstate s' e'), 
WF_Matrix A->
@NZ_Mixed_State_aux (2^(e'-s')) rho ->
@Mixed_State_aux (2^(e'-s')) (super A rho).
Proof. intros. rewrite NZ_Mixed_State_aux_equiv'.
assert ((super A rho)= Zero \/ (super A rho) <> Zero).
apply Classical_Prop.classic. destruct H1.
right. assumption. left. 
apply nz_mixed_super_aux; try lia; auto_wf.   
assumption.  apply H1. 
Qed.

Lemma mixed_super_ge_0'{s' e':nat}:forall (A:Square (2^(e'-s'))) (rho : qstate s' e'), 
WF_Matrix A->
WWF_qstate rho ->
WWF_qstate  (super A rho)\/ (super A rho)= Zero.
Proof. intros. 
assert ((super A rho)= Zero \/ (super A rho) <> Zero).
apply Classical_Prop.classic. destruct H1.
right. assumption. left. apply WWF_qstate_super; try assumption.
Qed.


Lemma  QMeas_trace{s' e':nat}:  forall (s e i j:nat) sigma (rho: qstate s' e') mu,
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
        (c_update i j sigma,  QMeas_fun s e j rho)) ); try assumption.

        simpl. unfold s_trace. simpl.  
        rewrite (big_sum_eq_bounded _  (fun i0 : nat =>
        (Cmod (@trace (2 ^ (e'-s'))   ((q_update  (I (2 ^ (s - s'))
        ⊗ (∣ i0 ⟩_ (2^(e - s)) × ⟨ i0 ∣_ (2^(e - s))) ⊗ I (2 ^ (e' - e))) rho))))));
        try reflexivity.

        rewrite <-big_sum_Cmod. f_equal.  rewrite big_sum_trace.
        rewrite (big_sum_eq_bounded _ (fun x : nat =>
        trace (I (2 ^ (s-s')) ⊗ (∣ x ⟩_ (2^(e - s)) × ⟨ x ∣_ (2^(e - s))) ⊗ I (2 ^ (e' - e))
        × rho)) _ ).
        
        rewrite <-big_sum_trace.  rewrite <-Mmult_Msum_distr_r.
        rewrite <-kron_Msum_distr_r .  rewrite <-kron_Msum_distr_l.
        rewrite big_sum_I. rewrite id_kron. rewrite id_kron.
        rewrite Mmult_1_l.
        assert((2 ^ (e'-s'))= 2 ^ (s-s') * 2 ^ (e - s) * 2 ^ (e' - e)%nat).
        type_sovle'. destruct H2.  
        unfold q_trace. reflexivity. 
         apply WF_Mixed_aux.
        unfold WWF_qstate in H0. assert(2 ^ (s-s') * 2 ^ (e - s) * 2 ^ (e' - e) = (2 ^ (e'-s'))%nat).
        type_sovle'. destruct H2. 
        apply NZ_Mixed_State_aux_is_Mixed_State_aux. apply H0.

        unfold q_update.  unfold super.
        intros.  rewrite trace_mult. 
        assert(  (2 ^ (s-s') * 2 ^ (e - s) * 2 ^ (e' - e))%nat= (2 ^ (e'-s'))%nat).
        type_sovle'. destruct H3. 
        repeat rewrite kron_adjoint. repeat rewrite id_adjoint_eq.
        rewrite Mmult_adjoint. rewrite adjoint_involutive.
        rewrite <-Mmult_assoc. 
        repeat  rewrite kron_mixed_product.  repeat rewrite Mmult_1_r; auto_wf.
        rewrite <-Mmult_assoc.  rewrite (Mmult_assoc _ (⟨ x ∣_ (2^(e - s))) _).
        rewrite base_inner_1. unfold c_to_Vector1.  Msimpl. reflexivity.
        assumption.
        
        unfold q_update.
        intros. apply (@mixed_super_ge_0 s' e'); try assumption; auto_wf.
        apply H0.
        
        intros. 
        apply (@mixed_super_ge_0' s' e'); try assumption; auto_wf.
Qed.



Lemma QInit_fun_sum{s' e':nat}: forall n s e (q: nat-> qstate s' e'), 
QInit_fun s e (@big_sum (Matrix (2^(e'-s')) (2^(e'-s'))) _ q n) =
@big_sum  (Matrix (2^(e'-s')) (2^(e'-s'))) _ (fun i => QInit_fun s e (q i)) n .
Proof. 
  induction n;  intros; unfold q_update; unfold qstate.
simpl. rewrite QInit_Zero. reflexivity.    
simpl.  rewrite <-IHn.
rewrite <-QInit_fun_plus. f_equal.
Qed.


Lemma QUnit_One_fun_sum{s' e':nat}: forall n s e U (q: nat-> qstate s' e'), 
QUnit_One_fun s e U (big_sum q n) =
big_sum (fun i => QUnit_One_fun s e U (q i)) n .
Proof. intros. unfold QUnit_One_fun. unfold q_update.
rewrite <-(@super_sum (2 ^ (e' - s'))). reflexivity.
Qed.  




Lemma QUnit_Ctrl_fun_sum{s' e':nat}: forall n s0 e0 s1 e1 U (q: nat-> qstate s' e'), 
QUnit_Ctrl_fun s0 e0 s1 e1  U (big_sum q n) =
big_sum (fun i => QUnit_Ctrl_fun s0 e0 s1 e1  U (q i)) n .
Proof. intros. unfold QUnit_Ctrl_fun. unfold q_update.
rewrite <-(@super_sum (2 ^ (e' - s'))). reflexivity.
Qed.

Lemma QMeas_fun_sum{s' e':nat}: forall n s e j (q: nat-> qstate s' e'), 
QMeas_fun s e j (big_sum q n) =
big_sum (fun i => QMeas_fun s e j (q i)) n .
Proof. intros.  unfold QMeas_fun . unfold q_update.
rewrite <-(@super_sum (2 ^ (e' - s'))). reflexivity.
Qed.

(*-------------------------------ceval---------------------------------*)

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



Local Open Scope bool_scope.
Lemma state_eq_aexp{s0 e0 s1 e1 :nat}: forall (st :state s0 e0 )  (st':state s1 e1) (a:aexp),
(fst st) = (fst st')-> (aeval st a) = aeval st' a.
Proof. intros. induction a;  simpl; try (rewrite IHa1; rewrite IHa2);
try rewrite IHa3; try reflexivity.
      rewrite H. reflexivity.
Qed.

Lemma state_eq_bexp{ s0 e0 s1 e1:nat}: forall (st:state s0 e0) (st' : state s1 e1) (b:bexp),
(fst st) = (fst st')-> (beval st b) = beval st' b.
Proof. intros. induction b; simpl;
        try  rewrite (state_eq_aexp  st st' a1); try rewrite (state_eq_aexp st st' a2);
        try assumption;
       try rewrite IHb; try (rewrite IHb1; rewrite IHb2);  try reflexivity.
Qed.


Require Import Coq.Arith.PeanoNat.
Local Open Scope nat_scope.
Lemma pred_sub_1:forall n:nat, pred n=n-1 .
Proof. lia.
Qed.

Lemma S_add_1:forall n:nat, S n=n+1 .
Proof. lia.
Qed.

Lemma WWF_qstate_init{s' e'}: forall s e (rho:qstate s' e'),
s'<=s/\s<=e/\ e<=e'-> 
WWF_qstate rho-> 
WWF_qstate (QInit_fun s e rho).
Proof. intros. unfold QInit_fun.  split.   
       apply (@nz_Mixed_State_aux_big_sum (e'-s')). apply Nat.pow_nonzero. lia.
       intros. unfold q_update. apply mixed_super_ge_0.
       apply WF_kron; type_sovle'; auto_wf. apply WF_kron; type_sovle'; try auto_wf.
       apply WF_mult; auto_wf. apply WF_base. apply pow_gt_0.
       apply H0. apply big_sum_not_0. 
       intro. 
    
destruct H0. pose H0. apply nz_mixed_state_trace_gt0_aux  in n.
rewrite <-(@QInit_trace s' e' s e) in n; try lia;auto_wf.

    remember ((fun i : nat => q_update (I (2 ^ (s - s'))
       ⊗ (∣ 0 ⟩_ (2^(e - s))
          × ⟨ i ∣_ (2^(e - s)))
       ⊗ I (2 ^ (e' - e))) rho)).
    assert ((@big_sum
    (Matrix (Nat.pow (S (S O)) (Init.Nat.sub e' s'))
       (Nat.pow (S (S O)) (Init.Nat.sub e' s')))
    (M_is_monoid (Nat.pow (S (S O)) (Init.Nat.sub e' s'))
       (Nat.pow (S (S O)) (Init.Nat.sub e' s')))
    q (2 ^ (e - s)) )=QInit_fun s e rho). rewrite Heqq.
    unfold QInit_fun. reflexivity.
    rewrite H3 in H1. rewrite H1 in n.
    rewrite Zero_trace in n. unfold RtoC in *. simpl in *.
   lra. lia. 
Qed.


Lemma WF_qstate_init{s' e'}: forall s e (rho:qstate s' e'),
s'<=s/\s<=e/\ e<=e'-> 
WF_qstate rho-> 
WF_qstate (QInit_fun s e rho).
Proof. intros. 
rewrite  WWF_qstate_to_WF_qstate in *. 
split. apply WWF_qstate_init. lia.  apply H0.
unfold q_trace.
 rewrite QInit_trace. intuition. lia. destruct H0. destruct H0. auto_wf.
Qed. 


Lemma WWF_qstate_QUnit_One{s' e'}: forall s e (rho:qstate s' e') (U:Square (2^(e-s))),
s'<=s/\s<=e/\ e<=e'-> 
WF_Unitary U->
WWF_qstate rho-> 
WWF_qstate (QUnit_One_fun s e U rho).
Proof. intros.
unfold WWF_qstate. split.  
 apply nz_mixed_unitary_aux.  
 assert( (2 ^ (s-s') * 2 ^ (e - s) * 2 ^ (e' - e))%nat = (2^ (e'-s')) ) .
type_sovle'. destruct H2.
 apply kron_unitary. apply kron_unitary. apply id_unitary. 
 assumption. apply id_unitary. apply H1. lia. 
Qed.


Lemma WF_qstate_QUnit_One{s' e'}: forall s e (rho:qstate s' e') (U:Square (2^(e-s))),
s'<=s/\s<=e/\ e<=e'-> 
WF_Unitary U->
WF_qstate rho-> 
WF_qstate (QUnit_One_fun s e U rho).
Proof. 
intros. 
rewrite WWF_qstate_to_WF_qstate in *. 
split. apply WWF_qstate_QUnit_One; try lia. intuition. apply H1.
unfold q_trace.  
 rewrite QUnit_One_trace. intuition. lia. 
 apply WF_NZ_Mixed_aux. apply H1. assumption. 
Qed.

Lemma WWF_qstate_QUnit_Ctrl{s' e'}: forall s0 e0 s1 e1  (rho:qstate s' e') (U:nat ->Square (2^(e1-s1))),
s'<=s0/\s0<=e0/\ e0<=s1/\ s1<=e1 /\ e1<= e'-> 
(forall j, WF_Unitary (U j))->
WWF_qstate rho-> 
WWF_qstate (QUnit_Ctrl_fun s0 e0 s1 e1 U rho).
Proof. intros. 
unfold WWF_qstate. split; try apply H1.  
 apply nz_mixed_unitary_aux. 
 apply QUnit_Ctrl_unitary. intuition.
 intuition.   assumption. apply H1.
Qed.


Lemma WF_qstate_QUnit_Ctrl{s' e'}: forall s0 e0 s1 e1  (rho:qstate s' e') (U:nat ->Square (2^(e1-s1))),
s'<=s0/\s0<=e0/\ e0<=s1/\ s1<=e1 /\ e1<= e'-> 
(forall j, WF_Unitary (U j))->
WF_qstate rho-> 
WF_qstate (QUnit_Ctrl_fun s0 e0 s1 e1 U rho).
Proof. 
intros. 
rewrite WWF_qstate_to_WF_qstate in *. 
split.  apply WWF_qstate_QUnit_Ctrl. lia. intuition.
apply H1. unfold q_trace. 
 rewrite QUnit_Ctrl_trace. intuition. lia. lia.  
 apply WF_NZ_Mixed_aux. apply H1. assumption.
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


Lemma Cmod_fst_eq{n:nat}:forall (q:Square (2^n)),
Mixed_State_aux q->
Cmod (trace q)= fst (trace q).
Proof. intros. rewrite NZ_Mixed_State_aux_equiv' in H. destruct H. apply Cmod_snd_0.
       apply nz_mixed_state_trace_gt0_aux. assumption.
       apply nz_mixed_state_trace_real_aux. assumption.
       rewrite H. rewrite Zero_trace.
       simpl. rewrite Cmod_0. reflexivity.
  
Qed.

Lemma big_sum_fst : forall f n,
  fst (big_sum f n) = big_sum (fun i => fst (f i)) n.
Proof. induction n as [| n'].
       - simpl. reflexivity.
       - simpl. f_equal.  auto.
Qed.

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

Lemma WWF_qstate_QMeas{s' e'}: forall s e (rho:qstate s' e') j,
s'<=s/\s<=e/\ e<=e'-> 
QMeas_fun s e j rho <> Zero ->
(j<2^(e-s))->
WWF_qstate rho-> 
WWF_qstate (QMeas_fun s e j rho).
Proof. intros.
unfold WWF_qstate. unfold QMeas_fun in *. unfold q_update in *.
split. apply nz_mixed_super_aux; try assumption; auto_wf.   apply H2. lia.  
Qed.


Lemma  QMeas_le{s' e'}: forall s e (rho:qstate s' e') c (i:nat) j (x:list (cstate * qstate s' e')),
s'<=s/\s<=e/\ e<=e'-> 
WWF_qstate rho->
(j<2^(e-s))->
big_app' (fun j0 : nat =>
        (c_update i j0 c, QMeas_fun s e j0 rho))
       (2 ^ (e - s)) x ->
(q_trace (QMeas_fun s e j rho) <= d_trace_aux x)%R.
Proof. intros. 
rewrite (big_app'_trace ((2 ^ (e - s))) (fun j0 : nat =>
(c_update i j0 c, QMeas_fun s e j0 rho)) x); try assumption.
unfold s_trace. simpl.  unfold q_trace.
rewrite Cmod_fst_eq; auto.  
rewrite (big_sum_eq_bounded _ (fun i0 : nat =>
fst (@trace (2^(e'-s'))  (QMeas_fun s e i0 rho)))). 
apply (big_sum_member_le_bound ((fun i0 : nat =>
fst (trace (QMeas_fun s e i0 rho))) )); try lia. 
intros. rewrite <-Cmod_fst_eq; auto. apply Cmod_ge_0.
apply (@mixed_super_ge_0 s' e'); try lia; auto_wf. apply H0.
intros.  rewrite Cmod_fst_eq; auto.
apply (@mixed_super_ge_0 s' e'); try lia; auto_wf. apply H0.
apply (@mixed_super_ge_0 s' e'); try lia; auto_wf. apply H0.
intros.
apply (@mixed_super_ge_0' s' e'); try lia; auto_wf. apply H0. 
  
Qed.


Lemma WF_qstate_QMeas{s' e'}: forall s e (rho:qstate s' e') (c:cstate) (i:nat) j,
s'<=s/\s<=e/\ e<=e'-> 
QMeas_fun s e j rho <> Zero ->
(j<2^(e-s))->
WF_qstate rho-> 
WF_qstate (QMeas_fun s e j rho).
Proof. 
intros.  
rewrite WWF_qstate_to_WF_qstate in *. 
split. apply WWF_qstate_QMeas; try assumption. 
apply H2.
pose (big_app'_exsist  (2 ^ (e - s)) (fun j0 : nat => (c_update i j0 c, QMeas_fun s e j0 rho))).
destruct e0. 
apply Rle_trans with (d_trace_aux x). 
apply QMeas_le with c i; try lia; try assumption; apply H2.
rewrite (QMeas_trace s e i j c rho);
try lia; try assumption; apply H2.
Qed.

Lemma WF_qstate_QMeas_app{s' e'}: forall s e (rho:qstate s' e') (c:cstate) (i:nat) n mu,
s'<=s/\s<=e/\ e<=e'-> 
(n<=2^(e-s))->
WF_qstate rho-> 
(big_app' (fun j0 : nat => (c_update i j0 c, QMeas_fun s e j0 rho))
n mu)->
WF_dstate_aux mu.
Proof. intros. apply WWF_dstate_aux_to_WF_dstate_aux.
split.  

apply WWF_dstate_big_app' with n
(fun j0 : nat =>  (c_update i j0 c, QMeas_fun s e j0 rho));
try assumption.
intros. assert (i0<(2^(e-s))). lia. 
apply (@mixed_super_ge_0' s' e'); try lia; auto_wf. 
apply WWF_qstate_to_WF_qstate; try assumption.

pose (big_app'_exsist  (2 ^ (e - s)) (fun j0 : nat => (c_update i j0 c, QMeas_fun s e j0 rho))).
destruct e0.
apply Rle_trans with (d_trace_aux x).
rewrite (big_app'_trace n (fun j0 : nat =>
(c_update i j0 c, QMeas_fun s e j0 rho))); try assumption.
rewrite (big_app'_trace ((2 ^ (e - s)) ) (fun j0 : nat =>
(c_update i j0 c, QMeas_fun s e j0 rho))); try assumption.
unfold s_trace. simpl.
apply big_sum_le; auto. intros. apply Cmod_ge_0.  
intros.
apply (@mixed_super_ge_0' s' e'); try lia; auto_wf;
try apply WWF_qstate_to_WF_qstate; try assumption.
intros. assert (i0<(2^(e-s))). lia. 
apply (@mixed_super_ge_0' s' e'); try lia; auto_wf;
try apply WWF_qstate_to_WF_qstate; try assumption.
rewrite (QMeas_trace s e i n c rho) ; try lia; try 
try apply WWF_qstate_to_WF_qstate; try assumption.
Qed.


Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Arith.Peano_dec.

Ltac WWF_ceval_solve s e mu :=
  induction mu; intros; try match goal with 
H: ceval_single ?a ?b ?c |- _ => inversion H; subst end;
[try apply WF_nil' | try apply WWF_d_app_aux; try econstructor;try apply (@WF_nil' s e)];
try match goal with 
H0: WWF_dstate_aux (?a :: ?b) |- _ => inversion_clear H0 end;
try  match goal with 
H: existT ?a ?b ?c = existT ?x ?y ?z|-_ => apply inj_pair2_eq_dec in H end;
try  match goal with 
H: existT ?a ?b ?c = existT ?x ?y ?z|-_ => apply inj_pair2_eq_dec in H; destruct H end;
try apply Nat.eq_dec;
[unfold WWF_state in *; simpl snd in  *;
try apply WWF_qstate_init; try apply WWF_qstate_QUnit_One;
try apply WWF_qstate_QUnit_Ctrl; try assumption; 
try match goal with 
H': big_app' ?f ?n ?mu'' |- _ => apply (WWF_dstate_big_app') in H' end;
try intros; try apply mixed_super_ge_0'; auto_wf; 
try lia| try match goal with 
IHmu: _ |- _ => apply IHmu end ]; try assumption.


Lemma WF_ceval'{s e:nat} : forall c (mu mu':list (cstate *qstate s e)), 
WWF_dstate_aux mu->
ceval_single c mu mu'->
WWF_dstate_aux mu'. 
Proof. induction c; try WWF_ceval_solve s e mu. 
--intros. inversion H0; subst. assumption.
   apply IHc2 with mu1.
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
Qed. 



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

Ltac d_trace_app_solve:= 
      rewrite d_trace_app_aux; 
      try match goal with 
      H: WWF_dstate_aux ((?sigma, ?rho) :: ?mu) |- _ => inversion_clear H end;
      [|  try match goal with 
      H: WWF_state (?a,?b),
      H': ceval_single ?c ?d ?f |- _  =>
      try apply WF_ceval' with  c  [(a, b)] ; try apply WF_state_dstate_aux;
      try econstructor; try assumption; try apply ceval_Qinit; try apply ceval_QUnit_One;
      try apply ceval_QUnit_Ctrl; try apply ceval_QMeas;
      try lia; try assumption; try econstructor end|
      try match goal with 
      H: ceval_single ?c ?d ?f |- _ => apply WF_ceval' in H; try assumption end].

Ltac ceval_trace_sovle mu :=induction mu; intros;
try match goal with 
H: ceval_single ?a ?b ?c |- _ => inversion H; subst; clear H end; try reflexivity; 
try  match goal with 
H: existT ?a ?b ?c = existT ?x ?y ?z|-_ => apply inj_pair2_eq_dec in H end;
try  match goal with 
H: existT ?a ?b ?c = existT ?x ?y ?z|-_ => apply inj_pair2_eq_dec in H; destruct H end;
try apply Nat.eq_dec;
      
      d_trace_app_solve; simpl; try rewrite Rplus_0_r; unfold s_trace; unfold q_trace;
       simpl; f_equal; try match goal with IHmu:_ |- _ => eapply IHmu end; try assumption .


Local Open Scope com_scope.
Lemma ceval_trace_Qinit{s' e'}: forall  (mu mu':list (cstate * qstate s' e')) s e,
WWF_dstate_aux mu->
ceval_single (QInit s e) mu mu'-> (d_trace_aux mu = d_trace_aux mu').
Proof.  ceval_trace_sovle mu. 
       try rewrite QInit_trace; try lia; try apply WF_NZ_Mixed_aux; try apply H0; try reflexivity.
       apply H7.
Qed.


Lemma ceval_trace_QUnit_one{s' e'}: forall  (mu mu':list (cstate * qstate s' e')) s e (U: Square (2 ^ (e - s))),
WWF_dstate_aux mu->
ceval_single (QUnit_One s e U) mu mu'-> (d_trace_aux mu = d_trace_aux mu').
Proof. ceval_trace_sovle mu.   
  rewrite QUnit_One_trace; try lia; try apply WF_NZ_Mixed_aux; try apply H0; try assumption.
f_equal.  apply H9.
Qed.


Lemma ceval_trace_QUnit_ctrl{s' e'}: forall (mu mu':list (cstate * qstate s' e')) s0 e0  s1 e1 (U: nat-> Square (2 ^ (e1 - s1))),
WWF_dstate_aux mu->
ceval_single (QUnit_Ctrl s0 e0 s1 e1 U) mu mu'-> (d_trace_aux mu = d_trace_aux mu').
Proof. 
ceval_trace_sovle mu. 
rewrite QUnit_Ctrl_trace; try lia; try apply WF_NZ_Mixed_aux; try apply H0; try assumption.
f_equal.  apply H11. 
Qed.


Lemma ceval_trace_QMeas{s' e'}: forall  (mu mu':list (cstate * qstate s' e')) s e i,
WWF_dstate_aux mu->
ceval_single <{ i :=M [[s e]] }> mu mu'-> (d_trace_aux mu = d_trace_aux mu').
Proof.  
ceval_trace_sovle mu.
symmetry.
eapply (@QMeas_trace s' e' s e i); try lia; try assumption; apply H9.  
apply H8.
Qed.


Lemma ceval_trace_eq{s' e'}: forall c  (mu mu':list (cstate * qstate s' e')),
WWF_dstate_aux mu->
ceval_single c mu mu'-> ((d_trace_aux mu' = d_trace_aux mu)%R).
Proof. induction c. 
--intros. apply ceval_skip_1 in H0. rewrite <- H0. intuition.
-- intros. rewrite <-(ceval_trace_assgn mu _ i a). lra. assumption. assumption.
--intros. inversion_clear H0; try reflexivity. 
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
Qed.


Lemma ceval_trace_eq': forall c s e  (mu mu':dstate s e),
WWF_dstate mu->
ceval c mu mu'-> ((d_trace mu' = d_trace mu)%R).
Proof. intros  c s e(mu,IHmu) (mu', IHmu').
   unfold WWF_dstate.  simpl. intros. inversion_clear H0. 
   unfold d_trace. 
   simpl in *.  apply ceval_trace_eq with c. assumption.
   assumption.
Qed.


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

Ltac ceval_sorted_sovle mu IHmu Hm:= 
  induction mu; intros; inversion H;subst; try assumption;
  inversion_clear Hm;  
  try  match goal with 
H: existT ?a ?b ?c = existT ?x ?y ?z|-_ => apply inj_pair2_eq_dec in H end;
try  match goal with 
H: existT ?a ?b ?c = existT ?x ?y ?z|-_ => apply inj_pair2_eq_dec in H; destruct H end;
try apply Nat.eq_dec;
  try apply StateMap.Raw.map2_sorted; 
  [try match goal with 
  H:big_app' ?f ?n ?mu |- _ => apply big_app'_sorted with f n; try assumption end;
  try apply Sorted_cons; 
  try apply Sorted_nil;  try  apply HdRel_nil| try apply IHmu; try assumption].

Lemma ceval_sorted{ s e:nat}: forall c (mu mu':list (cstate *qstate s e)) 
 (Hm: Sorted (StateMap.Raw.PX.ltk (elt:=qstate s e)) mu)
(H:ceval_single c mu mu'),
Sorted (StateMap.Raw.PX.ltk (elt:=qstate s e)) mu'.
Proof. 
induction c; try ceval_sorted_sovle mu IHmu Hm.
-intros. inversion H;subst. intuition. intuition.
-intros. inversion H;subst. intuition. intuition.
-intros; inversion H;subst; try assumption. 
apply IHc2 with mu1; try assumption. 
apply IHc1 with ((sigma, rho) :: mu0); try assumption. 
-induction mu; intros; inversion H;subst; try assumption;
inversion_clear Hm.  
apply StateMap.Raw.map2_sorted.  
apply IHc1 with [(sigma, rho)]; try assumption. 
apply Sorted_cons. 
apply Sorted_nil.  apply HdRel_nil. intuition.
apply StateMap.Raw.map2_sorted.  
apply IHc2 with [(sigma, rho)]. 
apply Sorted_cons. 
apply Sorted_nil.  apply HdRel_nil. intuition.
apply IHmu; try assumption.
- intros. remember <{while b do c end}> as original_command eqn:Horig. 
induction H;  try inversion Horig; subst. apply Sorted_nil.
apply StateMap.Raw.map2_sorted. apply IHceval_single3.
apply IHc with [(sigma, rho)].  apply Sorted_cons. 
apply Sorted_nil.  apply HdRel_nil. assumption. reflexivity. 
apply IHceval_single1. inversion_clear Hm. intuition. reflexivity.
 apply StateMap.Raw.map2_sorted. apply Sorted_cons. 
 apply Sorted_nil.  apply HdRel_nil. apply IHceval_single. 
 inversion Hm. subst. intuition. intuition.
Qed.