From Quan Require Import QState_L.
From Quan Require Import QIMP_L.

(* We focus on the divergent program (CWhile BTrue CSkip) *)

(* The initial list of states has to be non-empty *)
Remark ceval_nil : forall n m, @ceval_single n m (CWhile BTrue CSkip) nil nil.
Proof.
  intros; apply E_nil; cbn.
  - constructor.
  - intros elt absurd. inversion absurd.
Qed.

Require Import Lists.List.

Definition non_empty_list {A} (l : list A) :=
  match l with _ :: _ => IDProp | _ => False end.

Definition keepBTrue b :=
  match b with
  | BTrue => IDProp -> False
  | _ => IDProp
  end.

Lemma discr_BTrue {s e} {st : state s e} :  beval st BTrue = false -> keepBTrue BTrue.
Proof. discriminate. Qed.

Lemma no_final_state_for_while_true_skip_core :
  forall {s' e'} {st st' : list (state s' e')},
    ceval_single (CWhile BTrue CSkip) st st' -> non_empty_list st -> False.
Proof.
  intros s' e'.
  fix loop 3.
  intros * ev.
  refine match ev with
         | E_nil (CWhile BTrue CSkip) wf subs => fun Fa : non_empty_list nil  => Fa
         | E_While_true sigma rho mu mu' m'' mu1 cSkip b etr ev' evc evw => _
         | E_While_false sigma rho mu mu' CSkip b efa ev' =>
             match b as bb return _ -> keepBTrue bb 
             with
             | BTrue => discr_BTrue
             | _ => fun _ => idProp
             end efa
         | E_While_false sigma rho mu mu' _ b efa ev' => match b with BTrue => idProp end
         end.
  - destruct b; try exact idProp.
    destruct cSkip; try exact idProp.
    intros _.
    apply (loop _ _ evw).
    refine match evc with
           | E_Skip sigma' rho' mu' => _
           | E_nil CSkip wf subs => idProp
           end. 
    destruct mu'; exact idProp.
Qed.

Corollary no_final_state_for_while_true_skip :
  forall {s' e'} (st : list (state s' e')), non_empty_list st ->
  (exists st', ceval_single (CWhile BTrue CSkip) st st') -> False.
Proof.
  intros s' e' st nemp [st' ev].
  exact (no_final_state_for_while_true_skip_core ev nemp).
Qed.

(* JFM -> Huilin: please provide any initial state with suitable dimensions *)

(* TODO: replace the following parameter by a definition *)
Parameter some_initial_state : state 0 0.

Theorem claim_false :
  (forall c (st : list (state 0 0)), exists st', ceval_single c st st') -> False.
Proof.
  intro claim. specialize (claim (CWhile BTrue CSkip)).
  apply (no_final_state_for_while_true_skip (some_initial_state :: nil) idProp).
  apply claim.
Qed.
    
