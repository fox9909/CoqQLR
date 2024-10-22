Local Open Scope nat_scope.    

Parameter t:nat.
Parameter L:nat.
Parameter U_plus:Square (2^L).
Parameter U: Square (2^L).
Parameter f: R-> nat.
Parameter QFT: Matrix (2^t) (2^t).

Hypothesis HQFT:    WF_Unitary QFT /\ forall k:nat, QFT × (Vec (2 ^ t) k) =
1 / √ (2 ^ t) .* (big_sum (fun j : nat => (cos (((2 * PI)/(2^t)) * j * k),  sin (((2 * PI)/(2^t)) * j * k)) .*  Vec (2 ^ t) j) (2 ^ t)).
Hypothesis HU_plus: WF_Unitary U_plus /\ ( U_plus × (Vec (2^L) 0) = (Vec (2^L) 1) ).


Definition  U_f (i:nat):= exp_U U i.
(* Definition  Us (s:nat):= 1 / √ r .* (big_sum (fun k:nat=> (cos (- ((2 * PI)/r) * s * k),  sin (- ((2 * PI)/(r)) * s * k)) .*  Vec (2 ^ L) (x ^ k mod N)) (r) ) . *)
Definition z:nat := 0.
Definition b:nat := 1.
Definition z':nat:=2 .



(* Definition b' :=(Nat.modulo (Nat.pow x z) N) .

Definition  P (s:nat): Pure_formula := (BEq z' (s/r * 2^t)) . *)


Definition OF (x:nat) (N:nat) :=
   let r:= ord x N in
   let b':=(Nat.modulo (Nat.pow x z) N) in
    <{ z := 1 ;
       b := b' ;
       while  b<>1  do 
       QInit 0 t;
       QInit t (t+L);
       QUnit_One 0 t (kron_n t hadamard);
       QUnit_One t (t+L) (U_plus);
       QUnit_Ctrl 0 t t (t+L) U_f;
       QUnit_One 0 t (adjoint QFT);
       QMeas z' 0 t;
       z := f (z'/2^t);
       b := b'
       end }>. 


Lemma HU_s: forall  (r x N:nat), 
ord x N =r->
let Us (s:nat) := 1 / √ r .* (big_sum (fun k:nat=> (cos (- ((2 * PI)/r) * s * k),  sin (- ((2 * PI)/(r)) * s * k)) .*  Vec (2 ^ L) (x ^ k mod N)) (r)) in 
 1 / √ r .*  (big_sum (fun s:nat=> Us s) (r) ) =(Vec (2^L) 1).
Proof. Admitted.

Lemma  simpl_H_Uplus: forall (r x N:nat),
ord x N =r->
let Us (s:nat) := 1 / √ r .* (big_sum (fun k:nat=> (cos (- ((2 * PI)/r) * s * k),  sin (- ((2 * PI)/(r)) * s * k)) .*  Vec (2 ^ L) (x ^ k mod N)) (r)) in 
C1 / √ 2 ^ t
    .* big_sum (fun z0 : nat => ∣ z0 ⟩_ (t)) (2 ^ t)
    ⊗ ∣ 1 ⟩_ (L)=
    1 / √ (r *2^t) .*  (big_sum (fun s:nat=>(big_sum (fun j=>(Vec (2^t) j)) (2^t)) ⊗ (Us s)) (r) ).
Proof. intros.  rewrite<- HU_s with r x N.  
   rewrite Mscale_kron_dist_l.
   rewrite Mscale_kron_dist_r.
   rewrite Mscale_assoc.
   f_equal.
    
Set Printing Coercions.
rewrite RtoC_pow. repeat rewrite <-RtoC_div.
rewrite RtoC_mult. f_equal. 
 rewrite Rmult_div. rewrite Rmult_1_l.
 f_equal.  admit.  admit. admit. admit. admit. admit.
  
   rewrite kron_Msum_distr_l.
   apply big_sum_eq_bounded.
   intros. reflexivity. apply H. 
Admitted.


Lemma simpl_expU:forall r x N j s ,
ord x N =r-> 
 (WF_Unitary U /\ (forall j:nat, j< N -> U × (Vec (2 ^ L) j) = (Vec (2 ^ t) (x * j mod N))) /\ 
                                (forall j:nat, j>=N -> U × (Vec (2 ^ L) j) = (Vec (2 ^ t) j))) ->
let Us (s:nat) := 1 / √ r .* (big_sum (fun k:nat=> (cos (- ((2 * PI)/r) * s * k),  sin (- ((2 * PI)/(r)) * s * k)) .*  Vec (2 ^ L) (x ^ k mod N)) (r)) in 
U_f j × Us s = (cos ((2*PI/2^t)* j *(s/r * 2^t)), sin ((2*PI/2^t)* j *(s/r * 2^t))) .* Us s.
Proof. intros.  induction j. simpl. rewrite Mmult_1_l.
     rewrite Rmult_0_r. rewrite Rmult_0_l. rewrite cos_0. rewrite sin_0.
rewrite Mscale_1_l. reflexivity. admit.
 unfold U_f in *.  simpl exp_U.
rewrite Mmult_assoc.
rewrite IHj.
rewrite Mscale_mult_dist_r.
  destruct H0. 
Admitted.


Lemma U_f': forall (v:Vector (2^t *(2^L))) , 
UCtrl_v 0 t t (t + L) 0 (t + L) U_f v =
Mmult (big_sum
(fun i : nat =>
 (∣ i ⟩_ (t) × ⟨ i ∣_ (t)) ⊗ (U_f i)) 
(2 ^ t)) v.
Proof.  intros. unfold UCtrl_v.
repeat rewrite add_sub_eq. repeat rewrite Nat.sub_0_r.
repeat rewrite Nat.sub_diag. repeat rewrite pow_0.
f_equal; type_sovle'; try lia. 
apply big_sum_eq_bounded. intros. 
repeat rewrite kron_1_l. rewrite kron_1_r.
apply Logic.eq_trans with (∣ x⟩_ (t) × ⟨ x ∣_ (t) ⊗ I (2 ^ L)
× (I (2 ^ t) ⊗  U_f x)).
f_equal; type_sovle'; try lia. 
rewrite kron_mixed_product. rewrite Mmult_1_r.
rewrite Mmult_1_l. reflexivity. admit.
 auto_wf. auto_wf.
Admitted.

Lemma base_inner_0:forall i j :nat,
i<>j->
(⟨ i ∣_ (t) × ∣ j ⟩_ (t))=0 .* I 1 .
Proof.  induction t. simpl. intros. 
destruct i. destruct j. intuition.
     Admitted.

Lemma  simpl_Uf: forall (r x N:nat),
ord x N =r-> 
WF_Unitary U /\ (forall j:nat, j< N -> U × (Vec (2 ^ L) j) = (Vec (2 ^ t) (x * j mod N))) /\ 
                                (forall j:nat, j>=N -> U × (Vec (2 ^ L) j) = (Vec (2 ^ t) j)) ->
let Us (s:nat) := 1 / √ r .* (big_sum (fun k:nat=> (cos (- ((2 * PI)/r) * s * k),  sin (- ((2 * PI)/(r)) * s * k)) .*  Vec (2 ^ L) (x ^ k mod N)) (r)) in 
UCtrl_v 0 t t (t + L) 0 (t + L) U_f
(1 / √ (r * 2 ^ t)
 .* big_sum
      (fun s : nat =>
       big_sum (fun j : nat => ∣ j ⟩_ (t)) (2 ^ t)
       ⊗ Us s) r) =
      (1 / √ (r)
       .* big_sum
            (fun s : nat =>
            (1/ √ (2 ^ t)).* big_sum (fun j : nat =>(cos ((2*PI/2^t)* j *(s/r * 2^t)), sin ((2*PI/2^t)* j *(s/r * 2^t))) .* ∣ j ⟩_ (t)) (2 ^ t)
             ⊗ Us s) r).
Proof. intros.
rewrite U_f'. 
rewrite Mscale_mult_dist_r.
rewrite Mmult_Msum_distr_l.
assert((1 / √ (r * 2 ^ t))%C= (1 / √ r * (1 / √ (2 ^ t)))%C ).
admit. rewrite H1. rewrite <-Mscale_assoc.
f_equal. rewrite <-Mscale_Msum_distr_r.
apply big_sum_eq_bounded. intros.
rewrite Mscale_kron_dist_l.  f_equal.
repeat rewrite kron_Msum_distr_r.
rewrite Mmult_Msum_distr_l.
apply big_sum_eq_bounded. intros.
rewrite Mmult_Msum_distr_r.
apply big_sum_unique .
exists x1. split. assumption. 
split. 
apply Logic.eq_trans with ((
(∣ x1 ⟩_ (t) × ⟨ x1 ∣_ (t) × ∣ x1 ⟩_ (t)) ⊗  ((cos ((2*PI/2^t)* x1 *(x0/r * 2^t)), sin ((2*PI/2^t)* x1 *(x0/r * 2^t))) .* Us x0))).
rewrite kron_mixed_product. f_equal.
unfold Us.
rewrite simpl_expU. f_equal. assumption.
assumption. 
rewrite Mmult_assoc. rewrite Vec_inner_1.
rewrite Mmult_1_r.  rewrite Mscale_kron_dist_r.
rewrite Mscale_kron_dist_l.
reflexivity.  auto_wf. assumption.
intros.
rewrite kron_mixed_product.
rewrite Mmult_assoc. rewrite base_inner_0.
rewrite Mscale_0_l. rewrite Mmult_0_r.
rewrite kron_0_l. reflexivity. intuition.
Admitted.

Lemma unitary_trans{n:nat}: forall (U:Square n) (v1 v2:Vector n),
WF_Unitary U->WF_Matrix v1->
U × v1 = v2-> (U) † × v2 = v1 .
Proof. intros. unfold WF_Unitary in H. destruct H.
rewrite <-H1. rewrite <-Mmult_assoc. rewrite H2.
rewrite Mmult_1_l. reflexivity. assumption.
   
Qed.

Lemma  simpl_QFT': forall (r x N:nat),
ord x N =r-> 
let Us (s:nat) := 1 / √ r .* (big_sum (fun k:nat=> (cos (- ((2 * PI)/r) * s * k),  sin (- ((2 * PI)/(r)) * s * k)) .*  Vec (2 ^ L) (x ^ k mod N)) (r)) in 
@U_v t (t+L) 0 t 0 (t + L) (QFT) †
(1 / √ r
 .* big_sum
      (fun s : nat =>
       1 / √ (2 ^ t)
       .* big_sum
            (fun j : nat =>
             (cos
                (2 * PI / 2 ^ t * j * (s / r * 2 ^ t)),
              sin
                (2 * PI / 2 ^ t * j * (s / r * 2 ^ t)))
             .* ∣ j ⟩_ (t)) (2 ^ t) ⊗ 
       Us s) r)=
       (1 / √ r
 .* big_sum
      (fun s : nat =>
       (Vec (2^t) (s/r * 2^t)) ⊗ 
       Us s) r) .
Proof. 
 unfold U_v. 
repeat rewrite add_sub_eq. repeat rewrite Nat.sub_0_r.
repeat rewrite Nat.sub_diag. repeat rewrite pow_0.
rewrite kron_1_l. assert(2^t=1* 2^t). lia. destruct H.
assert( 2^t * 2^L= 2^(t+L)). type_sovle'. destruct H.
intros.
rewrite Mscale_mult_dist_r. f_equal.
rewrite Mmult_Msum_distr_l. 
apply big_sum_eq_bounded.  intros. 
(* rewrite Mscale_kron_dist_l.
rewrite Mscale_mult_dist_r. *)
(* repeat rewrite Mscale_kron_dist_l.
f_equal. rewrite <-Mscale_kron_dist_l.  *)
rewrite kron_mixed_product.
rewrite Mmult_1_l.
(* rewrite <-Mscale_kron_dist_l. *)
f_equal.
pose HQFT. 
apply unitary_trans. intuition.
apply WF_vec. admit.
destruct a. rewrite H2.  
f_equal. 
apply big_sum_eq_bounded. intros.
f_equal. f_equal; f_equal; f_equal; admit.
admit.
apply WF_adjoint. apply HQFT.
Admitted.


Theorem OF_correctness: forall (r x N:nat),
ord x N =r->   
WF_Unitary U /\ (forall j:nat, j< N -> U × (Vec (2 ^ L) j) = (Vec (2 ^ t) (x * j mod N))) /\ 
                                (forall j:nat, j>=N -> U × (Vec (2 ^ L) j) = (Vec (2 ^ t) j)) ->
let  P (s:nat): Pure_formula := (BEq z' (s/r * 2^t)) in
let  Us (s:nat) := 1 / √ r .* (big_sum (fun k:nat=> (cos (- ((2 * PI)/r) * s * k),  sin (- ((2 * PI)/(r)) * s * k)) .*  Vec (2 ^ L) (x ^ k mod N)) (r)) in 
{{BEq (ANum (Nat.gcd x N)) (ANum 1) }} OF x N {{BEq z (ANum r)}}.
Proof. intros.  
unfold OF.
eapply rule_seq.
eapply rule_conseq_l'.
eapply rule_assgn with (P:=(BEq (ANum z) (ANum 1))). 
admit.
eapply rule_seq.
eapply rule_conseq_l'.
eapply rule_assgn with (P:=(BAnd (BEq (ANum z) (ANum 1))  ( BEq b (ANum (x mod N))))).
admit. 
eapply rule_conseq_l with (P':=( (BNeq (ANum z) (ANum r) /\ (BNeq b (ANum 1))))).
admit.
eapply rule_conseq.
eapply rule_while with (F0:= (BNeq (ANum z) (ANum r))) (F1:= (BEq (ANum z) (ANum r))).
*eapply rule_seq.
eapply rule_conseq_l.
apply rule_PT.
apply rule_QInit. 
*eapply rule_seq.
eapply rule_conseq_l.
apply rule_OdotE.
eapply rule_qframe'. simpl. admit.
split. apply rule_QInit. simpl. 
split. apply inter_empty. left. reflexivity.
right. admit.
* eapply rule_seq.
eapply rule_qframe. simpl. admit. 
split. apply rule_QUnit_One'. lia. 
simpl. 
split. apply inter_empty. left. reflexivity.
right. admit.
unfold U_v. repeat rewrite Nat.sub_diag. rewrite Nat.sub_0_r. simpl.
rewrite kron_1_l; auto_wf. rewrite kron_1_r; auto_wf. 
rewrite Had_N.  
* eapply rule_seq.
eapply rule_qframe'. simpl. admit.
split. apply rule_QUnit_One'. lia. 
simpl.
split. apply inter_empty. left. reflexivity.
right. admit.
 unfold U_v. repeat rewrite Nat.sub_diag.
simpl. pose HU_plus. rewrite kron_1_l; auto_wf. rewrite kron_1_r; auto_wf.
destruct a. assert(L=t + L - t). lia. destruct H3.
rewrite H2.
* eapply rule_seq.
eapply rule_conseq_l.
eapply rule_odotT.
eapply rule_conseq_l.
eapply rule_Separ.
assert(L=t + L - t). lia. destruct H3.
assert(t=t-0). lia. destruct H3.
rewrite simpl_H_Uplus with r x N.
eapply rule_QUnit_Ctrl'. lia. 
assumption.
rewrite simpl_Uf.
* eapply rule_seq.
eapply rule_QUnit_One'. lia. 
assert(t=t-0). lia. destruct H3.
assert(t+L=t+L-0). lia. destruct H3.
rewrite simpl_QFT'.
* eapply rule_seq. 
eapply rule_conseq_l'.
eapply rule_QMeas with (s:=0) (e:=t+L) (P:=P)
(v:= 1 / √ r .*  (big_sum (fun s:nat=>kron  (Vec (2^t) (s/r * 2^t) ) (Us s)) (r) )). lia.
apply big_pOplus'_to_pOplus. intros. 
admit. admit. 
*eapply rule_seq. 
eapply rule_conseq_l. 
eapply rule_Oplus. rewrite big_pOplus_get_npro.
eapply rule_conseq_l'.
eapply rule_assgn.
admit. admit. assumption. assumption.
assumption.  destruct a.  
assert(L=t+L-t). lia. destruct H3.
destruct H1. 
apply H1.
admit. admit.
Admitted.

Parameter random: nat -> nat -> nat.
Hypothesis Hran: forall a b, (a <=? random a b) && (random a b <=? b)=true.

Lemma bool_true: forall (a b:nat),
a=b-> (a=? b =true).
Proof. induction a; induction b0; intros.
       simpl. intuition. intuition. intuition.
       simpl.
       injection H. intuition. 
Qed.

Theorem rule_Clet: forall (a b:nat),
{{BTrue}}
Clet a b
{{ BEq (ANum a) (ANum b) }} .
Proof. unfold hoare_triple. intros.
       destruct mu as [mu IHmu].
       destruct mu' as [mu' IHmu'].
       rewrite sat_Assert_to_State in *.
       inversion_clear H. simpl in *.
       inversion H3; subst.
       inversion_clear H0. simpl in H4. 
       destruct H4. unfold x0.
       rewrite seman_find. split.
       assumption. split. discriminate.
       intros. simpl.
       rewrite bool_true. intuition.
       reflexivity.
Qed.

Definition y:nat := 3.
Definition x:nat := 4.



Definition Shor (N:nat):=
  let N2 := (N mod 2) in
  let b2 (x:nat) :=(BAnd (BEq (AMod z (ANum 2)) (ANum 0)) (BNeq (ANum ((x^(z/2) mod N))) (ANum 1))) in
  let b3 (x:nat) :=(BAnd (BNeq (AGcd (APow ((ANum x)) ((AMinus(ADiv z (ANum 2)) (ANum 1)))) (ANum N)) (ANum 1))  (BNeq (ANum (Nat.gcd (x ^ (z / 2) - 1) N)) (ANum N))) in
  <{  if BEq (ANum N2) (ANum 0) then
           y:=ANum 2
      else  
           Clet x ((random 2 (N-1)));
           y:= AGcd (ANum x) (ANum N);
           while BEq y (ANum 1) do 
                  OF x N;
                  if b2 x then
                      if  b3 x then 
                          y:=AGcd (APow ((ANum x)) ((AMinus(ADiv z (ANum 2)) (ANum 1)))) (ANum N)
                      else 
                          y:=AGcd (APow ((ANum x)) ((APlus(ADiv z (ANum 2)) (ANum 1)))) (ANum N)
                      end 
                  else 
                       Clet x ((random 2 (N-1)));
                       y := AGcd ((ANum x)) (ANum N)
                  end 
            end 
      end 
  }>.


Theorem rule_while_classic: forall F (b:bexp) (c:com),
         {{F /\ b}} c {{ F}}
      -> {{F}}
         while b do c end
         {{ (F /\ (BNot b)) }}.
Proof. Admitted.

Theorem rule_cond_classic: forall (F1 F2: State_formula) (c1 c2:com) (b:bexp),
        ({{F1 /\ (b)}} c1 {{F2 }} /\ {{F1 /\ ((BNot b) )}} c2 {{F2 }})
     -> ({{F1 }}
        if b then c1 else c2 end
        {{F2}}).
Proof. Admitted.

Theorem rule_qframe'': forall (F1 F2 F3: State_formula) c,
         ({{F1}} c {{F2}}) /\  (NSet.inter (fst (Free_state F3)) (fst (MVar c)) =NSet.empty) 
         /\ (NSet.inter (snd (Free_state F3)) (snd (MVar c)) =NSet.empty) 
         ->  {{F3 /\ F1}} c {{F3 /\ F2}}. Admitted.

         Theorem rule_conseq_r' : forall (P Q Q' : Assertion) c,
         {{P}} c {{Q'}} ->
         (Q'->> Q) ->
               
                {{P}} c {{Q}}.
                Proof. intros. eapply rule_conseq. apply H. 
                apply implies_refl. assumption. Qed.   

 (* Lemma aeval_update_eq{n:nat}: forall (sigma:cstate) (q:qstate n) (i:aexp) (x0:nat), 
aeval (c_update x0 (aeval (sigma, q) i) sigma, q) i=
aeval (sigma, q) i. 
Proof.  induction i; intros; simpl.
    { reflexivity.  }
    { assert(i=x0 \/ i<>x0). apply Classical_Prop.classic.
     destruct H. rewrite H. rewrite c_update_find_eq.
     reflexivity. rewrite c_update_find_not. reflexivity. intuition.  }
    { rewrite IHi1. with x0.   }
    -reflexivity.
    -simpl. assumption.
    -reflexivity.
    -simpl. apply IHsigma.
Qed. *)



(* Lemma Assn_implies: forall (P:State_formula) (x:nat) (i:aexp),
P ->> ( P /\ (Assn_sub x i (BEq x i))) .
Proof. intros. unfold assert_implies.
    intros.  rewrite sat_Assert_to_State in *.
    rewrite seman_find in *.
     split.  intuition.
     split. intuition.
     intros. split.  apply H. assumption. 
     induction i.  
     simpl. rewrite c_update_find_eq.
     admit. 
     simpl. 
     assert(x0=i\/x0<>i).
     apply Classical_Prop.classic.
     destruct H1. rewrite H1.
     rewrite c_update_find_eq. 
     induction (c_find i x1). 
     simpl. intuition. simpl. assumption.
     rewrite c_update_find_eq.
     rewrite c_update_find_not. 
     induction (c_find i x1). 
     simpl. intuition. simpl. assumption.
     assumption. 


Qed. *)

Lemma rule_AndT: forall (P:State_formula),
P ->> P /\ BTrue .
Proof. unfold assert_implies. intros.
      rewrite sat_Assert_to_State in *.
      rewrite seman_find in *. split.
      intuition. split. intuition. 
      intros. econstructor. apply H.
      assumption. econstructor.
  
Qed.


Definition Cop (N:nat): Pure_formula := PExists
(fun a => (BAnd (BAnd (BLe (ANum 2) (ANum a))  (BLe (ANum a) (ANum (N-1))))
 (BEq (ANum (N mod a)) (ANum 0)))).

Lemma Cop_5{n:nat}:forall (st:state n),
  (Pure_eval (Cop 4) st).
Proof. intros. unfold Cop.   unfold Pure_eval. 
exists 2. unfold beval. unfold aeval.  
   simpl. intuition.
Qed.

Definition F_1(y x N:nat): bexp := BAnd (BAnd (BEq y ((ANum (Nat.gcd (x ^ ((ord x N) / 2) - 1) N)))) 
(BNeq y (ANum 1))) (BNeq y (ANum N)).

Definition F_2(y x N:nat): bexp := BAnd (BAnd (BEq y ((ANum (Nat.gcd (x ^ (((ord x N)) / 2) + 1) N)))) 
(BNeq y (ANum 1))) (BNeq y (ANum N)).

Definition F_3(y x N:nat): bexp := (BAnd (BEq y ((ANum (Nat.gcd x N)))) 
(BNeq y (ANum N))) .

Theorem Shor_correctness (N:nat):

{{Cop (N)}} Shor N {{  (BEq (ANum (N mod y)) (ANum 0)) /\ (BNeq y (ANum 1)) /\ (BNeq y ((ANum N)))}} .
Proof. unfold Shor. 
       eapply rule_cond_classic. split.
       {eapply rule_conseq_l with ((Cop (N) /\ (BEq (ANum ((N mod 2))) (ANum 0))) /\ (Assn_sub_P y (ANum 2) (BEq y (ANum 2)))).
        intros. unfold assert_implies.
        intros.  rewrite sat_Assert_to_State in *.
        rewrite seman_find in *.
        split.  intuition.
        split. intuition.
        intros. split.  apply H. assumption.
        unfold State_eval. unfold Pure_eval.
        unfold s_update_cstate.  
        unfold beval. unfold aeval. unfold fst.
        rewrite c_update_find_eq. simpl. intuition.
       eapply rule_conseq_r'.
       eapply rule_qframe''.
       split.  apply rule_assgn. admit.
        }
       eapply rule_seq with ((Cop (N) /\  (BNot (BEq ((ANum (N mod 2))) ((ANum 0))))) 
       /\ ((BAnd (BLe ((ANum 2)) (ANum x))  (BLe ((ANum x)) ((ANum (N-1))))))). 
          {eapply rule_conseq_l. apply rule_AndT.
          eapply rule_conseq_r'.
          eapply rule_qframe''. 
          split.   eapply rule_Clet. admit.
          intros. unfold assert_implies.
        intros.  rewrite sat_Assert_to_State in *.
        rewrite seman_find in *.
        split.  intuition.
        split. intuition.
        intros. split.  apply H. assumption.
        destruct H. destruct H1. apply H2 in H0.
        destruct H0. unfold State_eval in *. unfold Pure_eval in *.
        unfold beval in *. unfold aeval in *.
        bdestruct (x =? random 2 (N - 1)).
        rewrite H4.
        rewrite Hran. intuition. destruct H3. 
        }
          eapply rule_seq with ((Cop (N) /\  (BNot (BEq ((ANum (N mod 2))) (ANum 0))) /\ (BAnd (BLe (ANum 2) (ANum x) ) (BLe (ANum x) (ANum (N-1)))))
          /\(BOr (F_1 y x N) (BOr (F_2 y x N) (F_3 y x N)))).
          {eapply rule_conseq_l with (((Cop (N) /\  (BNot (BEq ((ANum ((N mod 2)))) (ANum 0))) /\ ((BAnd (BLe (ANum 2) (ANum x) ) (BLe (ANum x) (ANum (N-1))))))) /\ Assn_sub_P y ((AGcd (ANum x) (ANum N))) (BEq y ((AGcd (ANum x) (ANum N))))).
          intros. unfold assert_implies.
          intros.  rewrite sat_Assert_to_State in *.
          rewrite seman_find in *.
          split.  intuition.
          split. intuition.
          intros. split.  
          split. apply H. assumption.
          split. apply H. assumption. 
         apply H. assumption.
          unfold State_eval. unfold Pure_eval.
          unfold s_update_cstate.  
          unfold beval. unfold aeval. unfold fst.
          rewrite c_update_find_eq.
          induction (Nat.gcd x N);
         simpl; intuition. 
          eapply rule_conseq_r'.
          eapply rule_qframe''.
          split.  apply rule_assgn. admit.
          }
          eapply rule_conseq_r'.
          apply rule_while_classic.
          
           eapply rule_seq with ((Cop (N) /\  (BNot (BEq ((ANum (N mod 2))) (ANum 0))) /\ (BAnd (BLe (ANum 2) (ANum x) ) (BLe (ANum x) (ANum (N-1)))))
           /\(BEq z (ANum (ord x N)))). 
           eapply rule_conseq_l with (((Cop (N) /\  (BNot (BEq ((ANum (N mod 2))) (ANum 0))) /\ (BAnd (BLe (ANum 2) (ANum x) ) (BLe (ANum x) (ANum (N-1)))))
           /\(BEq (ANum (Nat.gcd x N)) (ANum 1)))).
           admit.
           apply rule_qframe''. 
           split. 
           apply OF_correctness. reflexivity. admit.
           admit.
           apply rule_cond_classic. split.
           eapply rule_conseq_l with (((Cop (N) /\  (BNot (BEq ((ANum (N mod 2))) (ANum 0))) /\ (BAnd (BLe (ANum 2) (ANum x) ) (BLe (ANum x) (ANum (N-1)))))
           /\( BEq z (ANum (ord x N))) /\ (BOr (F_1 y x N) (F_2 y x N)))). admit.
           apply rule_cond_classic. split.
           eapply rule_conseq_l with 
           ( ((Cop (N) /\  (BNot (BEq ((ANum (N mod 2))) (ANum 0))) /\ (BAnd (BLe (ANum 2) (ANum x) ) (BLe (ANum x) (ANum (N-1))))) /\(F_1 y x N)) /\ (Assn_sub_P y (AGcd (APow ((ANum x)) ((AMinus(ADiv z (ANum 2)) (ANum 1)))) (ANum N)) (BEq y (ANum (Nat.gcd (x^ ((ord x N) / 2 - 1)) N))))).
            {admit.
              (*intros. unfold assert_implies.
           intros.  rewrite sat_Assert_to_State in *.
           rewrite seman_find in *.
            split.  intuition.
            split. intuition. 
            intros. econstructor. apply H. assumption.
             unfold State_eval. unfold Pure_eval.
             unfold s_update_cstate. 
          unfold beval. unfold aeval. unfold fst.
          rewrite c_update_find_eq.
          rewrite c_update_find_not.
          induction (Nat.gcd (c_find x' x0) N);
         simpl; intuition. unfold y. unfold x'. lia. *)
             } 
            eapply rule_conseq_r'.
          eapply rule_qframe''.
          split.  apply rule_assgn.
          admit. admit.
          eapply rule_conseq_l with 
          ( (Cop (N) /\  (BNot (BEq ((ANum (N mod 2))) (ANum 0))) /\ (BAnd (BLe (ANum 2) (ANum x) ) (BLe (ANum x) (ANum (N-1)))) /\(F_2 y x N)) /\ (Assn_sub_P y (AGcd (APow ((ANum x)) ((APlus(ADiv z (ANum 2)) (ANum 1)))) (ANum N)) (BEq y (ANum (Nat.gcd (x^ ((ord x N) / 2 + 1)) N))))).
          admit. 
         eapply rule_conseq_r'.
         eapply rule_qframe''.
         split.  apply rule_assgn.
         admit. admit.
         eapply rule_seq with ((Cop (N) /\  (BNot (BEq ((ANum (N mod 2))) ((ANum 0))))) 
       /\ ((BAnd (BLe ((ANum 2)) (ANum x))  (BLe ((ANum x)) ((ANum (N-1))))))). 
          {eapply rule_conseq_l. apply rule_AndT.
          eapply rule_conseq_r'.
          eapply rule_qframe''. 
          split.   eapply rule_Clet. admit.
          intros. unfold assert_implies.
        intros.  rewrite sat_Assert_to_State in *.
        rewrite seman_find in *.
        split.  intuition.
        split. intuition.
        intros. split. split.  apply H. assumption.
        apply H. assumption.
        destruct H. destruct H1. apply H2 in H0.
        destruct H0. unfold State_eval in *. unfold Pure_eval in *.
        unfold beval in *. unfold aeval in *.
        bdestruct (x =? random 2 (N - 1)).
        rewrite H4.
        rewrite Hran. intuition. destruct H3. 
        }
        {eapply rule_conseq_l with (((Cop (N) /\  (BNot (BEq ((ANum ((N mod 2)))) (ANum 0))) /\ ((BAnd (BLe (ANum 2) (ANum x) ) (BLe (ANum x) (ANum (N-1))))))) /\ Assn_sub_P y ((AGcd (ANum x) (ANum N))) (BEq y ((AGcd (ANum x) (ANum N))))).
          intros. unfold assert_implies.
          intros.  rewrite sat_Assert_to_State in *.
          rewrite seman_find in *.
          split.  intuition.
          split. intuition.
          intros. split.  
          split. apply H. assumption.
          split. apply H. assumption. 
         apply H. assumption.
          unfold State_eval. unfold Pure_eval.
          unfold s_update_cstate.  
          unfold beval. unfold aeval. unfold fst.
          rewrite c_update_find_eq.
          induction (Nat.gcd x N);
         simpl; intuition. 
          eapply rule_conseq_r'.
          eapply rule_qframe''.
          split.  apply rule_assgn. admit.
          admit.
          } admit. 
Admitted.

End OF.
