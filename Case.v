Require Import Lists.List.
Require Import Reals.
Require Import Coquelicot.Complex.
Require Import Strings.String.


From Quan Require Import Matrix.
From Quan Require Import Quantum.
From Quan Require Import Basic_Supplement.
From Quan Require Import ParDensityO.
From Quan Require Import QState.
From Quan Require Import QIMP.
From Quan Require Import QAssert.
From Quan Require Import QRule_E.
From Quan Require Import QRule_Q.
From Quan Require Import QRule_I.
From Quan Require Import Basic_Supplement.




Module HHL.

Local Open Scope com_scope.
Local Open Scope assert_scope.
Local Open Scope nat_scope.
Local Open Scope matrix_scope.
Local Open Scope rule_scope.

Theorem rule_conseq_l' : forall (P P' Q : Assertion) c,
           {{P'}} c {{Q}} ->
           (P ->> P') ->
           {{P}} c {{Q}}.
Proof. intros. eapply rule_conseq. apply H. assumption.
apply implies_refl.
     Qed.
Coercion INR : nat >-> R.
Local Open Scope R_scope.

Definition v:nat:= 0.

Parameter n m:nat .
Parameter A:Square (2^m).
Parameter b:Vector (2^m).
Parameter x:Vector (2^m).
Parameter lamda:nat-> R.
Parameter mu_j:nat-> Vector (2^m).
Parameter b_j:nat-> C.
Parameter c:R.
Parameter U_b:Square (2^m).
Parameter U_f:Matrix (2^m) (2^m).
Parameter QFT: Matrix (2^n) (2^n).
Parameter U_c: (Matrix (2^n * 2^ 1)) ( (2^n * 2^ 1)).

Hypothesis HAx: A × x =b.
Hypothesis Hmu_j:forall j, norm (mu_j j)=1.
Hypothesis Hb_j:forall j, norm (mu_j j)=1.
Hypothesis Hb: norm b =1.
Hypothesis HB_decom: big_sum (fun j=>(b_j j) .* (mu_j j)) (2^m)= b.
Hypothesis HA_decom: big_sum (fun j=>(lamda j) .* (mu_j j)) (2^m)= b.
Hypothesis HU_b: WF_Unitary U_b /\ ( U_b × (Vec (2^m) 0) = b).
Hypothesis HU_c: WF_Unitary U_c /\ (U_c × (Vec (2^n) 0 ⊗ Vec 2 0)) = (Vec (2^n) 0 ⊗ Vec 2 0) /\
                          (forall j:nat, U_c × (Vec (2^n) j ⊗ Vec 2 1) = (Vec (2^n) j ⊗ ((sqrt (1-(( c^2)/( j^2)))) .* (Vec 2 0) .+ (c/j .* Vec 2 1)))).

 Local Open Scope nat_scope.                  
Definition HHL :=
    <{ v := 0;
       while  v=0  do 
       QInit 0 n;
       QInit n m;
       QInit (n+m) (n+m+1);
       QUnit_One n m (U_b);
       QUnit_One 0 n (kron_n n hadamard);
       QUnit_Ctrl 0 n n m U_f;
       QUnit_One 0 n (adjoint QFT);
       QUnit_Ctrl 0 n (n+m) (n+m+1) (U_c);
       QUnit_One 0 n (QFT);
       QUnit_Ctrl 0 n n m (adjoint U_f);
       QUnit_One 0 n (kron_n n hadamard);
       QMeas v n (n+1)
       end }>.

Theorem correctness_HHL: 
{{BTrue}}
HHL
{{QExp_s n m x}}.
Proof. unfold HHL. 
       eapply rule_seq.
       eapply rule_conseq_l'. 
       eapply (rule_assgn (BEq v 0)).
       admit.
       eapply rule_conseq.
       eapply (rule_while BTrue).
       eapply rule_conseq_l.
       apply rule_PT.
       eapply rule_conseq_l.
       apply rule_OdotE.
       eapply rule_seq.
       apply rule_qframe.
       split. eapply rule_QInit. admit.
       eapply rule_conseq_l.
       eapply rule_OdotE.
       eapply rule_seq.
       eapply rule_qframe.
       split. eapply rule_conseq_l.
       apply rule_OdotC.
       eapply rule_qframe. split.
       apply rule_QInit. admit. admit.
       eapply rule_seq.
       eapply rule_conseq_l.
       apply rule_OdotC.
       eapply rule_qframe.  split. 
       apply rule_QInit. simpl. admit.
       eapply rule_conseq_l.
       apply rule_OdotC.
       eapply rule_conseq_l.
       apply rule_OdotA.
       eapply (rule_while BTrue).
       eapply (rule_conseq_l _ (BTrue ⊙ BTrue ⊙ BTrue)).
       eapply rule_QInit. 
       admit.
       eapply rule_seq.
       eapply rule_conseq_l.
       eapply rule_QInit.

    
End HHL.

