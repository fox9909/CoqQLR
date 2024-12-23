
 

  (*----------------------------------------------------*)






Fixpoint Free_QExp'(qs :QExp) := 
match qs with 
|QExp_s s e v => (s, e) 
|QExp_t qs1 qs2 => (min (fst (Free_QExp' qs1)) (fst (Free_QExp' qs2)),
                  max  (snd (Free_QExp' qs1))  (snd (Free_QExp' qs2) ))
end.

Definition option_beq (a b:option (nat * nat)) :=
       match a, b with 
       |None, None =>true
       |None , _ => false  
       |_, None => false
       |Some (x,y), Some (x',y') => (x=?x') && (y=?y') 
       end. 

Definition option_free(a:option (nat*nat)):=
match a with 
|None  => (0, 0)
|Some x => x 
end.


Fixpoint Free_State(F:State_formula): option (nat * nat):=
match F with 
|SPure P => None
|SQuan qs=> Some (Free_QExp' qs) 
|SOdot F1 F2=>if  (option_beq (Free_State F1)  None) 
              then Free_State F2 
              else if (option_beq (Free_State F2)  None)
              then Free_State F1 
              else let a:= option_free (Free_State F1) in let b:=option_free (Free_State F2) in 
              Some (min (fst a) (fst b),
              max  (snd a)  (snd b))
|SAnd F1 F2 => if  (option_beq (Free_State F1)  None) 
              then Free_State F2 
              else if (option_beq (Free_State F2)  None)
              then Free_State F1 
              else let a:= option_free (Free_State F1) in let b:=option_free (Free_State F2) in 
              Some (min (fst a) (fst b),
              max  (snd a)  (snd b))
|SAssn i a F => Free_State F
end.

Fixpoint Considered_QExp (qs:QExp) : Prop :=
match qs with 
|QExp_s s e v => s<e  
|QExp_t qs1 qs2 => Considered_QExp qs1 /\ Considered_QExp qs2 /\ 
              (((snd (Free_QExp' qs1))=(fst (Free_QExp' qs2)))
              \/ ((snd (Free_QExp' qs2))=(fst (Free_QExp' qs1))))
end.


Fixpoint Considered_Formula (F:State_formula) : Prop:=
match F with
| SPure P => True 
| SQuan s => Considered_QExp s
| SOdot F1 F2 =>  if  (option_beq (Free_State F1)  None) 
then Considered_Formula F2 
else if (option_beq (Free_State F2)  None)
then Considered_Formula F1
else   let a:= option_free (Free_State F1) in let b:=option_free (Free_State F2) in 
      ( Considered_Formula F1 /\ Considered_Formula F2 
              /\ (((snd a)=(fst b))
              \/ ((snd b)=(fst a))))
|SAnd F1 F2 =>   if  (option_beq (Free_State F1)  None) 
then Considered_Formula F2 
else if (option_beq (Free_State F2)  None)
then  Considered_Formula F1
else  let a:= option_free (Free_State F1) in let b:=option_free (Free_State F2) in 
                     (Considered_Formula F1 /\ Considered_Formula F2 
              /\  ((((fst a)=(fst b))/\
                     ((snd a)=(snd b)))
                     \/ ((snd a)=(fst b)) 
                    \/ (((snd b)=(fst a)))))
|SAssn i a F => Considered_Formula F
end. 

(*--------------------------------------------*)





  


Require Import OrderedType.
Module MD := OrderedTypeFacts(D).









        











Import Basic.



































































Lemma union_not_empty: forall x y, 
~ NSet.Equal (NSet.union x y) NSet.empty->
~ NSet.Equal x NSet.empty \/ ~ NSet.Equal y NSet.empty.
Proof. intros. assert(NSet.Equal x NSet.empty \/ ~NSet.Equal x NSet.empty).
  apply Classical_Prop.classic. destruct H0. right. 
  intro. destruct H. apply union_empty. auto. 
  left. assumption. 
Qed.
































































































