/-

Prove the following simple logical conjectures.

Give a formal and an English proof of each one.

Your English language proofs should be complete

in the sense that they identify all the axioms

and/or theorems that you use.

-/

example : true := true.intro

-- example : false :=     

-- trick question? why? because false has no value, there are no proofs.




example : ∀ (P : Prop), P ∨ P ↔ P := 

begin

  assume P,

  apply iff.intro _ _,

  -- forward

    assume porp,

    apply or.elim porp,

    --left disjunct is true

    assume p,

    exact p,

    --right disjunct is true

    assume p,

    exact p,

  -- backward

    assume p,

    exact or.intro_left P p,

end



/-

we first assume P, an arbiturary propisition. 

afterwards, we utilize iff.intro, which splits the

propisition into two parts, back and forth.



from here, we have to goals to solve: P ∨ P → P and  P → P ∨ P. 



for the first goal, we first assume that there is proof for 

P ∨ P. This leaves us just needing to prove P, which we can

get to through utilizing or.elim. This branches the first goal

into two goals of P → P, which can be solved by assuming a proof of

P (p), and then using this proof to prove the P it implies.



for the second goal, we can first assume a proof of P (p). 

We then simply have to prove P → P, which can be solved

by assuming a proof of P (p), and then using this proof to prove

the P it implies. 



this completes the proof.

-/



example : ∀ (P : Prop), P ∧ P ↔ P := 

begin

  assume P,

  apply iff.intro _ _,

  

  assume pandp,

  apply and.elim_left pandp,



  assume p,

  apply and.intro p p,



end



/-

we first assume P, an arbiturary propisition. 

afterwards, we utilize iff.intro, which splits the

propisition into two parts, back and forth.



the two goals that remain to be proved are P ∧ P → P and P → P ∧ P. 



for the first goal, we assume the we have a proof of P ∧ P (pandp).

this leaves us with P, which can be proved using and.elim_left

on pandp, which isolates and produces and a proof of P.



for the second goal, we assume we have a proof of P (p). This 

leaves us needing to prove P ∧ P, which we can do so through

and.intro, which breaks the and statement into two parts, both

of which can be proved using the previously assumed proof of P (p).



this completes the proof.



-/



example : ∀ (P Q : Prop), P ∨ Q ↔ Q ∨ P := 

begin

  assume P,

  assume Q,

  apply iff.intro _ _,

  

  assume porq,

  apply or.elim porq,

  assume p,

  apply or.intro_right,

  exact p,

  assume q,

  apply or.intro_left,

  exact q,



  assume qorp,

  apply or.elim qorp,

  assume q,

  apply or.intro_right,

  exact q,

  assume p,

  apply or.intro_left,

  exact p,

end



/-

we first assume P and Q, arbiturary propisitions. 

afterwards, we utilize iff.intro, which splits the

propisition into two parts, back and forth.



after this, we are left with two goals

to prove: P ∨ Q → Q ∨ P and Q ∨ P → P ∨ Q. 



to prove the first goal, we assume that we have a proof of

P ∨ Q (porq) and then use or.elim on it in order branch into two goals

of P → Q ∨ P and Q → Q ∨ P. 



we prove the first branch of the first goal

by assuming we have a proof of P (p). 

after this, we are simply left with Q ∨ P, which we can simply

prove by or.intro_right, which simply leaves us with P, which 

we can prove with the proof of p we assumed earlier. 



we prove the second branch of the first goal similarly.

we first assume a proof of Q (q). we are then left with Q ∨ P. 

we solve this utilizing or.intro_left, which just leaves us Q, which

we can prove utilizing q, the proof of Q we assumed earlier. 



to prove the second goal, we essentially do the same thing but

backwards. we first assume that we have a proof of

Q ∨ P (qorp) and then use or.elim on it in order branch into two goals

of P → P ∨ Q and Q → P ∨ Q. 



we prove the first branch of the first goal

by assuming we have a proof of Q (q). 

after this, we are simply left with P ∨ Q, which we can simply

prove by or.intro_right, which simply leaves us with Q, which 

we can prove with the proof of q we assumed earlier.



we prove the second branch of the first goal similarly.

we first assume a proof of P (p). we are then left with P ∨ Q. 

we solve this utilizing or.intro_left, which just leaves us P, which

we can prove utilizing p, the proof of P we assumed earlier. 



-/



example : ∀ (P Q : Prop), P ∧ Q ↔ Q ∧ P := 

begin

  assume P,

  assume Q,

  apply iff.intro _ _,



  assume pandq,

  apply and.elim pandq,

  assume p,

  assume q,

  apply and.intro q p,



  assume qandp, 

  apply and.elim qandp,

  assume q,

  assume p,

  apply and.intro p q,



end

/-

we first assume P and Q, arbiturary propisitions. 

afterwards, we utilize iff.intro, which splits the

propisition into two parts, back and forth.



after the split, we are left with two

goals: P ∧ Q → Q ∧ P and Q ∧ P → P ∧ Q.



to prove the first goal, we first start out with an assumption

of a proof or P ∧ Q (pandq). we then apply and.elim on pandq,

which alters the proof to be P → Q → P ∧ Q. in order to prove this,

we assume we have a proof of P (p) and then a proof of Q (q),

leaving us with just P ∧ Q. we then use the and

introduction rule alongside the two proofs of Q and P to prove

this propisition.



the second goal is essentially just the first goal but backwards.

to prove the second goal, we first start out with an assumption

of a proof or Q ∧ P (qandp). we then apply and.elim on qandp,

which alters the proof to be Q → P → Q ∧ P. in order to prove this,

we assume we have a proof of Q (q) and then a proof of P (p),

leaving us with just Q ∧ P. we then use the and

introduction rule alongside the two proofs of P and Q to prove

this propisition.

-/

example : ∀ (P Q R : Prop), P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := 

begin

  assume P Q R,

  apply iff.intro _ _,



  assume h,

  apply and.elim h,

  assume p,

  assume qr,

  apply or.intro_right,

  apply and.intro p,



end

/-

we first assume P Q R, arbiturary propisitions. 

afterwards, we utilize iff.intro, which splits the

propisition into two parts, back and forth.



im not sure how to finish this proof i ran into a dead end. i 

am not quite sure how to prove r in this situation.

-/

example : ∀ (P Q R : Prop), P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R) := 

begin

  assume P Q R,

  apply iff.intro _ _,



  assume pqr,

  apply and.intro _ _,

  apply or.intro_left,

  

end

/-

we first assume P Q R, arbiturary propisitions. 

afterwards, we utilize iff.intro, which splits the

propisition into two parts, back and forth.



im not sure how to finish this proof i ran into a dead end. im not

sure how to isolate and prove q in this scenario.

-/

example : ∀ (P Q : Prop), P ∧ (P ∨ Q) ↔ P := 

begin

  assume P Q,

  apply iff.intro _ _,



  assume h,

  apply and.elim_left h,



  assume p,

  apply and.intro,

  exact p,



  apply or.intro_left,

  exact p,

end

/-

we first assume P Q, arbiturary propisitions. 

afterwards, we utilize iff.intro, which splits the

propisition into two parts, back and forth.



after the split, we are left with two goals 

to prove: P ∧ (P ∨ Q) → P and P → P ∧ (P ∨ Q). 



in order to prove the first goal, we first assume a proof

of P ∧ (P ∨ Q) (h). here, we are simply left with P, which

we can prove using and.elim_left, which isolates a proof of P

and therefore completes the goal.



for the second goal, we first assume a proof of P (p), which 

leaves us with P ∧ (P ∨ Q). to solve this, we use the and

introduction rule and seperate this into two goals, P and (P ∨ Q).

P can simply be proved through the previously assumed proof of P (p). 

P ∨ Q can be simplified further using or.intro_left, which leaves

us with just P, which can again be proved through the previously 

assumed proof of P (p).



-/

example : ∀ (P Q : Prop), P ∨ (P ∧ Q) ↔ P := 

begin

  assume P Q,

  apply iff.intro _ _,



  assume ppq,

  apply or.elim ppq,

  

  assume p,

  exact p,



  assume pq,

  apply and.elim_left pq,



  assume p,

  apply or.intro_left,

  exact p,




end

/-

we first assume P Q, arbiturary propisitions. 

afterwards, we utilize iff.intro, which splits the

propisition into two parts, back and forth.



after the split, we are left with two goals to 

prove: P ∨ P ∧ Q → P and P → P ∨ P ∧ Q. 



for the first goal, we first assume a proof or P ∨ P ∧ Q (ppq).

we then further break down this proof using or.elim on the proof,

which produces the two goals of P → P and P ∧ Q → P.



to prove P → P, all we need to do is assume a proof of P (p), 

and then use this proof to prove the P that it implies. 



to prove P ∧ Q → P, we first assume a proof of P ∧ Q (pq). 

we then need to prove P, which we can produce a proof of

through the and.elim_left on pq, which isolates a proof of P

which can be used to prove the remaining P. 



for the second goal, we first assume a proof of P (p). this

leaves us with P ∨ O ∧ Q. using the or.intro_left rule, we can

isolate just a P. this P can be proved using the previously

assumed proof of P (p). 



-/

example : ∀ (P : Prop), P ∨ true ↔ true := 

begin

  assume P,

  apply iff.intro _ _,



  assume portrue,

  apply true.intro,



  assume t,

  apply or.intro_right,

  apply true.intro,

end

/-

we first assume P, an arbiturary propisition. 

afterwards, we utilize iff.intro, which splits the

propisition into two parts, back and forth.



after the split, we are left with two main goals to 

prove: P ∨ true → true and true → P ∨ true.



to prove the first goal, we can assume a proof of P ∨ true (portrue).

after this assumption, we are left with true, which can easily

proved using the introductary for true, which basically means

true is always true. 



to prove the second goal, we can first assume a proof of true. 

we are then left with P ∨ true. we use then or.intro_left 

inorder to isolate the statement to just true, which can

again be proved through the introductary rule for true.

-/



example : ∀ (P : Prop), P ∨ false ↔ P := 

begin

  assume P,

  apply iff.intro _ _,



  assume porfalse,

  apply or.elim porfalse,



  assume p,

  exact p,



  assume f,

  cases f,



  assume p,

  apply or.intro_left,

  exact p,



end

/-

we first assume P, an arbiturary propisition. 

afterwards, we utilize iff.intro, which splits the

propisition into two parts, back and forth.



after the split, we are left with two main goals to 

prove: P ∨ false → P and P → false ∨ P.



for the first goal, we first assume a proof of P ∨ false (porfalse). 

with this proof, we utilize or.elim on it to branch it into two

separate goals, P → P and false → P. 



for the first branch, we can assume a proof of P (p) and then

simply use this proof to prove the P it implies. 



for the second branch, we assume a proof of false and then use 

cases on this proof to test whether or not this is 

contradictary, which leads us to completing the goal. 



for the second goal, we assume a proof of P (p). this leaves us

with P ∨ false, which can be simplified further using or.intro_left,

isolating the P. this P can be proved using the previously assumed

proof of P (p). 

-/

example : ∀ (P : Prop), P ∧ true ↔ P := 

begin

  assume P,

  apply iff.intro _ _,

   

  assume pandtrue,

  apply and.elim_left pandtrue,



  assume p,

  apply and.intro,

  exact p,

  apply true.intro,

end

/-

we first assume P, an arbiturary propisition. 

afterwards, we utilize iff.intro, which splits the

propisition into two parts, back and forth.



after the split we are left with two main

goals to prove: P ∧ true → P and P → P ∧ true. 



for the first goal we assume a proof or P ∧ true (pandtrue).

what remains is P, which can be proved using and.intro_left on 

pandtrue, which isolates a proof of P. 



for the second goal we assume a proof of P (p). what remains is 

P ∧ true, which can be further broken down using and.intro. 

now, we just individually prove each side of the statement. 

we can prove P using the previously assumed proof of P (p) and

we can prove true by just using the introductary rule of true, 

meaning that true is always true. this completes the proof.

-/

example : ∀ (P : Prop), P ∧ false ↔ false := 

begin

  assume P,

  apply iff.intro _ _,



  assume pandfalse,

  apply and.elim_right pandfalse,



  assume f,

  cases f,

end



/-

we first assume P, an arbiturary propisition. 

afterwards, we utilize iff.intro, which splits the

propisition into two parts, back and forth.



after the split, we are left with two goals to

prove: P ∧ false → false and false → P ∧ false.



in order to prove the first goal, we first assume a proof 

of P ∧ false (pandfalse). what remains is false, which can

be proved using the and.elim_right rule on the pandfalse

proof. this isolates a proof of false and therefore completes 

the goal.



in order to prove the second goal, we begin by assuming a proof of

false, and then using cases on this assumption to prove that

there exists no possible cases, thereby completing the goal.

-/