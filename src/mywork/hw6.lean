import data.set

/-
Exercise: Prove that for any set, L, L ∩ L = L.
-/

example : ∀ (α : Type) (L : set α), L ∩ L = L :=
begin
  intros α L,
  apply set.ext _,
  assume x,
  apply iff.intro _ _,

  assume h,
  cases h,
  apply h_left,

  assume h,
  apply and.intro h h,
end


/-
Exercise: Give a formal statement and proof, then an 
English language proof, that the union operator on 
sets is commutative.
-/

example : ∀ (α : Type) (L X : set α), L ∪ X = X ∪ L :=
begin
  intros α L X,
  apply set.ext _,
  assume x,
  apply iff.intro _ _,

  assume h,
  cases h,
  apply or.intro_right,
  exact h,
  apply or.intro_left,
  exact h,

  assume h,
  cases h,
  apply or.intro_right,
  exact h,
  apply or.intro_left,
  exact h,
end

/- ENGLISH LANGUAGE PROOF
The first step is to assume type α, 
and the sets L and X of type α.

Next, set.ext is used to the = to an ↔, making it
a familiar proof.

Then, the value x of type α is assumed to exist 
and iff.intro is applied to split the ↔ into 
a forward and backwards proof.

From here, we need to prove that x is in the
union of set L and set X. Another way of thinking
about this can be x is in set X or set L. 

Because we have a proof of x ∈ L ∪ X, we can use cases 
to split it into seperate proofs of x ∈ L and x ∈ X. 

From here, it becomes simple as we can split what we need 
to prove using or.intro and then exacting appropriately. 

The same method can be used for the backwards proof.
-/

/-
Exercise: Prove that ⊆ is reflexive and transitive.
Give a formal statement, a formal proof, and an English
language (informal) proof of this fact.
-/

example : ∀ (α : Type) (A: set α), A ⊆ A ∧ ∀ (α : Type) (A B C : set α), A ⊆ B → B ⊆ C → A ⊆ C :=
begin
  intros α A,
  split,
  assume x,
  assume h,
  exact h,

  intros α A B C,
  assume h,
  assume c,
  assume x,
  assume e,

  have xinB := h e,
  have xinC := c xinB,
  exact xinC,
end

/- ENGLISH LANGUAGE PROOF
This proof is a combination of reflexivity and transitive.
These two proofs are connected by an ∧. They are proved
seperately one at a time using split.

The first step is to prove reflexivity is to
assume type α, and the set A of type α.
The first section of the proposition that
is being proved is reflexivity, or A ⊆ A.

To prove this, a value of type α is first assumed.
Once assumed, the proof needed to be proved is one
of simple reflexivity, x ∈ A → x ∈ A. We just assume 
the first half and then exact it to prove this.axioms

The second proof is the transitive property.
To begin, type α and A B C are assumed.
All proofs are assumed for the implications,
giving us proofs that A ⊆ B and B ⊆ C, as well
as x ∈ A. From here, we just create proofs based 
on previously established proofs. Because we know 
that x is in A, we know that x is in B, and therefore
we know x is C, thus proving that x is in A and B,
proving the transivity of ⊆.
-/

/-
Exercise: Prove that ∪ and ∩ are associative.
Give a formal statement, a formal proof, and an 
English language (informal) proof of this fact.
-/

example :  ∀ (α : Type) (A B C: set α), A ∩ (B ∩ C) = (A ∩ B) ∩ C ∧ A ∪ (B ∪ C) = (A ∪ B) ∪ C :=
begin
intros α A B C,
apply and.intro,
apply set.ext _,
assume h,
apply iff.intro _ _,

assume h,
cases h,
cases h_right,
apply and.intro,
apply and.intro,
exact h_left,
exact h_right_left,
exact h_right_right,

assume h,
apply and.intro,
cases h,
cases h_left,
exact h_left_left,
split,

cases h,
cases h_left,
exact h_left_right,

cases h,
cases h_left,
exact h_right,

apply set.ext _,
assume h,
apply iff.intro _ _,

assume h,
cases h,
apply or.intro_left,
apply or.intro_left,
exact h_1,

cases h_1,
apply or.intro_left,
apply or.intro_right,
exact h_1,

apply or.intro_right,
exact h_1,

assume h,
cases h,
cases h_1,
apply or.intro_left,
exact h_1,

apply or.intro_right,
apply or.intro_left,
exact h_1,

apply or.intro_right,
apply or.intro_right,
exact h_1,
end

/- ENGLISH LANGUAGE PROOF
This is a proof to prove that ∪ and ∩ are associative. 

This is proof is split into two parts, one for ∪ and 
one for ∩. These two proofs are split using and.intro. 

The first step is to assume type α, and the sets A, B, and C
of type α. set.ext is applied to transform the = to ↔ and
iff.intro is used to split the proof into two parts,
forwards and backwards. 

The statemet which needs to be proved now
is A ∩ (B ∩ C) → h ∈ A ∩ B ∩ C. We assume the
first half is true and now need to prove that it
implies the second half. 

The first step would be to simplify the proof we currently
have to state x can be in every single set, which
is true because the sets are connected by ∩. This can be
done with cases. Once we have proof that x is in every set,
we can exact these proofs accordingly. This proves the forward
direction. This same principle can be used for the
backwards direction. 

The next step is to prove that the associative property 
applies to ∪ as well. 

To begin, we apply set.ext once more to transform the
= to an ↔ and use iff.intro to split the proof forwards
and backwards. We assume the first half of the implication
is true and then prove the second half, h ∈ A ∪ B ∪ C. With
the proof we assumed, we apply cases onto it to prove
that the statement can be true for every element of it, making
the entirety of it to be true. This is done with cases. 
Once there are seperate proofs for each element of the 
∪ statement, we use or.intro to isolate to the specific proof
we need. This is repeated until the goal is accomplished.

-/

/-
Assignment: read (at least skim) the Sections 1 and 2 of 
the Wikipedia page on set identities: 
https://en.wikipedia.org/wiki/List_of_set_identities_and_relations 
There, , among *many* other facts, you will find definitions 
of left and right distributivity. To complete the remainder
of this assignment, you need to understand what it means for 
one operator to be left- (or right-) distributive over another. 
-/

/-
Exercise: Formally state and prove both formally and 
informally that ∩ is left-distributive over ∩.
-/

example : ∀ (α : Type) (A B C: set α), A ∩ (B ∩ C) = (A ∩ B) ∩ (A ∩ C) :=
begin
intros α A B C,
apply set.ext _,
assume x,
apply iff.intro _ _,

assume h,
apply and.intro,
cases h,
cases h_right,
apply and.intro h_left h_right_left,

cases h,
cases h_right,
apply and.intro h_left h_right_right,

assume h,
apply and.intro,
cases h,
cases h_left,
exact h_left_left,

cases h,
cases h_left,
cases h_right,
apply and.intro h_left_right h_right_right,
end

/- ENGLISH LANGUAGE PROOF
The first step is to assume type α, and the sets A, B, and C
of type α.

The proof that needs to be solved is 
A ∩ (B ∩ C) = (A ∩ B) ∩ (A ∩ C).

The first step is to transform the = to ↔ and
then apply iff.intro to seperate the proofs
forwards and backwards. 

For the forwards direction, the first step is to assume
the left side of the implication. With this proof,
we want to break down the proofs into three different
proofs proving that α can be in all of the sets. 
Using this, we can use and.intro and exact to prove that α exists
in every set. This is repeated for every proof until the
goal is reached.


-/

/-
Exercise: Formally state and prove both formally 
and informally that ∪ is left-distributive over ∩.
-/

example : ∀ (α : Type) (A B C: set α), A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) :=
begin
intros α A B C,
apply set.ext _,
assume x,
apply iff.intro _ _,

assume h,
apply and.intro,
cases h,
apply or.intro_left,
exact h,

cases h,
apply or.intro_right,
exact h_left,

cases h,
apply or.intro_left,
exact h,

cases h,
apply or.intro_right,
exact h_right,

assume h,
cases h,
cases h_left,
cases h_right,
apply or.intro_left,
exact h_left,

apply or.intro_left,
exact h_left,

cases h_right,
apply or.intro_left,
exact h_right,

apply or.intro_right,
apply and.intro h_left h_right,
end

/- ENGLISH LANGUAGE PROOF
The first step is to assume type α, and the sets A, B, and C
of type α.

The proof to be proved here is A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C). 
The first step is to transform the = to an ↔ and apply iff.intro. 

We assume the first half of the implication and then we need to 
prove the second half. But first, we have to break apart
the assumption into proofs we can exact. We do this
using cases. After fully breaking down the proof into individual
sections, we can break down what we need to prove using or.intro
and and.intro. From there, we can intuitively exact our proofs. 
We repeat this until the goal is accomplished. 
-/