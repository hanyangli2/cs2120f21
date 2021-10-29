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




