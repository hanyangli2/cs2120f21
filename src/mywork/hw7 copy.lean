import data.set
import tactic.ring

namespace relation

-- PRELIMINARY SETUP

/-
Preliminary set up. For the rest of this file,
we specify an arbitrary binary relation, r, on
an arbitrary type, β, as a two-place predicate, 
with infix notation x ≺ y for (r x y). One can
pronounce these expressions in English as "x is
related to y".
-/
variables {α β : Type}  (r : β → β → Prop)
local infix `≺` : 50 := r  


/-
The default Lean libraries are missing definitions
for the assympetric property of relations and for
the notion of a powerset. We define these terms for
use in the rest of this file.
-/
def asymmetric := ∀ ⦃x y⦄, x ≺ y → ¬ y ≺ x
def powerset (s : set β) := { s' | s' ⊆ s}


-- PROBLEMS

/- 
#1: Give both a formal and an English-language proof. Then
answer the question, is the proposition true if you remove
the first condition, that β is inhabited? Briefly explain
your answer (in English).
-/
example : (∃ (b : β), true) → asymmetric r → ¬reflexive r :=
begin
  assume h,
  cases h,
  unfold asymmetric reflexive,
  assume h,
  assume k,
  have a := k h_w,
  have b := h a,
  contradiction,
end

/-
English Language Proof

The propisition to be proved here is that if something
is asymmetric, then it cannot be reflexive. The first
step is to assume that there exists a value b of type
β.  

After this, I unfolded the definitions of asymmetric and 
reflexive, making it so that so that we can solve it 
in lean's language.

After this we are left with:
∀ ⦃x y : β⦄, r x y → ¬r y x) → (¬∀ (x : β), r x x). 

To prove this, we assume both parts of this statement. 
Using these two proofs and our proof that there exists
a value of type β, we feed our proof of beta into
these proofs and get specific examples pretaining to 
the proofs. 

The proofs we create are: 
a: r h_w h_w
b: ¬r h_w h_w

These two proofs clearly contradict, so we can complete
this proof using contradiction. 
-/

/-
Is the proposition true if you remove
the first condition, that β is inhabited?

No, because then we have no proof that
there exists a value of type β. 
-/


/-
#2. Logic, like programming, is subtle. It's very easy for humans
to miss subtle corner cases. As an example, today I ran across
a problem in a textbook by Paul Traiger, a professor emeritus
of philosophy and cognitive science at Occidental College. He
asks students to prove that if a relation is both transitive and 
reflexive that it cannot be anti-symmetric. See the question at
the very bottom of the page here:
https://sites.oxy.edu/traiger/logic/exercises/chapter13/properties_of_relations_exercise.html

Is the conjecture actually logically valid? If not, what condition 
needs to be added to make it so? Try prove this/his version of the
conjecture, as articulated slightly differently below. If you get
stuck, then you need to figure out an additional condition that needs 
to be added as a premise to make the proposition true. In that case,
add the premise and then show that the updated conjecture is true.
-/
example :(∃ (b : β), true) → transitive r → reflexive r → ¬ asymmetric r :=
begin
  unfold transitive reflexive asymmetric,
  assume b trans refl,
  assume assym,
  cases b,
  have rbb := refl b_w,
  have nrbb := assym rbb,
  contradiction,
end

/-
#3: Prove that the subset relation on the powerset of any
set, s, is antisymmetric. Formally state and prove, and
then give an informal proof of, this proposition.
-/
example : ∀ (s : set β) 
            (s1 s2 ∈ powerset s), 
            s1 ⊆ s2 → 
            s2 ⊆ s1 → 
            s1 = s2 :=
begin
  assume s s1 s2,
  assume s1ins s2ins,
  assume s1s2 s2s1,
  apply set.ext,
  assume x,
  split,
  
  assume xs1,
  have pf := s1s2 xs1,
  exact pf,

  assume xs2,
  have pf := s2s1 xs2,
  exact pf,
end

/-
In order to prove that if s1 is a subset of s2 and
s2 is a subset of s1, then they are equivalent,
the first step is to assume the sets, the propisition that
they are both under the powerset s, and that they are subsets 
of one another. 

We then apply set.ext to transform the = into ↔. 

From here, we assume that there exists a value x and
then split it into forwards and backwards. 

First we assume that x is in s1 and feed it into the 
proof that s1 is a subset of s2. This finishes the forwards proof. 

The backwards proof is the same principle just with s2 rather
than s1.


-/


/-
Given two natural numbers, n and m, we will say that m divides n
if there is a natural number, k, such that n = k*m. Here's a formal
definition of this relation.
-/
def divides (m n : ℕ) := ∃ k, n = k * m


/- 
#4: Formally and informally state and prove each of the following
propositions. Remember that the ring tactic is useful for producing
proofs of simple algebraic equalities involving + and *. You can use
the phrase, "by basic algebra" when translating the use of this tactic
into English. (Or if you wanted to be truly Hobbit-like you could say 
"by the ring axioms!")
-/

-- A: For any n, 1 divides n.
example : ∀ n, divides 1 n :=
begin
  assume a,
  unfold divides,
  apply exists.intro a,
  ring,
end

/-
In order to prove that for any n, 1 divides n, the
first step is to assume that there exists ℕ.

Then, we unfold the definiton of divides so 
that we can solve it in the lean language. 

From here, we need to prove:
∃ (k : ℕ), a = k * 1

To do this, we need to assume that there exists 
a value k. Because we can choose which value
exists, we choose for k to equal a, because
this is the value that makes the statement true.

After replacing k with a, we can end
the proof by using basic algebra.
-/

-- B. For any n, n divides n
example : ∀ n, divides n n :=
begin
  assume a,
  unfold divides,
  apply exists.intro 1,
  ring,
end

/-
In order to prove that for any n, n divides n, the
first step is to assume that there exists ℕ.

Then, we unfold the definiton of divides so 
that we can solve it in the lean language. 

From here, we need to prove:
∃ (k : ℕ), a = k * a

To do this, we need to assume that there exists 
a value k. Because we can choose which value
exists, we choose for k to equal 1, because
this is the value that makes the statement true.

After replacing k with 1, we can end
the proof by using basic algebra.
-/

-- #C. prove that divides is reflexive 
example : reflexive divides :=
begin
  assume a,
  unfold reflexive divides,
  apply exists.intro 1,
  ring,
end 

/-
In order to prove that for any divides is 
reflexive, we need to first asssume ℕ.

Then, we unfold the definiton of divides
and reflexive so that we can solve it in 
the lean language. 

From here, we need to prove:
∃ (k : ℕ), a = k * a

To do this, we need to assume that there exists 
a value k. Because we can choose which value
exists, we choose for k to equal 1, because
this is the value that makes the statement true.

After replacing k with 1, we can end
the proof by using basic algebra.
-/

-- #D. prove that divides is transitive
example : transitive divides :=
begin
  unfold transitive divides,
  assume h n z,
  assume a,
  assume b,
  cases a,
  cases b,

  rw a_h at b_h,

  apply exists.intro (b_w * (a_w)),
  rw b_h,
  ring,  
end 

/-
In order to prove that divides is transitive,
the first step is to unfold transitive and divides. 

After this, we assume all values of type ℕ as well as
two of the transitive propisitions. 

We apply cases to both the propisitions to show that
there are values that exist for these propisitions. 

After this, we subsitute n in b_h with the 
our proof of a_h, which states that:

n = a_w * h. 

With our new proof of b_h, we can state that 
there exists a value k of b_w * a_w. 

This matches with the proof we need to prove. 

-/

/- 
E. Is divides symmetric? if yes, give a proof, otherwise 
give a counterexample and a brief explanation to show that 
it's not. 

divides is not symmetric because a/b is not the same as b/a.

-/


/- 
#F. Prove that divides is antisymmetric. 
-/
example : anti_symmetric divides := 
begin
  unfold anti_symmetric divides,
  assume x,
  assume y,
  assume a,
  assume b,
  cases a,
  cases b,
  rw a_h,
  have z : a_w = 1 := sorry,
  rw z,
  ring,
end

/-
In order to prove that divides is anti_symmetric, we first
need to unfold the definitions of anti_symmetric and
divides. 

We then assume all values of type ℕ and the two propisitions. 

We then apply cases on the two propisitions to show that there
exists a value k of type ℕ. 

We then rewrite the proof we currently we have with 
the proof of our definition of y = a_w * x. 

From here, we can assume that there exists a value a_w of
1. 

With this, we have the proof that a_w = 1 * a_w, which we can just
assume to be true.
-/


/- #4
Prove the following propositions. Remember that
throughout this file, each definition implicitly
includes β as a type and r as an arbitrary binary 
relation on β. In addition to formal proofs, give
an English language proof of the last of the three
problems.
-/

-- A
example : asymmetric r → irreflexive r :=
begin
  unfold asymmetric irreflexive,
  assume h,
  assume a,
  assume b,
  have notb := h b,
  contradiction,
end

/-
In order to prove that if r is asymmetric, then r is 
irreflexive, the first step is to unfold the
definitions of assymetric and irreflexive. 

Once unfolded, we assume the propisition
that for all values, r x y → ¬ r y x 
as well as r x x being true (b). 

We then feed b into our propisition,
which returns the value ¬ r x x in
order to create a contradiction. 
-/

-- B
example : irreflexive r → transitive r → asymmetric r :=
begin
  unfold irreflexive transitive asymmetric,
  intros,
  assume ryx,
  have h := ᾰ_1 ᾰ_2 ryx,
  have notraa := ᾰ x,
  contradiction,
end

/-
In order to prove the irreflexive implies transitive implies asymmetric,
the first step is to unfold all values.

We then assume all values. This includes the propisitions,
the values of type β, and the proofs of ryx and rxy. 

We first feed ryx and rxy into the transitive property, returing 
rxx. 

We then feed rxx into irreflexive, which returns ¬rxx. 

This creates a contradiction.
-/

-- C
example : transitive r → ¬ symmetric r → ¬ irreflexive r :=
begin
  unfold transitive symmetric irreflexive,
  assume a b c,
end

/-
This one is not solvable. 
-/

end relation
