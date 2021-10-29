import data.set

/-
CS2120 F21 HW5

The goals of this assignment are to give you
practice with proofs of propositions that use
existential quantificaton, and to develop your
understanding of formal and informal proofs in
set theory.
-/

/-
PART I: EXISTENTIAL QUANTIFICATION.
-/

/-
To start, suppose that α and β are arbitrary
types, and p and q are predicates on values
of these types: α and β, respectively.
-/

axioms 
  (α β : Type)    -- data types
  (p : α → Prop)  -- predicates
  (q : β → Prop)

/-
In this context complete the following tasks:

(1) Write a fluent English-language statement
of the proposition to be proved. 


(2) Provide a formal proof of the proposition.

--

(3) Write an informal proof of the proposition.
-/

-- here's the proposition
example : 
  (∃ (f : α → β), ∀ (a : α), p a → q (f a)) →
  (∃ (a : α), p a) → 
  (∃ (b : β), q b) := 



/-
What does this propositon say? Explain it in
plain English. Here's a start: "If there's a 
function that maps/takes every α value that ... 
-- your completed English rendition here:
-/

/-
if there exists a function, f, which states that for all values of a,
α, implies β, and that the propisition q (f a) is true if p a, this implies 
that there exists a value a of type α which has property p, which implies 
that there is a b of type β which has property q. 
-/

-- Give your formal proof here
begin
  assume a,
  assume b,
  cases a,
  cases b,
  apply exists.intro (a_w b_w),
  exact (a_h b_w b_h),
end

/- informal proof
assume all parts of the propisition. using cases,
break that propisition down to its individual elements. 
using these parts, we can use exists intro and feed it
our proofs of the existence of a value b : β because
we have a proof of α and a proof of α → β. from here,
we need to prove that there exists a_w and b_w with property
q, which we can prove by exacting the previously assumed values
from the original propisition.


-/

  

