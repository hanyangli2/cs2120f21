
/-
A simple predicate.
-/
def ev (n : ℕ) : Prop := n%2=0


/-
Introduction rule for exists
-/
example : exists (n : ℕ), ev n :=
begin
end

example : exists n, ev n := _


example : exists (a b c : ℕ), a*a + b*c = c*c := 
_


example : ∀ (n : ℕ), ∃ (m : ℕ), n = 2 * m :=
begin
  intros,
  apply exists.intro _,
end

example : ∀ (m : ℕ), ∃ (n : ℕ), n = 2 * m :=
begin
  intros,
  apply exists.intro (2*m),
end

example : (∃ (n : nat), ev n) → true :=
begin
assume h,
cases h with v pf,
intros,
end


def pythagorean_triple (a b c : ℕ) : Prop :=
  a * a + b * b = c * c

example: ∃ (a b c : ℕ), pythagorean_triple a b c :=

begin
  unfold pythagorean_triple,
  apply eq.refl,
end
