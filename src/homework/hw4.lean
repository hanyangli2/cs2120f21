-- 1
example : 0 ≠ 1 :=
begin
  -- ¬ (0 = 1)
  -- (0 = 1) → false
  assume h,
  cases h,
end


-- 2
example : 0 ≠ 0 → 2 = 3 :=
begin
  assume h,
  have f := h (eq.refl 0),
  exact false.elim (f),
end

-- 3
example : ∀ (P : Prop), P → ¬¬P :=
begin
  assume P,
  assume (p : P),
  assume h,
  have f := h p,
  exact f,
end 

-- We might need classical (vs constructive) reasoning 
#check classical.em
open classical
#check em

/-
axiom em : ∀ (p : Prop), p ∨ ¬p

This is the famous and historically controversial
"law" (now axiom) of the excluded middle. It's is
a key to proving many intuitive theorems in logic
and mathematics. But it also leads to giving up on
having evidence *why* something is either true or
not true, in that you no longer need a proof of 
either P or of ¬P to have a proof of P ∨ ¬P.
-/

-- 4
theorem neg_elim : ∀ (P : Prop), ¬¬P → P :=
begin
  assume P,
  assume h,
  have pornp := classical.em P,
  cases pornp with p pn,
  assumption,
  contradiction,
end

-- 5
theorem demorgan_1 : ∀ (P Q : Prop), ¬ (P ∧ Q) ↔ ¬ P ∨ ¬ Q :=
begin
  assume P Q,
  apply iff.intro _ _,

  assume h,
  have p := em P,
  have q := em Q,
  cases p,
  cases q,
  
  have pandq := and.intro p q,
  contradiction,

  apply or.intro_right,
  exact q,

  apply or.intro_left,
  exact p,

  assume npornq,

  assume h,
  apply and.elim h,

  assume p,
  assume q,

  cases npornq,  

  contradiction,

  contradiction,
end 


-- 6
theorem demorgan_2 : ∀ (P Q : Prop), ¬ (P ∨ Q) → ¬P ∧ ¬Q :=
begin
  assume P Q,
  assume h,

  have pornp := em P,
  have qornq := em Q,

  cases pornp,
  cases qornq,

  have pq := and.intro pornp qornq,
  apply and.intro,


  --why does contradiction not work here?

end


-- 7
theorem disappearing_opposite : 
  ∀ (P Q : Prop), P ∨ ¬P ∧ Q ↔ P ∨ Q := 
begin
  assume P Q, 
  apply iff.intro _ _,
  
  assume h,
  cases h with p npq,

  apply or.intro_left,
  exact p,

  have pfQ := and.elim_right npq,
  apply or.intro_right,
  exact pfQ,

  assume porq,
  cases porq,

  apply or.intro_left,
  apply porq,

  have pornp := em P,
  cases pornp,

  apply or.intro_left,
  exact pornp,

  apply or.intro_right,

  apply and.intro,
  exact pornp,
  exact porq,

end


-- 8
theorem distrib_and_or : 
  ∀ (P Q R: Prop), (P ∨ Q) ∧ (P ∨ R) ↔
                    P ∨ (Q ∧ R) :=
begin
  assume P Q R,
  apply iff.intro _ _,

  assume h,
  cases h,

  cases h_left,
  cases h_right,

  apply or.intro_left,
  apply h_left,

  apply or.intro_left,
  apply h_left,
  
  cases h_right,

  apply or.intro_left,

  exact h_right,

  apply or.intro_right,

  have qr := and.intro h_left h_right,
  exact qr,

  assume h,
  
  cases h,

  apply and.intro,

  apply or.intro_left,
  exact h,

  apply or.intro_left,
  exact h,

  apply and.elim h,

  assume q,
  assume r,

  apply and.intro,

  apply or.intro_right,
  exact q,

  apply or.intro_right,
  exact r,
end

-- remember or is right associative
-- you need this to know what the lefts and rights are
-- 9
theorem distrib_and_or_foil : 
  ∀ (P Q R S : Prop),
  (P ∨ Q) ∧ (R ∨ S) ↔
  (P ∧ R) ∨ (P ∧ S) ∨ (Q ∧ R) ∨ (Q ∧ S) :=
begin
  assume P Q R S,
  apply iff.intro _ _,

  assume h,
  cases h,

  cases h_left,
  cases h_right,

  have pr := and.intro h_left h_right, 
  
  apply or.intro_left,
  exact pr,

  have ps := and.intro h_left h_right,
  apply or.intro_right,
  apply or.intro_left,
  exact ps,

  cases h_right,

  have qr := and.intro h_left h_right,
  apply or.intro_right,
  apply or.intro_right,
  apply or.intro_left,
  exact qr,

  have qs := and.intro h_left h_right,
  apply or.intro_right,
  apply or.intro_right,
  apply or.intro_right,
  exact qs,

  assume h,
  cases h,
  
  apply and.intro,

  have p := and.elim_left h,
  apply or.intro_left,
  apply p,

  have r := and.elim_right h,
  apply or.intro_left,
  exact r,

  cases h,
  apply and.intro,

  have p := and.elim_left h,
  apply or.intro_left,
  exact p,

  have s := and.elim_right h,
  apply or.intro_right,
  exact s,

  cases h,
  apply and.intro,
  
  have q := and.elim_left h,
  apply or.intro_right,
  exact q,

  have r := and.elim_right h,
  apply or.intro_left,
  exact r,

  apply and.intro,

  have q := and.elim_left h,
  apply or.intro_right,
  exact q,

  have s := and.elim_right h,
  apply or.intro_right,
  exact s,
end


/- 10
Formally state and prove the proposition that
not every natural number is equal to zero.
-/
lemma not_all_nats_are_zero : (∀ n : ℕ, n = 0) → false :=
begin
  assume h,
  have x := h 3,
  cases x,
end 

-- 11. equivalence of P→Q and (¬P∨Q)
example : ∀ (P Q : Prop), (P → Q) ↔ (¬P ∨ Q) :=
begin
  assume P Q,
  apply iff.intro _ _,

  assume h,

  have pornp := em P,
  cases pornp,

  have q := h pornp,
  

  apply or.intro_right,
  exact q,

  apply or.intro_left,
  exact pornp,

  assume h,
  assume p,

  cases h,

  contradiction,

  exact h,


  
end

-- 12
example : ∀ (P Q : Prop), (P → Q) → (¬ Q → ¬ P) :=
begin
  assume P Q,
  assume pq,

  have pornp := em P,
  cases pornp,

  have q := pq pornp,
  contradiction,

  assume nq,

  exact pornp,
end

-- 13
example : ∀ (P Q : Prop), ( ¬P → ¬Q) → (Q → P) :=
begin
  assume P Q,
  assume h,

  assume q,

  have pornp := em P,
  cases pornp,
  exact pornp,

  have nq := h pornp,
  contradiction,
end

