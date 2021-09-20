/-
Theorem: Equality is symmetric

Proof: First assume that T is a value of any arbiturary type. 
We have to objects x and y. 
What remains to be shown is that if x = y, then y = x. 
To prove this, we'll assume the premise, that x = y and in this context what remains to be proved is y = x. 
By the axiom of subsititubility of equals, and using the fact that x = y,
we can rewrite x in the goal as y, yielding y = y as our new proof goal. 
But this is true by the axiom of reflexibility. QED
-/

theorem eq_symm : 
  ∀ (T : Type) (x y : T), x = y → y = x :=
  begin
   assume (T : Type), 
   assume(x y : T),
   assume(e : x = y),
   rw e,
  end


  /-
  Prove that equality is transitive. 
  -/

  theorem eq_trans : 
    ∀ (T : Type) (x y z : T), x = y → y = z → x = z :=
    begin
      assume(T : Type),
      assume(x y z : T),
      assume(e : x = y),
      assume(e1 : y = z),
      rw e1,
      rw e2,
      exact e2,
    end