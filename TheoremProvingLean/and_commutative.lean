variable (p q : Prop)
theorem and_commutative : p ∧ q → q ∧ p :=
  fun hypq : p ∧ q =>
  have hp : p := And.left hypq
  have hq : q := And.right hypq
  show q ∧ p from And.intro hq hp

-- one-line version of and_commutative
example (hpq : p ∧ q) : q ∧ p :=
  And.intro (And.right hpq) (And.left hpq)

-- using canonical inductive type And constructor implicitly
example (hpq : p ∧ q) : q ∧ p :=
  ⟨hpq.right, hpq.left⟩

-- Or introduction and elimination
--
-- Introduction: given a proof of `a` and any Prop `b`, you get a proof
-- of `a ∨ b`
#check Or.intro_left  -- {a : Prop} (b: Prop) (h : a) : a ∨ b
-- Elimination: given a proof of `a ∨ b` and a way to prove `c` from both
-- `a` and `b` individually, you get a proof of `c`.
#check Or.elim        -- {a b c : Prop} (h : a ∨ b) (left : a → c) (right : b → c) : c
theorem or_commutative : p \/ q -> q \/ p :=
  fun hypq : p ∨ q =>
  have right : p → q ∨ p := Or.intro_right q
  have left : q → q ∨ p := Or.intro_left p
  show q ∨ p from Or.elim hypq right left

-- one-line version of or_commutative
example (hpq : p ∨ q) : q ∨ p :=
  Or.elim hpq (Or.intro_right q) (Or.intro_left p)