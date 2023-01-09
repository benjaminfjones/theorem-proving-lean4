variable {p : Prop}
variable {q : Prop}

-- given a value in `p`, exhibit a function that takes a `q` and returns a `p`.
theorem t1 : p → (q → p) := fun (vp : p) => (fun (_vq : q) => vp)
#print t1  -- fun {p q} vp _vq => vp

theorem t1_alt : p → q → p :=
  fun hp : p =>
  fun _hq : q =>
  show p from hp
#print t1_alt

theorem t1_alt2 (hp : p) (_hq : q) : p := hp
#print t1_alt2

axiom hp : p

/- Apply theorem t1 -/
theorem t2 : q → p := t1 hp

/-
section unsound
  axiom unsound : False
  theorem one_eq_zero : 1 = 0 := False.elim unsound
end unsound

#check unsound  -- unsoundness escapes the section!
-/

variable (p q r s : Prop)
theorem compose (h₁ : q → r) (h₂ : p → q) (hp : p) : r :=
  h₁ (h₂ hp)

theorem compose_alt (h₁ : q → r) (h₂ : p → q) : p → r :=
  fun hp : p =>
  show r from h₁ (h₂ hp)

-- p → q and ¬ q implies ¬ p
example (hpq: p → q) (hnq: ¬ q) : ¬ p :=
  fun hp : p => show False from hnq (hpq hp)

-- ex falso
example (hp : p) (hnp : ¬ p) : q :=
  show q from False.elim (hnp hp)

example (hp : p) (hnp : ¬ p) : q := absurd hp hnp
#check absurd  -- absurd.{v} {a : Prop} {b : Sort v} (h₁ : a) (h₂ : ¬a) : b


-- canonical proof of True
example (_t : True) := True.intro

-- logical equivalence

theorem and_swap : p ∧ q ↔ q ∧ p :=
  Iff.intro
    -- left => right
    (fun h : p ∧ q =>
     show q ∧ p from And.intro (And.right h) (And.left h))
    -- right => left
    (fun h : q ∧ p =>
     show p ∧ q from And.intro (And.right h) (And.left h))

#check and_swap p q    -- p ∧ q ↔ q ∧ p

-- compare to and_commutative.lean proof
example (h : p ∧ q) : q ∧ p := Iff.mp (and_swap p q) h

-- using anonymous constructors for structural types `Iff` and `And`
theorem and_swap_alt : p ∧ q ↔ q ∧ p :=
  ⟨ fun h => ⟨h.right, h.left⟩, fun h => ⟨h.right, h.left⟩ ⟩

example (h : p ∧ q) : q ∧ p := (and_swap p q).mp h
#check Iff.mp  -- Iff.mp {a b : Prop} (self : a ↔ b) (a✝ : a) : b

/-
 - Exercises: https://leanprover.github.io/theorem_proving_in_lean4/propositions_and_proofs.html
 -/

 section exercises
 variable (p q r : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p :=
  Iff.intro
    (fun (hpq : p ∧ q) => And.intro hpq.right hpq.left)
    (fun (hqp : q ∧ p) => And.intro hqp.right hqp.left)
example : p ∨ q ↔ q ∨ p :=
  Iff.intro
    (fun (hpq : p ∨ q) =>
      Or.elim hpq
        (fun hp : p => Or.inr hp)
        (fun hq : q => Or.inl hq))
    (fun (hqp : q ∨ p) =>
      Or.elim hqp
        (fun hq : q => Or.inr hq)
        (fun hp : p => Or.inl hp))

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  Iff.intro
    (fun hpqr =>
      have hr : r := hpqr.right
      have hpq : p ∧ q := hpqr.left
      ⟨hpq.left, hpq.right, hr⟩)
    (fun hpqr =>
      have hp : p := hpqr.left
      have hqr : q ∧ r := hpqr.right
      ⟨⟨hp, hqr.left⟩, hqr.right⟩)
example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := sorry

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := sorry
example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := sorry

-- De Morgan's Law
theorem de_morgan_1 : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
  Iff.intro
    (fun hnpoq : (p ∨ q → False) =>
      have hnp : ¬p := (fun hp: p => hnpoq (Or.inl hp))
      have hnq : ¬q := (fun hq: q => hnpoq (Or.inr hq))
      ⟨hnp, hnq⟩)
    (fun hnpnq : ¬p ∧ ¬q =>
      -- use partially applied And.left/And.right
      fun hpoq : p ∨ q => Or.elim hpoq hnpnq.left hnpnq.right)
theorem de_morgan_2 : ¬(p ∧ q) ↔ (¬p ∨ ¬q) := sorry

-- other properties
theorem pq_imply_r : (p → (q → r)) ↔ (p ∧ q → r) := sorry
#check @pq_imply_r
theorem pq_imply_false : (p → ¬q) ↔ ¬(p ∧ q) := @pq_imply_r p q False
#check pq_imply_false
#check Iff.mp
#check Iff.mp (@pq_imply_false p q)
-- use pq_imply_false and De Morgan to prove this alternate tautology
example : (p → ¬q) ↔ ¬p ∨ ¬q :=
  Iff.intro
    (fun lhs : (p → ¬q) =>
      have hnpq : ¬(p ∧ q) := (Iff.mp (@pq_imply_false p q)) lhs
      show (¬p ∨ ¬q) from (Iff.mp (@de_morgan_2 p q) hnpq))
    (fun rhs : ¬p ∨ ¬q =>
      have hnpaq : ¬ (p ∧ q) := (Iff.mpr (@de_morgan_2 p q)) rhs
      fun hp : p =>
      fun hq : q => hnpaq ⟨hp, hq⟩)


example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := sorry

example : ¬p ∨ ¬q → ¬(p ∧ q) := sorry
example : ¬(p ∧ ¬p) := sorry
example : p ∧ ¬q → ¬(p → q) := sorry
example : ¬p → (p → q) := sorry
example : (¬p ∨ q) → (p → q) := sorry
example : p ∨ False ↔ p := sorry
example : p ∧ False ↔ False := sorry
example : (p → q) → (¬q → ¬p) := sorry

end exercises