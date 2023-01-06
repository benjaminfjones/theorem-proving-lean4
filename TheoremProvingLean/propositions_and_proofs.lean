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

-- Note: stopped at Auxilliary Subgoals