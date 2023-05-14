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

section assume_p
axiom hp : p
/- Apply theorem t1 -/
theorem t2 : q → p := t1 hp
end assume_p

/-
section unsound
  axiom unsound : False
  theorem one_eq_zero : 1 = 0 := False.elim unsound
end unsound

#check unsound  -- unsoundness escapes the section!
-/

/-
Composition in dependent type theory corresponds to:
"If q implies r and p implies q, then p implies r"
in propositional logic.
-/
variable (p q r s : Prop)
theorem compose (h₁ : q → r) (h₂ : p → q) (hp : p) : r :=
  h₁ (h₂ hp)

theorem compose_alt (h₁ : q → r) (h₂ : p → q) : p → r :=
  fun hp : p =>
  show r from h₁ (h₂ hp)
#check compose_alt

-- p → q and ¬ q implies ¬ p
example (hpq: p → q) (hnq: ¬ q) : ¬ p :=
  fun hp : p => show False from hnq (hpq hp)

-- ex falso: p → ¬ p → q
-- or: p → (p → False) → q
example (hp : p) (hnp : ¬ p) : q :=
  show q from False.elim (hnp hp)

example (hp : p) (hnp : ¬ p) : q := absurd hp hnp
#check absurd  -- absurd.{v} {a : Prop} {b : Sort v} (h₁ : a) (h₂ : ¬a) : b

-- canonical proof of True
example (_t : True) := True.intro
#check True   -- constant of type Prop
#check False  -- constant of type Prop

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

-- By Curry-Howard, `and_swap` corresponds to `prod_swap` that swaps
-- the elements of a pair. (_, _) is introduction, and _.i is elimination
def prod_swap {α β : Type} (t : α × β) : (β × α) :=
  (t.2, t.1)
#check prod_swap (1, 2)
#eval prod_swap (1, 2)

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
example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
  Iff.intro
    (fun hpqr =>
      Or.elim hpqr
        (fun hpq => Or.elim hpq
          (fun hp => Or.inl hp)
          (fun hq => Or.inr (Or.inl hq))
        )
        (fun hr => Or.inr (Or.inr hr))
    )
    (fun hpqr =>
      Or.elim hpqr
        (fun hp => Or.inl (Or.inl hp))
        (fun hqr => Or.elim hqr
          (fun hq => Or.inl (Or.inr hq))
          (fun hr => Or.inr hr)
        )
    )

-- distributivity
-- example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := sorry
-- example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := sorry

-- Some useful validities
theorem pq_imply_r : (p → (q → r)) ↔ (p ∧ q → r) := sorry
#check @pq_imply_r
theorem pq_imply_false : (p → ¬q) ↔ ¬(p ∧ q) := @pq_imply_r p q False
#check pq_imply_false
#check Iff.mp
#check Iff.mp (@pq_imply_false p q)

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

section de_morgan_not_and
  open Classical
  -- Note: → requires classical reasoning!
  --       ← does not
  theorem de_morgan_2 : ¬(p ∧ q) ↔ (¬p ∨ ¬q) :=
    Iff.intro
      (fun hnpaq : ¬(p ∧ q) =>
        have hpinq : p → ¬q  := (pq_imply_false _ _).mpr hnpaq
        byCases
          (fun h : p => Or.inr (hpinq h))
          (fun h : ¬p => Or.inl h))
      (fun hnpnq : ¬p ∨ ¬q =>
        fun hpq : p ∧ q =>
          Or.elim hnpnq
            (fun hnp : ¬p => absurd hpq.left hnp)
            (fun hnq : ¬q => absurd hpq.right hnq))
end de_morgan_not_and

theorem de_morgan_2_rhs : ¬p ∨ ¬q → ¬(p ∧ q) :=
  fun hnpnq : ¬p ∨ ¬q =>
    fun hpq : p ∧ q =>
      Or.elim hnpnq
        (fun hnp : ¬p => absurd hpq.left hnp)
        (fun hnq : ¬q => absurd hpq.right hnq)

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

-- TODO:
-- example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := sorry
-- example : p ∧ ¬q → ¬(p → q) := sorry
-- example : ¬p → (p → q) := sorry
-- example : (¬p ∨ q) → (p → q) := sorry
-- example : p ∨ False ↔ p := sorry
-- example : p ∧ False ↔ False := sorry
-- example : (p → q) → (¬q → ¬p) := sorry

-- Exercise: prove double negation elimination from excluded middle
section classical
open Classical
#check em
theorem dne {p : Prop} (h : ¬¬p) : p :=
  Or.elim (em p)
    (fun hp : p => hp)
    (fun hnp : ¬p => absurd hnp h)
end classical

-- Exercise: constructively prove excluded middle, assuming
-- double negation elimination
section alt_classical
  variable (p q : Prop)
  axiom assumed_dne (h : ¬¬p) : p
  #check @assumed_dne q

  -- an absurdity from nothing
  theorem not_both : ¬(p ∧ ¬p) :=
    fun hpnp => absurd hpnp.left hpnp.right

  theorem de_morgan_2_self_lhs {r : Prop} : ¬(r ∧ ¬r) → (¬r ∨ ¬¬r) := sorry
  #check @de_morgan_2_self_lhs (¬p)

  -- use DeMorgan + absurdity
  -- TODO: de_morgan_2 requires classical reasoning, making this proof of
  -- `em` circular! Try using specialization de_morgan_2_self, proved with
  -- dne
  theorem neither_nor : ¬p ∨ ¬¬p :=
     have hpp : ¬(p ∧ ¬p) := @not_both p
     show ¬p ∨ ¬¬p from (@de_morgan_2_self_lhs _ hpp)

  -- use assumed_dne and previous theorems to get `em`
  theorem em {p : Prop} : p ∨ ¬ p :=
    have (hnn : ¬p ∨ ¬¬p) := neither_nor p
    Or.elim hnn
      (fun hnp => Or.inr hnp)
      (fun hnnp => Or.inl (assumed_dne p hnnp))
end alt_classical

end exercises