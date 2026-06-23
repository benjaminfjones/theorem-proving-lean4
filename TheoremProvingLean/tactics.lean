section inaccessible_names
  -- unhygenic tactic keyword
  example : ∀ a b c : Nat, a = b → a = c → c = b := by unhygienic
    intros
    apply Eq.trans
    apply Eq.symm
    exact a_2
    exact a_1

  -- rename_i tactic to give names to inaccessible terms
  example : ∀ a b c d : Nat, a = b → a = d → a = c → c = b := by
    intros
    rename_i h1 _ h2
    apply Eq.trans
    apply Eq.symm
    exact h2
    exact h1

end inaccessible_names

section revert
  example (x y : Nat) (h : x = y) : y = x := by
    revert x  -- beings h along with into the goal
    intros
    apply Eq.symm
    assumption
end revert

-- generalize an expression replacing it by a fresh variable
example : 3 = 3 := by
  generalize 3 = x
  rfl

example : 2 + 3 = 5 := by
  generalize h : 3 = x
  rw [← h]



--
-- Combinations of Tactics
--

-- a fancy combination of tactics
example (p q r : Prop) (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r := by
  constructor <;>        -- 2 goals: p and q ∧ r
  (try constructor) <;>  -- fails on 1st goal, succeeds on 2nd
  assumption             -- succeeds on 1st goal, fails on 2nd

-- a different parallel tactic strategy
example (p q r : Prop) (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r := by
  constructor
  all_goals (try constructor)  -- try `constructor` on all open goals
                               -- after this there are 2 top-level goals, one with 2 sub-goals
  all_goals assumption         -- then try `assumption` on all open goals (even sub-goals)

--
-- Rewrite
--

-- rewrite at a hypothesis
example (f : Nat → Nat) (a : Nat) (h : a + 0 = 0) : f a = f 0 := by
  rw [Nat.add_zero] at h
  -- h : a = 0
  -- goal : f a = f 0
  rw [h]

-- rewriting data: Tuples α n := lists of length n
def Tuple (α : Type) (n : Nat) := { as : List α // as.length = n }

example (α : Type) (n : Nat) (h : n = 0) (t : Tuple α n) : Tuple α 0 := by
  rw [h] at t
  exact t

--
-- Cases
--

example (p q : Nat → Prop) : (∃ x, p x) → ∃ x, p x ∨ q x := by
  intro h
  cases h with
  | intro w hpw =>
    constructor
    apply Or.inl
    exact hpw  -- dispatches both the proof goal and unifies the Nat goal with `w` at once

-- using the `exists` tactic
example (p q : Nat → Prop) : (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x := by
  intro h
  cases h with
  | intro w hpw =>
    cases hpw with
    | intro px qx =>
      -- unifes the metavariable with `w` and constructs fills the proof hole automatically
      exists w  -- notation for `refine w; try trivial`
      -- exact Exists.intro w ⟨ qx, px ⟩

-- cases and tactics with product data
def swap_pair (α β : Type) : α × β → β × α := by
  intro p
  cases p with
  | mk fst snd =>
    constructor <;> assumption

-- cases and tactics with sum data
def swap_sum (α β : Type) : α ⊕ β → β ⊕ α := by
  intro sum
  cases sum with
  | inl x => apply Sum.inr; assumption
  | inr x => apply Sum.inl; assumption

-- cases on Nat; induction example
open Nat
example (P : Nat → Prop) (h₀ : P 0) (h₁ : ∀ n, P (succ n)) (m : Nat) : P m := by
  cases m with
  | zero    => assumption
  | succ m' => apply h₁

-- using `match` like cases, combined with `intro` -> intro match combo
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro
    | ⟨hp, Or.inl hq⟩ =>
      apply Or.inl; constructor <;> assumption
    | ⟨hp, Or.inr hr⟩ =>
      apply Or.inr; constructor <;> assumption
  . intro
    | Or.inl ⟨hp, hq⟩ =>
      constructor; assumption; apply Or.inl; assumption
    | Or.inr ⟨hp, hr⟩ =>
      constructor; assumption; apply Or.inr; assumption


--
-- Simplify
--

section simplify_examples

  attribute [local simp] Nat.mul_comm Nat.mul_assoc Nat.mul_left_comm
  attribute [local simp] Nat.add_assoc Nat.add_comm Nat.add_left_comm

  example (w x y z : Nat) (p : Nat → Prop)
          (h : p (x * y + z * w * x)) : p (x * w * z + y * x) := by
    simp at *
    assumption

  -- same tactic proof works when `h` is modified to a non-canonical form since
  -- `simp at *` acts on `h` as well as the goal
  example (w x y z : Nat) (p : Nat → Prop)
          (h : p ((y * x) + z * w * x)) : p (x * w * z + y * x) := by
    simp at *
    assumption

  example (x y z : Nat) (p : Nat → Prop)
          (h₁ : p (1 * x + y)) (h₂ : p (x * z * 1))
          : p (y + 0 + x) ∧ p (z * x) := by
    simp at *
    -- h₁ : p (x + y)
    -- h₂ : p (x * z)
    -- ⊢ p (x + y) ∧ p (x * z)
    <;> constructor  -- now 2 goals, one for each ∧ argument
    <;> assumption   -- boom

  example (q : Prop) : q ↔ q := by simp

  -- non-trivial propositional reasoning by applying `simp` with all hypotheses
  example (p q : Prop) (hp : p) : p ∧ q ↔ q := by
    simp [*]  -- rewrites p ∧ q to True ∧ q to q, then q ↔ q by refl
    -- alt: simp [hp]

  example (p q : Prop) (hp : p) : p ∨ q := by
    simp [*]  -- alt: simp [hp]

  example (p q r : Prop) (hp : p) (hq : q) : p ∧ (q ∨ r) := by
    simp [*]  -- alt: simp [hp, hq]

  -- special arithmetic support
  example : 0 < 1 + x ∧ x + y + 2 ≥ y + 1 := by
    simp (config := { arith := true })
  -- same thing; shorthand
  example : 0 < 1 + x ∧ x + y + 2 ≥ y + 1 := by
    simp +arith

end simplify_examples

--
-- Exercises
--

-- 1.
section tactics_1

  example : p ∧ q ↔ q ∧ p := by
    apply Iff.intro <;>
    -- same tactic block solves both cases
    (intro ⟨_, _⟩
     constructor <;> assumption)

  example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := by
    apply Iff.intro
    . intro
      | ⟨⟨_, _⟩, _⟩ =>
        repeat (any_goals (first | constructor | assumption))
    . intro
      | ⟨_, ⟨_, _⟩⟩ =>
        repeat (any_goals (first | constructor | assumption))

  -- pq_implies_r
  example : (p → (q → r)) ↔ (p ∧ q → r) := by
    apply Iff.intro
    . intro h ⟨_, _⟩
      simp [*]
      -- alt: apply h <;> assumption
    . intro h _ _
      have : p ∧ q := by constructor <;> assumption
      simp [*]

  -- de_morgan_1
  example {p q : Prop} : ¬(p ∨ q) ↔ ¬p ∧ ¬q := by
    apply Iff.intro
    . intro h
      have : ¬p := fun hp => by
        apply h
        constructor; assumption
      have : ¬q := fun hq => by
        apply h
        -- constructor; assumption  -- doesn't work b/c picks first constructor, not second
        apply Or.inr; assumption
      constructor <;> assumption
    . intro ⟨hnp, hnq⟩ hpoq
      cases hpoq <;> contradiction

  -- Re-prove `em` from `dne` using tactics
  namespace alt_classical_redux
    axiom assumed_dne {p : Prop} (h : ¬¬p) : p
    axiom de_morgan_1 {p q : Prop} : ¬(p ∨ q) ↔ ¬p ∧ ¬q

    theorem alt_classical_redux_em {p : Prop}: p ∨ ¬p := by
      suffices ¬¬ (p ∨ ¬ p) by
        apply assumed_dne; assumption
      intro
      have h : ¬ p ∧ ¬¬p := by
        rw [← de_morgan_1]  -- much nicer!
        assumption
      cases h with
      | intro hnp hnnp => contradiction
  end alt_classical_redux
end tactics_1

section tactics_2
example (p q r : Prop) (hp : p)
        : (p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) := by
  simp [*]  -- that was too easy!
end tactics_2
