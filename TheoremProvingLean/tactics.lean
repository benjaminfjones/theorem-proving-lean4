
-- Re-prove `em` from `dne` using tactics
section alt_classical

  axiom assumed_dne {p : Prop} (h : ¬¬p) : p
  axiom de_morgan_1 {p q : Prop} : ¬(p ∨ q) ↔ ¬p ∧ ¬q

  theorem em {p q : Prop}: p ∨ ¬p := by
    suffices ¬¬ (p ∨ ¬ p) by
      apply assumed_dne; assumption
    intro
    have h : ¬ p ∧ ¬¬p := by
      apply (@de_morgan_1 p (¬ p)).mp
      assumption
    have : ¬ p := h.left
    have : ¬¬ p := h.right
    contradiction
end alt_classical

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
    simp_arith

end simplify_examples
