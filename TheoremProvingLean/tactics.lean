
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

