-- Forall introduction (λ abstraction) and elimination (function application)
example (α : Type) (p q : α → Prop) : (∀ x : α, p x ∧ q x) → ∀ y : α, p y :=
  fun h : ∀ x : α, p x ∧ q x =>
  fun y : α =>
  show p y from (h y).left

example (α : Type) (p q : α → Prop) : (∀ x : α, p x ∧ q x) → ∀ y : α, q y :=
  fun h : ∀ x : α, p x ∧ q x =>
  fun y : α =>
  show q y from (h y).right

section equiv_relation
  variable (α : Type) (r : α → α → Prop)

  variable (refl_r : ∀ x, r x x)
  variable (symm_r : ∀ {x y}, r x y → r y x)
  variable (trans_r : ∀ {x y z}, r x y → r y z → r x z)

  -- RAD! a ~ b, c ~ b, and c ~ d => a ~ d
  example (a b c d : α) (hab : r a b) (hcb : r c b) (hcd : r c d) : r a d :=
    have hbc : r b c := symm_r hcb
    have hac : r a c := trans_r hab hbc
    show r a d from trans_r hac hcd
end equiv_relation

/- Exercises on Universal Quantifiers -/
section universal_exercises_1
  variable (α : Type) (p q : α → Prop)

  example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
    Iff.intro
      (fun lhs : (∀ x, p x ∧ q x) =>
        have hp : (∀ x, p x) := fun x : α => (lhs x).left
        have hq : (∀ x, q x) := fun x : α => (lhs x).right
        ⟨ hp, hq ⟩)
      (fun rhs : ((∀ x, p x) ∧ (∀ x, q x)) =>
        fun x : α =>
          ⟨rhs.left x, rhs.right x⟩
      )

  example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
    fun (hpiq : ∀ x, p x → q x) (hfap : ∀ x, p x) =>
    show (∀ x, q x) from
      fun x =>
        have (f : p x → q x) := hpiq x 
        have (hp : p x) := hfap x
        show q x from f hp

  example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
    fun hfapofaq =>
      fun x =>
        Or.elim hfapofaq
          (fun hfap => Or.inl (hfap x))
          (fun hfaq => Or.inr (hfaq x))
end universal_exercises_1