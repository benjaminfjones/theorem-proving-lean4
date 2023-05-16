--
-- Universal Quantifiers
--

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

section universal_exercises_2
  variable (α : Type) (p q : α → Prop)
  variable (r : Prop)

  -- Given an inhabited type α, If you know a proposition holds for all values of
  -- α, then you can conclude the propsition hold in general.
  example : α → ((∀ _ : α, r) ↔ r) :=
    fun y =>
      Iff.intro
        (fun (h : (∀ _ : α, r)) =>
          show r from h y)
        (fun hr : r =>
          show (∀ _ : α, r) from fun _ => hr)

  open Classical  -- why do I feel guilty opening Classical?
  example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r :=
    Iff.intro
      (fun h : (∀ x, p x ∨ r) =>
        byCases  -- Proof by cases over `r`
          (fun hr : r => Or.inr hr)
          (fun hnr : ¬r =>
            have hfp : (∀ x, p x) :=
              fun x =>
                Or.elim (h x)
                  (fun hpx : p x => hpx)
                  (fun hr : r => absurd hr hnr)
            Or.inl hfp)
      )
      (fun h : (∀ x, p x) ∨ r =>
        byCases  -- Proof by cases over `r`
          (fun hr : r => fun x => Or.inr hr)
          (fun hnr : ¬r =>
            fun x =>
              have hp : p x :=
                Or.elim h
                  (fun hfp => hfp x)
                  (fun hr => absurd hr hnr)
              show p x ∨ r from Or.inl hp)
      )

  example : (∀ x, r → p x) ↔ (r → ∀ x, p x) :=
    Iff.intro
      -- proof by function application, both ways
      (fun hfxrp hr x => (hfxrp x) hr)
      (fun hrfxp x hr => (hrfxp hr) x)
end universal_exercises_2

section universal_exercises_3
  variable (men : Type) (barber : men)
  variable (shaves : men → men → Prop)

  open Classical  -- is this possible to prove w/o Classical?
  example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False :=
    have hs : (shaves barber barber ↔ ¬ shaves barber barber) := h barber
    byCases
      (fun hb : shaves barber barber => absurd hb (hs.mp hb))
      (fun hnb : ¬ shaves barber barber => absurd (hs.mpr hnb) hnb)
end universal_exercises_3

section universal_exercises_4
  def even (n : Nat) : Prop := ∃ k : Nat, n = 2*k
  def prime (n : Nat) : Prop :=
    n > 1 ∧
    (∀ k d : Nat, k > 0 ∧ d > 0 ∧ n = k * d → k = 1 ∨ k = n)
  def infinitely_many_primes : Prop :=
    ∀ n : Nat, ∃ p : Nat, p > n ∧ prime p

  -- def Fermat_prime (n : Nat) : Prop := sorry
  -- def infinitely_many_Fermat_primes : Prop := sorry
  -- def goldbach_conjecture : Prop := sorry
  -- def Goldbach's_weak_conjecture : Prop := sorry
  -- def Fermat's_last_theorem : Prop := sorry
section universal_exercises_4

--
-- Equality
--

#check Eq.mp
#check Eq.refl  -- Eq.refl.{u_1} {α : Sort u_1} (a : α) : a = a
#check Eq.symm
#check Eq.trans

-- with an explicit universe
universe u
#check Eq.refl.{u}  -- Eq.refl : ∀ (a : ?m.726), a = a

section manual_eq_proofs
  variable (α : Type) (a b c d : α)
  variable (hab : a = b) (hcb : c = b) (hcd : c = d)
  example : a = d :=
    have hbc : b = c := hcb.symm
    have hac : a = c := Eq.trans hab hbc
    show a = d from Eq.trans hac hcd

  example : a = d :=
    (hab.trans hcb.symm).trans hcd
end manual_eq_proofs

-- Substitution and ▸

--  Eq.subst.{u} {α : Sort u} {motive : α → Prop} {a b : α}
--    (h₁ : a = b) (h₂ : motive a) :
--    motive b
--
-- Note: motive : α → Prop provides the context in which the substitution is to
-- occur. Inferring the motive requires higher-order unification, in general.
#check Eq.subst

section see_the_motive
  set_option pp.explicit true  -- display implicit arguments
  variable (α : Type) (a b c d : α) (p : α → Prop)
  variable (hab : a = b) (h : p a)
  theorem a_sub : p b := @Eq.subst α _ a b hab h

  -- The synthesized motive is now visible with the pretty printer
  -- setting `pp.explicit true`:
  --
  -- theorem a_sub : ∀ (α : Type) (a b : α) (p : α → Prop),
  --   @Eq α a b → p a → p b :=
  --     fun α a b p hab h => @Eq.subst α p a b hab h
  --
  -- So the motive inferred was `p`! (as expected)
  #print a_sub

end see_the_motive

-- substitue equal term into a predicate's argument
example (α : Type) (a b : α) (p : α → Prop)
        (h1 : a = b) (h2 : p a) : p b :=
  Eq.subst h1 h2

example (α : Type) (a b : α) (p : α → Prop)
    (h1 : a = b) (h2 : p a) : p b :=
  h1 ▸ h2

example (α : Type) (a b : α) (p : α → Prop)
        (h1 : a = b) : p a → p b :=
  -- fun hpa => Eq.subst h1 hpa
  fun hpa => h1 ▸ hpa

--
-- Calculational Proofs
--

section calc_proofs
  variable (a b c d e : Nat)
  variable (h1 : a = b)
  variable (h2 : b = c + 1)
  variable (h3 : c = d)
  variable (h4 : e = 1 + d)

  theorem T : a = e :=
    calc
      a = b      := h1
      _ = c + 1  := h2
      _ = d + 1  := congrArg Nat.succ h3
      _ = 1 + d  := Nat.add_comm d 1
      _ = e      := Eq.symm h4

  theorem T2 : a = e :=
    calc
      a = b := h1
      _ = c + 1 := h2
      _ = d + 1 := by rw [h3]
      _ = e := by rw [Nat.add_comm, h4]

  theorem T3 : a = e := by simp [h1, h2, h3, h4, Nat.add_comm]

  example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  calc
    (x + y) * (x + y) = (x + y)*x + (x + y)*y   := by rw [Nat.mul_add]
    _                 = x*x + y*x + (x*y + y*y) := by rw [Nat.add_mul, Nat.add_mul]
    _                 = x*x + y*x + x*y + y*y   := by simp [Nat.add_assoc]
    -- (x + y) * (x + y) = (x + y) * x + (x + y) * y  := by rw [Nat.mul_add]
    --     _ = x * x + y * x + (x + y) * y            := by rw [Nat.add_mul]
    --     _ = x * x + y * x + (x * y + y * y)        := by rw [Nat.add_mul]
    --     _ = x * x + y * x + x * y + y * y          := by rw [←Nat.add_assoc]

section calc_proofs

section display_implicit_args
  variable (g : Nat → Nat → Nat)
  variable (hg : g 0 0 = 0)

  theorem gex1 : ∃ x, g x x = x := ⟨0, hg⟩
  theorem gex2 : ∃ x, g x 0 = x := ⟨0, hg⟩
  theorem gex3 : ∃ x, g 0 0 = x := ⟨0, hg⟩
  theorem gex4 : ∃ x, g x x = 0 := ⟨0, hg⟩

  set_option pp.explicit true  -- display implicit arguments
  #print gex1
  #print gex2
  #print gex3
  #print gex4

section display_implicit_args
end