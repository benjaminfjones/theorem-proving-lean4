variable {p : Prop}
variable {q : Prop}

-- given a value in `p`, exhibit a function that takes a `q` and returns a `p`.
theorem t1 : p → (q → p) := fun (vp : p) => (fun (_vq : q) => vp)
#print t1  -- fun {p q} vp _vq => vp

theorem t1_alt : p → q → p :=
  fun hp : p =>
  fun hq : q =>
  show p from hp
#print t1_alt

theorem t1_alt2 (hp : p) (hq : q) : p := hp
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