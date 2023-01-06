-- try it
/- Define some constants. -/

def m : Nat := 1       -- m is a natural number
def n : Nat := 0
def b1 : Bool := true  -- b1 is a Boolean
def b2 : Bool := false
def l : Nat := 14  -- -1 ==> failed to synthesize instance `Neg Nat`
def b3 := b1 && b2  -- Bool
def p1 := b1 /\ b2  -- Prop
def p2 := b1 \/ b2   -- Prop

/- Check their types. -/

#check m            -- output: Nat
#check n
#check n + 0        -- Nat
#check m * (n + 0)  -- Nat
#check b1           -- Bool
#check b1 && b2     -- "&&" is the Boolean and
#check b1 || b2     -- Boolean or
#check true         -- Boolean "true"

/- Evaluate -/

#eval 5 * 4         -- 20
#eval m + 2         -- 3
#eval b1 && b2      -- false
-- #eval p2 /\ !p2  -- Cannot synthesize instance Decidable (p2 /\ p2)

/- More Examples -/
#check Nat → Nat      -- type the arrow as "\to" or "\r"
#check Nat -> Nat     -- alternative ASCII notation
#check Bool → Bool

#check Nat × Nat      -- type the product as "\times"
#check Prod Nat Nat   -- alternative notation

#check Nat → Nat → Nat
#check Nat → (Nat → Nat)  --  same type as above

#check Nat × Nat → Nat
#check (Nat → Nat) → Nat -- a "functional"

#check Nat.succ     -- Nat → Nat
#check (0, 1)       -- Nat × Nat
#check Nat.add      -- Nat → Nat → Nat
#check Nat.gcd      -- Nat.gcd (a b : Nat) : Nat

#check Nat.succ 2   -- Nat
#check Nat.add 3    -- Nat → Nat
#check Nat.add 5 2  -- Nat
#check (5, 9).1     -- Nat
#check (5, 9).2     -- Nat

#eval Nat.succ 2   -- 3
#eval Nat.add 5 2  -- 7
#eval (5, 9).1     -- 5
#eval (5, 9).2     -- 9
#eval (1, 2, 3).1  -- 1
#eval (1, 2, 3).2  -- (2, 3)
#eval (1, 2, 3).2.1  -- 2
-- #eval (1, 2, 3).3  -- 1 -- invalid projection, structure only has 2 fields
#eval Nat.gcd 10 6 -- 2

/- Types as first class objects -/
#check Nat               -- Type
#check Bool              -- Type
#check Nat → Bool        -- Type
#check Nat × Bool        -- Type
#check Nat → Nat         -- ...
#check Nat × Nat → Nat
#check Nat → Nat → Nat
#check Nat → (Nat → Nat)
#check Nat → Nat → Bool
#check (Nat → Nat) → Nat

def α : Type := Nat
def β : Type := Bool
def F : Type → Type := List
def G : Type → Type → Type := Prod

#check α        -- Type
#check β        -- Type
#check F α      -- Type
#check F Nat    -- Type
#check List α
#check G α      -- Type → Type
#check G α β    -- Type
#check G α Nat  -- Type

#check Type     -- Type 1
#check Type 1   -- Type 2
#check Type 2   -- Type 3
#check Type 3   -- Type 4
#check Type 4   -- Type 5
-- #check Type ∈ Type 1 -- failed to synth `Membership (Type 1) (Type 2)

#check Prod     -- Prod.{u, v} (α : Type u) (β : Type v) : Type (max u v)
universe u
def H (γ : Type u) : Type u := Prod γ γ
def J (γ : Type 1) : Type 1 := List γ
#check H

#check fun (α β γ : Type) (g : β → γ) (f : α → β) (x : α) => g (f x)

def foo := let a := Nat; fun x : a => x + 2
/- body of `bar` does not make sense out of context of the `Nat` type, since
   it is defined in terms of adding 2 to an element of a. The type parameter
   `a` would beed to be constrained by a typeclass -/
/- def bar := (fun a => fun x : a => x + 2) Nat -/

/- Sections and variables -/
section useful
  variable (α β γ : Type)
  variable (g : β → γ) (f : α → β) (h : α → α)
  variable (x : α)

  def compose := g (f x)
  def doTwice := h (h x)
  def doThrice := h (h (h x))

  #print compose
  /- def compose : (α β γ : Type) → (β → γ) → (α → β) → α → γ :=
  fun α β γ g f x => g (f x) -/
end useful

/- lambda syntax -/
section foo
  variable (y : Type)
  def F2 := fun x : y => x
  def F3 := fun (x : y) => x
  def F4 := fun (_x1 x2 : y) => x2
  def F5 := fun (_x1 : y) (x2 : y) => x2
end foo
