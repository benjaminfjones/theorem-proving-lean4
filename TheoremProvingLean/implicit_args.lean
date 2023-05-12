/-
Type parameters that can generally be infered from context,
for example from the types of other explicit parameters, can be
made implicit using the { } braces.
-/

universe u
-- in the `Lst` type def there is no other context to infer from, so α
-- is explicit
def Lst (α : Type u) : Type u := List α
-- in `Lst.cons` and the rest, there is a subsequent parameter whose type
-- uniquely determines α
def Lst.cons {α : Type u} (a : α) (as : Lst α) : Lst α := List.cons a as
def Lst.nil {α : Type u} : Lst α := List.nil
def Lst.append {α : Type u} (as bs : Lst α) : Lst α := List.append as bs

#check Lst          -- Type u_1 → Type u_1
#check Lst.cons     -- (α : Type u_1) → α → Lst α → Lst α
#check Lst.nil      -- (α : Type u_1) → Lst α
#check Lst.append   -- (α : Type u_1) → Lst α → Lst α → Lst α

#eval Lst.cons 2 (Lst.nil)
#eval @Lst.cons Nat 2 (Lst.nil)
#eval @Lst.cons _ 2 (Lst.nil)
#eval Lst.append (Lst.cons 2 (Lst.nil)) (Lst.cons 3 (Lst.nil))

def ident {α : Type u} (x : α) := x

#check ident         -- ?m → ?m
#check ident 1       -- Nat
#check ident "hello" -- String
#check @ident        -- {α : Type u_1} → α → α

/- explicit type annotations to help the elaborator -/
#check List.nil               -- List ?m
#check id                     -- ?m → ?m

#check (List.nil : List Nat)  -- List Nat
#check (id : Nat → Nat)       -- Nat → Nat