namespace weekday

inductive Weekday where
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday
  deriving Repr

#eval Weekday.tuesday

open Weekday

def numberOfDay (d : Weekday) : Nat :=
  match d with
    | monday => 1
    | tuesday => 2
    | wednesday => 3
    | thursday => 4
    | friday => 5
    | saturday => 6
    | sunday => 7

#eval numberOfDay Weekday.monday

set_option pp.all true
#print numberOfDay
-- #print numberOfDay.match_1  -- error
#print Weekday.casesOn
/-
@[reducible] protected def weekday.Weekday.casesOn.{u} : {motive : weekday.Weekday → Sort u} →
  (t : weekday.Weekday) →
    motive weekday.Weekday.monday →
      motive weekday.Weekday.tuesday →
        motive weekday.Weekday.wednesday →
          motive weekday.Weekday.thursday →
            motive weekday.Weekday.friday →
              motive weekday.Weekday.saturday → motive weekday.Weekday.sunday → motive t :=
fun {motive : weekday.Weekday → Sort u} (t : weekday.Weekday) (monday : motive weekday.Weekday.monday)
    (tuesday : motive weekday.Weekday.tuesday) (wednesday : motive weekday.Weekday.wednesday)
    (thursday : motive weekday.Weekday.thursday) (friday : motive weekday.Weekday.friday)
    (saturday : motive weekday.Weekday.saturday) (sunday : motive weekday.Weekday.sunday) =>
  @weekday.Weekday.rec.{u} motive monday tuesday wednesday thursday friday saturday sunday t
  -/
#print Weekday.rec
/-
Recursor takes a predicate-like `motive X` for every variant case `X` and returns a `motive t`
where `t : Weekday`.

recursor weekday.Weekday.rec.{u} : {motive : weekday.Weekday → Sort u} →
  motive weekday.Weekday.monday →
    motive weekday.Weekday.tuesday →
      motive weekday.Weekday.wednesday →
        motive weekday.Weekday.thursday →
          motive weekday.Weekday.friday →
            motive weekday.Weekday.saturday → motive weekday.Weekday.sunday → (t : weekday.Weekday) → motive t
-/
#check Weekday.rec

--
-- Functions of Weekday
def next (d : Weekday) : Weekday :=
  match d with
  | sunday    => monday
  | monday    => tuesday
  | tuesday   => wednesday
  | wednesday => thursday
  | thursday  => friday
  | friday    => saturday
  | saturday  => sunday

def previous (d : Weekday) : Weekday :=
  match d with
  | sunday    => saturday
  | monday    => sunday
  | tuesday   => monday
  | wednesday => tuesday
  | thursday  => wednesday
  | friday    => thursday
  | saturday  => friday

#eval next (next tuesday)      -- Weekday.thursday
#eval next (previous tuesday)  -- Weekday.tuesday

example : next (previous tuesday) = tuesday :=
  rfl
def next_previous (d : Weekday) : next (previous d) = d := by
  cases d <;> rfl   -- rfl unfolds `next` and `previous` definitions and reduces

end weekday

namespace PartialComposition

inductive Option (α : Type) where
  | none : Option α
  | some : α → Option α
  deriving Repr

open Option

def a_one : Option Nat := some 1
#eval a_one

def comp_partial {α β γ : Type} (f : β → Option γ) (g : α → Option β) : α → Option γ :=
  fun x : α => match g x with
    | Option.none => none
    | Option.some y => f y
#check comp_partial

def all_none {α β : Type} : α → Option β := fun _ => Option.none

theorem comp_all_none_with {α β γ : Type} (g : α → Option β) (x : α)
  : (comp_partial (@all_none β γ) g) x = Option.none := by
    -- use `simp` to unfold definitions of the two defined functions involved
    -- then split the match cases and reduce
    simp [comp_partial, all_none]
    split <;> rfl

theorem comp_with_all_none {α β γ : Type} (f : β → Option γ) (x : α)
  : (comp_partial f (@all_none α β)) x = Option.none := by
    simp [comp_partial, all_none]

-- Version of `comp_all_none_with` using function extensionality
theorem comp_all_none_with_eq_all_none {α β γ : Type} (g : α → Option β) (x : α)
  : comp_partial (@all_none β γ) g = (@all_none α γ) := by
  funext
  apply comp_all_none_with

-- Version of `comp_with_all_none` using function extensionality
theorem comp_with_all_none_eq_all_none {α β γ : Type} (f : β → Option γ) (x : α)
  : comp_partial f (@all_none α β) = (@all_none α γ) := by
    funext
    apply comp_with_all_none


end PartialComposition

-- Inhabited is an inductive data type with a single constructor that takes a value of the
-- inhabited type
example : Inhabited Nat := Inhabited.mk 0
example : Inhabited Bool := ⟨true⟩

--
-- Exercises 1:
-- Natural Numbers from Scratch
--

namespace MyNat

inductive Nat where
  | zero : Nat
  | succ : Nat -> Nat
  deriving Repr

--
-- Recursors
--

/-
@Nat.rec : {motive : Nat → Sort u_1} →
  motive Nat.zero → ((a : Nat) → motive a → motive (Nat.succ a)) → (t : Nat) → motive t
-/
#check @Nat.rec
/-
@Nat.recOn : {motive : Nat → Sort u_1} →
  (t : Nat) → motive Nat.zero → ((a : Nat) → motive a → motive (Nat.succ a)) → motive t
-/
#check @Nat.recOn

--
-- Addition World
--

def add (n m : Nat) : Nat :=
  match m with
  | Nat.zero => n
  | Nat.succ k => Nat.succ (add n k)

open Nat
#eval add (succ (succ zero)) (succ zero)

instance : Add Nat where
  add := add

#eval (succ (succ zero)) + (succ zero)

theorem add_zero (m : Nat) : m + zero = m := by rfl
theorem add_succ (m k : Nat) : m + (succ k) = succ (m + k) := by rfl

-- Addition World: level 1
theorem zero_add (m : Nat) : zero + m = m := by
  induction m with
  | zero => rfl
  | succ k ih =>
    rw [add_succ, ih]

-- alternately, using recOn:
-- this is harder to use with tactics inside the minor premises
theorem zero_add_by_rec (m : Nat) : zero + m = m :=
  Nat.recOn (motive := fun x => zero + x = x)
  m
  (show zero + zero = zero by rfl)
  (fun (a : Nat) (ih : zero + a = a) =>
    show zero + (succ a) = succ a by rw [add_succ, ih])

-- Addition World: level 2
theorem add_assoc (m n k : Nat) : (m + n) + k = m + (n + k) := by
  induction k with
  | zero => repeat (apply add_zero)
  | succ l ih =>
    repeat (rw [add_succ])
    rw [ih]

-- Addition World: level 3
theorem succ_add (m k : Nat) : (succ k) + m = succ (k + m) := by
  induction m with
  | zero => rfl
  | succ l ih =>
    rw [add_succ, add_succ, ih]

-- Addition World: level 4 (boss level)
theorem add_comm (m n : Nat) : m + n = n + m := by
  induction n with
  | zero => simp [zero_add, add_zero]
  | succ l ih => simp [succ_add, add_succ, ih]

--
-- Numeric literals
--
-- Numeric literals are setup using the `OfNat` class.
-- It can be instantiated for any single primite nat, or all of them like in the
-- Lean prelude: https://github.com/leanprover/lean4/blob/master/src/Init/Prelude.lean#L1069
--

instance : OfNat Nat 0 where
  ofNat := zero

instance : OfNat Nat 1 where
  ofNat := succ zero

@[simp] theorem one_eq_succ_zero : 1 = succ 0 := by rfl
@[simp] theorem zero_eq_lit_zero : zero = 0 := by rfl

-- Addition World: level 5
theorem succ_eq_add_one (n : Nat) : succ n = n + 1 := by
  rw [one_eq_succ_zero, add_succ, ← zero_eq_lit_zero, add_zero]

-- Addition World: level 6
theorem add_comm_right (a b c : Nat) : a + b + c = a + c + b :=
  calc
    (a + b) + c = a + (b + c) := by rw [add_assoc]
    _           = a + (c + b) := by rw [add_comm b c]
    _           = (a + c) + b := by rw [add_assoc]

-- alt proof using tactics
example (a b c : Nat) : a + b + c = a + c + b := by
  rw [add_assoc, add_comm b c, add_assoc]

-- TODO: figure out how to get `simp` to prove this from the above theorems
-- Number World uses a builtin `add_comm_monoid` structure which doesn't exist
-- (builtin) in Lean4
--
-- example (a b c d e : Nat) : (((a+b)+c)+d)+e=(c+((b+e)+a))+d := by
--   simp [add_comm, add_assoc]
--   sorry

--
-- Bonus Exercise 1: total predecessor function
--

def pred (n : Nat) : Nat :=
  match n with
  | zero => zero
  | succ k => k

theorem succ_pred (n : Nat) : n ≠ zero → succ (pred n) = n := by
  intro h
  simp [pred]
  split
  . contradiction
  . rfl

theorem pred_succ (n : Nat) : pred (succ n) = n := by
  simp [pred]

theorem add_pred (m n : Nat) : n ≠ zero → m + pred n = pred (m + n) := by
  intro
  match n with
  | zero => contradiction
  | succ l =>
    rw [add_succ, pred_succ, pred_succ]

theorem pred_add (m n : Nat) : m ≠ zero → pred m + n = pred (m + n) := by
  intro hm
  rw [add_comm (pred m) n, add_pred n m hm, add_comm]


end MyNat
