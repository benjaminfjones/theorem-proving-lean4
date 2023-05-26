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

-- TODO: use function extensionality to prove:
-- theorem comp_with_all_none_eq_all_none {α β γ : Type} (f : β → Option γ) (x : α)
--   : comp_partial f (@all_none α β) = (@all_none α γ)

end PartialComposition

-- Inhabited is an inductive data type with a single constructor that takes a value of the
-- inhabited type
example : Inhabited Nat := Inhabited.mk 0
example : Inhabited Bool := ⟨true⟩