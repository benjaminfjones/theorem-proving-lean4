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

@[simp] theorem add_zero (m : Nat) : m + zero = m := by rfl
theorem add_succ (m k : Nat) : m + (succ k) = succ (m + k) := by rfl

-- Addition World: level 1
@[simp] theorem zero_add (m : Nat) : zero + m = m := by
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

def one : Nat := succ zero

instance : OfNat Nat 1 where
  ofNat := one

-- Unfortunately these literals don't work as well as they do in the Natural Number Game,
-- e.g. reduction to `zero` and `one` don't automatically occur after `rewrite` or `induction`

theorem one_eq_succ_zero : one = succ zero := by rfl
theorem lit_one_eq_succ_zero : 1 = succ zero := by rfl
theorem lit_zero_eq_zero : 0 = zero := by rfl

-- Addition World: level 5
theorem succ_eq_add_one (n : Nat) : succ n = n + one := by
  rw [one_eq_succ_zero, add_succ, add_zero]

-- Addition World: level 6
theorem add_comm_right (a b c : Nat) : a + b + c = a + c + b :=
  calc
    (a + b) + c = a + (b + c) := by rw [add_assoc]
    _           = a + (c + b) := by rw [add_comm b c]
    _           = (a + c) + b := by rw [add_assoc]

-- alt proof using tactics
example (a b c : Nat) : a + b + c = a + c + b := by
  rw [add_assoc, add_comm b c, add_assoc]

theorem add_left_comm (a b c : Nat) : a + (b + c) = b + (a + c) := by
  rw [← add_assoc, add_comm a b, add_assoc]

attribute [simp] add_assoc add_comm add_left_comm

-- Figuring out how to get `simp` to prove this from the above theorems is tricky.
-- Experimentation shows that defining `attribute [simp]` in the line above with
-- exactly these three theorems does the job. Using `add_assoc` and `add_comm` alone
-- does not, neither does adding `add_comm_right`.
--
-- Note: Number World uses a builtin `add_comm_monoid` structure which doesn't exist
-- (builtin) in Lean4
--
example (a b c d e : Nat) : (((a+b)+c)+d)+e=(c+((b+e)+a))+d := by
  simp

--
-- Bonus Exercise 1: total predecessor function, a.k.a. "Predecessor World"
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


--
-- Multiplication World
-- Ref: https://www.ma.imperial.ac.uk/~buzzard/xena/natural_number_game/?world=3&level=1
--

def mul (a b : Nat) : Nat :=
  match b with
  | zero => zero
  | succ b' => mul a b' + a

instance : Mul Nat where
  mul := mul

-- Stated as axioms in Multiplication World
@[simp] theorem mul_zero (a : Nat) : a * zero = zero := rfl
theorem mul_succ (a b : Nat) : a * succ b = (a * b) + a := rfl

-- Multiplication World: level 1
@[simp] theorem zero_mul (a : Nat) : zero * a = zero := by
  induction a
  . rfl
  . rw [mul_succ, add_zero]
    assumption

-- Multiplication World: level 2
@[simp] theorem mul_one (a : Nat) : a * one = a := by
  rw [one_eq_succ_zero, mul_succ, mul_zero, zero_add]

-- Multiplication World: level 3
theorem one_mul (a : Nat) : one * a = a := by
  induction a with
  | zero => rw [mul_zero]
  | succ a' ih => rw [mul_succ, ih, succ_eq_add_one]

-- Multiplication World: level 4
theorem mul_add (t a b : Nat) : t * (a + b) = t * a + t * b := by
  induction b with
  | zero =>
    rw [add_zero, mul_zero, add_zero]
  | succ b' ih =>
    rw [add_succ, mul_succ, ih, mul_succ, add_assoc]

-- Multiplication World: level 5
theorem mul_assoc (a b c : Nat) : (a * b) * c = a * (b * c) := by
  induction c with
  | zero => repeat (rw [mul_zero])
  | succ c' ih =>
    repeat (rw [mul_succ])
    rw [mul_add]
    rw [ih]

-- Multiplication World: level 6
theorem succ_mul (a b : Nat) : (succ a) * b = a * b + b := by
  induction b with
  | zero =>
    rw [mul_zero, mul_zero, add_zero]
  -- ih : succ a * b' = a * b' + b'
  | succ b' ih =>
    show succ a * succ b' = a * succ b' + succ b'
    exact
      calc
        succ a * succ b' = succ a * (b' + one) := by rw [succ_eq_add_one b']
        _                = succ a * b' + succ a * one := by rw [mul_add]
        _                = succ a * b' + succ a := by rw [mul_one]
        _                = a * b' + b' + succ a := by rw [ih]
        _                = a * b' + succ a + b' := by rw [add_comm_right]
        _                = a * b' + (a + one) + b' := by rw [succ_eq_add_one]
        _                = a * b' + a + one + b' := by simp only [add_assoc]
        _                = a * succ b' + one + b' := by rw [← mul_succ]
        _                = a * succ b' + b' + one := by rw [add_comm_right]
        _                = a * succ b' + (b' + one) := by rw [add_assoc]
        _                = a * succ b' + succ b' := by rw [succ_eq_add_one]
        -- phew!

-- simplifier version of `succ_mul` fully blasts both sides down to `add` and
-- primitive `mul` facts
example (a b : Nat) : (succ a) * b = a * b + b := by
  induction b with
  | zero =>
    rw [mul_zero, mul_zero, add_zero]
  | succ b' ih =>
    rw [succ_eq_add_one b', succ_eq_add_one a]
    simp [mul_add, mul_succ, one_eq_succ_zero, add_succ]
    rw [ih]
    rw [succ_add]
    -- only need additive assoc, comm, and injection from here
    -- ⊢ succ (a + (a * b' + b')) = succ (a + (b' + a * b'))
    simp

-- Multiplication World: level 7
theorem add_mul (a b t: Nat) : (a + b) * t = a * t + b * t := by
  induction t with
  | zero =>
    simp
  | succ t' ih =>
    rw [mul_succ, ih, mul_succ, mul_succ]
    -- Note: `simp` works well here after tweaking the simp attributes for addition (see above)
    -- ⊢ a * t' + b * t' + (a + b) = a * t' + a + (b * t' + b)
    simp

-- Multiplication World: level 8
theorem mul_comm (a b : Nat) : a * b = b * a := by
  induction b with
  | zero => simp
  | succ b' ih => rw [mul_succ, succ_mul, ih]

-- Multiplication World: level 9
theorem mul_left_comm (a b c : Nat) : a * (b * c) = b * (a * c) := by
  rw [← mul_assoc]
  rw [mul_comm a b]
  rw [mul_assoc]

-- Note: using same combo of simp attributes for multiplcation as addition, favouring
-- the `mul_left_comm` variant.
attribute [simp] mul_assoc mul_comm mul_left_comm

-- Witness the power!
example (a b c d e : Nat) : (((a*b)*c)*d)*e=(c*((b*e)*a))*d := by
  simp

--
-- Power World
--

def pow (m n : Nat): Nat :=
  match n with
  | zero => one
  | succ n' => pow m n' * m

-- introduces notation: `a ^ b`
instance : Pow Nat Nat where
  pow := pow

-- "Axioms"
theorem pow_zero (m : Nat) : m ^ zero = one := rfl
-- with literals
theorem pow_zero' (m : Nat) : m ^ 0 = 1 := rfl
theorem pow_succ (m n : Nat) : m ^ succ n = m ^ n * m := rfl

-- Power World: level 1
theorem zero_pow_zero : zero ^ zero = one := rfl
-- with literals
theorem zero_pow_zero' : 0 ^ 0 = 1 := rfl

-- Power World: level 2
theorem zero_pow_succ (n : Nat) : zero ^ succ n = zero := by
  -- rewriter:
  rw [pow_succ, mul_zero]
  -- explicit calc:
  --   calc
  --     0 ^ succ n = zero ^ succ n := by rfl
  --     _          = zero ^ n * zero := by rfl
  --     _          = zero := by rw [mul_zero]
  -- others:
  --   simp [pow]     -- using `0`, nope; using `zero` yep!
  --   rfl            -- yep!? not clear how...

-- Power World: level 3
theorem pow_one (m : Nat) : m ^ one = m := by
  rw [one_eq_succ_zero, pow_succ, pow_zero, one_mul]

-- Power World: level 4
theorem one_pow (n : Nat) : one ^ n = one := by
  induction n with
  | zero => rw [pow_zero]
  | succ n' ih =>
    rw [pow_succ, ih, mul_one]

-- Power World: level 5
theorem pow_add (a m n : Nat) : a ^ (m + n) = (a ^ m) * (a ^ n) := by
  induction n with
  | zero => rw [add_zero, pow_zero, mul_one]
  | succ n' ih =>
    rw [add_succ, pow_succ, pow_succ, ih, mul_assoc]

-- Power World: level 6
theorem mul_pow (a b n : Nat) : (a * b) ^ n = (a ^ n) * (b ^ n) := by
  induction n with
  | zero =>
    repeat (rw [pow_zero])
    rw [mul_one]
  | succ n' ih =>
    rw [pow_succ, ih]
    repeat (rw [pow_succ])
    simp  -- mul assoc and comm
    -- alternately:
    --   simp [ih, pow_succ]

-- Power World: level 7 (boss level!)
theorem pow_pow (a m n : Nat) : (a ^ m) ^ n = a ^ (m * n) := by
  induction n with
  | zero => rw [pow_zero, mul_zero, pow_zero]
  | succ n' ih => rw [pow_succ, ih, mul_succ, pow_add]

-- Power World: level 8 (oh snap, final boss level!)
def two : Nat := succ one
theorem two_eq_succ_one : two = succ one := rfl
theorem add_squared (a b : Nat) : (a + b) ^ two = a^two + b^two + two*a*b := by
  rw [two_eq_succ_one]
  rw [one_eq_succ_zero]
  -- repeat (rw [pow_succ])
  rw [pow_succ, pow_succ, pow_succ, pow_succ, pow_succ, pow_succ]
  -- repeat (rw [pow_zero, one_mul])
  rw [pow_zero, pow_zero, pow_zero]
  rw [one_mul, one_mul, one_mul]
  rw [add_mul, mul_add, mul_add]
  rw [succ_mul, succ_mul, zero_mul, zero_add, add_mul]
  -- simp  -- finishes the job
  --
  -- 22 rewrites to here, then simp. How many `rw`'s minimum are needed to replace `simp`?
  -- ⊢ a * a + a * b + (b * a + b * b) = a * a + b * b + (a * b + a * b)
  rw [add_assoc]
  rw [add_assoc (a*a) _ _]
  rw [add_left_comm (b*b) (a*b) (a*b)]
  rw [add_comm (b*b) (a*b)]
  rw [mul_comm a b]
  -- 27 rewrites total!
  -- Note: world record seems to be 18


  --
  -- Function World
  --

  section FunctionWorld

  -- Function World: level 1
  example (P Q : Type) (p : P) (h : P → Q) : Q := h p
  example (P Q : Type) (p : P) (h : P → Q) : Q := by exact h p

  -- Function World: level 2
  example : Nat → Nat :=
    fun n => (succ two) * n + two
  -- alt: using `intro`
  example : Nat → Nat := by
    intro x
    exact (succ two) * x + two

  -- Function World: level 3
  example (P Q R S T U: Type)
    (p : P)
    (h : P → Q)
    (i : Q → R)
    (j : Q → T)
    (k : S → T)
    (l : T → U)
    : U := by
      have q : Q := h p
      have t : T := j q
      exact l t

  -- Function World: level 4 using apply/assumption
  example (P Q R S T U: Type)
    (p : P)
    (h : P → Q)
    (i : Q → R)
    (j : Q → T)
    (k : S → T)
    (l : T → U)
    : U := by
      apply l
      apply j
      apply h
      assumption

  -- Function World: level 5
  example (P Q : Type) : P → (Q → P) := by
    intro p _
    exact p  -- or `assumption`
  -- alt: by projection
  example (P Q : Type) : P × Q → P := by
    intro t
    exact t.1

  -- Function World: level 6
  example (P Q R : Type) : (P → (Q → R)) → ((P → Q) → (P → R)) := by
    intro f g _
    apply f
    . assumption
    . apply g
      assumption

  -- Function World: level 7
  -- Contravariants of the functor Hom( ⬝ , F)
  example (P Q F : Type) : (P → Q) → ((Q → F) → (P → F)) := by
    intro f g _
    apply g
    apply f
    assumption

  -- Function World: level 8
  -- same proof, different level
  -- could have named the above example and instantiated `F` with `empty`
  example (P Q : Type) : (P → Q) → ((Q → empty) → (P → empty)) := by
    intro f g _
    apply g
    apply f
    assumption

  -- Function World: level 9 (a big maze)
  example (A B C D E F G H I J K L : Type)
    (f1 : A → B) (f2 : B → E) (f3 : E → D) (f4 : D → A) (f5 : E → F)
    (f6 : F → C) (f7 : B → C) (f8 : F → G) (f9 : G → J) (f10 : I → J)
    (f11 : J → I) (f12 : I → H) (f13 : E → H) (f14 : H → K) (f15 : I → L)
     : A → L := by
      intro
      apply f15
      apply f11
      apply f9
      apply f8
      apply f5
      apply f2
      apply f1
      assumption

  end FunctionWorld


end MyNat