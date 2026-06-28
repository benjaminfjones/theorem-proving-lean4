
/-
Back to the evaluator example. Goal is to prove that constant folding
preserves `eval`
-/
namespace Eval

inductive Expr where
  | const : (n : Nat) → Expr                -- a constant denoting the natural number n
  | var   : (n : Nat) → Expr                -- a variable, numbered n
  | plus  : (s : Expr) → (t : Expr) → Expr  -- denoting the sum of s and t
  | times : (s : Expr) → (t : Expr) → Expr  -- denoting the product of s and t
deriving Repr

abbrev Env := (Nat → Nat)  -- mapping variable IDs to values

def eval (env : Env) (e : Expr) : Nat :=
  match e with
  | .const n => n
  | .var n => env n
  | .plus s t => (eval env s) + (eval env t)
  | .times s t => (eval env s) * (eval env t) 

-- (1 |-> 1) (0 |-> 2) empty
def env0 : Env := fun n => if n == 0 then 2 else (if n == 1 then 1 else 0)

open Expr

#guard eval env0 (plus (const 1) (const 2)) == 3
#guard eval env0 (plus (var 0) (const 2)) == 4
#guard eval env0 (plus (var 1) (const 2)) == 3
#guard eval env0 (times (var 1) (const 2)) == 2

def env1 : Env
  | 0 => 5
  | 1 => 6
  | _ => 0

def sampleExpr : Expr :=
  plus (times (var 0) (const 7)) (times (const 2) (var 1))

#guard eval env1 sampleExpr == 47

def simpConst : Expr → Expr
  | .plus (.const n) (.const m) => const (n + m)
  | .times (.const n) (.const m) => const (n * m)
  | e => e

def fuse : Expr → Expr
  | .plus s t => simpConst (plus (simpConst s) (simpConst t))
  | .times s t => simpConst (times (simpConst s) (simpConst t))
  | e => e

theorem simpConst_eq (env : Env)
        : ∀ e : Expr, eval env (simpConst e) = eval env e := by
  intro
  | .const n => simp [simpConst]
  | .var n => simp [simpConst]
  | .plus s t =>
    simp [simpConst]
    cases s
    all_goals (
      cases t
      all_goals (try simp [eval]))
  | .times s t =>
    simp [simpConst]
    cases s
    all_goals (
      cases t
      all_goals (try simp [eval]))

theorem fuse_eq (env : Env)
        : ∀ e : Expr, eval env (fuse e) = eval env e := by
  simp [fuse]
  intro
  | .const n => simp only
  | .var n => simp only
  | .plus s t =>
    grind [eval, simpConst, simpConst_eq]  -- succeeds alone!
  | .times s t =>
    grind [eval, simpConst, simpConst_eq]

-- alternate proof
theorem fuse_eq' (v : Nat → Nat) : ∀ e : Expr, eval v (fuse e) = eval v e
  | const n     => rfl
  | var n       => rfl
  | plus e₁ e₂  => by
    rw [fuse, simpConst_eq, eval, eval, simpConst_eq, simpConst_eq]
  | times e₁ e₂ => by
    rw [fuse, simpConst_eq, eval, eval, simpConst_eq, simpConst_eq]

end Eval
