import Mathlib.Tactic -- import all the tactics

namespace Examples

#check fun (x) => x + 5
#check λ (x) => x + 5
#eval (fun (x: ℕ) => x + 5) 4
#eval (λ (x: ℕ) => x + 5) 4

def addTwo (x y: ℕ) := x + y  -- no 'fun' keyword
#eval addTwo 3 4
#eval (λ (x: ℕ) => λ (y: ℕ) => x + y) 4 5
#eval (λ x: ℕ => λ y: ℕ => x + y) 4 5  -- parens unnecessary

def subtractTwo (a b: ℤ) := a - b
#eval subtractTwo 4 5

variable (p q: Prop)

-- return type of curried function w/ no inputs
/-
  there's no direct analog type of Lean function that I can think of
-/
example: p → q → p := fun (hp: p) => fun (_: q) => hp

-- return type of just Prop w/ inputs
example (hp: p)(_: q): p := hp

-- now, take away the variables
example (a b: Prop)(ha: a)(_: b): a := ha

-- name it
theorem one (a b: Prop)(ha: a)(_: b): a := ha
theorem two: p → q → p := fun (hp: p) => fun (_: q) => hp

#print Examples.one
#print one

#check one
#check two  -- pretty much identical to @one

end Examples
