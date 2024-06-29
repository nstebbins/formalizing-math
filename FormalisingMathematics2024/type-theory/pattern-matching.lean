import Mathlib.Tactic -- imports all the Lean tactics

namespace Patterns

open Nat

def addOne: Nat → Nat
  | zero => succ zero
  | succ n => succ (succ n)

#eval addOne 4

open Bool

def subtractOneIfTrue: Nat × Bool → Nat
| (zero, true) => zero
| (zero, false) => zero
| (succ n, true) => n
| (succ n, false) => succ n

#eval subtractOneIfTrue (4, true)
#eval subtractOneIfTrue (4, false)
#eval subtractOneIfTrue (0, true)

def b := Prod.mk 3 2
def c := (3, 2)

def d: List ℕ := List.nil

example : b = c := rfl

def e := And true false

end Patterns
