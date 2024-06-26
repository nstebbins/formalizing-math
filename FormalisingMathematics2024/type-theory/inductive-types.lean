import Mathlib.Tactic.Basic

namespace Hidden

inductive Prod (α: Type*) where
| a : α
| b : α

#eval Prod.mk 1 2
-- Prod.a is not a thing for inductive types

universe u

structure ProdStructure (α: Type u) where
 a : α
 b : α
 deriving Repr  /- nice output -/

#eval ProdStructure.mk 1 2
def g := ProdStructure.mk 1 2
def h := ProdStructure.mk 0 10
#eval h

-- we've now got projections!
#eval ProdStructure.a g
#eval ProdStructure.b (ProdStructure.mk 1 2)

def ProdStructure.add (x y: ProdStructure Nat) :=
  ProdStructure.mk (x.a + y.a) (x.b + y.b)

#eval ProdStructure.add g h
#eval g.add h

example (r: ProdStructure Nat)(s: ProdStructure Nat): r.add s = s.add r := by
  have h₀ : r.a + s.a = s.a + r.a := by
    rw [Nat.add_comm]
  have h₁ : r.add s = ProdStructure.mk (r.a + s.a) (r.b + s.b) := by
    rfl
  have h₂ : s.add r = ProdStructure.mk (s.a + r.a) (s.b + r.b) := by
    rfl
  rw [h₁, h₂]
  rw [h₀]
  sorry  -- rfl doesn't work here :/

end Hidden
