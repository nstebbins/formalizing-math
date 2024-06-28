import Mathlib.Tactic.Basic

namespace Hidden

inductive Prod (α: Type*) where
| a : α
| b : α

inductive Weekday where
| monday : Weekday
| tuesday : Weekday
| wednesday : Weekday
| thursday : Weekday
| friday : Weekday
| saturday : Weekday
| sunday : Weekday
deriving Repr

open Weekday

#check Weekday.friday

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

open Weekday

def numberOfDay (d : Weekday) : Nat :=
  match d with
  | sunday    => 1
  | monday    => 2
  | tuesday   => 3
  | wednesday => 4
  | thursday  => 5
  | friday    => 6
  | saturday  => 7

set_option pp.all true

#print numberOfDay
-- ... numberOfDay.match_1
#print numberOfDay.match_1
-- ... Weekday.casesOn ...
#print Weekday.casesOn
-- ... Weekday.rec ...
#check @Weekday.rec

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

lemma next_previous (d : Weekday) : next (previous d) = d := by
  cases d <;> rfl

#eval previous monday

inductive Bool where
| f : Bool
| t : Bool
deriving Repr

open Bool

def and(a b: Bool): Bool :=
  match a with
  | t => b
  | f => f

def neg(a: Bool): Bool :=
  match a with
  | t => f
  | f => t

#eval and t f  -- Hidden.Bool.f
#eval and f f  -- Hidden.Bool.f
#eval neg t    -- Hidden.Bool.f
#eval neg f    -- Hidden.Bool.t

inductive Maybe (α : Type) where
| none : Maybe α
| some : α → Maybe α
deriving Repr

def exampleMaybe : Maybe Nat := Maybe.some 5
def exampleMaybeNone : Maybe Nat := Maybe.none

#eval exampleMaybe  -- Hidden.Maybe.some 5
#eval exampleMaybeNone  -- Hidden.Maybe.none

def isNone(m: Maybe Nat) :=
  match m with
  | Maybe.none => t
  | Maybe.some _ => f

#eval isNone exampleMaybe
#eval isNone exampleMaybeNone

end Hidden
