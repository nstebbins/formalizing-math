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

example (p : Nat → Prop) (hz : p 0) (hs : ∀ n, p (Nat.succ n)) : ∀ n, p n := by
  intro n
  cases n
  . exact hz
  . apply hs

open Nat

example (n : Nat) (h : n ≠ 0) : succ (pred n) = n := by
  cases n with
  | zero => exact absurd rfl h
  | succ k => rfl

example (x y z w : Nat) (h₁ : x = y) (h₂ : y = z) (h₃ : z = w) : x = w := by
  rw [← h₃]  -- x = z
  rw [← h₂]  -- x = y
  assumption

lemma a (p q r: Prop)(hp: p)(hq: q)(hr: r): p ∧ (q ∧ r) := by
  sorry

#check a

#check test

universe u v

structure MyStruct where
    {α : Type u}
    {β : Type v}
    a : α
    b : β

structure MyStruct2 (α: Type u)(β: Type v) where
    a : α
    b : β

structure MyStruct3 (α: Type u) where
  a : α
  b : α

#check { a := 10, b := true : MyStruct }
-- #check { a := 10, b := true : MyStruct2 } -- type-related error
#check { a := 10, b := true : MyStruct2 Nat Bool }
#check { a := 10, b := 11 : MyStruct3 Nat }

structure Point where
x : Nat
y : Nat
deriving Repr

structure RGB (α: Type u) where
  red: α
  green: α
  blue: α
  deriving Repr

structure RGBY (α: Type u) extends RGB α where
  yellow: α
  deriving Repr

def rgb1: RGB Nat := RGB.mk 1 2 3
-- def rgb2: RGBY Nat := RGBY.mk 1 2 3 4  -- type-related error
def rgb3 : RGBY Nat :=
{ red := 1, green := 2, blue := 3, yellow := 4}

#print rgb1
#print rgb3
#eval rgb3.red
#eval rgb3.yellow
