import Mathlib.Tactic -- import all the tactics

-- simple function

def squareNat (x: ℕ): ℕ := x * x

#reduce squareNat 2

-- higher order function

def applyNat (f: ℕ → ℕ)(a: ℕ) :=
  f a

#reduce applyNat squareNat 2

-- higher order ∧ generic function

def applyGeneric (α: Type*)(f: α → α)(a: α): α :=
  f a

#reduce applyGeneric ℕ squareNat 2

-- cartesian

def x := 4
def y : ℕ := 5  -- explicit type

def z := (x, y)

#check z
#check 4

def addTwo(x: ℕ × ℕ): ℕ := x.1 + x.2

#eval addTwo z  -- 9
#eval addTwo (4, 14) -- 18

#reduce addTwo z

-- lambda functions

#reduce (λ x : ℕ => x + 5) 4

#reduce (λ x: ℤ => λ y: ℤ => x - y) 4 5

#reduce (λ a: ℤ × ℤ => a.1 - a.2) (4, 5)

-- lists

def l : List ℕ := [1, 2, 3]

#check l
#check List
#check List ℕ
#check ℕ

-- inductive types
inductive day
| monday: day
| tuesday
| wednesday
| thursday
| friday
| saturday
| sunday

#check day
#check day.monday

-- inductive types within universes

#check Type
#check Type 0
#check Type 1

namespace hidden
section hidden1

universe u

inductive NoahList (α : Type u) where
  /-- `[]` is the empty list. -/
  | nil : NoahList α
  /-- If `a : α` and `l : List α`, then `cons a l`, or `a :: l`, is the
  list whose first element is `a` and with `l` as the rest of the list. -/
  | cons (head : α) (tail : NoahList α) : NoahList α

def l : NoahList ℕ := NoahList.nil
def l2 := NoahList.cons 1 l
def l3 := NoahList.cons 2 l2

#check NoahList
#check l
#check l2
#check l3

def NoahVector (α : Type u) (n : ℕ) :=
  { l : List α // l.length = n }

end hidden1
end hidden

-- props

variables (p q : Prop)
variables (A B: Type)
variable (f: A → B)

#check p ∧ q
#check p → q → p
#check p → q  -- doesn't feel like a function...
#check f
