
namespace Ex

-- ad hoc polymorphism

class Add (a : Type) where
 add : a → a → a

/-
it's basically like operator overloading in C++
-/

instance : Add Nat where
  add := Nat.add

instance : Add Int where
  add := Int.sub

instance : Add Float where
  add := Float.div

instance {a: Type} [Add a] : Add (Array a) where
  add x y := Array.zipWith x y (fun x y => Add.add x y)

def double {a : Type} [Add a] (x : a) : a :=
  Add.add x x

/-
Look at how much we can do with such few definitions.
-/

#eval Add.add 1 2 -- 3
#eval Add.add 1.0 2.0 -- 0.5
#eval Add.add (1: Int) 2 -- -1

-- literals for composite types in Lean
def arr : Array Nat := #[1, 2, 3]
#eval arr.toList -- [1, 2, 3]
def lst : List Nat := [11, 2, 3]
#eval Add.add arr lst.toArray -- #[12, 4, 6]

#eval double 1 -- 2
#eval double 1.5 -- 1.000...
#eval double lst.toArray -- #[22, 4, 6]

universe u

class Inhabited (a : Type u) where
  default : a

instance : Inhabited Nat where
  default := 0

instance : Inhabited Int where
  default := 0

instance : Inhabited Bool where
  default := true

export Inhabited (default)

#eval (default : Nat) -- 0

#eval (default : Bool) -- true

instance {a b: Type u} [Inhabited a] [Inhabited b] : Inhabited (a × b) where
  default := (default, default)

#eval (default : Nat × Bool)
#eval (default : Nat × Nat)

-- a function can have a special inhabited value too
instance {a b: Type u} [Inhabited b] : Inhabited (a → b) where
  default := fun _ => default

#eval (default : Nat → Bool) 8
#eval (default : Nat → Bool) 0

#print inferInstance

structure Person where
  name : String
  age : Nat

-- toString is a type class built into Lean
#eval toString 4

-- but that doesn't stop us from creating instances of it
instance : ToString Person where
  toString p := p.name ++ " is " ++ toString p.age

#eval toString { name := "Alice", age := 42 : Person }

end Ex
