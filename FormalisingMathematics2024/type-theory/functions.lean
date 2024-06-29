
def double(x: Nat) := x + x
def square(x: Nat) := x * x

#eval 10 |> double |> square -- 400
#eval 10 |> square |> double -- 200
#eval double <| square <| 10 -- 200 (same thing)

def doubleList(xs: List Nat) := xs.map double

#eval doubleList [1, 2, 3, 4] -- [2, 4, 6, 8]

-- lean lists
/-
  exploring List/Basic.lean functions
-/

def a: List Nat := [1, 2, 3, 4, 5]  -- some fancy shorthand
def b: List Nat := 1 :: 2 :: 3 :: 4 :: 5 :: List.nil  -- shorthand for cons
def c: List Nat := List.cons 4 (List.cons 5 List.nil) -- explicitly using constructor cons
def d: List Nat := List.nil |> List.cons 5 |> List.cons 4 -- pipelining cons

#eval c
#eval d

example: a = b := by rfl
example: c = d := by rfl

#eval a.dropLast
#eval c.dropLast

#eval a.length
#eval c.length

def poor_mans_length {α: Type} : List α → Nat
| List.nil => 0
| List.cons _ tail => 1 + poor_mans_length tail

#eval poor_mans_length [1, 2, 3, 4, 5]
#eval poor_mans_length [4, 5]
