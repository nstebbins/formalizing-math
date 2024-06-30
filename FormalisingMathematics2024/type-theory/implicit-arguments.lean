import Mathlib.Tactic

namespace Ex

universe u
variable (α: Type u)
variable {β: Type u}
variable (x: α)
variable (y: β)

def ident := x
def ident2 := y

def ident3(α: Type u)(x: α) := x
#eval ident3 Nat 5
#check ident3

def ident4{α: Type u}(x: α) := x

#check ident
#check @ident
#check ident2
#check @ident2
#check ident Nat
#check @ident Nat
#check ident2 Nat -- gives confusing output
#check @ident2 Nat -- explicitly binds type to implicit arg

#eval ident Nat 5
#eval ident Nat 5
#eval ident (x := 2) -- named arg
#eval ident2 5 -- ℕ is implicit
#eval ident2 (y := 2) -- named arg
#eval @ident4 Nat 4 -- using @

def a : ℝ := 37
def b : ℝ := 42

#check add_comm a b -- add_comm a b : a + b = b + a

end Ex
