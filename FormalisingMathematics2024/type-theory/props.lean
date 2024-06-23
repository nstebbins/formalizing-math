import Mathlib.Tactic -- import all the tactics

namespace TestProps

variable (a p q: Prop)

theorem one: p → p :=
  fun (hp: p) => hp

#print one

theorem modus_ponens_f (hp: p)(hq: q): p :=
  hp

#print modus_ponens_f

axiom ha: a

theorem already_true: q → a :=
  modus_ponens_f ha -- partially applied modus_ponens

#print already_true

theorem modus_ponens: p → q → p :=
  fun (hp: p) => fun (hq: q) => hp

#print modus_ponens  -- same as modus_ponens_f!

theorem repeated: p → p → p :=
  fun (hp: p) => fun (hp: p) => hp

#print repeated

theorem repeated_two: q → p → p :=
  fun (hq: q) => fun (hp: p) => hp

#print repeated_two

variable {d e f: Prop}

theorem t1 (p q : Prop) (hp : p) (hq : q) : p := hp

variable (p q r s : Prop)

#check modus_ponens_f p q                -- p → q → p
#check t1 p q                -- p → q → p
#check t1 r s                -- r → s → r
#check t1 (r → s) (s → r)    -- (r → s) → (s → r) → r → s

variable (h : r → s)
#check t1 (r → s) (s → r) h  -- (s → r) → r → s

theorem t2 (h₁ : q → r) (h₂ : p → q) : p → r :=
  fun (hp: p) => h₁ (h₂ hp)

end TestProps

namespace TestProps2

variable (p q : Prop)

#check p → q → p ∧ q
#check ¬p → p ↔ False
#check p ∨ q → q ∨ p

example (hp : p) (hq : q) : p ∧ q := And.intro hp hq

example (hp: p ∧ q) : p := And.left hp

example (h : p ∧ q) : q ∧ p :=
  And.intro (And.right h) (And.left h)

example (q: Prop)(h: p): p ∨ q :=
  Or.inl h

example (q: Prop)(h: p): q ∨ p :=
  Or.inr h

variable (hp : p) (hq : q)
#check (⟨hp, hq⟩: p ∧ q)  -- infer constructor

variable (xs : List Nat)

#check List.length xs
#check xs.length

-- tried this. didn't work
/-
example (h : p ∧ q) : q ∧ p ∧ q :=
  have hp: p := And.left h
  have hq: q := And.right h
  have ha: q ∧ p := And.intro hq hp
  And.intro ha hp
-/

example (h : p ∧ q) : q ∧ p ∧ q :=
  have hp: p := And.left h
  have hq: q := And.right h
  -- And.intro (And.intro hq hp) hq
  ⟨And.right h, ⟨And.left h, And.right h⟩⟩


end TestProps2
