import Mathlib.Tactic -- import all the tactics

namespace Examples

variable (p q r : Prop)

example (hp: p)(hq: q) : q ∧ p :=
  And.intro hq hp

example (_: p)(hq: q) : q ∨ p :=
  Or.inl hq

example (_: p)(hq: q) : Or q p :=
  Or.inl hq

example (hp: p → r)(hq: q → r)(ho: p ∨ q) : r :=
  Or.elim ho hp hq

example (hp: p → r)(hr: r → p) : p ↔ r :=
  Iff.intro hp hr

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p := by
  apply Iff.intro
  case mp =>
    intro h
    have hq : q := And.right h
    have hp : p := And.left h
    apply And.intro hq hp
  case mpr => sorry

theorem andOne (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro hp (And.intro hq hp)

theorem andTwo (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  case right =>
    exact And.intro hq hp
  case left =>
    exact hp

example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  case mp =>
    intro h
    sorry
  case mpr =>
    intro h
    sorry

#check Eq.trans

variable (x y z: ℕ)

example (hp: x = y)(hq: y = z): x = z :=
  Eq.trans hp hq

example (hp: False): Prop :=
  False.elim hp

example (x y : Nat) (h : x = y) : y = x := by
  revert h
  exact Eq.symm
  done

example (x : Nat) : x = x := by
  revert x
  intro y
  exact rfl

end Examples
