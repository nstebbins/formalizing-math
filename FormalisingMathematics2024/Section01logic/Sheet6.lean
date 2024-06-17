/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics


/-!

# Logic in Lean, example sheet 6 : "or" (∨`)

We learn about how to manipulate `P ∨ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following tactics

* `left` and `right`
* `cases'` (new functionality)

-/


-- Throughout this sheet, `P`, `Q`, `R` and `S` will denote propositions.
variable (P Q R S : Prop)

example : P → P ∨ Q := by
  intro h
  left
  exact h
  done

example : Q → P ∨ Q := by
  intro h
  right
  exact h
  done

example : P ∨ Q → (P → R) → (Q → R) → R := by
  intros h1 h2 h3
  cases' h1 with l r
  apply h2 at l
  exact l
  apply h3 at r
  exact r
  done

-- symmetry of `or`
example : P ∨ Q → Q ∨ P := by
  intro h
  cases' h with l r
  right
  exact l
  left
  exact r
  done

-- associativity of `or`
example : (P ∨ Q) ∨ R ↔ P ∨ Q ∨ R := by
  constructor
  intro h
  cases' h with l r
  cases' l with one two
  left
  exact one
  right
  left
  exact two
  right
  right
  exact r
  intro h
  cases' h with l r
  left
  left
  exact l
  cases' r with one two
  left
  right
  exact one
  right
  exact two
  done

example : (P → R) → (Q → S) → P ∨ Q → R ∨ S := by
  intros h1 h2 h3
  cases' h3 with l r
  apply h1 at l
  left
  exact l
  apply h2 at r
  right
  exact r
  done

example : (P → Q) → P ∨ R → Q ∨ R := by
  sorry
  done

example : (P ↔ R) → (Q ↔ S) → (P ∨ Q ↔ R ∨ S) := by
  sorry
  done

-- de Morgan's laws
example : ¬(P ∨ Q) ↔ ¬P ∧ ¬Q := by
  constructor
  intro h
  constructor
  by_contra h2
  apply h
  left
  exact h2
  by_contra h2
  apply h
  right
  exact h2
  intro h
  by_contra h2
  cases' h with one two
  cases' h2 with three four
  apply one at three
  exact three
  apply two at four
  exact four
  done

example : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q := by
  sorry
  done
