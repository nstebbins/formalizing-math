/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics


/-!

# Logic in Lean, example sheet 4 : "and" (`∧`)

We learn about how to manipulate `P ∧ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following tactics:

* `cases'`
* `constructor`

-/

-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.
variable (P Q R : Prop)

example : P ∧ Q → P := by
  intros h
  cases' h with l r
  exact l
  done

example : P ∧ Q → Q := by
  intro h
  cases' h with l r
  exact r
  done

example : (P → Q → R) → P ∧ Q → R := by
  intros h1 h2
  apply h1
  cases' h2 with l r
  exact l
  cases' h2 with l r
  exact r
  done

example : P → Q → P ∧ Q := by
  intros h1 h2
  constructor
  exact h1
  exact h2
  done

/-- `∧` is symmetric -/
example : P ∧ Q → Q ∧ P := by
  intros h1
  constructor
  cases' h1 with l r
  exact r
  cases' h1 with l r
  exact l
  done

example : P → P ∧ True := by
  intro h
  constructor
  exact h
  triv
  done

example : False → P ∧ False := by
  intro h
  by_contra h2
  exact h
  done

/-- `∧` is transitive -/
example : P ∧ Q → Q ∧ R → P ∧ R := by
  intros h1 h2
  constructor
  cases' h1 with left right
  exact left
  cases' h2 with left right
  exact right
  done

example : (P ∧ Q → R) → P → Q → R := by
  intros h1 h2 h3
  apply h1
  constructor
  exact h2
  exact h3
  done
