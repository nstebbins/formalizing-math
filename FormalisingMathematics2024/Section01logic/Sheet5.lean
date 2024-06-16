/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics

/-!

# Logic in Lean, example sheet 5 : "iff" (`↔`)

We learn about how to manipulate `P ↔ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following two new tactics:

* `rfl`
* `rw`

-/


variable (P Q R S : Prop)

example : P ↔ P := by
  constructor
  intro h
  exact h
  intro h
  exact h
  done

lemma one_way : (P ↔ Q) → (Q ↔ P) := by
  intro h
  rw [h]
  done

example : (P ↔ Q) ↔ (Q ↔ P) := by
  constructor
  apply one_way
  apply one_way
  done

example : (P ↔ Q) → (Q ↔ R) → (P ↔ R) := by
  intros h1 h2
  rw [h1, h2]
  done

example : P ∧ Q ↔ Q ∧ P := by
  constructor
  intro h
  constructor
  cases' h with l r
  exact r
  cases' h with l r
  exact l
  intro h
  constructor
  cases' h with l r
  exact r
  cases' h with l r
  exact l
  done

lemma one_way_and : (P ∧ Q) ∧ R → P ∧ Q ∧ R := by
  intro h
  cases' h with l r
  constructor
  cases' l with one two
  exact one
  cases' l with one two
  constructor
  exact two
  exact r
  done

example : (P ∧ Q) ∧ R ↔ P ∧ Q ∧ R := by
  constructor
  apply one_way_and
  intro h
  constructor
  cases' h with l r
  cases' r with r2 r3
  constructor
  exact l
  exact r2
  cases' h with l r
  cases' r with r2 r3
  exact r3
  done

example : P ↔ P ∧ True := by
  constructor
  intro h1
  constructor
  exact h1
  triv
  intro h1
  cases' h1 with l r
  exact l
  done

example : False ↔ P ∧ False := by
  constructor
  intro h
  by_contra h1
  exact h
  intro h
  cases' h with l r
  exact r
  done

example : (P ↔ Q) → (R ↔ S) → (P ∧ R ↔ Q ∧ S) := by
  sorry
  done

example : ¬(P ↔ ¬P) := by
  sorry
  done
