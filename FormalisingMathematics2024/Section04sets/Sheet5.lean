/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- import all the tactics

/-!

# Sets in Lean, sheet 5 : equality of sets

Sets are extensional objects to mathematicians, which means that
if two sets have the same elements, then they are equal.

## Tactics

Tactics you will need to know for this sheet:

* `ext`

### The `ext` tactic

If the goal is `⊢ A = B` where `A` and `B` are subsets of `X`, then
the tactic `ext x,` will create a hypothesis `x : X` and change
the goal to `x ∈ A ↔ x ∈ B`.

-/

open Set

variable (X : Type)
  -- Everything will be a subset of `X`
  (A B C D E : Set X)
  -- A,B,C,D,E are subsets of `X`
  (x y z : X)

-- x,y,z are elements of `X` or, more precisely, terms of type `X`
example : A ∪ A = A := by
  ext x1
  constructor
  intro h
  cases' h with l r
  exact l
  exact r
  intro h
  constructor
  exact h
  done

example : A ∩ A = A := by
  ext x1
  constructor
  intros h1
  cases' h1 with l r
  exact l
  intro h1
  constructor
  exact h1
  exact h1
  done

example : A ∩ ∅ = ∅ := by
  ext x1
  constructor
  intros h
  cases' h with l r
  exact r
  intro h1
  constructor
  cases h1
  exact h1
  done

example : A ∪ univ = univ := by
  ext x1
  constructor
  intro h
  triv
  intro h
  right
  triv
  done


example : A ⊆ B → B ⊆ A → A = B := by
  intros h1 h2
  rw [subset_def] at *
  ext x1
  constructor
  intros h3
  specialize h1 x1
  specialize h2 x1
  apply h1
  exact h3
  intro h3
  specialize h1 x1
  specialize h2 x1
  apply h2
  exact h3
  done


example : A ∩ B = B ∩ A := by
  ext x1
  constructor
  intros h1
  cases' h1 with l r
  constructor
  exact r
  exact l
  intros h1
  cases' h1 with l r
  constructor
  exact r
  exact l
  done

example : A ∩ (B ∩ C) = A ∩ B ∩ C := by
  ext x1
  constructor
  intros h1
  cases' h1 with l r
  cases' r with r1 r2
  constructor
  constructor
  exact l; exact r1; exact r2;
  intros h1
  cases' h1 with l r
  cases' l with r1 r2
  constructor
  exact r1
  constructor
  exact r2
  exact r
  done

example : A ∪ (B ∪ C) = A ∪ B ∪ C := by sorry

example : A ∪ B ∩ C = (A ∪ B) ∩ (A ∪ C) := by sorry

example : A ∩ (B ∪ C) = A ∩ B ∪ A ∩ C := by
  ext x1
  constructor
  intros h1
  cases' h1 with l r
  cases' r with one two
  left
  constructor
  exact l; exact one;
  right
  constructor
  exact l; exact two;
  intros h1
  constructor
  cases' h1 with one two
  cases' one with l r
  exact l
  cases' two with l r
  exact l
  cases' h1 with one two
  left
  cases' one with l r
  exact r
  cases' two with l r
  right
  exact r
