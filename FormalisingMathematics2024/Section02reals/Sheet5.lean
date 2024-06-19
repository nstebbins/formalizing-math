/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic
-- imports all the Lean tactics
import FormalisingMathematics2024.Solutions.Section02reals.Sheet3
-- import the definition of `TendsTo` from a previous sheet

namespace Section2sheet5

open Section2sheet3solutions

-- you can maybe do this one now
theorem tendsTo_neg {a : ℕ → ℝ} {t : ℝ} (ha : TendsTo a t) : TendsTo (fun n ↦ -a n) (-t) := by
  sorry

/-
`tendsTo_add` is the next challenge. In a few weeks' time I'll
maybe show you a two-line proof using filters, but right now
as you're still learning I think it's important that you
try and suffer and struggle through the first principles proof.
BIG piece of advice: write down a complete maths proof first,
with all the details there. Then, once you know the maths
proof, try translating it into Lean. Note that a bunch
of the results we proved in sheet 4 will be helpful.
-/
/-- If `a(n)` tends to `t` and `b(n)` tends to `u` then `a(n) + b(n)`
tends to `t + u`. -/
theorem tendsTo_add {a b : ℕ → ℝ} {t u : ℝ} (ha : TendsTo a t) (hb : TendsTo b u) :
    TendsTo (fun n ↦ a n + b n) (t + u) :=
  by
  rw [tendsTo_def]; rw [tendsTo_def] at ha; rw [tendsTo_def] at hb;
  intro epsilon
  specialize ha (epsilon/2)
  specialize hb (epsilon/2)
  intro h
  specialize ha h
  specialize hb h
  cases' ha with a_val ha
  cases' hb with b_val hb
  use max a_val b_val
  intros h2 h3
  specialize ha h2
  specialize hb h2
  specialize ha h3
  specialize hb h3
  rw [abs_lt] at *
  constructor <;> linarith
  done


/-- If `a(n)` tends to t and `b(n)` tends to `u` then `a(n) - b(n)`
tends to `t - u`. -/
theorem tendsTo_sub {a b : ℕ → ℝ} {t u : ℝ} (ha : TendsTo a t) (hb : TendsTo b u) :
    TendsTo (fun n ↦ a n - b n) (t - u) := by
  -- this one follows without too much trouble from earlier results.
  apply tendsTo_neg at hb
  apply tendsTo_add ha hb
  done

end Section2sheet5
