/-
Polya-Szego Problem 124
Part One, Chapter 3

Original problem:
A bounded convex function $[\mathrm{p} .65]$ is everywhere continuous and it is even everywhere differentiable from the left and from the right.\\

Formalization notes: We formalize the statement about bounded convex functions on ℝ:
1. A function f : ℝ → ℝ that is convex and bounded is continuous everywhere
2. It has left and right derivatives everywhere
-/

import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.Algebra.Order.LeftRightLim

/-!
Formalization notes:
We formalize the statement about bounded convex functions on ℝ:
1. A function f : ℝ → ℝ that is convex and bounded is continuous everywhere
2. It has left and right derivatives everywhere

We break this into three separate theorems for clarity:
1. Continuity everywhere
2. Existence of left derivatives everywhere  
3. Existence of right derivatives everywhere

Note: The book's "differentiable from the left/right" means the existence of 
one-sided derivatives, not necessarily that the function is differentiable in 
the usual sense (which would require both one-sided derivatives to be equal).
-/

open Set
open scoped Topology

/-- A bounded convex function on ℝ is continuous everywhere. -/
theorem problem_124_part1 {f : ℝ → ℝ} (hconv : ConvexOn ℝ univ f) (hbdd : ∃ M, ∀ x, |f x| ≤ M) :
    Continuous f := by
  sorry

/-- A bounded convex function on ℝ has a left derivative at every point. -/
theorem problem_124_left_deriv {f : ℝ → ℝ} (hconv : ConvexOn ℝ univ f) (hbdd : ∃ M, ∀ x, |f x| ≤ M) 
    (x : ℝ) : ∃ L, Tendsto (λ h : ℝ => (f (x + h) - f x) / h) (𝓝[<] 0) (𝓝 L) := by
  sorry

/-- A bounded convex function on ℝ has a right derivative at every point. -/
theorem problem_124_right_deriv {f : ℝ → ℝ} (hconv : ConvexOn ℝ univ f) (hbdd : ∃ M, ∀ x, |f x| ≤ M) 
    (x : ℝ) : ∃ R, Tendsto (λ h : ℝ => (f (x + h) - f x) / h) (𝓝[>] 0) (𝓝 R) := by
  sorry

/-- Combined statement: A bounded convex function is continuous and has both one-sided derivatives. -/
theorem problem_124_complete {f : ℝ → ℝ} (hconv : ConvexOn ℝ univ f) (hbdd : ∃ M, ∀ x, |f x| ≤ M) :
    Continuous f ∧ 
    (∀ x, ∃ L, Tendsto (λ h : ℝ => (f (x + h) - f x) / h) (𝓝[<] 0) (𝓝 L)) ∧
    (∀ x, ∃ R, Tendsto (λ h : ℝ => (f (x + h) - f x) / h) (𝓝[>] 0) (𝓝 R)) := by
  refine ⟨problem_124_part1 hconv hbdd, 
          λ x => problem_124_left_deriv hconv hbdd x,
          λ x => problem_124_right_deriv hconv hbdd x⟩

-- Proof attempt:
theorem problem_124_part1 {f : ℝ → ℝ} (hconv : ConvexOn ℝ univ f) (hbdd : ∃ M, ∀ x, |f x| ≤ M) :
    Continuous f := by
  -- A convex function on ℝ is continuous at every point in the interior of its domain
  -- Since our domain is all of ℝ, the interior is ℝ, so it's continuous everywhere
  exact hconv.continuous_of_bddAbove_univ hbdd