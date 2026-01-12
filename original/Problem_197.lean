/-
Polya-Szego Problem 197
Part Three, Chapter 4

Original problem:
A function (not necessarily schlicht) that maps the closed unit disk onto a domain contained in the open unit disk has exactly one fixed point. I.e. if $f(z)$ is regular in the disk $|z| \leqq 1$ and if $|f(z)|<1$ in $|z| \leqq 1$ then the equation $f(z)-z=0$ has exactly one root in $|z| \leqq 1$.\\

Formalization notes: -- We formalize the statement: If f is holomorphic on the closed unit disk 𝔻 = {z | |z| ≤ 1}
-- and satisfies |f(z)| < 1 for all z with |z| ≤ 1, then f has exactly one fixed point in 𝔻.
-- We use `Metric.closedBall (0 : ℂ) 1` for the closed unit disk.
-- The condition "regular" means holomorphic/analytic in this context.
-- The conclusion "exactly one root" means there exists a unique z in the closed disk with f(z) = z.
-/

import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Analysis.Complex.ArgumentPrinciple
import Mathlib.Analysis.Complex.Rouche

-- Formalization notes:
-- We formalize the statement: If f is holomorphic on the closed unit disk 𝔻 = {z | |z| ≤ 1}
-- and satisfies |f(z)| < 1 for all z with |z| ≤ 1, then f has exactly one fixed point in 𝔻.
-- We use `Metric.closedBall (0 : ℂ) 1` for the closed unit disk.
-- The condition "regular" means holomorphic/analytic in this context.
-- The conclusion "exactly one root" means there exists a unique z in the closed disk with f(z) = z.

open Complex
open Metric
open Set

theorem problem_197 {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (closedBall 0 1))
    (h_bound : ∀ z, z ∈ closedBall (0 : ℂ) 1 → Complex.abs (f z) < 1) :
    ∃! z, z ∈ closedBall (0 : ℂ) 1 ∧ f z = z := by
  sorry

-- Proof attempt:
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Analysis.Complex.ArgumentPrinciple
import Mathlib.Analysis.Complex.Rouche

open Complex Metric Set

theorem problem_197 {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (closedBall 0 1))
    (h_bound : ∀ z, z ∈ closedBall (0 : ℂ) 1 → Complex.abs (f z) < 1) :
    ∃! z, z ∈ closedBall (0 : ℂ) 1 ∧ f z = z := by
  -- First show f is a contraction on the closed unit ball
  have h_lip : LipschitzWith (Real.toNNReal 1) f := by
    apply DifferentiableOn.lipschitzOn_of_nnnorm_deriv_le hf
    intro z hz
    have := SchwarzLemma.of_mem_ball hf (by simp) h_bound z hz
    simp at this
    exact this.le

  -- The closed unit ball is complete and nonempty
  have : IsComplete (closedBall (0 : ℂ) 1) := isComplete_closedBall (0 : ℂ) 1
  have : closedBall (0 : ℂ) 1 ≠ ∅ := by simp [closedBall_ne_empty]

  -- Apply Banach fixed-point theorem to show existence and uniqueness
  obtain ⟨z, hz, hfz⟩ := exists_unique_fixed_point' h_lip this
  · use z
    simp [hz, hfz]
    intro w hw hfw
    exact hfz w hw hfw
  · intro z w hz hw hfz hfw
    have : dist (f z) (f w) < dist z w := by
      refine lt_of_le_of_ne (h_lip.dist_le_mul z w) ?_
      intro heq
      have := h_bound z hz
      have := h_bound w hw
      simp [dist_eq, hfz, hfw] at heq
      linarith [Complex.abs.nonneg z, Complex.abs.nonneg w]
    linarith [this, dist_nonneg]