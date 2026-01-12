/-
Polya-Szego Problem 266
Part Three, Chapter 6

Original problem:
The maximum of $|f(z)|$ on the disk $|z| \leqq r$ is $M(r)$.\\

Formalization notes: -- We formalize the statement about the maximum modulus principle for entire functions.
-- For an entire function f : ℂ → ℂ, we define M(r) = sup {|f z| : |z| ≤ r}
-- The theorem states that M(r) is non-decreasing and log M(r) is convex in log r.
-- This is Hadamard's three circles theorem in the special case of entire functions.
-/

import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.PhragmenLindelof

-- Formalization notes:
-- We formalize the statement about the maximum modulus principle for entire functions.
-- For an entire function f : ℂ → ℂ, we define M(r) = sup {|f z| : |z| ≤ r}
-- The theorem states that M(r) is non-decreasing and log M(r) is convex in log r.
-- This is Hadamard's three circles theorem in the special case of entire functions.

open Complex
open Metric
open Set
open Filter

theorem problem_266 (f : ℂ → ℂ) (hf : Differentiable ℂ f) :
    ∃ M : ℝ → ℝ, 
      (∀ r : ℝ, 0 ≤ r → M r = sSup (|f '' (closedBall (0 : ℂ) r)|)) ∧
      MonotoneOn M (Set.Ici 0) ∧
      ConvexOn ℝ (Set.Ioi 0) (fun r : ℝ => Real.log (M r)) := by
  sorry

-- Proof attempt:
theorem problem_266 (f : ℂ → ℂ) (hf : Differentiable ℂ f) :
    ∃ M : ℝ → ℝ, 
      (∀ r : ℝ, 0 ≤ r → M r = sSup (|f '' (closedBall (0 : ℂ) r)|)) ∧
      MonotoneOn M (Set.Ici 0) ∧
      ConvexOn ℝ (Set.Ioi 0) (fun r : ℝ => Real.log (M r)) := by
  let M := fun r ↦ sSup (|f '' (closedBall (0 : ℂ) r)|)
  refine ⟨M, ?_, ?_, ?_⟩
  · intro r hr
    rfl
  · -- Monotonicity
    refine MonotoneOn.mono (fun r₁ r₂ hr₁ hr₂ h ↦ ?_)
    have h_subset : closedBall 0 r₁ ⊆ closedBall 0 r₂ := closedBall_subset_closedBall h
    apply csSup_le_csSup
    · refine ⟨‖f 0‖, ?_⟩
      intro y hy
      obtain ⟨x, hx, rfl⟩ := hy
      exact norm_nonneg (f x)
    · exact (nonempty_closedBall.2 hr₁).image f
    · exact (nonempty_closedBall.2 hr₂).image f
    · exact image_subset _ h_subset
  · -- Convexity of log M
    refine ⟨convex_Ioi 0, fun r₁ r₂ hr₁ hr₂ a b ha hb hab ↦ ?_⟩
    have hf' : DifferentiableOn ℂ f (closedBall 0 (max r₁ r₂)) :=
      fun _ _ ↦ hf.differentiableAt.differentiableWithinAt
    have hM : ∀ r ∈ Ioi 0, M r = ‖f‖_[closedBall 0 r] := by
      intro r hr
      rw [norm_eq_norm_of_mem_frontier (nonempty_closedBall.2 (le_of_lt hr)) (sphere_subset_closedBall)]
      exact hf'.abs_max_closure (nonempty_closedBall.2 (le_of_lt hr)) isCompact_closedBall
    simp_rw [hM _ (lt_of_lt_of_le (by linarith) (le_max_left r₁ r₂)),
             hM _ (lt_of_lt_of_le (by linarith) (le_max_right r₁ r₂)),
             hM _ (by linarith [ha, hb, hr₁, hr₂])]
    exact (hf'.subharmonicOn isClosed_ball).log_norm_subharmonic.convexOn_log _ _ ha hb hab