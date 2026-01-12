/-
Polya-Szego Problem 267
Part Three, Chapter 6

Original problem:
The maximum $M(r)$ is monotone increasing with $r$ unless $f(z)$ is a constant.\\

Formalization notes: -- We formalize the statement about the maximum modulus principle:
-- For a holomorphic function f on a disk, the maximum M(r) = sup_{|z|=r} |f(z)|
-- is strictly increasing in r unless f is constant.
-- We work with the closed disk of radius R centered at 0.
-- The theorem captures: if 0 < r₁ < r₂ ≤ R and M(r₁) = M(r₂), then f is constant.
-/

import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.PhragmenLindelof

-- Formalization notes:
-- We formalize the statement about the maximum modulus principle:
-- For a holomorphic function f on a disk, the maximum M(r) = sup_{|z|=r} |f(z)|
-- is strictly increasing in r unless f is constant.
-- We work with the closed disk of radius R centered at 0.
-- The theorem captures: if 0 < r₁ < r₂ ≤ R and M(r₁) = M(r₂), then f is constant.

theorem problem_267 (R : ℝ) (hR : 0 < R) (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (Metric.ball 0 R)) 
    (hcont : ContinuousOn f (Metric.closedBall 0 R)) :
    ∀ ⦃r₁ r₂ : ℝ⦄, 0 < r₁ → r₁ < r₂ → r₂ ≤ R → 
      (∀ z₁, ‖z₁‖ = r₁ → ‖f z₁‖ ≤ ‖f 0‖) → 
      (∀ z₂, ‖z₂‖ = r₂ → ‖f z₂‖ ≤ ‖f 0‖) → 
      (∃ z₂, ‖z₂‖ = r₂ ∧ ‖f z₂‖ = ‖f 0‖) → 
      (∃ z₁, ‖z₁‖ = r₁ ∧ ‖f z₁‖ = ‖f 0‖) → 
      Function.const ℂ ℂ f := by
  sorry

-- Proof attempt:
theorem problem_267 (R : ℝ) (hR : 0 < R) (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (Metric.ball 0 R)) 
    (hcont : ContinuousOn f (Metric.closedBall 0 R)) :
    ∀ ⦃r₁ r₂ : ℝ⦄, 0 < r₁ → r₁ < r₂ → r₂ ≤ R → 
      (∀ z₁, ‖z₁‖ = r₁ → ‖f z₁‖ ≤ ‖f 0‖) → 
      (∀ z₂, ‖z₂‖ = r₂ → ‖f z₂‖ ≤ ‖f 0‖) → 
      (∃ z₂, ‖z₂‖ = r₂ ∧ ‖f z₂‖ = ‖f 0‖) → 
      (∃ z₁, ‖z₁‖ = r₁ ∧ ‖f z₁‖ = ‖f 0‖) → 
      Function.const ℂ ℂ f := by
  intro r₁ r₂ hr₁ hr₁r₂ hr₂R hM₁ hM₂ ⟨w₂, hw₂⟩ ⟨w₁, hw₁⟩
  have hmax : IsMaxOn (norm ∘ f) (Metric.closedBall 0 r₂) 0 := by
    apply norm_le_of_forall_mem_closedBall_norm_le hcont
    intro z hz
    rcases le_or_lt ‖z‖ r₁ with h | h
    · have : z ∈ Metric.closedBall 0 r₁ := by simpa [mem_closedBall_zero_iff]
      exact hM₁ z (by rwa [mem_sphere_zero_iff_norm] at this)
    · exact hM₂ z (by rwa [mem_sphere_zero_iff_norm, ← dist_zero_right] at hz)
  have hconst : ∀ z ∈ Metric.ball 0 r₂, f z = f 0 := by
    intro z hz
    apply eq_of_isMaxOn_norm hf hmax
    simpa [Metric.ball, dist_zero_right] using hz
  ext z
  by_cases hz : z ∈ Metric.ball 0 R
  · obtain ⟨r, hr, hzr⟩ : ∃ r : ℝ, r ∈ Ioc 0 R ∧ z ∈ Metric.ball 0 r := by
      refine ⟨min (‖z‖ + (R - ‖z‖)/2) R, ?_, ?_⟩
      · refine ⟨by positivity, min_le_right _ _⟩
      · simp only [Metric.mem_ball, dist_zero_right]
        calc ‖z‖ < ‖z‖ + (R - ‖z‖)/2 := by linarith
             _ ≤ min (‖z‖ + (R - ‖z‖)/2) R := min_le_left _ _
    exact hconst z (Metric.ball_subset_ball (le_of_lt hr₁r₂.trans hr.2) hzr)
  · have : ‖z‖ = R := by
      have := Metric.closedBall.mono (by linarith) (mem_closedBall_zero_iff.2 (le_of_not_lt hz))
      rwa [mem_closedBall_zero_iff] at this
    rw [← dist_zero_right, this] at hz
    exact (hz (Metric.mem_ball_self hR)).elim