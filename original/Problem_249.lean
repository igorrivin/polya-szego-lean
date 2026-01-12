/-
Polya-Szego Problem 249
Part Three, Chapter 5

Original problem:
We ass\\
converges inside to 0 as $z$ tends :

Then there are 1\\
(1) $f(z)$ vanis\\
(2) $z=1$ is\\
vergence\\
-de of convergence of a oles of first order on this of coefficients is bounded. the circle of convergence\\
ower series of a rational be numerator) has degree lenotes the largest among

Defficients among the $n$ lifs (and no other singue: series\\
:- of such poles is not\\
…, $a_{n}, \ldots$ of the power that $Q e^{i x}$ and $Q e^{-i x}$ are tonvergence, $0<\alpha<\pi$. zuence $a_{0}, a

Formalization notes: -- We formalize the main theorem of Problem 249:
-- Let f(z) = Σ a_n z^n be a power series with radius of convergence ≥ 1.
-- Assume that for all n, the n-th derivative f^{(n)}(z) → 0 as z → 1 along the real axis.
-- Then either f is identically zero on the unit disk, or z=1 is a singular point of f.
-- We also formalize the sufficient condition for the first case: if limsup (log|a_n|)/√n < 0,
-- then f must be identically zero.
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log

-- Formalization notes:
-- We formalize the main theorem of Problem 249:
-- Let f(z) = Σ a_n z^n be a power series with radius of convergence ≥ 1.
-- Assume that for all n, the n-th derivative f^{(n)}(z) → 0 as z → 1 along the real axis.
-- Then either f is identically zero on the unit disk, or z=1 is a singular point of f.
-- We also formalize the sufficient condition for the first case: if limsup (log|a_n|)/√n < 0,
-- then f must be identically zero.

theorem problem_249 {a : ℕ → ℂ} (h_conv : HasSum (λ n ↦ a n * (z : ℂ) ^ n) (f z)) 
    (h_radius : 1 ≤ FormalMultilinearSeries.radius (λ n ↦ ContinuousMultilinearMap.mkPiAlgebra ℂ (Fin n) ℂ) 
      (λ n ↦ a n • ContinuousMultilinearMap.mkPiAlgebra ℂ (Fin n) ℂ)) 
    (h_deriv_tendsto : ∀ (n : ℕ), Tendsto (λ (x : ℝ) ↦ iteratedDeriv n f (x : ℂ)) (𝓝[<] 1) (𝓝 0)) :
    (∀ z : ℂ, Complex.abs z < 1 → f z = 0) ∨ 
    (¬ DifferentiableOn ℂ f (Metric.ball (0 : ℂ) 1) ∨ 
     ∃ (z : ℂ), Complex.abs z = 1 ∧ ¬ AnalyticAt ℂ f z) := by
  sorry

theorem problem_249_sufficient_condition {a : ℕ → ℂ} 
    (h_coeff_bound : limsup (λ n ↦ Real.log (Complex.abs (a n)) / Real.sqrt n) atTop < 0) :
    ∀ (f : ℂ → ℂ), (∀ z : ℂ, Complex.abs z < 1 → HasSum (λ n ↦ a n * z ^ n) (f z)) → 
    ∀ z : ℂ, Complex.abs z < 1 → f z = 0 := by
  sorry

-- Proof attempt:
theorem problem_249 {a : ℕ → ℂ} (h_conv : HasSum (λ n ↦ a n * (z : ℂ) ^ n) (f z)) 
    (h_radius : 1 ≤ FormalMultilinearSeries.radius (λ n ↦ ContinuousMultilinearMap.mkPiAlgebra ℂ (Fin n) ℂ) 
      (λ n ↦ a n • ContinuousMultilinearMap.mkPiAlgebra ℂ (Fin n) ℂ)) 
    (h_deriv_tendsto : ∀ (n : ℕ), Tendsto (λ (x : ℝ) ↦ iteratedDeriv n f (x : ℂ)) (𝓝[<] 1) (𝓝 0)) :
    (∀ z : ℂ, Complex.abs z < 1 → f z = 0) ∨ 
    (¬ DifferentiableOn ℂ f (Metric.ball (0 : ℂ) 1) ∨ 
     ∃ (z : ℂ), Complex.abs z = 1 ∧ ¬ AnalyticAt ℂ f z) := by
  -- First, establish that f is analytic on the open unit disk
  have h_analytic : AnalyticOn ℂ f (Metric.ball (0 : ℂ) 1) := by
    intro z hz
    rw [Metric.mem_ball] at hz
    exact hasSum_powerSeries_analytic h_conv (by linarith [h_radius, hz.le])
  
  -- Now consider two cases: either f is identically zero on the disk, or not
  by_cases h_zero : ∀ z : ℂ, Complex.abs z < 1 → f z = 0
  · left; exact h_zero
  · right
    push_neg at h_zero
    obtain ⟨z₀, hz₀, hfz₀⟩ := h_zero
    -- Since f is not identically zero, we need to show z=1 is a singular point
    -- We'll show that f cannot be analytic at 1
    have h_not_analytic_at_1 : ¬ AnalyticAt ℂ f 1 := by
      intro h_ana
      -- If f were analytic at 1, all derivatives would be continuous there
      have h_cont_diff : ∀ n, ContinuousAt (iteratedDeriv n f) 1 := by
        intro n
        exact (h_ana.iteratedDeriv n).continuousAt
      -- But our assumption says derivatives tend to 0 as z→1⁻
      have h_deriv_zero : ∀ n, iteratedDeriv n f 1 = 0 := by
        intro n
        have := (h_cont_diff n).tendsto
        rw [ContinuousAt] at this
        have := tendsto_nhds_unique (h_deriv_tendsto n) this
        simp at this
        exact this
      -- Now by Taylor expansion at 0, f must be identically zero
      have hf_zero : ∀ z ∈ Metric.ball (0 : ℂ) 1, f z = 0 := by
        intro z hz
        have h_ts := hasFPowerSeriesOnBall_analyticAt h_conv (by linarith [h_radius, hz.le])
        refine eq_zero_of_hasFPowerSeriesOnBall_eq_zero h_ts ?_ z hz
        intro n
        rw [iteratedDeriv_eq_zero_of_hasFPowerSeriesOnBall h_ts]
        exact h_deriv_zero n
      -- This contradicts h_zero
      exact hfz₀ (hf_zero z₀ hz₀)
    -- Since f is not analytic at 1, and |1| = 1, we're done
    exact Or.inr ⟨1, by simp, h_not_analytic_at_1⟩