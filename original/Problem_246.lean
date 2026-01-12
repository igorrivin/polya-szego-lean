/-
Polya-Szego Problem 246
Part Three, Chapter 5

Original problem:
If there is aiso a pole among the singularities on the circle of convergence the power series converges at no point of the circle of convergence.\\

Formalization notes: -- We formalize: If a power series ∑ aₙzⁿ has radius of convergence R = 1,
-- and has a pole among its singularities on the circle |z| = 1,
-- then the series diverges at every point on the circle of convergence.
-- We focus on the case where the pole is at z = 1 for simplicity.
-- The theorem captures: pole on circle of convergence → divergence everywhere on circle.
-/

import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Complex.Polynomial
import Mathlib.Analysis.SpecialFunctions.Pow.Real

-- Formalization notes:
-- We formalize: If a power series ∑ aₙzⁿ has radius of convergence R = 1,
-- and has a pole among its singularities on the circle |z| = 1,
-- then the series diverges at every point on the circle of convergence.
-- We focus on the case where the pole is at z = 1 for simplicity.
-- The theorem captures: pole on circle of convergence → divergence everywhere on circle.

theorem problem_246 (a : ℕ → ℂ) (R : ℝ) (hR : R = 1) 
    (h_conv_radius : HasSum (fun n : ℕ ↦ a n * (z : ℂ) ^ n) (f z) := by
    sorry
  -- The series has radius of convergence 1
  (h_radius : EMetric.ball (0 : ℂ) 1 ⊆ {z | Summable fun n => a n * z ^ n} ∧
    ¬ EMetric.ball (0 : ℂ) 1 ⊂ {z | Summable fun n => a n * z ^ n}) :
    -- There is a pole at z = 1 on the circle of convergence
    (h_pole : Tendsto (fun z : ℂ => ∑' n : ℕ, a n * z ^ n) (𝓝[≠] 1) atTop) →
    -- Then for all z on the unit circle, the series diverges
    ∀ z : ℂ, Complex.abs z = 1 → ¬ Summable (fun n : ℕ => a n * z ^ n) := by
  sorry

-- Proof attempt:
theorem problem_246 (a : ℕ → ℂ) (R : ℝ) (hR : R = 1) 
    (h_conv_radius : EMetric.ball (0 : ℂ) 1 ⊆ {z | Summable fun n => a n * z ^ n} ∧
    ¬ EMetric.ball (0 : ℂ) 1 ⊂ {z | Summable fun n => a n * z ^ n}) :
    (h_pole : Tendsto (fun z : ℂ => ∑' n : ℕ, a n * z ^ n) (𝓝[≠] 1) atTop) →
    ∀ z : ℂ, Complex.abs z = 1 → ¬ Summable (fun n : ℕ => a n * z ^ n) := by
  intro z hz
  by_contra h_sum
  have h_lim : Tendsto a atTop (𝓝 0) := by
    apply Summable.tendsto_atTop_zero
    exact h_sum
  have h_aux : Tendsto (fun z ↦ (1 - z) * ∑' n, a n * z ^ n) (𝓝[≠] 1) (𝓝 0) := by
    apply Tendsto.mul
    · apply tendsto_nhdsWithin_of_tendsto_nhds
      simp only [sub_self]
      exact (continuous_const.sub continuous_id).tendsto 1
    · exact h_pole
  have h_lim' : Tendsto (fun n ↦ a n) atTop (𝓝 0) := by
    convert h_lim
    simp
  have h_lim'' : Tendsto (fun n ↦ a n / 1) atTop (𝓝 0) := by
    simp [h_lim']
  have h_eq : ∀ n, a n / 1 = a n := by simp
  have h_final := tendsto_nhds_unique h_aux (tendsto_congr' (eventually_of_forall h_eq) h_lim'')
  rw [tendsto_nhds_unique_iff] at h_final
  have : ¬Tendsto (fun z : ℂ => ∑' n : ℕ, a n * z ^ n) (𝓝[≠] 1) atTop := by
    rw [h_final]
    exact not_tendsto_atTop_of_tendsto_nhds (tendsto_const_nhds (x := 0))
  contradiction