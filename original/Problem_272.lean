/-
Polya-Szego Problem 272
Part Three, Chapter 6

Original problem:
If an analytic function is regular in a closed disk and not a constant its absolute value at the center of the disk is smaller than the arithmetic mean of its absolute value on the boundary of the disk.\\

Formalization notes: -- We formalize the statement: For a non-constant analytic function f on a closed disk,
-- the value at the center is strictly less than the average of |f| on the boundary.
-- We use `ℂ` for complex numbers, `Metric.ball` and `Metric.closedBall` for disks,
-- and assume f is analytic on an open set containing the closed disk.
-- The arithmetic mean on the boundary is expressed as (1/(2π)) * ∫_0^{2π} |f(R*exp(iθ))| dθ
-/

import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral

-- Formalization notes:
-- We formalize the statement: For a non-constant analytic function f on a closed disk,
-- the value at the center is strictly less than the average of |f| on the boundary.
-- We use `ℂ` for complex numbers, `Metric.ball` and `Metric.closedBall` for disks,
-- and assume f is analytic on an open set containing the closed disk.
-- The arithmetic mean on the boundary is expressed as (1/(2π)) * ∫_0^{2π} |f(R*exp(iθ))| dθ

theorem problem_272 (R : ℝ) (hR : 0 < R) (f : ℂ → ℂ) (z₀ : ℂ) 
    (h_analytic : AnalyticOn ℂ f (Metric.closedBall z₀ R)) 
    (h_nonconst : ¬∀ z, f z = f z₀) :
    Complex.abs (f z₀) < (1 / (2 * π)) * ∫ θ in (0)..(2 * π), Complex.abs (f (z₀ + R * Complex.exp (θ * Complex.I)))) := by
  sorry

-- Proof attempt:
theorem problem_272 (R : ℝ) (hR : 0 < R) (f : ℂ → ℂ) (z₀ : ℂ) 
    (h_analytic : AnalyticOn ℂ f (Metric.closedBall z₀ R)) 
    (h_nonconst : ¬∀ z, f z = f z₀) :
    Complex.abs (f z₀) < (1 / (2 * π)) * ∫ θ in (0)..(2 * π), Complex.abs (f (z₀ + R * Complex.exp (θ * Complex.I)))) := by
  -- First, simplify by translating to origin
  let g : ℂ → ℂ := fun z => f (z + z₀)
  have hg_analytic : AnalyticOn ℂ g (Metric.closedBall 0 R) := by
    rw [← Metric.closedBall_add_singleton]
    exact h_analytic.comp (analyticOn_id.add_const _)
  have hg_nonconst : ¬∀ z, g z = g 0 := by
    simp only [g]
    contrapose! h_nonconst
    intro z
    have := h_nonconst (z - z₀)
    simp [this]
  
  -- Now work with g instead of f
  suffices Complex.abs (g 0) < (1 / (2 * π)) * ∫ θ in (0)..(2 * π), Complex.abs (g (R * Complex.exp (θ * Complex.I))) by
    convert this using 2
    · simp [g]
    · simp [g]
      congr with θ
      simp [add_comm]
  
  -- Apply mean value property for analytic functions
  have mean_value : g 0 = (1 / (2 * π)) * ∫ θ in (0)..(2 * π), g (R * Complex.exp (θ * Complex.I)) :=
    Complex.two_pi_I_inv_smul_circleIntegral_sub_singleton 0 hR.le (by simp) 
      (hg_analytic.mono (Metric.closedBall_subset_ball hR))
  
  -- Take absolute value of both sides
  have abs_mean_value : Complex.abs (g 0) ≤ (1 / (2 * π)) * ∫ θ in (0)..(2 * π), Complex.abs (g (R * Complex.exp (θ * Complex.I))) := by
    rw [mean_value]
    simp only [Complex.abs_mul, Complex.abs_one_div, Complex.abs_two_pi]
    apply mul_le_mul_of_nonneg_left (Complex.abs.integral_le_integral_abs _)
    simp [Real.pi_pos.le]
  
  -- Show strict inequality using maximum modulus principle
  by_contra h
  push_neg at h
  have eq : ∀ z ∈ Metric.sphere 0 R, Complex.abs (g z) = Complex.abs (g 0) := by
    apply Complex.eqOn_abs_of_isMaxOn hg_analytic.norm.continuousOn
      (Metric.isCompact_closedBall _ _).isCompact_sphere hR
    · intro z hz
      exact hg_analytic.norm (Metric.sphere_subset_closedBall hz)
    · intro z hz
      rw [← h]
      exact le_of_eq rfl
  
  -- Now g must be constant on the closed ball
  have h_const : ∀ z ∈ Metric.closedBall 0 R, g z = g 0 := by
    apply Complex.eqOn_closedBall_of_eqOn_sphere hR hg_analytic.continuousOn
      (hg_analytic.mono (Metric.closedBall_subset_ball hR))
    intro z hz
    exact Complex.eq_of_abs_eq (eq z hz)
  
  -- Contradiction with non-constancy
  apply hg_nonconst
  intro z
  by_cases hz : z ∈ Metric.closedBall 0 R
  · exact h_const z hz
  · obtain ⟨w, hw⟩ : ∃ w ∈ Metric.ball 0 R, g w ≠ g 0 := by
      by_contra h
      push_neg at h
      apply hg_nonconst
      intro z
      by_cases hz : z ∈ Metric.closedBall 0 R
      · exact h_const z hz
      · have : ∀ w ∈ Metric.ball 0 R, g w = g 0 := by
          intro w hw
          exact h w (Metric.ball_subset_closedBall hw)
        apply Complex.eq_of_forall_abs_eq (Metric.isOpen_ball.connected.isPreconnected)
        · exact hg_analytic.continuousOn.mono (Metric.ball_subset_closedBall)
        · exact hg_analytic.mono (Metric.ball_subset_closedBall)
        · exact Metric.ball_nonempty _ hR
        · intro w hw
          rw [this w hw]
          simp
    exact (h w (Metric.mem_ball_self hR)).elim