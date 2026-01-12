/-
Polya-Szego Problem 172
Part One, Chapter 4

Original problem:
Suppose that the polynomial $P(x)=a_{1} x+a_{2} x^{2}+\cdots+a_{r} x^{r}$ has at least one irrational coefficient. Then the numbers

$$
P(n)-[P(n)], \quad n=1,2,3, \ldots
$$

have infinitely many limit points.\\

Formalization notes: -- We formalize the key equation (118) from the book's solution, which shows that
-- the difference between the integral of f over the unit circle and 2πf(0)
-- equals an integral that vanishes as r → 1⁻.
-- The theorem captures the analytic content: for a bounded analytic function f
-- on the open unit disk with finitely many discontinuities on the boundary,
-- the integral over the unit circle equals 2πf(0).
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.MeasureTheory.Integral.IntervalIntegral

-- Formalization notes:
-- We formalize the key equation (118) from the book's solution, which shows that
-- the difference between the integral of f over the unit circle and 2πf(0)
-- equals an integral that vanishes as r → 1⁻.
-- The theorem captures the analytic content: for a bounded analytic function f
-- on the open unit disk with finitely many discontinuities on the boundary,
-- the integral over the unit circle equals 2πf(0).

theorem problem_172 {f : ℂ → ℂ} (hf_analytic : DifferentiableOn ℂ f (Metric.ball 0 1))
    (hf_bounded : ∃ M : ℝ, ∀ z ∈ Metric.ball 0 1, ‖f z‖ ≤ M)
    (hf_discontinuities : Set.Finite {θ : ℝ | ¬ContinuousAt (fun θ' : ℝ => f (Real.cos θ' + Real.sin θ' * Complex.I)) θ}) :
    (∫ θ in (0 : ℝ)..2 * π, f (Real.cos θ + Real.sin θ * Complex.I)) = 2 * π * f 0 := by
  sorry

-- Proof attempt:
theorem problem_172 {f : ℂ → ℂ} (hf_analytic : DifferentiableOn ℂ f (Metric.ball 0 1))
    (hf_bounded : ∃ M : ℝ, ∀ z ∈ Metric.ball 0 1, ‖f z‖ ≤ M)
    (hf_discontinuities : Set.Finite {θ : ℝ | ¬ContinuousAt (fun θ' : ℝ => f (Real.cos θ' + Real.sin θ' * Complex.I)) θ}) :
    (∫ θ in (0 : ℝ)..2 * π, f (Real.cos θ + Real.sin θ * Complex.I)) = 2 * π * f 0 := by
  -- First apply Cauchy's integral formula for the unit disk
  have cauchy_integral : ∀ r ∈ Ioo (0 : ℝ) 1,
      (∫ θ in 0..2 * π, f (r * (Real.cos θ + Real.sin θ * Complex.I))) = 2 * π * f 0 := by
    intro r hr
    have h_cont : ContinuousOn (fun z => f z) (Metric.sphere 0 r) :=
      hf_analytic.continuousOn.mono (Metric.sphere_subset_ball hr.2)
    have h_int : CircleIntegrable f r :=
      ContinuousOn.circleIntegrable h_cont (by linarith [hr.1])
    rw [← Complex.two_pi_I_inv_smul_circleIntegral_sub_inv_smul hf_analytic.differentiableOn
      (Metric.ball_mem_nhds 0 hr.2) h_int]
    simp [hr.1.ne']

  -- Set up for dominated convergence
  let F : ℝ → ℂ → ℂ := fun r z => f (r * z)
  let g : ℝ → ℝ → ℂ := fun r θ => f (r * (Real.cos θ + Real.sin θ * Complex.I))
  
  -- Show the integral converges to the desired value as r → 1⁻
  have main : Tendsto (fun r => ∫ θ in 0..2 * π, g r θ) (𝓝[<] 1) (𝓝 (2 * π * f 0)) := by
    refine tendsto_integral_of_dominated_convergence_bound _ _ _ _ _ _
    · -- Dominating function
      obtain ⟨M, hM⟩ := hf_bounded
      use fun θ => M
      · intro r hr θ hθ
        simp only [g]
        apply hM
        simp [Complex.norm_eq_abs, Complex.abs_mul, Complex.abs_cos_add_sin_mul_I]
        exact (mul_lt_one_of_nonneg_of_lt_one_left (mem_Ioo.mp hr).1.le (mem_Ioo.mp hr).2) rfl
      · exact MeasureTheory.IntegrableOn.const M
    · -- Almost everywhere convergence
      rw [ae_restrict_iff']
      · intro θ hθ
        apply ContinuousAt.tendsto
        have h_cont : ContinuousAt (fun r => g r θ) 1 := by
          simp only [g]
          refine ContinuousAt.comp ?_ (continuousAt_const.mul (continuousAt_id))
          by_cases h : ContinuousAt (fun θ' => f (Real.cos θ' + Real.sin θ' * Complex.I)) θ
          · exact hf_analytic.continuousAt (Metric.ball_mem_nhds 0 one_pos)
          · have : θ ∉ {θ | ¬ContinuousAt (fun θ' => f (Real.cos θ' + Real.sin θ' * Complex.I)) θ} := h
            simp only [mem_setOf_eq, not_not] at this
            exact this
        exact h_cont
      · exact measurableSet_Ioi
    · -- Integrability
      intro r hr
      obtain ⟨M, hM⟩ := hf_bounded
      apply MeasureTheory.Integrable.mono' (MeasureTheory.IntegrableOn.const M)
      · intro θ _
        exact hM _ (by simp [Complex.norm_eq_abs, Complex.abs_mul, Complex.abs_cos_add_sin_mul_I];
          exact (mul_lt_one_of_nonneg_of_lt_one_left (mem_Ioo.mp hr).1.le (mem_Ioo.mp hr).2) rfl)
      · exact MeasureTheory.aestronglyMeasurable_const
    · -- Limit
      filter_upwards [self_mem_nhdsWithin] with r hr
      exact cauchy_integral r (mem_Ioo.mpr ⟨zero_lt_one.trans_lt hr, hr⟩)
  
  -- Take limit as r → 1⁻
  have : (∫ θ in 0..2 * π, f (Real.cos θ + Real.sin θ * Complex.I)) = 
         Tendsto.limUnder (𝓝[<] 1) (fun r => ∫ θ in 0..2 * π, g r θ) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
    simp [g]
    congr
    simp [Complex.exp_eq_cos_add_sin_mul_I]
  
  rw [this, tendsto.limUnder_eq main]