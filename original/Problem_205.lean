/-
Polya-Szego Problem 205
Part Three, Chapter 4

Original problem:
Suppose that $f(t)$ is a positive valued, never decreasing function, defined on the interval $0 \leqq t<1$ and that its integral $\int_{0}^{1} f(t) d t$ is finite. The entire function

$$
\int_{0}^{1} f(t) \cos z t d t
$$

has real zeros only. [185.]\\

Formalization notes: -- 1. We formalize the statement: If f is a positive, non-decreasing function on [0,1) 
--    with finite integral, then the entire function F(z) = ∫₀¹ f(t) cos(zt) dt has only real zeros.
-- 2. We use `intervalIntegral` for the Riemann integral.
-- 3. The "entire function" property means F is analytic on ℂ.
-- 4. "Real zeros only" means all zeros of F are in ℝ.
-- 5. We assume f is measurable and integrable on [0,1).
-- 6. The condition "0 ≤ t < 1" is represented as `Set.Ico (0 : ℝ) 1`.
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Calculus.FTC
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral

-- Formalization notes:
-- 1. We formalize the statement: If f is a positive, non-decreasing function on [0,1) 
--    with finite integral, then the entire function F(z) = ∫₀¹ f(t) cos(zt) dt has only real zeros.
-- 2. We use `intervalIntegral` for the Riemann integral.
-- 3. The "entire function" property means F is analytic on ℂ.
-- 4. "Real zeros only" means all zeros of F are in ℝ.
-- 5. We assume f is measurable and integrable on [0,1).
-- 6. The condition "0 ≤ t < 1" is represented as `Set.Ico (0 : ℝ) 1`.

theorem problem_205 {f : ℝ → ℝ} 
    (hpos : ∀ t, t ∈ Set.Ico (0 : ℝ) 1 → 0 < f t)
    (hmono : ∀ x y, x ∈ Set.Ico (0 : ℝ) 1 → y ∈ Set.Ico (0 : ℝ) 1 → x ≤ y → f x ≤ f y)
    (hint : ∫ t in (0:ℝ)..1, f t ≠ ∞) : 
    let F : ℂ → ℂ := fun z => ∫ t in (0:ℝ)..1, (f t : ℂ) * Complex.cos (z * (t : ℂ))
    in FunctionAnalyticOn ℂ F Set.univ ∧ 
       ∀ z : ℂ, F z = 0 → z.im = 0 := by
  sorry

-- Proof attempt:
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Calculus.FTC
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Analysis.Complex.UpperHalfPlane
import Mathlib.Analysis.Fourier.PoissonSummation

open Complex Set MeasureTheory intervalIntegral

theorem problem_205 {f : ℝ → ℝ} 
    (hpos : ∀ t, t ∈ Ico (0 : ℝ) 1 → 0 < f t)
    (hmono : ∀ x y, x ∈ Ico (0 : ℝ) 1 → y ∈ Ico (0 : ℝ) 1 → x ≤ y → f x ≤ f y)
    (hint : ∫ t in (0:ℝ)..1, f t ≠ ∞) : 
    let F : ℂ → ℂ := fun z => ∫ t in (0:ℝ)..1, (f t : ℂ) * cos (z * (t : ℂ))
    in FunctionAnalyticOn ℂ F Set.univ ∧ 
       ∀ z : ℂ, F z = 0 → z.im = 0 := by
  intro F
  constructor
  · -- Show F is entire
    apply AnalyticOn.integral
    · exact measurableSet_Ioc
    · intro t ht
      apply AnalyticOn.const_mul
      apply Complex.analyticOn_cos.comp
      apply AnalyticOn.mul
      · exact analyticOn_const
      · exact analyticOn_id
    · intro t ht
      exact Continuous.aestronglyMeasurable <| by
        apply Continuous.mul
        · exact continuous_ofReal.comp (continuous_const : Continuous fun _ : ℂ => f t)
        · exact Complex.continuous_cos.comp (Continuous.mul continuous_id continuous_const)
    · rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
      apply IntervalIntegrable.const_mul
      apply intervalIntegrable_of_integrableOn
      · exact measurableSet_Ioc
      · rw [← integrableOn_Ioc_iff_integrableOn_Ioo]
        apply Integrable.mono' hint
        · exact measurable_of_continuousOn (ContinuousOn.mono continuousOn_id isOpen_Ioc.measurableSet subset_closure)
        · apply eventually_of_forall
          intro t ht
          rw [norm_of_nonneg (hpos t ht).le]
          exact le_rfl

  · -- Show zeros are real
    intro z hz
    -- Suppose for contradiction z has positive imaginary part
    by_contra h
    push_neg at h
    have hz_im_ne : z.im ≠ 0 := h
    wlog hz_im_pos : 0 < z.im using z
    · have : 0 < (-z).im := by simp [hz_im_ne, hz_im_pos]
      have : F (-z) = 0 := by
        simp [F, ← integral_neg, ← Complex.cos_neg, neg_mul, mul_comm]
      exact this (this (by simpa using hz))
    
    -- Key estimate using monotonicity and positivity
    have key : 0 < (∫ t in (0:ℝ)..1, f t * Real.cosh (z.im * t)).re := by
      refine integral_pos_of_pos_on measurableSet_Ioc ?_ ?_
      · intro t ht
        refine mul_pos (hpos t ht) ?_
        exact Real.cosh_pos _
      · apply Continuous.aestronglyMeasurable
        exact Continuous.mul (continuous_ofReal.comp (continuous_const)) 
          (Real.continuous_cosh.comp (Continuous.mul continuous_const continuous_id))
    
    -- Compute F(z) in terms of its real and imaginary parts
    have : F z = ∫ t in (0:ℝ)..1, f t * (cos (z.re * t) * cosh (z.im * t) - 
          sin (z.re * t) * sinh (z.im * t) * I) := by
      refine integral_congr fun t _ => ?_
      rw [← Complex.cos_add_mul_I]
      ring_nf
      congr
      rw [mul_comm]
    
    -- Extract imaginary part
    have im_part : (F z).im = -∫ t in (0:ℝ)..1, f t * sin (z.re * t) * sinh (z.im * t) := by
      rw [this]
      simp [integral_of_real, ← intervalIntegral.integral_of_real]
    
    -- Show imaginary part is negative (contradicting F(z) = 0)
    have : (F z).im < 0 := by
      refine integral_neg_of_neg_on measurableSet_Ioc ?_ ?_
      · intro t ht
        refine mul_pos (hpos t ht) <| mul_pos ?_ ?_
        · exact Real.sin_pos_of_pos_of_lt_pi (mul_pos (by linarith) ht.1) (by nlinarith [ht.2])
        · exact Real.sinh_pos (mul_pos hz_im_pos ht.1)
      · apply Continuous.aestronglyMeasurable
        exact Continuous.mul (continuous_ofReal.comp continuous_const)
          (Continuous.mul (Real.continuous_sin.comp (Continuous.mul continuous_const continuous_id))
            (Real.continuous_sinh.comp (Continuous.mul continuous_const continuous_id)))
    
    linarith [this, hz]