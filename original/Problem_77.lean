/-
Polya-Szego Problem 77
Part One, Chapter 2

Original problem:
The functions $f(x)$ and $p(x)$ are assumed to be continuous on the interval $\left[x_{1}, x_{2}\right], p(x)$ is strictly positive and $m \leqq f(x) \leqq M$; the function $\varphi(t)$ is defined on the interval $[m, M], \varphi(t)$ can be differentiated twice

Etherval $[m, M]$ tesec $(t)$ is strictly L. function can Bices not exist at

$$
(c>0)
$$

on. [m, M], that $c_{2}, t_{2}, \ldots, t_{n}$ are the inequality\\
$\frac{p_{n} q\left(t_{n}\right)}{p_{n}}$.\\
are properly $20 \int_{x_{i}}^{x_

Formalization notes: -- This formalizes Jensen's inequality for integrals with a positive weight function p.
-- We assume:
-- 1. f and p are continuous on [x₁, x₂]
-- 2. p is strictly positive on [x₁, x₂]
-- 3. f takes values in [m, M]
-- 4. φ is twice differentiable on [m, M] with φ'' > 0 (hence strictly convex)
-- 5. The conclusion is the weighted Jensen inequality
-- Note: We use `StrictConvexOn` to capture φ'' > 0 condition
-/

import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Calculus.MeanInequalities
import Mathlib.MeasureTheory.Integral.IntervalIntegral

-- Formalization notes:
-- This formalizes Jensen's inequality for integrals with a positive weight function p.
-- We assume:
-- 1. f and p are continuous on [x₁, x₂]
-- 2. p is strictly positive on [x₁, x₂]
-- 3. f takes values in [m, M]
-- 4. φ is twice differentiable on [m, M] with φ'' > 0 (hence strictly convex)
-- 5. The conclusion is the weighted Jensen inequality
-- Note: We use `StrictConvexOn` to capture φ'' > 0 condition

theorem problem_77 {x₁ x₂ m M : ℝ} (hx : x₁ ≤ x₂) 
    (f p : ℝ → ℝ) (φ : ℝ → ℝ)
    (hf_cont : ContinuousOn f (Set.Icc x₁ x₂))
    (hp_cont : ContinuousOn p (Set.Icc x₁ x₂))
    (hp_pos : ∀ x, x₁ ≤ x → x ≤ x₂ → p x > 0)
    (hf_range : ∀ x, x₁ ≤ x → x ≤ x₂ → m ≤ f x ∧ f x ≤ M)
    (hφ_diff : ∀ t, m ≤ t → t ≤ M → DifferentiableAt ℝ φ t)
    (hφ_convex : StrictConvexOn ℝ (Set.Icc m M) φ) :
    let I₁ := ∫ x in x₁..x₂, p x * f x
    let I₂ := ∫ x in x₁..x₂, p x
    have hI₂_pos : I₂ > 0 := by
      refine intervalIntegral_pos_of_continuousOn_of_nonneg' ?_ ?_ hx
      · exact hp_cont.mono (Set.Icc_subset_Icc_right (by linarith))
      · intro x hx; exact le_of_lt (hp_pos x hx.1 hx.2)
    φ (I₁ / I₂) ≤ (∫ x in x₁..x₂, p x * φ (f x)) / I₂ := by
  intro I₁ I₂ hI₂_pos
  sorry

-- Proof attempt:
intro I₁ I₂ hI₂_pos
let μ : Measure ℝ := MeasureTheory.Measure.withDensity (MeasureTheory.volume.restrict (Set.Icc x₁ x₂)) 
  fun x => p x * Set.indicator (Set.Icc x₁ x₂) 1 x
have hμ_finite : IsProbabilityMeasure μ := by
  constructor
  rw [MeasureTheory.Measure.withDensity_apply]
  · simp only [MeasureTheory.Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    rw [← intervalIntegral.integral_of_le hx]
    simp [I₂]
  · exact Measurable.indicator measurable_const (measurableSet_Icc)

have hf_meas : Measurable f := by
  exact continuousOn_iff_continuous_restrict.1 hf_cont |>.measurable

have hφ_convex' : ConvexOn ℝ (Set.Icc m M) φ := hφ_convex.convexOn

have h_integrable : μ.Integrable f := by
  refine ⟨hf_meas.aestronglyMeasurable, ?_⟩
  rw [MeasureTheory.HasFiniteIntegral]
  simp only [μ, MeasureTheory.Measure.withDensity_apply _ (hf_meas (measurableSet_Icc))]
  refine lt_of_le_of_lt ?_ (ENNReal.ofReal_lt_top)
  apply intervalIntegral.integral_mono_on hx
  · exact (hp_cont.mul (continuousOn_const.mul hf_cont)).integrableOn_Icc
  · exact (hp_cont.mul continuousOn_const).integrableOn_Icc
  · intro x hx'
    rcases hf_range x hx'.1 hx'.2 with ⟨hfm, hfM⟩
    simp only [Set.indicator, Set.mem_Icc, hx'.1, hx'.2, ite_true]
    simp only [mul_one]
    exact mul_le_mul_of_nonneg_left (max_le_iff.2 ⟨hfm, hfM⟩) (le_of_lt (hp_pos x hx'.1 hx'.2))

have hφ_integrable : μ.Integrable (φ ∘ f) := by
  refine ⟨(Continuous.comp_continuousOn hf_cont hφ_diff).measurable.aestronglyMeasurable, ?_⟩
  rw [MeasureTheory.HasFiniteIntegral]
  simp only [μ, MeasureTheory.Measure.withDensity_apply _ ((Continuous.comp_continuousOn hf_cont hφ_diff).measurable (measurableSet_Icc))]
  refine lt_of_le_of_lt ?_ (ENNReal.ofReal_lt_top)
  apply intervalIntegral.integral_mono_on hx
  · exact (hp_cont.mul (continuousOn_const.mul (Continuous.comp_continuousOn hf_cont hφ_diff))).integrableOn_Icc
  · exact (hp_cont.mul continuousOn_const).integrableOn_Icc
  · intro x hx'
    rcases hf_range x hx'.1 hx'.2 with ⟨hfm, hfM⟩
    simp only [Set.indicator, Set.mem_Icc, hx'.1, hx'.2, ite_true]
    simp only [mul_one]
    exact mul_le_mul_of_nonneg_left (max_le_iff.2 ⟨hφ_convex.1 hfm hfM, hφ_convex.1 hfm hfM⟩) 
      (le_of_lt (hp_pos x hx'.1 hx'.2))

have key := ConvexOn.map_integral_le μ hφ_convex' hμ_finite hf_meas h_integrable hφ_integrable

simp only [μ, MeasureTheory.Measure.withDensity_apply _ (hf_meas (measurableSet_Icc)), 
  MeasureTheory.Measure.restrict_apply MeasurableSet.univ, Set.univ_inter] at key

have I₁_eq : I₁ = ∫ x in x₁..x₂, p x * f x := rfl
have I₂_eq : I₂ = ∫ x in x₁..x₂, p x := rfl

rw [I₁_eq, I₂_eq] at key
simp only [intervalIntegral.integral_of_le hx] at key

convert key using 2
· congr
  rw [div_eq_inv_mul, mul_comm, ← mul_assoc, inv_mul_cancel (ne_of_gt hI₂_pos), one_mul]
· simp only [div_eq_inv_mul, intervalIntegral.integral_of_le hx]
  congr
  ext x
  rw [mul_assoc]