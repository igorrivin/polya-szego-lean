/-
Polya-Szego Problem 81
Part One, Chapter 2

Original problem:
Suppose that $f(x)$ and $g(x)$ denote two functions that are properly integrable over the interval $\left[x_{1}, x_{2}\right]$. Then

$$
\left(\int_{x_{1}}^{x_{2}} f(x) g(x) d x\right)^{2} \leqq \int_{x_{1}}^{x_{2}}[f(x)]^{2} d x \int_{x_{1}}^{x_{2}}[g(x)]^{2} d x
$$

(Schwarz's inequality.)\\

Formalization notes: -- 1. We formalize the Cauchy-Schwarz inequality for integrals (also known as the Schwarz inequality)
-- 2. We use `IntegrableOn` to ensure functions are properly integrable on the interval
-- 3. The inequality is stated for real-valued functions on a closed interval [a, b]
-- 4. We use ℝ for the real numbers and `∫ x in a..b, f x` for the definite integral
-- 5. The theorem is a special case of the more general Cauchy-Schwarz inequality in inner product spaces
-/

import Mathlib.Analysis.Calculus.Integral.Basic
import Mathlib.Analysis.InnerProductSpace.Basic

-- Formalization notes:
-- 1. We formalize the Cauchy-Schwarz inequality for integrals (also known as the Schwarz inequality)
-- 2. We use `IntegrableOn` to ensure functions are properly integrable on the interval
-- 3. The inequality is stated for real-valued functions on a closed interval [a, b]
-- 4. We use ℝ for the real numbers and `∫ x in a..b, f x` for the definite integral
-- 5. The theorem is a special case of the more general Cauchy-Schwarz inequality in inner product spaces

theorem schwarz_inequality_integral {a b : ℝ} (hab : a ≤ b) {f g : ℝ → ℝ}
    (hf : IntegrableOn f (Set.Icc a b)) (hg : IntegrableOn g (Set.Icc a b)) :
    (∫ x in a..b, f x * g x) ^ 2 ≤ (∫ x in a..b, f x ^ 2) * (∫ x in a..b, g x ^ 2) := by
  sorry

-- Proof attempt:
theorem schwarz_inequality_integral {a b : ℝ} (hab : a ≤ b) {f g : ℝ → ℝ}
    (hf : IntegrableOn f (Set.Icc a b)) (hg : IntegrableOn g (Set.Icc a b)) :
    (∫ x in a..b, f x * g x) ^ 2 ≤ (∫ x in a..b, f x ^ 2) * (∫ x in a..b, g x ^ 2) := by
  -- First show that f^2 and g^2 are integrable
  have hf2 : IntegrableOn (fun x => f x ^ 2) (Set.Icc a b) := by
    apply IntegrableOn.mono hf (fun x hx => ?_)
    simp only [Set.mem_Icc] at hx
    exact sq_nonneg (f x)
  have hg2 : IntegrableOn (fun x => g x ^ 2) (Set.Icc a b) := by
    apply IntegrableOn.mono hg (fun x hx => ?_)
    simp only [Set.mem_Icc] at hx
    exact sq_nonneg (g x)
  
  -- Show that f*g is integrable
  have hfg : IntegrableOn (fun x => f x * g x) (Set.Icc a b) := by
    apply Integrable.mul_continuousOn hf hg
    exact continuousOn_id.mul continuousOn_id
  
  -- Apply the Cauchy-Schwarz inequality for inner product spaces
  -- We're using the L² space with the inner product ∫ f g
  let μ : Measure ℝ := volume.restrict (Set.Icc a b)
  have := @inner_mul_inner_self_le ℝ (Lp ℝ 2 μ) _ _ (MeasureTheory.Lp.mk 2 (hf.toL1 f)) (MeasureTheory.Lp.mk 2 (hg.toL1 g))
  
  -- Convert back to integrals
  simp only [MeasureTheory.Lp.inner_def, MeasureTheory.L2.inner_def, MeasureTheory.Lp.mk_eq_mk,
    MeasureTheory.Memℒp.toLp_coe_fn, MeasureTheory.Memℒp.toLp_eq_toLp] at this
  simp [← MeasureTheory.set_integral_eq_integral, ← MeasureTheory.integral_mul_left, ← MeasureTheory.integral_mul_right] at this
  
  -- The integrals are exactly what we need
  exact this