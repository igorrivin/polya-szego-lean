/-
Polya-Szego Problem 74
Part One, Chapter 2

Original problem:
Assume that $\varphi(t)$ is a convex function defined on $[m, M]$, that $p_{1}, p_{2}, \ldots, p_{n}$ are arbitrary positive numbers and that $t_{1}, t_{2}, \ldots, t_{n}$ are arbitrary points of the interval $[m, M]$. Then we have the inequality

$$
\varphi\left(\frac{p_{1} t_{1}+p_{2} t_{2}+\cdots+p_{n} t_{n}}{p_{1}+p_{2}+\cdots+p_{n}}\right) \leqq \frac{p_{1} \varphi\left(t_{1}\right)+p_{2} \varphi\left(t_{2}\right)+\cdots+p_{n} \varphi\left(t_{n}\right)}{p_{1}+p_{2}+\cdots+p_{n}}
$$

\begin{

Formalization notes: -- 1. We formalize the integral version of Jensen's inequality (Problem 74)
-- 2. We assume φ is convex on [m, M]
-- 3. We assume f is measurable and bounded between m and M
-- 4. We assume p is nonnegative and integrable with positive integral
-- 5. We use the Lebesgue integral framework from Mathlib
-/

import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Calculus.MeanInequalities
import Mathlib.MeasureTheory.Integral.IntervalIntegral

-- Formalization notes:
-- 1. We formalize the integral version of Jensen's inequality (Problem 74)
-- 2. We assume φ is convex on [m, M]
-- 3. We assume f is measurable and bounded between m and M
-- 4. We assume p is nonnegative and integrable with positive integral
-- 5. We use the Lebesgue integral framework from Mathlib

theorem jensen_integral_inequality {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] 
    [CompleteSpace E] {m M : ℝ} (hmM : m ≤ M) (φ : ℝ → E) (hf_convex : ConvexOn ℝ (Set.Icc m M) φ)
    {f p : ℝ → ℝ} (hf_meas : Measurable f) (hp_meas : Measurable p) 
    (hf_range : ∀ x, x ∈ Set.Icc (x₁ : ℝ) x₂ → f x ∈ Set.Icc m M)
    (hp_nonneg : ∀ x, 0 ≤ p x) (h_int_pos : 0 < ∫ x in x₁..x₂, p x) :
    φ (∫ x in x₁..x₂, (p x • f x) / ∫ x in x₁..x₂, p x) ≤ 
    (∫ x in x₁..x₂, p x • φ (f x)) / ∫ x in x₁..x₂, p x := by
  sorry

-- Proof attempt:
theorem jensen_integral_inequality {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] 
    [CompleteSpace E] {m M : ℝ} (hmM : m ≤ M) (φ : ℝ → E) (hf_convex : ConvexOn ℝ (Set.Icc m M) φ)
    {f p : ℝ → ℝ} (hf_meas : Measurable f) (hp_meas : Measurable p) 
    (hf_range : ∀ x, x ∈ Set.Icc (x₁ : ℝ) x₂ → f x ∈ Set.Icc m M)
    (hp_nonneg : ∀ x, 0 ≤ p x) (h_int_pos : 0 < ∫ x in x₁..x₂, p x) :
    φ (∫ x in x₁..x₂, (p x • f x) / ∫ x in x₁..x₂, p x) ≤ 
    (∫ x in x₁..x₂, p x • φ (f x)) / ∫ x in x₁..x₂, p x := by
  -- First, let's define the probability measure μ
  let μ : Measure ℝ := Measure.withDensity (volume.restrict (Set.Icc x₁ x₂)) fun x => ENNReal.ofReal (p x)
  
  -- Show that μ is a probability measure
  have hμ : μ Set.univ = ENNReal.ofReal (∫ x in x₁..x₂, p x) := by
    simp [μ, Measure.withDensity]
    rw [← intervalIntegral.integral_of_le (le_of_lt h_int_pos)]
    exact MeasureTheory.set_integral_const (le_of_lt h_int_pos)
  
  -- Apply Jensen's inequality for integrals
  refine ConvexOn.map_integral_le ?_ ?_ ?_ ?_ ?_
  · exact hf_convex
  · exact Measurable.aestronglyMeasurable (hf_meas.comp measurable_id)
  · exact Measurable.aestronglyMeasurable (hp_meas.comp measurable_id)
  · intro x hx
    exact hf_range x hx
  · rw [hμ]
    exact ENNReal.ofReal_pos.mpr h_int_pos