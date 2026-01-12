/-
Polya-Szego Problem 14
Part Three, Chapter 1

Original problem:
We assume that the real functions $f(t)$ and $\varphi(t)$ are defined on the interval $a \leqq t \leqq b$, that $f(t)$ is positive and continuous and $\varphi(t)$ properly integrable. Then

$$
\left|\int_{a}^{b} f(t) e^{i \varphi(t)} d t\right| \leqq \int_{a}^{b} f(t) d t
$$

Equality holds if and only if the function $\varphi(t)$ assumes the same value $\bmod 2 \pi$ at all its points of continuity.\\

Formalization notes: -- 1. We use `intervalIntegral` for ∫_a^b
-- 2. `f` is continuous and positive on [a, b]
-- 3. `φ` is integrable on [a, b] (using `IntegrableOn` for proper Riemann integrability)
-- 4. The inequality |∫ f(t) * exp(i * φ(t)) dt| ≤ ∫ f(t) dt
-- 5. The equality condition: φ(t) is constant mod 2π at all continuity points
-- Note: The "points of continuity" condition is subtle; we formalize a sufficient condition
-- where φ is constant mod 2π almost everywhere (which holds if it's constant at all continuity points)
-/

import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Analysis.Complex.Basic

-- Formalization notes:
-- 1. We use `intervalIntegral` for ∫_a^b
-- 2. `f` is continuous and positive on [a, b]
-- 3. `φ` is integrable on [a, b] (using `IntegrableOn` for proper Riemann integrability)
-- 4. The inequality |∫ f(t) * exp(i * φ(t)) dt| ≤ ∫ f(t) dt
-- 5. The equality condition: φ(t) is constant mod 2π at all continuity points
-- Note: The "points of continuity" condition is subtle; we formalize a sufficient condition
-- where φ is constant mod 2π almost everywhere (which holds if it's constant at all continuity points)

theorem problem_14 {a b : ℝ} (hab : a ≤ b) {f φ : ℝ → ℝ}
    (hf_cont : ContinuousOn f (Set.Icc a b))
    (hf_pos : ∀ t, t ∈ Set.Icc a b → 0 < f t)
    (hφ_int : IntervalIntegrable φ MeasureTheory.volume a b) :
    Complex.abs (∫ t in a..b, (f t : ℂ) * Complex.exp (Complex.I * (φ t : ℂ))) ≤ 
    ∫ t in a..b, f t := by
  sorry

-- Alternative version with more precise equality condition
theorem problem_14_with_equality {a b : ℝ} (hab : a ≤ b) {f φ : ℝ → ℝ}
    (hf_cont : ContinuousOn f (Set.Icc a b))
    (hf_pos : ∀ t, t ∈ Set.Icc a b → 0 < f t)
    (hφ_int : IntervalIntegrable φ MeasureTheory.volume a b) :
    let I := ∫ t in a..b, (f t : ℂ) * Complex.exp (Complex.I * (φ t : ℂ)) in
    Complex.abs I ≤ ∫ t in a..b, f t ∧
    (Complex.abs I = ∫ t in a..b, f t ↔ 
      ∃ (c : ℝ), ∀ᵐ t ∂MeasureTheory.volume.restrict (Set.Icc a b), 
        φ t - c ∈ Set.range (fun (k : ℤ) => (k : ℝ) * (2 * π))) := by
  sorry

-- Proof attempt:
theorem problem_14 {a b : ℝ} (hab : a ≤ b) {f φ : ℝ → ℝ}
    (hf_cont : ContinuousOn f (Set.Icc a b))
    (hf_pos : ∀ t, t ∈ Set.Icc a b → 0 < f t)
    (hφ_int : IntervalIntegrable φ MeasureTheory.volume a b) :
    Complex.abs (∫ t in a..b, (f t : ℂ) * Complex.exp (Complex.I * (φ t : ℂ))) ≤ 
    ∫ t in a..b, f t := by
  set I := ∫ t in a..b, (f t : ℂ) * Complex.exp (Complex.I * (φ t : ℂ)) with hI
  set θ := Complex.arg I with hθ
  have hI_eq : Complex.abs I = Complex.re (Complex.exp (-Complex.I * θ) * I) := by
    simp [hθ, Complex.abs_eq_re_of_exp_mul_I]
  rw [hI_eq]
  have h_re_le : Complex.re (Complex.exp (-Complex.I * θ) * I) ≤ ∫ t in a..b, f t := by
    rw [← intervalIntegral.integral_of_le hab]
    simp_rw [← intervalIntegral.integral_of_le hab, Complex.exp_neg, mul_assoc]
    have : Complex.re (∫ t in a..b, (f t : ℂ) * Complex.exp (Complex.I * (φ t - θ))) =
           ∫ t in a..b, f t * Real.cos (φ t - θ) := by
      rw [intervalIntegral.integral_re, ← intervalIntegral.integral_of_le hab]
      refine intervalIntegral.integral_congr_ae hab ?_
      filter_upwards with t ht using ?_
      simp [Complex.exp_mul_I, Complex.re]
      ring_nf
    rw [this]
    have hcos_le : ∀ t, t ∈ Set.Icc a b → Real.cos (φ t - θ) ≤ 1 := by
      intro t ht; exact Real.cos_le_one _
    have hf_nonneg : ∀ t, t ∈ Set.Icc a b → 0 ≤ f t := by
      intro t ht; exact le_of_lt (hf_pos t ht)
    refine intervalIntegral.integral_mono_on hab ?_ ?_ ?_
    · exact ContinuousOn.mul hf_cont (ContinuousOn.cos (hφ_int.1.sub continuousOn_const))
    · exact hf_cont
    · intro t ht; exact mul_le_mul_of_nonneg_left (hcos_le t ht) (hf_nonneg t ht)
  exact h_re_le

theorem problem_14_with_equality {a b : ℝ} (hab : a ≤ b) {f φ : ℝ → ℝ}
    (hf_cont : ContinuousOn f (Set.Icc a b))
    (hf_pos : ∀ t, t ∈ Set.Icc a b → 0 < f t)
    (hφ_int : IntervalIntegrable φ MeasureTheory.volume a b) :
    let I := ∫ t in a..b, (f t : ℂ) * Complex.exp (Complex.I * (φ t : ℂ)) in
    Complex.abs I ≤ ∫ t in a..b, f t ∧
    (Complex.abs I = ∫ t in a..b, f t ↔ 
      ∃ (c : ℝ), ∀ᵐ t ∂MeasureTheory.volume.restrict (Set.Icc a b), 
        φ t - c ∈ Set.range (fun (k : ℤ) => (k : ℝ) * (2 * π))) := by
  intro I
  constructor
  · exact problem_14 hab hf_cont hf_pos hφ_int
  · constructor
    { intro h
      set θ := Complex.arg I with hθ
      have hI_eq : Complex.abs I = Complex.re (Complex.exp (-Complex.I * θ) * I) := by
        simp [hθ, Complex.abs_eq_re_of_exp_mul_I]
      rw [hI_eq] at h
      have h_re_eq : Complex.re (Complex.exp (-Complex.I * θ) * I) = ∫ t in a..b, f t := by
        linarith [problem_14 hab hf_cont hf_pos hφ_int]
      have hcos_eq : ∀ᵐ t ∂MeasureTheory.volume.restrict (Set.Icc a b), Real.cos (φ t - θ) = 1 := by
        have h_int : ∫ t in a..b, f t * (1 - Real.cos (φ t - θ)) = 0 := by
          rw [← sub_eq_zero, ← intervalIntegral.integral_sub, ← h_re_eq]
          simp_rw [← intervalIntegral.integral_of_le hab, Complex.exp_neg, mul_assoc]
          rw [intervalIntegral.integral_re, ← intervalIntegral.integral_of_le hab]
          refine intervalIntegral.integral_congr_ae hab ?_
          filter_upwards with t ht using ?_
          simp [Complex.exp_mul_I, Complex.re]
          ring_nf
        have h_nonneg : ∀ᵐ t ∂MeasureTheory.volume.restrict (Set.Icc a b), 0 ≤ f t * (1 - Real.cos (φ t - θ)) := by
          filter_upwards with t ht
          refine mul_nonneg (le_of_lt (hf_pos t ht)) ?_
          simp only [sub_nonneg]
          exact Real.cos_le_one _
        rw [intervalIntegral.integral_eq_zero_iff_of_nonneg_ae h_nonneg] at h_int
        filter_upwards [h_int] with t ht
        have hft_pos : f t ≠ 0 := by exact ne_of_gt (hf_pos t (by assumption))
        simp only [mul_eq_zero, sub_eq_zero] at ht
        cases ht with
        | inl h => exact False.elim (hft_pos h)
        | inr h => exact h
      use θ
      filter_upwards [hcos_eq] with t ht
      rw [Real.cos_eq_one_iff] at ht
      exact ht }
    { rintro ⟨c, hc⟩
      have hφ_eq : ∀ᵐ t ∂MeasureTheory.volume.restrict (Set.Icc a b), ∃ k : ℤ, φ t = c + k * (2 * π) := by
        filter_upwards [hc] with t ht
        simp at ht
        obtain ⟨k, hk⟩ := ht
        use k
        rw [sub_eq_iff_eq_add] at hk
        exact hk.symm
      have h_exp_eq : ∀ᵐ t ∂MeasureTheory.volume.restrict (Set.Icc a b),
          Complex.exp (Complex.I * φ t) = Complex.exp (Complex.I * c) := by
        filter_upwards [hφ_eq] with t ht
        obtain ⟨k, hk⟩ := ht
        simp [hk]
        rw [Complex.exp_add, Complex.exp_mul_I_int_mul_two_pi]
        simp }
      simp_rw [Complex.abs, Complex.norm_eq_abs]
      rw [intervalIntegral.integral_congr_ae hab h_exp_eq]
      simp [Complex.abs_exp, ← intervalIntegral.integral_of_le hab] }