/-
Polya-Szego Problem 93
Part One, Chapter 2

Original problem:
Let $a, A, b, B$ be positive numbers $a<A, b<B$. If the two functions $f(x)$ and $g(x)$ are properly integrable over the interval $\left[x_{1}, x_{2}\right]$ and if $a \leqq f(x) \leqq A, b \leqq g(x) \leqq B$ on $\left[x_{1}, x_{2}\right]$ then

$$
1 \leqq \frac{\int_{x_{1}}^{x_{2}}[f(x)]^{2} d x \int_{x_{1}}^{x_{2}}[g(x)]^{2} d x}{\left(\int_{x_{1}}^{x_{2}} f(x) g(x) d x\right)^{2}} \leqq\left(\frac{\sqrt{\frac{A B}{a b}}+\sqrt{\frac{a b}{A B}}}{2}\right)^{2}
$$

The first inequality is identi

Formalization notes: -- 1. We formalize the inequality for Riemann integrable functions on ℝ
-- 2. We use `a ≤ f x ≤ A` and `b ≤ g x ≤ B` as bounds
-- 3. The integrals are formalized using `∫ x in x₁..x₂, f x`
-- 4. The inequality becomes two separate inequalities connected by `∧`
-- 5. We assume x₁ ≤ x₂ for the interval to be valid
-/

import Mathlib.Analysis.Calculus.Integral.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.InnerProductSpace.Basic

-- Formalization notes:
-- 1. We formalize the inequality for Riemann integrable functions on ℝ
-- 2. We use `a ≤ f x ≤ A` and `b ≤ g x ≤ B` as bounds
-- 3. The integrals are formalized using `∫ x in x₁..x₂, f x`
-- 4. The inequality becomes two separate inequalities connected by `∧`
-- 5. We assume x₁ ≤ x₂ for the interval to be valid

theorem problem_93 {x₁ x₂ : ℝ} (hx : x₁ ≤ x₂) {a A b B : ℝ} (ha_pos : 0 < a) (hA_pos : 0 < A) 
    (hb_pos : 0 < b) (hB_pos : 0 < B) (haA : a < A) (hbB : b < B)
    {f g : ℝ → ℝ} (hf_int : IntervalIntegrable f volume x₁ x₂) 
    (hg_int : IntervalIntegrable g volume x₁ x₂)
    (hf_bounds : ∀ x, x ∈ Set.Icc x₁ x₂ → a ≤ f x ∧ f x ≤ A)
    (hg_bounds : ∀ x, x ∈ Set.Icc x₁ x₂ → b ≤ g x ∧ g x ≤ B) :
    let I_f_sq := ∫ x in x₁..x₂, (f x)^2
    let I_g_sq := ∫ x in x₁..x₂, (g x)^2
    let I_fg := ∫ x in x₁..x₂, f x * g x in
    1 ≤ (I_f_sq * I_g_sq) / (I_fg)^2 ∧ 
    (I_f_sq * I_g_sq) / (I_fg)^2 ≤ ((Real.sqrt (A * B / (a * b)) + Real.sqrt (a * b / (A * B))) / 2)^2 := by
  sorry

-- Proof attempt:
theorem problem_93 {x₁ x₂ : ℝ} (hx : x₁ ≤ x₂) {a A b B : ℝ} (ha_pos : 0 < a) (hA_pos : 0 < A) 
    (hb_pos : 0 < b) (hB_pos : 0 < B) (haA : a < A) (hbB : b < B)
    {f g : ℝ → ℝ} (hf_int : IntervalIntegrable f volume x₁ x₂) 
    (hg_int : IntervalIntegrable g volume x₁ x₂)
    (hf_bounds : ∀ x, x ∈ Set.Icc x₁ x₂ → a ≤ f x ∧ f x ≤ A)
    (hg_bounds : ∀ x, x ∈ Set.Icc x₁ x₂ → b ≤ g x ∧ g x ≤ B) :
    let I_f_sq := ∫ x in x₁..x₂, (f x)^2
    let I_g_sq := ∫ x in x₁..x₂, (g x)^2
    let I_fg := ∫ x in x₁..x₂, f x * g x in
    1 ≤ (I_f_sq * I_g_sq) / (I_fg)^2 ∧ 
    (I_f_sq * I_g_sq) / (I_fg)^2 ≤ ((Real.sqrt (A * B / (a * b)) + Real.sqrt (a * b / (A * B))) / 2)^2 := by
  set I_f_sq := ∫ x in x₁..x₂, (f x)^2
  set I_g_sq := ∫ x in x₁..x₂, (g x)^2
  set I_fg := ∫ x in x₁..x₂, f x * g x
  constructor
  · -- First inequality: Cauchy-Schwarz
    have h₁ : 0 ≤ ∫ x in x₁..x₂, (f x)^2 := by
      apply intervalIntegral.integral_nonneg
      intro x hx
      exact sq_nonneg (f x)
    have h₂ : 0 ≤ ∫ x in x₁..x₂, (g x)^2 := by
      apply intervalIntegral.integral_nonneg
      intro x hx
      exact sq_nonneg (g x)
    have h₃ : (∫ x in x₁..x₂, f x * g x)^2 ≤ (∫ x in x₁..x₂, (f x)^2) * (∫ x in x₁..x₂, (g x)^2) :=
      intervalIntegral.integral_mul_le_integral_sq_mul_sq f g hf_int hg_int
    rw [div_le_one]
    · exact h₃
    · exact pow_two_pos_of_ne_zero _ (by contrapose! h₃; simp [h₃])
    · exact mul_nonneg h₁ h₂
  · -- Second inequality
    have hf_lower : ∀ x, x ∈ Set.Icc x₁ x₂ → 0 < f x := by
      intro x hx
      exact lt_of_lt_of_le ha_pos (hf_bounds x hx).1
    have hg_lower : ∀ x, x ∈ Set.Icc x₁ x₂ → 0 < g x := by
      intro x hx
      exact lt_of_lt_of_le hb_pos (hg_bounds x hx).1
    have hf_upper : ∀ x, x ∈ Set.Icc x₁ x₂ → f x ≤ A := by
      intro x hx
      exact (hf_bounds x hx).2
    have hg_upper : ∀ x, x ∈ Set.Icc x₁ x₂ → g x ≤ B := by
      intro x hx
      exact (hg_bounds x hx).2
    
    -- Apply the inequality from Problem 92 (which would be a separate lemma)
    have h_main : ∀ (t : ℝ), t ∈ Set.Icc x₁ x₂ → 
      (f t)^2 * (g t)^2 ≤ ((A * B) / (a * b) + (a * b) / (A * B) + 2) / 4 * (f t * g t)^2 := by
      intro t ht
      have hf := hf_bounds t ht
      have hg := hg_bounds t ht
      have := (mul_div_mul_comm (f t) (g t) (a * b) (A * B)).symm
      have := (mul_div_mul_comm (f t) (g t) (A * B) (a * b)).symm
      set α := f t / Real.sqrt (a * A)
      set β := g t / Real.sqrt (b * B)
      have h_alpha : 0 < α := by
        apply div_pos (hf_lower t ht)
        exact Real.sqrt_pos.mpr (mul_pos ha_pos hA_pos)
      have h_beta : 0 < β := by
        apply div_pos (hg_lower t ht)
        exact Real.sqrt_pos.mpr (mul_pos hb_pos hB_pos)
      have h_alpha_bound : α ≤ Real.sqrt (A / a) := by
        rw [div_le_div_right (Real.sqrt_pos.mpr (mul_pos ha_pos hA_pos))]
        exact hf_upper t ht
      have h_beta_bound : β ≤ Real.sqrt (B / b) := by
        rw [div_le_div_right (Real.sqrt_pos.mpr (mul_pos hb_pos hB_pos))]
        exact hg_upper t ht
      have h_alpha_lower : Real.sqrt (a / A) ≤ α := by
        rw [le_div_iff (Real.sqrt_pos.mpr (mul_pos ha_pos hA_pos))]
        exact hf_bounds t ht).1
      have h_beta_lower : Real.sqrt (b / B) ≤ β := by
        rw [le_div_iff (Real.sqrt_pos.mpr (mul_pos hb_pos hB_pos))]
        exact hg_bounds t ht).1
      have key_ineq : (α / β + β / α)^2 ≤ (Real.sqrt (A * B / (a * b)) + Real.sqrt (a * b / (A * B)))^2 := by
        have h1 : α / β ≤ Real.sqrt (A * B / (a * b)) := by
          rw [div_eq_mul_inv, Real.sqrt_div (mul_nonneg (ha_pos.le) (hA_pos.le)), 
              Real.sqrt_mul (ha_pos.le), Real.sqrt_mul (hA_pos.le), 
              ← div_mul_div, mul_comm (Real.sqrt A), ← mul_assoc, 
              ← div_mul_div, mul_comm (Real.sqrt B), ← mul_assoc]
          apply mul_le_mul h_alpha_bound h_beta_lower (by positivity) (by positivity)
        have h2 : β / α ≤ Real.sqrt (a * b / (A * B)) := by
          rw [div_eq_mul_inv, Real.sqrt_div (mul_nonneg (hb_pos.le) (hB_pos.le)), 
              Real.sqrt_mul (hb_pos.le), Real.sqrt_mul (hB_pos.le), 
              ← div_mul_div, mul_comm (Real.sqrt b), ← mul_assoc, 
              ← div_mul_div, mul_comm (Real.sqrt a), ← mul_assoc]
          apply mul_le_mul h_beta_bound h_alpha_lower (by positivity) (by positivity)
        linarith [sq_le_sq (by positivity) (by positivity).2 (add_le_add h1 h2)]
      rw [← div_pow, ← div_pow, sq_sqrt (mul_pos ha_pos hA_pos).le, sq_sqrt (mul_pos hb_pos hB_pos).le,
          mul_pow, mul_pow, ← mul_div_mul_left _ _ (mul_pos ha_pos hA_pos).ne', 
          ← mul_div_mul_left _ _ (mul_pos hb_pos hB_pos).ne']
      ring_nf
      rw [div_eq_mul_inv, div_eq_mul_inv, mul_assoc (α^2), ← mul_assoc (β^2), 
          mul_comm (β^2), mul_assoc, mul_assoc, ← add_mul, ← add_mul, 
          ← mul_add, mul_assoc, ← sq, ← sq, ← sq, ← sq]
      norm_num
      rw [mul_assoc, mul_assoc, ← mul_add, ← mul_add, mul_comm _ (4⁻¹), 
          mul_assoc, mul_assoc, mul_assoc, ← mul_add, ← mul_add]
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      rw [← Real.sqrt_div, ← Real.sqrt_div, ← Real.sqrt_mul, ← Real.sqrt_mul]
      · exact key_ineq
      all_goals positivity
    
    -- Integrate the pointwise inequality
    have h_int := intervalIntegral.integral_mono_on hx 
      (Continuous.integrableOn_Icc (by continuity) (by continuity)) 
      (Continuous.integrableOn_Icc (by continuity) (by continuity)) 
      h_main
    
    simp_rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add, 
             intervalIntegral.integral_const, smul_eq_mul] at h_int
    rw [← mul_assoc, ← mul_assoc, ← mul_add, ← mul_add, ← mul_div_right_comm, 
        ← mul_div_right_comm, ← mul_div_right_comm] at h_int
    
    have h_denom_pos : 0 < ∫ x in x₁..x₂, (f x * g x)^2 := by
      apply intervalIntegral.integral_pos_of_pos_on hx
      · exact Continuous.integrableOn_Icc (by continuity) (by continuity)
      · intro x hx
        exact pow_two_pos_of_ne_zero _ (mul_ne_zero (hf_lower x hx).ne' (hg_lower x hx).ne')
    
    rw [div_le_div_iff (mul_pos (integral_pos_of_pos_on hx 
          (Continuous.integrableOn_Icc (by continuity) (by continuity)) 
          (fun x hx => pow_two_pos_of_ne_zero _ (hf_lower x hx).ne')) 
        (integral_pos_of_pos_on hx 
          (Continuous.integrableOn_Icc (by continuity) (by continuity)) 
          (fun x hx => pow_two_pos_of_ne_zero _ (hg_lower x hx).ne'))) 
        (pow_pos h_denom_pos 2)]
    
    simp only [mul_pow]
    convert h_int using 1
    · ring
    · ring
    · field_simp
      ring
    · positivity