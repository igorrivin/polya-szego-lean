/-
Polya-Szego Problem 6
Part Three, Chapter 1

Original problem:
Suppose $\Re a>0$. For any point of the $z$-plane

$$
\left|\frac{a-z}{\bar{a}+z}\right|
$$

is either $<1$, or $=1$, or $>1$, and so the whole plane is divided into three subsets. Describe them.\\

Formalization notes: -- 1. We formalize the complex plane using ℂ in Mathlib4
-- 2. We represent the expression |(a - z)/(conj a + z)| as a complex norm
-- 3. We formalize the three cases described in the problem
-- 4. We'll assume a is fixed with positive real part and prove properties for all z
-- 5. We use the standard notation: Complex.re for real part, ‖x‖ for modulus
-- 6. Note: in Lean, Complex.conj is the complex conjugate
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Complex.Module

-- Formalization notes:
-- 1. We formalize the complex plane using ℂ in Mathlib4
-- 2. We represent the expression |(a - z)/(conj a + z)| as a complex norm
-- 3. We formalize the three cases described in the problem
-- 4. We'll assume a is fixed with positive real part and prove properties for all z
-- 5. We use the standard notation: Complex.re for real part, ‖x‖ for modulus
-- 6. Note: in Lean, Complex.conj is the complex conjugate

theorem problem_6 (a : ℂ) (ha : 0 < Complex.re a) :
    let denominator := Complex.conj a
    ∀ (z : ℂ),
      let expr := ‖(a - z) / (denominator + z)‖
      (expr < 1 ∧ Complex.re z > 0) ∨
      (expr = 1 ∧ Complex.re z = 0) ∨
      (expr > 1 ∧ Complex.re z < 0) := by
  sorry

-- Proof attempt:
theorem problem_6 (a : ℂ) (ha : 0 < Complex.re a) :
    let denominator := Complex.conj a
    ∀ (z : ℂ),
      let expr := ‖(a - z) / (denominator + z)‖
      (expr < 1 ∧ Complex.re z > 0) ∨
      (expr = 1 ∧ Complex.re z = 0) ∨
      (expr > 1 ∧ Complex.re z < 0) := by
  intro z
  let denom := Complex.conj a + z
  by_cases hdenom : denom = 0
  · -- Case when denominator is zero (z = -conj a)
    have hz : Complex.re z = -Complex.re a := by
      rw [← Complex.conj_re a, ← Complex.add_re, hdenom]
      simp only [Complex.zero_re]
    right; right
    simp [hz, expr, hdenom, div_zero, norm_zero, ha]
    linarith [hz]
  
  · -- Main case when denominator is non-zero
    let expr := ‖(a - z) / denom‖
    have : expr < 1 ↔ Complex.re z > 0 := by
      rw [← norm_div]
      simp only [norm_eq_abs]
      rw [← abs_div]
      have key : ‖a - z‖^2 - ‖Complex.conj a + z‖^2 = -2 * Complex.re a * Complex.re z := by
        simp only [norm_sq_sub, norm_sq_add, Complex.mul_conj, Complex.conj_conj]
        rw [← Complex.add_re, ← Complex.sub_re]
        simp only [Complex.conj_re, Complex.conj_im, neg_mul, sub_neg_eq_add]
        ring
      rw [← pow_lt_pow_iff (by norm_num), ← mul_lt_mul_left (by linarith [ha] : 0 < 2 * Complex.re a)]
      rw [div_pow, div_pow, ← norm_sq_eq_abs, ← norm_sq_eq_abs]
      simp only [key]
      rw [neg_mul, neg_lt_neg_iff, mul_lt_mul_left ha]
      exact Iff.refl _
    have : expr = 1 ↔ Complex.re z = 0 := by
      rw [← norm_div]
      simp only [norm_eq_abs]
      rw [← abs_div]
      rw [← pow_eq_pow_iff (by norm_num), ← mul_eq_mul_left (by linarith [ha] : 2 * Complex.re a ≠ 0)]
      rw [div_pow, div_pow, ← norm_sq_eq_abs, ← norm_sq_eq_abs]
      simp only [key]
      rw [neg_mul, neg_eq_neg_iff, mul_eq_mul_left_iff, ha.ne', or_false]
      exact Iff.refl _
    have : expr > 1 ↔ Complex.re z < 0 := by
      rw [← norm_div]
      simp only [norm_eq_abs]
      rw [← abs_div]
      rw [← pow_gt_pow_iff (by norm_num), ← mul_gt_mul_left (by linarith [ha] : 0 < 2 * Complex.re a)]
      rw [div_pow, div_pow, ← norm_sq_eq_abs, ← norm_sq_eq_abs]
      simp only [key]
      rw [neg_mul, neg_gt_neg_iff, mul_gt_mul_left ha]
      exact Iff.refl _
    by_cases hz : Complex.re z > 0
    · left; exact ⟨this.1.mpr hz, hz⟩
    · by_cases hz' : Complex.re z = 0
      · right; left; exact ⟨this.2.1.mpr hz', hz'⟩
      · right; right
        have : Complex.re z < 0 := by linarith
        exact ⟨this.3.1.mpr this, this⟩