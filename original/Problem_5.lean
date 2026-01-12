/-
Polya-Szego Problem 5
Part Three, Chapter 1

Original problem:
Assume $|a|<1$. For any point of the complex $z$-plane

$$
\left|\frac{z-a}{1-\bar{a} z}\right|
$$

is either $<1$, or $=1$, or $>1$, and so the whole plane is divided into three subsets. Describe them.\\

Formalization notes: -- We formalize the statement about the modulus of the Möbius transformation (z - a)/(1 - a̅z)
-- The theorem states that for |a| < 1, the complex plane is partitioned into three regions:
-- 1. Points where |(z - a)/(1 - a̅z)| < 1 (the open unit disk)
-- 2. Points where |(z - a)/(1 - a̅z)| = 1 (the unit circle)
-- 3. Points where |(z - a)/(1 - a̅z)| > 1 (the exterior of the unit disk)
-- We formalize this as a trichotomy theorem with explicit descriptions of each region.
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

-- Formalization notes:
-- We formalize the statement about the modulus of the Möbius transformation (z - a)/(1 - a̅z)
-- The theorem states that for |a| < 1, the complex plane is partitioned into three regions:
-- 1. Points where |(z - a)/(1 - a̅z)| < 1 (the open unit disk)
-- 2. Points where |(z - a)/(1 - a̅z)| = 1 (the unit circle)
-- 3. Points where |(z - a)/(1 - a̅z)| > 1 (the exterior of the unit disk)
-- We formalize this as a trichotomy theorem with explicit descriptions of each region.

theorem problem_5 (a : ℂ) (ha : Complex.abs a < 1) (z : ℂ) :
    (Complex.abs ((z - a) / (1 - conj a * z)) < 1 ∧ Complex.abs z < 1) ∨
    (Complex.abs ((z - a) / (1 - conj a * z)) = 1 ∧ Complex.abs z = 1) ∨
    (Complex.abs ((z - a) / (1 - conj a * z)) > 1 ∧ Complex.abs z > 1) := by
  sorry

-- Proof attempt:
theorem problem_5 (a : ℂ) (ha : Complex.abs a < 1) (z : ℂ) :
    (Complex.abs ((z - a) / (1 - conj a * z)) < 1 ∧ Complex.abs z < 1) ∨
    (Complex.abs ((z - a) / (1 - conj a * z)) = 1 ∧ Complex.abs z = 1) ∨
    (Complex.abs ((z - a) / (1 - conj a * z)) > 1 ∧ Complex.abs z > 1) := by
  -- Key idea: Compute |(z - a)/(1 - a̅z)|² and compare it to 1
  let w := (z - a) / (1 - conj a * z)
  have hdenom : 1 - conj a * z ≠ 0 := by
    contrapose! ha
    rw [← Complex.abs.map_mul, ← Complex.abs.conj a] at ha
    simp only [map_one, one_mul] at ha
    exact ha
  have hw : Complex.abs w ^ 2 = (Complex.abs z ^ 2 + Complex.abs a ^ 2 - 2 * (a.re * z.re + a.im * z.im)) /
    (1 + Complex.abs a ^ 2 * Complex.abs z ^ 2 - 2 * (a.re * z.re + a.im * z.im)) := by
    rw [← Complex.abs.map_mul, ← Complex.abs.map_div, div_mul_div, Complex.abs.map_sub, Complex.abs.map_sub,
        Complex.abs.map_one, Complex.abs.map_mul, Complex.abs.conj a]
    ring
  -- Compare numerator and denominator
  have key : Complex.abs w ^ 2 - 1 = (Complex.abs z ^ 2 - 1) * (1 - Complex.abs a ^ 2) /
    (1 + Complex.abs a ^ 2 * Complex.abs z ^ 2 - 2 * (a.re * z.re + a.im * z.im)) := by
    rw [hw]
    field_simp
    ring
  -- The denominator is always positive
  have denom_pos : 0 < 1 + Complex.abs a ^ 2 * Complex.abs z ^ 2 - 2 * (a.re * z.re + a.im * z.im) := by
    have := Complex.abs_mul_le (conj a) z
    simp only [Complex.abs.conj] at this
    linarith [ha, Complex.abs.nonneg z]
  -- Analyze the sign of |w|² - 1 based on |z|² - 1
  rcases lt_trichotomy (Complex.abs z ^ 2) 1 with (hz | hz | hz)
  · left
    constructor
    · rw [← sq_lt_one_iff (Complex.abs.nonneg w), key]
      have h1 : Complex.abs z ^ 2 - 1 < 0 := by linarith
      have h2 : 1 - Complex.abs a ^ 2 > 0 := by linarith [ha]
      have := mul_neg_of_neg_of_pos h1 h2
      rw [div_neg_of_neg_of_pos this denom_pos]
      norm_num
    · rwa [← sq_lt_one_iff (Complex.abs.nonneg z)]
  · rcases eq_or_ne (Complex.abs z) 0 with (hz0 | hz0)
    · right; right
      have : Complex.abs w = Complex.abs a := by simp [w, hz0]
      constructor
      · rw [this]; exact ha
      · simp [hz0]
    · right; left
      constructor
      · rw [← sq_eq_one_iff (Complex.abs.nonneg w), key, hz]
        simp
      · rwa [← sq_eq_one_iff (Complex.abs.nonneg z)]
  · right; right
    constructor
    · rw [← one_lt_sq_iff (Complex.abs.nonneg w), key]
      have h1 : Complex.abs z ^ 2 - 1 > 0 := by linarith
      have h2 : 1 - Complex.abs a ^ 2 > 0 := by linarith [ha]
      exact div_pos (mul_pos h1 h2) denom_pos
    · rwa [← one_lt_sq_iff (Complex.abs.nonneg z)]