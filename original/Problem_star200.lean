/-
Polya-Szego Problem *200
Part One, Chapter 4

Original problem:
Show that

$$
\sum_{n=k}^{\infty} \frac{s_{k}^{n} z^{n}}{n!}=\frac{1}{k!}\left(\log \frac{1}{1-z}\right)^{k} .
$$

(Compare 200 with 190, 199 with 188, and again 199 with 191. See also VII 54.2 and VIII 247.1.)

Define $\tilde{S}_{k}^{n}$ as the number of partitions of a set of $n$ elements into $k$ classes each of which contains more than one element.

\footnotetext{${ }^{1}$ See, e.g., Garrett Birkhoff and Saunders MacLane: A Survey of Modern Algebra, 3rd Ed. New York: Macmillan 1965, p. 137.


Formalization notes: -- 1. We formalize the identity for complex z with |z| < 1
-- 2. sₖⁿ represents Stirling numbers of the first kind (unsigned)
-- 3. The sum is from n = k to ∞, with k ≥ 0
-- 4. We use Complex.log for the principal branch of the logarithm
-- 5. The equality holds for |z| < 1 where the series converges absolutely
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Real.Pow
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.Calculus.Deriv.Pow

-- Formalization notes:
-- 1. We formalize the identity for complex z with |z| < 1
-- 2. sₖⁿ represents Stirling numbers of the first kind (unsigned)
-- 3. The sum is from n = k to ∞, with k ≥ 0
-- 4. We use Complex.log for the principal branch of the logarithm
-- 5. The equality holds for |z| < 1 where the series converges absolutely

theorem problem_200 (k : ℕ) (z : ℂ) (hz : ‖z‖ < 1) :
    ∑' (n : ℕ), (if k ≤ n then (Nat.stirling1 n k).toComplex * z ^ n / (Nat.factorial n : ℂ) else 0) =
    (1 / (Nat.factorial k : ℂ)) * (Complex.log (1 / (1 - z))) ^ k := by
  sorry

-- Proof attempt:
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Real.Pow
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Factorial.Cast

open Complex
open Nat

theorem problem_200 (k : ℕ) (z : ℂ) (hz : ‖z‖ < 1) :
    ∑' (n : ℕ), (if k ≤ n then (stirling1 n k).toComplex * z ^ n / (n.factorial : ℂ) else 0) =
    (1 / (k.factorial : ℂ)) * (log (1 / (1 - z))) ^ k := by
  -- The key is the generating function for Stirling numbers of the first kind
  -- (1 - t)^(-x) = ∑' n, (x)_n / n! * t^n where (x)_n is the rising factorial
  -- And also equals exp(-x * log(1 - t))
  -- The Stirling numbers appear when expanding (x)_n = ∑ k, s(n,k) x^k
  -- We'll use these facts to derive our identity
  
  -- First, recall the generating function for rising factorials
  have h_gen : ∀ (x : ℂ) (t : ℂ), ‖t‖ < 1 → 
      (1 - t)⁻¹ ^ x = exp (-x * log (1 - t)) := by
    intro x t ht
    rw [← exp_log (by rw [norm_one]; exact one_ne_zero), ← Real.exp_eq_exp, ← rpow_def_of_pos]
    · simp only [one_div, Real.rpow_neg, Real.rpow_one, ← exp_log]
      rw [exp_eq_exp]
      field_simp
      rw [← mul_assoc, mul_comm (-x), mul_assoc]
      congr 1
      rw [log_inv]
      simp [log_one_sub]
    · rw [sub_pos, norm_lt_one_iff]
      exact ht

  -- The rising factorial generating function can also be expanded as:
  have h_rising : ∀ (x : ℂ) (t : ℂ), ‖t‖ < 1 → 
      (1 - t)⁻¹ ^ x = ∑' (n : ℕ), (ascFactorial x n) * t ^ n / n.factorial := by
    intro x t ht
    rw [ascFactorial_eq_pochhammer]
    exact Complex.hasSum_pochhammer' x ht

  -- Now specialize to x = k and extract coefficients
  let x := k
  let t := z
  have h_sum_eq : 
      ∑' (n : ℕ), (ascFactorial x n) * t ^ n / n.factorial = 
      ∑' (k' : ℕ), x ^ k' / k'.factorial * (log (1 / (1 - t))) ^ k' := by
    rw [h_gen x t hz, h_rising x t hz, Complex.exp_eq_exp_series]
    simp only [pow_mul, ← mul_pow, ← mul_assoc, neg_mul]
    congr
    ext k'
    rw [mul_comm (x ^ k' / k'.factorial), ← mul_assoc]

  -- The key step: match coefficients of x^k on both sides
  -- The left side expands the rising factorial using Stirling numbers
  have h_stirling_expansion : 
      ∀ n, (ascFactorial x n) = ∑ k in Finset.range (n + 1), (stirling1 n k) * x ^ k := by
    intro n
    simp [ascFactorial_eq_pochhammer, pochhammer_eq_stirling1_sum]

  -- Rewrite the left side using the Stirling expansion
  have h_left_expanded : 
      ∑' (n : ℕ), (ascFactorial x n) * t ^ n / n.factorial = 
      ∑' (n : ℕ), (∑ k in Finset.range (n + 1), (stirling1 n k) * x ^ k) * t ^ n / n.factorial := by
    congr with n
    rw [h_stirling_expansion n]

  -- Rearrange the sums
  have h_rearranged : 
      ∑' (n : ℕ), (∑ k in Finset.range (n + 1), (stirling1 n k) * x ^ k) * t ^ n / n.factorial =
      ∑' (k : ℕ), x ^ k * (∑' (n : ℕ), if k ≤ n then (stirling1 n k) * t ^ n / n.factorial else 0) := by
    simp_rw [mul_sum, sum_mul, mul_assoc]
    exact tsum_comm_tsum_of_summable_norm
      (by simp [norm_smul, norm_div, norm_pow, norm_eq_abs, abs_cast_nat, abs_factorial,
                summable_geometric_of_lt_1 (norm_lt_one_iff.1 hz)])

  -- Now specialize to our particular case where x = k
  -- We need to extract the coefficient of x^k from both sides
  -- The right side is easy: it's exactly the term when k' = k
  have h_right_coeff : 
      (∑' (k' : ℕ), x ^ k' / k'.factorial * (log (1 / (1 - t))) ^ k') = 
      x ^ k / k.factorial * (log (1 / (1 - t))) ^ k + 
      (∑' (k' in {k}ᶜ), x ^ k' / k'.factorial * (log (1 / (1 - t))) ^ k') := by
    rw [tsum_eq_add_tsum_ite k]

  -- The coefficient of x^k on the right side is exactly our goal
  -- On the left side, it's the sum over n ≥ k of (stirling1 n k) * t^n / n!
  have h_left_coeff :
      (∑' (k' : ℕ), x ^ k' * (∑' (n : ℕ), if k' ≤ n then (stirling1 n k') * t ^ n / n.factorial else 0)) =
      x ^ k * (∑' (n : ℕ), if k ≤ n then (stirling1 n k) * t ^ n / n.factorial else 0) +
      (∑' (k' in {k}ᶜ), x ^ k' * (∑' (n : ℕ), if k' ≤ n then (stirling1 n k') * t ^ n / n.factorial else 0)) := by
    rw [tsum_eq_add_tsum_ite k]

  -- Now equate coefficients of x^k
  have h_eq_coeff : 
      x ^ k * (∑' (n : ℕ), if k ≤ n then (stirling1 n k) * t ^ n / n.factorial else 0) = 
      x ^ k / k.factorial * (log (1 / (1 - t))) ^ k := by
    rw [← h_sum_eq, h_left_expanded, h_rearranged, h_right_coeff, h_left_coeff]
    simp only [add_right_inj]
    apply congr_arg
    ext k'
    split
    · simp
    · simp

  -- Cancel x^k from both sides (x = k ≠ 0 if k > 0, but holds when k = 0 too)
  simp only [← mul_assoc, one_div, inv_mul_cancel_right₀] at h_eq_coeff
  rotate_left
  · exact Nat.cast_ne_zero.2 (factorial_ne_zero k)
  · exact pow_ne_zero _ (Nat.cast_ne_zero.2 (factorial_ne_zero k))
  
  -- Final result
  rw [← h_eq_coeff]
  congr
  ext n
  split_ifs with h
  · simp [div_eq_mul_inv, mul_assoc]
  · simp