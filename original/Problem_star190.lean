/-
Polya-Szego Problem *190
Part One, Chapter 4

Original problem:
Show that

$$
\sum_{n=k}^{\infty} \frac{S_{k}^{n} z^{n}}{n!}=\frac{\left(e^{z}-1\right)^{k}}{k!} .
$$

Formalization notes: -- 1. S_k^n represents Stirling numbers of the second kind, written as Nat.stirlingSnd n k in Mathlib4
-- 2. The sum is from n = k to ∞, but Stirling numbers S_k^n = 0 when n < k
-- 3. We use Complex for generality, but could also use Real if z is real
-- 4. The equality holds for all z in ℂ (or ℝ)
-- 5. We use the power series expansion of exp and the known identity for (exp z - 1)^k
-/

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.Calculus.Series
import Mathlib.Data.Nat.Choose.Sum

-- Formalization notes:
-- 1. S_k^n represents Stirling numbers of the second kind, written as Nat.stirlingSnd n k in Mathlib4
-- 2. The sum is from n = k to ∞, but Stirling numbers S_k^n = 0 when n < k
-- 3. We use Complex for generality, but could also use Real if z is real
-- 4. The equality holds for all z in ℂ (or ℝ)
-- 5. We use the power series expansion of exp and the known identity for (exp z - 1)^k

theorem problem_190 (k : ℕ) (z : ℂ) :
    ∑' (n : ℕ), (Nat.stirlingSnd n k : ℂ) * z ^ n / (Nat.factorial n : ℂ) = 
    ((Complex.exp z - 1) ^ k) / (Nat.factorial k : ℂ) := by
  sorry

-- Proof attempt:
theorem problem_190 (k : ℕ) (z : ℂ) :
    ∑' (n : ℕ), (Nat.stirlingSnd n k : ℂ) * z ^ n / (Nat.factorial n : ℂ) = 
    ((Complex.exp z - 1) ^ k) / (Nat.factorial k : ℂ) := by
  -- First express (exp z - 1)^k using the binomial expansion
  have h_exp : (Complex.exp z - 1) ^ k = 
      ∑ i in Finset.range (k + 1), (-1 : ℂ) ^ i * (Nat.choose k i) * Complex.exp ((k - i) * z) := by
    simp_rw [← Complex.exp_nat_mul, sub_mul]
    exact Complex.add_pow (k) (Complex.exp z) (-1)
  
  -- Expand each exponential term into its power series
  rw [h_exp]
  simp_rw [Complex.exp_eq_exp_series]
  
  -- Swap sums and combine coefficients
  rw [tsum_finset_sum']
  swap; exact summable_exp_series z
  simp_rw [tsum_mul_left, tsum_mul_right, ← tsum_pow_series_div_factorial z]
  
  -- Recognize the Stirling number formula in the coefficients
  have h_stirling : ∀ n, ∑ i in Finset.range (k + 1), (-1 : ℂ) ^ i * (Nat.choose k i) * (k - i : ℂ) ^ n = 
      (Nat.factorial k : ℂ) * (Nat.stirlingSnd n k : ℂ) := by
    intro n
    simp_rw [← Nat.cast_pow, ← Nat.cast_mul, ← Nat.cast_comm, ← Nat.cast_sum]
    norm_cast
    exact Nat.sum_choose_mul_stirlingSnd_eq n k
  
  -- Rewrite the inner sum using the Stirling number identity
  simp_rw [h_stirling, mul_assoc]
  conv => enter [2, n]; rw [mul_comm _ (Nat.factorial k : ℂ), ← mul_assoc, inv_mul_cancel_left₀]
  try simp [Nat.factorial_ne_zero]
  
  -- Simplify the resulting expression
  simp_rw [← mul_div_assoc, tsum_mul_left]
  congr
  norm_cast
  simp [Nat.factorial]