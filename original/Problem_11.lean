/-
Polya-Szego Problem 11
Part Three, Chapter 1

Original problem:
For what values of $z$ is the absolute value of the $n$-th term $\frac{z^{n}}{n!}$ of

$$
1+\frac{z}{1!}+\frac{z^{2}}{2!}+\cdots+\frac{z^{n}}{n!}+\cdots
$$

(exponential series in the complex plane) larger than the absolute value of any other term? $n=0,1,2, \ldots$\\

Formalization notes: -- We formalize the condition for when the n-th term of the exponential series
-- has strictly larger absolute value than all other terms.
-- The theorem states: For complex z and natural n, the n-th term |z^n/n!| is 
-- strictly greater than all other terms |z^k/k!| (k ≠ n) if and only if
-- n < |z| < n+1.
-- We exclude the boundary cases where |z| = n or |z| = n+1 since there
-- the n-th term equals either the (n-1)-th or (n+1)-th term in absolute value.
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Data.Complex.Exponential

-- Formalization notes:
-- We formalize the condition for when the n-th term of the exponential series
-- has strictly larger absolute value than all other terms.
-- The theorem states: For complex z and natural n, the n-th term |z^n/n!| is 
-- strictly greater than all other terms |z^k/k!| (k ≠ n) if and only if
-- n < |z| < n+1.
-- We exclude the boundary cases where |z| = n or |z| = n+1 since there
-- the n-th term equals either the (n-1)-th or (n+1)-th term in absolute value.

theorem problem_11 (z : ℂ) (n : ℕ) :
    (∀ k : ℕ, k ≠ n → Complex.abs (z ^ n / (Nat.factorial n : ℂ)) > 
                    Complex.abs (z ^ k / (Nat.factorial k : ℂ))) ↔
    (n : ℝ) < Complex.abs z ∧ Complex.abs z < (n + 1 : ℝ) := by
  sorry

-- Proof attempt:
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Data.Complex.Exponential

theorem problem_11 (z : ℂ) (n : ℕ) :
    (∀ k : ℕ, k ≠ n → Complex.abs (z ^ n / (Nat.factorial n : ℂ)) > 
                    Complex.abs (z ^ k / (Nat.factorial k : ℂ))) ↔
    (n : ℝ) < Complex.abs z ∧ Complex.abs z < (n + 1 : ℝ) := by
  let r := Complex.abs z
  have r_nonneg : 0 ≤ r := Complex.abs.nonneg z
  simp only [Complex.abs.map_div, Complex.abs.map_pow, Complex.abs_natCast]
  simp only [div_eq_mul_inv, ← mul_inv]
  have h : ∀ k : ℕ, Complex.abs (z ^ k / (Nat.factorial k : ℂ)) = r ^ k / (Nat.factorial k : ℝ) := by
    intro k
    simp [Complex.abs.map_div, Complex.abs.map_pow, Complex.abs_natCast]
  simp_rw [h]
  constructor
  · intro h
    have hn : r ^ n / n.factorial > r ^ (n + 1) / (n + 1).factorial := by
      apply h (n + 1); simp
    have hn' : r ^ n / n.factorial > r ^ (n - 1) / (n - 1).factorial := by
      cases n
      · simp at hn
      · apply h (n - 1); simp
    simp [Nat.factorial_succ, mul_comm (n + 1 : ℝ), ← div_div] at hn
    simp [Nat.factorial_succ, mul_comm (n : ℝ), ← div_div] at hn'
    rw [div_lt_iff] at hn hn'
    · rw [lt_div_iff] at hn'
      · exact ⟨hn', hn⟩
      · exact Nat.cast_pos.2 (Nat.factorial_pos _)
    · exact Nat.cast_pos.2 (Nat.factorial_pos _)
  · intro h k hk
    cases' lt_or_gt_of_ne hk with hk' hk'
    · have hk'' : k ≤ n := Nat.lt_succ.1 (hk'.trans_le (Nat.lt_succ.1 h.2).le)
      clear hk'
      induction' n - k with m hm generalizing k
      · simp at hm
      · have : k < n := by
          apply lt_of_le_of_ne hk'' hk.symm
        have := hm (k + 1) (by omega) (Nat.sub_eq_of_eq_add (by omega))
        rw [Nat.factorial_succ, Nat.cast_mul, ← div_div, mul_comm (k + 1 : ℝ), div_mul_eq_div_div]
        rw [div_lt_iff (Nat.cast_pos.2 (Nat.factorial_pos _))] at this
        rw [pow_succ, div_mul_eq_div_div, ← div_lt_div_iff (pow_pos r_nonneg _) (Nat.cast_pos.2 (Nat.factorial_pos _))]
        exact this
    · have hk'' : n + 1 ≤ k := hk'
      clear hk'
      induction' k - (n + 1) with m hm generalizing k
      · simp at hk''
        have := h.2
        simp [Nat.factorial_succ, mul_comm (n + 1 : ℝ), ← div_div] at this ⊢
        rw [div_lt_iff (Nat.cast_pos.2 (Nat.factorial_pos _))] at this
        rw [pow_succ, div_mul_eq_div_div, ← lt_div_iff (pow_pos r_nonneg _)]
        exact this
      · have := hm (k - 1) (by omega) (Nat.sub_eq_of_eq_add (by omega))
        rw [Nat.factorial_succ, Nat.cast_mul, ← div_div, mul_comm (k : ℝ), div_mul_eq_div_div]
        rw [lt_div_iff (Nat.cast_pos.2 (Nat.factorial_pos _))] at this
        rw [pow_succ, div_mul_eq_div_div, ← lt_div_iff (pow_pos r_nonneg _)]
        exact this