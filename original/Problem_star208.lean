/-
Polya-Szego Problem *208
Part One, Chapter 4

Original problem:
$\tilde{T}_{n}=\binom{n}{0} T_{n}-\binom{n}{1} T_{n-1}+\binom{n}{2} T_{n-2}-\cdots+(-1)^{n}\binom{n}{n} T_{0}$.\\
( $\tilde{T}_{n}=\Delta^{n} T_{0}$, if we use the notation of the calculus of finite differences, see introduction to III 220.)\\

Formalization notes: -- We formalize the combinatorial identity for finite differences.
-- T : ℕ → ℝ is an arbitrary sequence (could be generalized to any commutative ring)
-- The tilde_T n is defined as the alternating sum of binomial coefficients times T_k
-- This represents the n-th finite difference Δ^n T_0
-- We also formalize the generating function relation from the book's solution
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

-- Formalization notes:
-- We formalize the combinatorial identity for finite differences.
-- T : ℕ → ℝ is an arbitrary sequence (could be generalized to any commutative ring)
-- The tilde_T n is defined as the alternating sum of binomial coefficients times T_k
-- This represents the n-th finite difference Δ^n T_0
-- We also formalize the generating function relation from the book's solution

open Finset
open Complex
open Real

variable (T : ℕ → ℝ)

-- Definition of the finite difference operator
def tilde_T (n : ℕ) : ℝ :=
  ∑ k in range (n + 1), (-1 : ℝ) ^ k * (Nat.choose n k : ℝ) * T (n - k)

-- Formalization of the combinatorial identity
theorem problem_208_combinatorial (n : ℕ) :
    tilde_T T n = ∑ k in range (n + 1), (-1 : ℝ) ^ k * (Nat.choose n k : ℝ) * T (n - k) :=
  rfl

-- Formalization of the generating function relation (equation 34 in the book)
-- We use formal power series via the exponential generating functions
theorem problem_208_generating_function :
    (Complex.exp (-1 : ℂ)) * (∑' n : ℕ, (T n : ℂ) * (Complex.exp 1) ^ n / (Nat.factorial n : ℂ)) =
      ∑' n : ℕ, (tilde_T T n : ℂ) * (Complex.exp 1) ^ n / (Nat.factorial n : ℂ) := by
  sorry

-- Alternative: Formalizing the relation using sums up to N (for computational purposes)
theorem problem_208_generating_function_partial (N : ℕ) :
    (Complex.exp (-1 : ℂ)) * (∑ n in range N, (T n : ℂ) * (Complex.exp 1) ^ n / (Nat.factorial n : ℂ)) =
      ∑ n in range N, (tilde_T T n : ℂ) * (Complex.exp 1) ^ n / (Nat.factorial n : ℂ) +
        (Complex.exp (-1 : ℂ)) * (∑ n in range N, (T n : ℂ) * (Complex.exp 1) ^ n / (Nat.factorial n : ℂ)) -
        ∑ n in range N, (tilde_T T n : ℂ) * (Complex.exp 1) ^ n / (Nat.factorial n : ℂ) := by
  sorry

-- Proof attempt:
theorem problem_208_generating_function :
    (Complex.exp (-1 : ℂ)) * (∑' n : ℕ, (T n : ℂ) * (Complex.exp 1) ^ n / (Nat.factorial n : ℂ)) =
      ∑' n : ℕ, (tilde_T T n : ℂ) * (Complex.exp 1) ^ n / (Nat.factorial n : ℂ) := by
  simp_rw [tilde_T, ← mul_assoc, ← mul_div_assoc, ← sum_div, ← Complex.exp_nat_mul, ← neg_one_mul]
  rw [tsum_mul_tsum_of_summable_norm]
  · simp_rw [← tsum_mul_right]
    congr
    ext n
    rw [← tsum_mul_left]
    congr
    ext k
    rw [mul_assoc, mul_assoc, mul_comm _ (T (n - k) : ℂ), ← mul_assoc, ← mul_assoc]
    norm_cast
    rw [← Nat.choose_symm (Nat.le_of_lt (Nat.lt_succ_iff.mpr (mem_range.mp (by simp)).2))]
    ring
  · simp [summable_norm_iff]
    exact summable_of_summable_norm (summable_exp_mul (1 : ℂ))
  · simp [summable_norm_iff]
    exact summable_of_summable_norm (summable_exp_mul (1 : ℂ))