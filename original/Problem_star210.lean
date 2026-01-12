/-
Polya-Szego Problem *210
Part One, Chapter 4

Original problem:
Derive the identities in the variables $z$ and $w$ :


\begin{align*}
& \sum_{n=0}^{\infty} \sum_{k \leqq n}\binom{n}{k} \frac{w^{k} z^{n}}{n!}=e^{z(w+1)}  \tag{1}\\
& \sum_{n=0}^{\infty} \sum_{k \leqq n} S_{k}^{n} \frac{w^{k} z^{n}}{n!}=e^{\left(e^{z}-1\right) w}  \tag{2}\\
& \sum_{n=0}^{\infty} \sum_{k \leqq n} S_{k}^{n} \frac{w^{k} z^{n}}{n!}=(1-z)^{-w} \tag{3}
\end{align*}


either on the basis of the foregoing $[\mathbf{1 0}, \mathbf{1 9 0 , 2 0 0}]$ or independently of the\\
(On the other 

Formalization notes: -- We formalize the three identities from Problem 210 as separate theorems.
-- (1) involves binomial coefficients, (2) involves Stirling numbers of the second kind,
-- (3) involves Stirling numbers of the first kind.
-- We use Finset.sum for finite sums and tsum for infinite sums.
-- The identities hold for complex z and w within appropriate convergence radii.
-/

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Pi
import Mathlib.Data.Complex.Exponential
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.Data.Finset.Sum

-- Formalization notes:
-- We formalize the three identities from Problem 210 as separate theorems.
-- (1) involves binomial coefficients, (2) involves Stirling numbers of the second kind,
-- (3) involves Stirling numbers of the first kind.
-- We use Finset.sum for finite sums and tsum for infinite sums.
-- The identities hold for complex z and w within appropriate convergence radii.

open Complex
open Real
open Finset
open Nat
open scoped BigOperators

-- Theorem (1): ∑_{n=0}^∞ ∑_{k≤n} C(n,k) w^k z^n / n! = exp(z(w+1))
theorem problem_210_part1 (z w : ℂ) : 
    ∑' (n : ℕ), ∑ k in range (n+1), ((Nat.choose n k : ℂ) * w ^ k * z ^ n) / (n ! : ℂ) = 
    exp (z * (w + 1)) := by
  sorry

-- Theorem (2): ∑_{n=0}^∞ ∑_{k≤n} S(n,k) w^k z^n / n! = exp((exp z - 1) w)
-- where S(n,k) are Stirling numbers of the second kind
theorem problem_210_part2 (z w : ℂ) : 
    ∑' (n : ℕ), ∑ k in range (n+1), ((stirling2 n k : ℂ) * w ^ k * z ^ n) / (n ! : ℂ) = 
    exp ((exp z - 1) * w) := by
  sorry

-- Theorem (3): ∑_{n=0}^∞ ∑_{k≤n} s(n,k) w^k z^n / n! = (1 - z)^{-w}
-- where s(n,k) are Stirling numbers of the first kind
-- Note: For |z| < 1 to ensure convergence
theorem problem_210_part3 (z w : ℂ) (hz : ‖z‖ < 1) : 
    ∑' (n : ℕ), ∑ k in range (n+1), ((stirling1 n k : ℂ) * w ^ k * z ^ n) / (n ! : ℂ) = 
    (1 - z) ^ (-w) := by
  sorry

-- Proof attempt:
theorem problem_210_part1 (z w : ℂ) : 
    ∑' (n : ℕ), ∑ k in range (n+1), ((Nat.choose n k : ℂ) * w ^ k * z ^ n) / (n ! : ℂ) = 
    exp (z * (w + 1)) := by
  simp_rw [← mul_assoc, ← div_mul_eq_mul_div, mul_comm _ (z^n), ← mul_assoc (w^k)]
  rw [tsum_eq_tsum_of_ne_zero (fun n => by simp [Nat.cast_ne_zero, factorial_ne_zero])]
  simp_rw [← sum_mul, mul_comm _ (z^n / n.factorial), ← mul_assoc, ← mul_sum]
  simp_rw [← Complex.exp_add]
  have : ∑' n, (z * (w + 1)) ^ n / n.factorial = exp (z * (w + 1)) := by
    rw [Complex.exp_eq_tsum]
  rw [← this]
  apply tsum_congr
  intro n
  rw [← mul_pow, add_pow]
  simp [mul_comm, mul_assoc, mul_left_comm, Nat.cast_comm]