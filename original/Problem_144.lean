/-
Polya-Szego Problem 144
Part One, Chapter 3

Original problem:
Work out the polynomials $K_{n}(x), n=0,1,2, \ldots$ for

$$
f(x)=1, \quad f(x)=x, \quad f(x)=x^{2}, \quad f(x)=e^{x} .
$$

\begin{enumerate}
  \setcounter{enumi}{144}
  \item Let $x$ be any point on $[0,1]$ and
\end{enumerate}

$$
1=\sum_{v=0}^{n}\binom{n}{v} x^{v}(1-x)^{n-v}=\Sigma^{\mathrm{I}}+\Sigma^{\mathrm{II}},
$$

where $\Sigma^{1}$ refers to the subscripts for which $|v-n x| \leqq n^{3 / 4}$ and $\Sigma^{11}$ to those for which $|v-n x|>n^{3 / 4}, n \geqq 1$. Then

$$
\Sigma^{\mathrm{II

Formalization notes: -- 1. We formalize Bernstein polynomials: K_n(f)(x) = ∑_{v=0}^n f(v/n) * (n choose v) * x^v * (1-x)^{n-v}
-- 2. Part 1: Compute K_n for f(x) = 1, f(x) = x, f(x) = x^2, f(x) = e^x
-- 3. Part 2: Prove the bound on the tail sum where |v - n*x| > n^{3/4}
-- Note: The problem statement has some OCR/text recognition issues in the latter part
-/

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Calculus.ContDiff
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Interval
import Mathlib.Analysis.NormedSpace.Basic

-- Formalization notes:
-- 1. We formalize Bernstein polynomials: K_n(f)(x) = ∑_{v=0}^n f(v/n) * (n choose v) * x^v * (1-x)^{n-v}
-- 2. Part 1: Compute K_n for f(x) = 1, f(x) = x, f(x) = x^2, f(x) = e^x
-- 3. Part 2: Prove the bound on the tail sum where |v - n*x| > n^{3/4}
-- Note: The problem statement has some OCR/text recognition issues in the latter part

open Real
open Complex
open Finset
open BigOperators

/-- Bernstein polynomial operator -/
noncomputable def bernstein_poly (f : ℝ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  ∑ v in range (n + 1), f (v / n) * (Nat.choose n v) * x ^ v * (1 - x) ^ (n - v)

/-- Part 1: Compute Bernstein polynomials for specific functions -/
theorem problem_144_part1 : 
  -- For f(x) = 1
  (∀ (n : ℕ) (x : ℝ), bernstein_poly (λ _ => (1 : ℝ)) n x = 1) ∧
  -- For f(x) = x
  (∀ (n : ℕ) (x : ℝ), bernstein_poly (λ t => t) n x = x) ∧
  -- For f(x) = x^2
  (∀ (n : ℕ) (x : ℝ), bernstein_poly (λ t => t^2) n x = x^2 + (x - x^2) / n) ∧
  -- For f(x) = e^x
  (∀ (n : ℕ) (x : ℝ), bernstein_poly Real.exp n x = ((Real.exp (1/n) - 1) * x + 1) ^ n) := by
  sorry

/-- Part 2: Bound on the tail sum of binomial probabilities -/
theorem problem_144_part2 (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) (n : ℕ) (hn : n ≥ 1) :
  let S_I : ℝ := ∑ v in (range (n + 1)).filter (λ v => |(v : ℝ) - n * x| ≤ (n : ℝ) ^ (3/4 : ℝ)),
      (Nat.choose n v : ℝ) * x ^ v * (1 - x) ^ (n - v);
      S_II : ℝ := ∑ v in (range (n + 1)).filter (λ v => |(v : ℝ) - n * x| > (n : ℝ) ^ (3/4 : ℝ)),
      (Nat.choose n v : ℝ) * x ^ v * (1 - x) ^ (n - v)
  in S_I + S_II = 1 ∧ S_II < (1/4 : ℝ) * (n : ℝ) ^ (-1/2 : ℝ) := by
  sorry

/-- Alternative formulation focusing on the key inequality -/
theorem problem_144_inequality (x : ℝ) (hx : 0 ≤ x ∧ x ≤ 1) (n : ℕ) (hn : n ≥ 1) :
  let total_sum := ∑ v in range (n + 1), (Nat.choose n v : ℝ) * x ^ v * (1 - x) ^ (n - v);
      tail_sum := ∑ v in (range (n + 1)).filter (λ v => |(v : ℝ) - n * x| > (n : ℝ) ^ (3/4 : ℝ)),
        (Nat.choose n v : ℝ) * x ^ v * (1 - x) ^ (n - v)
  in total_sum = 1 ∧ tail_sum < (1/4 : ℝ) * (Real.sqrt n)⁻¹ := by
  sorry

/-- Convergence of Bernstein polynomials for continuous functions (Weierstrass approximation) -/
theorem problem_145 (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc (0 : ℝ) 1)) :
  ∀ (ε : ℝ) (hε : ε > 0), ∃ (N : ℕ), ∀ (n : ℕ) (hn : n ≥ N) (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1),
    |bernstein_poly f n x - f x| < ε := by
  sorry

-- Proof attempt:
theorem problem_144_part1 : 
  (∀ (n : ℕ) (x : ℝ), bernstein_poly (λ _ => (1 : ℝ)) n x = 1) ∧
  (∀ (n : ℕ) (x : ℝ), bernstein_poly (λ t => t) n x = x) ∧
  (∀ (n : ℕ) (x : ℝ), bernstein_poly (λ t => t^2) n x = x^2 + (x - x^2) / n) ∧
  (∀ (n : ℕ) (x : ℝ), bernstein_poly Real.exp n x = ((Real.exp (1/n) - 1) * x + 1) ^ n) := by
  constructor
  · -- Case f(x) = 1
    intro n x
    simp [bernstein_poly]
    rw [← mul_one (1 - x) ^ n]
    conv => 
      rhs
      rw [← Nat.sum_range_choose_mul_pow x (1 - x) n]
    simp
  constructor
  · -- Case f(x) = x
    intro n x
    simp [bernstein_poly]
    rw [Finset.sum_range_succ]
    simp [Nat.choose_zero_right, Nat.choose_self, Nat.sub_self, pow_zero]
    conv => 
      rhs
      rw [← Nat.sum_range_choose_mul_pow x (1 - x) n]
    simp
    have h : ∑ v in range n, (v : ℝ) / n * Nat.choose n (v + 1) * x ^ (v + 1) * (1 - x) ^ (n - (v + 1)) = 
             x * ∑ v in range n, Nat.choose (n - 1) v * x ^ v * (1 - x) ^ (n - 1 - v) := by
      rw [Finset.sum_congr rfl]
      intro k hk
      rw [mem_range] at hk
      have : Nat.choose n (k + 1) = n * Nat.choose (n - 1) k / (k + 1) := by
        rw [Nat.choose_succ_succ, Nat.mul_choose_div]
        omega
      rw [this, div_mul_eq_mul_div, ← mul_assoc, ← mul_assoc]
      congr 1
      rw [pow_succ, ← mul_assoc, mul_comm ((1 - x) ^ _), ← mul_assoc]
      field_simp
      ring
    rw [h]
    simp [Nat.sum_range_choose_mul_pow, ← add_zero x]
  constructor
  · -- Case f(x) = x^2
    intro n x
    simp [bernstein_poly]
    rw [Finset.sum_range_succ]
    simp [Nat.choose_zero_right, Nat.choose_self, Nat.sub_self, pow_zero]
    have h1 : ∑ v in range n, (v : ℝ)^2 / n^2 * Nat.choose n (v + 1) * x ^ (v + 1) * (1 - x) ^ (n - (v + 1)) = 
              x / n * ∑ v in range n, (v + 1) * Nat.choose (n - 1) v * x ^ v * (1 - x) ^ (n - 1 - v) := by
      rw [Finset.sum_congr rfl]
      intro k hk
      rw [mem_range] at hk
      have : Nat.choose n (k + 1) = n * Nat.choose (n - 1) k / (k + 1) := by
        rw [Nat.choose_succ_succ, Nat.mul_choose_div]
        omega
      rw [this, div_mul_eq_mul_div, ← mul_assoc, ← mul_assoc]
      congr 1
      rw [pow_succ, ← mul_assoc, mul_comm ((1 - x) ^ _), ← mul_assoc]
      field_simp
      ring
    rw [h1]
    have h2 : ∑ v in range n, (v + 1) * Nat.choose (n - 1) v * x ^ v * (1 - x) ^ (n - 1 - v) = 
              ∑ v in range n, Nat.choose (n - 1) v * x ^ v * (1 - x) ^ (n - 1 - v) + 
              ∑ v in range n, v * Nat.choose (n - 1) v * x ^ v * (1 - x) ^ (n - 1 - v) := by
      simp_rw [add_mul]
      rw [Finset.sum_add_distrib]
    rw [h2]
    simp [Nat.sum_range_choose_mul_pow, Nat.sum_range_choose_mul_pow_mul_v]
    ring
  · -- Case f(x) = e^x
    intro n x
    simp [bernstein_poly]
    rw [← Real.exp_mul, ← Finset.sum_mul]
    conv => 
      rhs
      rw [← Nat.sum_range_choose_mul_pow (x * Real.exp (1 / n)) (1 - x) n]
    simp
    congr
    ext v
    rw [← Real.exp_add, ← mul_div_right_comm, add_comm, ← add_div, mul_comm]