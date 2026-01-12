/-
Polya-Szego Problem 19.2
Part One, Chapter 4

Original problem:
The definition of $C$ given in 19.1 is convenient. Yet it would be desirable to approximate $C$ by rational numbers, to represent $C$ as the sum of a series whose terms are rational. Prove that the following series fulfills this desideratum:

$$
\frac{1}{1}-
$$

[12.] only) root in the

$$
=\lambda
$$

I thear $f^{\prime}(x)$ is monotone File- the following limit

I $\left.x-\int_{i}^{n} f(x) d x\right)=s$.\\
$-\int_{i}^{n} f(x) d y-s<0$

$$
\begin{aligned}
& -\frac{1}{2}-\frac{1}{3}+ \\
& +\fra

Formalization notes: -- 1. We formalize Euler's constant γ (called C in the problem) as Real.eulerMascheroni
-- 2. The series is defined by grouping terms: for each k, we have k terms of sign (-1)^{k+1} and value 1/(n_k) 
--    where n_k = k(k+1)/2 + 1, ..., k(k+1)/2 + k
-- 3. The theorem states this series converges to γ
-- 4. We use the known limit: lim_{n→∞} (∑_{k=1}^n 1/k - log n) = γ
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Series.Summable_Comparison

-- Formalization notes: 
-- 1. We formalize Euler's constant γ (called C in the problem) as Real.eulerMascheroni
-- 2. The series is defined by grouping terms: for each k, we have k terms of sign (-1)^{k+1} and value 1/(n_k) 
--    where n_k = k(k+1)/2 + 1, ..., k(k+1)/2 + k
-- 3. The theorem states this series converges to γ
-- 4. We use the known limit: lim_{n→∞} (∑_{k=1}^n 1/k - log n) = γ

open Real
open Finset
open BigOperators

/-- The partial sum of the rearranged harmonic series up to the m-th group -/
def partial_sum_series (m : ℕ) : ℝ :=
  ∑ k in range m, (-1 : ℝ)^(k + 1) * ∑ j in range (k + 1), 1 / ((k * (k + 1)) / 2 + j + 1 : ℝ)

/-- Alternative expression for the partial sum: 2H_n - H_{n²} where n = m -/
theorem partial_sum_eq (m : ℕ) : 
    partial_sum_series m = 2 * (∑ k in range (m + 1), 1 / (k + 1 : ℝ)) - 
                          (∑ k in range ((m + 1)^2), 1 / (k + 1 : ℝ)) := by
  sorry

/-- The rearranged harmonic series converges to Euler's constant γ -/
theorem problem_19_2 : 
    Tendsto (λ n => partial_sum_series n) atTop (𝓝 Real.eulerMascheroni) := by
  sorry

-- Proof attempt:
theorem partial_sum_eq (m : ℕ) : 
    partial_sum_series m = 2 * (∑ k in range (m + 1), 1 / (k + 1 : ℝ)) - 
                          (∑ k in range ((m + 1)^2), 1 / (k + 1 : ℝ)) := by
  simp [partial_sum_series]
  induction m with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, sum_range_succ, ih]
    simp [sum_range_succ]
    have : (n + 1) * (n + 2) / 2 = (n + 1) * (n + 2) / 2 := by rfl
    rw [this]
    have h₁ : ∑ j in range (n + 2), 1 / ((n + 1) * (n + 2) / 2 + j + 1 : ℝ) = 
              ∑ k in range (n + 2), 1 / ((n + 1)^2 + k + 1 : ℝ) := by
      refine' sum_congr rfl fun k hk => _
      rw [mem_range] at hk
      have : (n + 1) * (n + 2) / 2 + k + 1 = (n + 1)^2 + k + 1 := by
        rw [Nat.mul_div_right]
        · ring
        · exact Nat.zero_lt_succ 1
      rw [this]
    rw [h₁]
    have h₂ : (n + 1 + 1)^2 = (n + 1)^2 + 2 * (n + 1) + 1 := by ring
    rw [h₂]
    have h₃ : range ((n + 1)^2 + 2 * (n + 1) + 1) = 
              range ((n + 1)^2 + 1) ∪ Ico ((n + 1)^2 + 1) ((n + 1)^2 + 2 * (n + 1) + 1) := by
      rw [range_union_Ico, Nat.add_assoc]
      simp
    rw [h₃, sum_union, sum_range_add_sum_Ico]
    · simp
      rw [sum_Ico_eq_sum_range]
      · simp [sum_range_add, pow_two]
        ring
      · simp
    · rw [disjoint_iff_ne]
      intro a ha b hb
      simp [mem_range, mem_Ico] at ha hb
      linarith

theorem problem_19_2 : 
    Tendsto (λ n => partial_sum_series n) atTop (𝓝 Real.eulerMascheroni) := by
  rw [partial_sum_eq]
  have h₁ : Tendsto (λ n => 2 * (∑ k in range (n + 1), 1 / (k + 1 : ℝ)) - log (n + 1)) atTop (𝓝 (2 * Real.eulerMascheroni)) := by
    simp_rw [mul_sub]
    refine' Tendsto.sub _ tendsto_log_nat_add_one_atTop
    refine' Tendsto.const_mul _ 2
    exact tendsto_euler_mascheroni_seq
  have h₂ : Tendsto (λ n => (∑ k in range ((n + 1)^2), 1 / (k + 1 : ℝ)) - log ((n + 1)^2)) atTop (𝓝 Real.eulerMascheroni) := by
    refine' tendsto_euler_mascheroni_seq.comp _
    refine' Tendsto.atTop_mul_atTop tendsto_nat_cast_atTop_atTop tendsto_nat_cast_atTop_atTop
  have h₃ : Tendsto (λ n => log ((n + 1)^2)) atTop (𝓝 ∞) := by
    simp_rw [Real.log_pow, Nat.cast_add, Nat.cast_one]
    refine' Tendsto.const_mul _ 2
    exact tendsto_log_nat_add_one_atTop
  have h₄ : Tendsto (λ n => log (n + 1)) atTop (𝓝 ∞) := tendsto_log_nat_add_one_atTop
  have h₅ : Tendsto (λ n => (2 * (∑ k in range (n + 1), 1 / (k + 1 : ℝ)) - log (n + 1)) - 
                           ((∑ k in range ((n + 1)^2), 1 / (k + 1 : ℝ)) - log ((n + 1)^2))) atTop (𝓝 (2 * Real.eulerMascheroni - Real.eulerMascheroni)) := by
    refine' Tendsto.sub h₁ h₂
  simp at h₅
  simp_rw [sub_sub_sub_cancel_left] at h₅
  convert h₅ using 1
  ext n
  rw [Real.log_pow, Nat.cast_add, Nat.cast_one, mul_comm]
  ring