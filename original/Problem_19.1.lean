/-
Polya-Szego Problem 19.1
Part One, Chapter 4

Original problem:
We may regard the relation [18]

$$
\lim _{n \rightarrow \infty}\left(1+\frac{1}{2}+\frac{1}{3}+\cdots+\frac{1}{n}-\log n\right)=C
$$

as the definition of Euler's constant $C$. Derive hence that

$$
1-\frac{1}{2}+\frac{1}{3}-\cdots+\frac{1}{2 n-1}-\frac{1}{2 n}+\cdots=\log 2
$$

Formalization notes: -- 1. We formalize the two main statements from the problem
-- 2. Statement 1: The limit defining Euler's constant C exists
-- 3. Statement 2: The alternating harmonic series converges to log 2
-- 4. H n := harmonic number (sum_{k=1}^n 1/k)
-- 5. The second statement is derived from the first, though we state them separately
-/

-- Imports
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SumConst

-- Formalization notes: 
-- 1. We formalize the two main statements from the problem
-- 2. Statement 1: The limit defining Euler's constant C exists
-- 3. Statement 2: The alternating harmonic series converges to log 2
-- 4. H n := harmonic number (sum_{k=1}^n 1/k)
-- 5. The second statement is derived from the first, though we state them separately

open Real
open Finset
open Filter
open Topology

-- Harmonic number up to n
noncomputable def harmonic (n : ℕ) : ℝ :=
  ∑ k in range n, 1 / ((k + 1 : ℕ) : ℝ)

-- Statement 1: Limit defining Euler's constant exists
theorem euler_constant_exists : ∃ (C : ℝ), Tendsto (λ n : ℕ ↦ harmonic n - Real.log (n : ℝ)) atTop (𝓝 C) := by
  sorry

-- Auxiliary theorem for the book's derivation step
theorem harmonic_relation : 
    Tendsto (λ n : ℕ ↦ harmonic (2 * n) - harmonic n) atTop (𝓝 (Real.log 2)) := by
  sorry

-- Statement 2: Alternating harmonic series converges to log 2
theorem alternating_harmonic_series_sum :
    Tendsto (λ n : ℕ ↦ ∑ k in range n, (-1 : ℝ) ^ k / ((k + 1 : ℕ) : ℝ)) atTop (𝓝 (Real.log 2)) := by
  sorry

-- Alternatively, using the definition with alternating signs more explicitly
theorem alternating_harmonic_series_alt : 
    Tendsto (λ n : ℕ ↦ ∑ k in range (2 * n), (-1 : ℝ) ^ k / ((k + 1 : ℕ) : ℝ)) atTop (𝓝 (Real.log 2)) := by
  sorry

-- Proof attempt:
theorem euler_constant_exists : ∃ (C : ℝ), Tendsto (λ n : ℕ ↦ harmonic n - Real.log (n : ℝ)) atTop (𝓝 C) := by
  exact Real.tendsto_euler_mascheroni

theorem harmonic_relation : 
    Tendsto (λ n : ℕ ↦ harmonic (2 * n) - harmonic n) atTop (𝓝 (Real.log 2)) := by
  have h1 : Tendsto (λ n ↦ harmonic (2 * n) - Real.log (2 * n : ℝ)) atTop (𝓝 Real.eulerMascheroni) := by
    refine Tendsto.comp Real.tendsto_euler_mascheroni ?_
    apply tendsto_atTop_atTop_of_monotone' (fun n ↦ 2 * n)
    · intro a b hab; exact mul_le_mul_left' hab 2
    · intro b; use b; linarith
  have h2 : Tendsto (λ n ↦ harmonic n - Real.log (n : ℝ)) atTop (𝓝 Real.eulerMascheroni) :=
    Real.tendsto_euler_mascheroni
  have h3 : Tendsto (λ n ↦ Real.log (2 * n : ℝ) - Real.log (n : ℝ)) atTop (𝓝 (Real.log 2)) := by
    simp_rw [← Real.log_div]
    simp only [Nat.cast_mul, mul_div_right_comm, div_self, ne_eq, Nat.cast_eq_zero, two_ne_zero, not_false_iff, 
               div_one]
    exact tendsto_const_nhds
  have h4 : Tendsto (λ n ↦ (harmonic (2 * n) - Real.log (2 * n : ℝ)) - 
                          (harmonic n - Real.log (n : ℝ))) atTop (𝓝 (Real.eulerMascheroni - Real.eulerMascheroni)) :=
    Tendsto.sub h1 h2
  simp only [sub_sub_sub_cancel_right] at h4
  have h5 : Tendsto (λ n ↦ harmonic (2 * n) - harmonic n) atTop (𝓝 (Real.log 2)) := by
    convert Tendsto.add h4 h3 using 1
    ext n
    ring
  exact h5

theorem alternating_harmonic_series_sum :
    Tendsto (λ n : ℕ ↦ ∑ k in range n, (-1 : ℝ) ^ k / ((k + 1 : ℕ) : ℝ)) atTop (𝓝 (Real.log 2)) := by
  have h : ∀ n : ℕ, harmonic (2 * n) - harmonic n = ∑ k in range n, (-1 : ℝ) ^ k / (k + 1 : ℝ) := by
    intro n
    induction' n with n ih
    · simp [harmonic]
    · rw [harmonic, harmonic, mul_succ, range_succ, sum_range_succ, sum_range_succ, ih]
      simp only [Nat.cast_add, Nat.cast_one, add_comm _ (1 : ℝ), add_div, one_div]
      ring
  rw [tendsto_congr' (eventually_of_forall h)]
  exact harmonic_relation

theorem alternating_harmonic_series_alt : 
    Tendsto (λ n : ℕ ↦ ∑ k in range (2 * n), (-1 : ℝ) ^ k / ((k + 1 : ℕ) : ℝ)) atTop (𝓝 (Real.log 2)) := by
  have h : ∀ n : ℕ, ∑ k in range (2 * n), (-1 : ℝ) ^ k / (k + 1 : ℝ) = 
             ∑ k in range n, (-1 : ℝ) ^ (2 * k) / (2 * k + 1 : ℝ) + 
             ∑ k in range n, (-1 : ℝ) ^ (2 * k + 1) / (2 * k + 2 : ℝ) := by
    intro n
    rw [sum_range_add_sum_Ico _ (by omega), sum_range_add_sum_Ico _ (by omega)]
    · simp only [Nat.mul_succ, range_mul, sum_union]
      congr
      · simp only [pow_mul, neg_one_sq, one_pow, one_div]
      · simp only [pow_add, pow_one, mul_neg, neg_div, one_div]
    · intro m hm
      omega
  simp_rw [h]
  have h1 : ∀ n : ℕ, ∑ k in range n, (-1 : ℝ) ^ (2 * k) / (2 * k + 1 : ℝ) + 
                      ∑ k in range n, (-1 : ℝ) ^ (2 * k + 1) / (2 * k + 2 : ℝ) = 
                      harmonic (2 * n) - harmonic n := by
    intro n
    rw [← alternating_harmonic_series_sum h n]
    exact (sum_range_add_sum_Ico _ (by omega)).symm
  rw [tendsto_congr' (eventually_of_forall h1)]
  exact harmonic_relation