/-
Polya-Szego Problem 38
Part Three, Chapter 1

Original problem:
There exist complex sequences $z_{1}, z_{2}, \ldots, z_{n}, \ldots$ for which all the series

$$
z_{1}^{k}+z_{2}^{k}+\cdots+z_{n}^{k}+\cdots, \quad k=1,2,3, \ldots
$$

converge and all the series

$$
\left|z_{1}\right|^{k}+\left|z_{2}\right|^{k}+\cdots+\left|z_{n}\right|^{k}+\cdots, \quad k=1,2,3, \ldots
$$

diverge.\\

Formalization notes: -- We're formalizing Problem 38 from Polya-Szego Part Three, Chapter 1
-- The theorem asserts the existence of a complex sequence (z : ℕ → ℂ)
-- such that for every k : ℕ, k ≥ 1:
-- 1. The series ∑_{n=0}^∞ z_n^k converges (in ℂ)
-- 2. The series ∑_{n=0}^∞ |z_n|^k diverges (in ℝ, extended to ℝ≥0)
-- We use `HasSum` for convergence of series and formalize divergence as ¬(Summable)
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Real.Basic

-- Formalization notes:
-- We're formalizing Problem 38 from Polya-Szego Part Three, Chapter 1
-- The theorem asserts the existence of a complex sequence (z : ℕ → ℂ)
-- such that for every k : ℕ, k ≥ 1:
-- 1. The series ∑_{n=0}^∞ z_n^k converges (in ℂ)
-- 2. The series ∑_{n=0}^∞ |z_n|^k diverges (in ℝ, extended to ℝ≥0)
-- We use `HasSum` for convergence of series and formalize divergence as ¬(Summable)

theorem problem_38 : ∃ (z : ℕ → ℂ), 
    (∀ (k : ℕ), 1 ≤ k → HasSum (λ n : ℕ ↦ (z n) ^ k) (∑' n : ℕ, (z n) ^ k)) ∧
    (∀ (k : ℕ), 1 ≤ k → ¬ Summable (λ n : ℕ ↦ Complex.abs (z n) ^ k)) := by
  sorry

-- Proof attempt:
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.NumberTheory.Divisors

theorem problem_38 : ∃ (z : ℕ → ℂ), 
    (∀ (k : ℕ), 1 ≤ k → HasSum (λ n : ℕ ↦ (z n) ^ k) (∑' n : ℕ, (z n) ^ k)) ∧
    (∀ (k : ℕ), 1 ≤ k → ¬ Summable (λ n : ℕ ↦ Complex.abs (z n) ^ k)) := by
  let z (n : ℕ) : ℂ := (1 / (n + 1)) * exp (2 * π * Complex.I / (n + 1))
  use z
  constructor
  · intro k hk
    have h_sum : HasSum (fun n ↦ (z n) ^ k) 0 := by
      refine' hasSum_of_ne_finset_zero fun n hn ↦ _
      simp [z]
      rw [mul_pow, exp_nat_mul]
      have hn' : 0 < n + 1 := Nat.succ_pos n
      have : (2 * π * k) / (n + 1) ≠ 2 * π * m for any m ∈ ℤ := by
        intro m hm
        apply (mul_ne_iff.mp (div_ne_zero_iff.mpr ⟨_, _⟩)).1
        · exact (mul_ne_zero two_ne_zero pi_ne_zero).mpr (Nat.cast_ne_zero.mpr hn'.ne')
        · rw [mul_div_cancel_left _ (Nat.cast_ne_zero.mpr hn'.ne')]
          exact (Int.ediv_eq_iff (Nat.cast_ne_zero.mpr hn'.ne')).mp rfl |>.2
      simp [exp_eq_one_iff, this]
    exact h_sum
  · intro k hk
    simp [z]
    have : (fun n ↦ Complex.abs (1 / (n + 1) * exp (2 * π * Complex.I / (n + 1))) ^ k) = 
            fun n ↦ (1 / (n + 1)) ^ k := by
      ext n
      simp [Complex.abs.exp, Complex.abs.of_nonneg (by positivity)]
    rw [this]
    have : ¬Summable (fun n ↦ (1 / (n + 1 : ℝ)) ^ k) := by
      rw [summable_nat_add_iff 1]
      apply Real.not_summable_one_div_rpow.mpr
      simp [hk]
    exact this