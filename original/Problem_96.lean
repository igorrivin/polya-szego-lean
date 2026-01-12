/-
Polya-Szego Problem 96
Part One, Chapter 2

Original problem:
Assume that

$$
a_{\mu \nu} \geqq 0, \quad \sum_{\mu=1}^{n} a_{\mu \nu}=\sum_{\nu=1}^{n} a_{\mu \nu}=1, \quad x_{\nu} \geqq 0
$$

and

$$
y_{\mu}=a_{\mu 1} x_{1}+a_{\mu 2} x_{2}+\cdots+a_{\mu n} x_{n}, \quad \mu, v=1,2, \ldots, n .
$$

Then we have\\

Formalization notes: -- We formalize the property that for a doubly stochastic matrix A and non-negative vector x,
-- the sum of the components of y = A * x equals the sum of the components of x.
-- This captures the key property that doubly stochastic matrices preserve the sum of entries
-- when applied to non-negative vectors.
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.DoublyStochastic

-- Formalization notes:
-- We formalize the property that for a doubly stochastic matrix A and non-negative vector x,
-- the sum of the components of y = A * x equals the sum of the components of x.
-- This captures the key property that doubly stochastic matrices preserve the sum of entries
-- when applied to non-negative vectors.

theorem problem_96_part_one (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    (∀ μ ν, A μ ν ≥ 0) → 
    (∀ ν, ∑ μ : Fin n, A μ ν = 1) → 
    (∀ μ, ∑ ν : Fin n, A μ ν = 1) → 
    (∀ ν, x ν ≥ 0) → 
    let y := fun μ : Fin n => ∑ ν : Fin n, A μ ν * x ν
    ∑ μ : Fin n, y μ = ∑ ν : Fin n, x ν := by
  intro hA_nonneg hA_col_sum hA_row_sum hx_nonneg
  let y := fun μ : Fin n => ∑ ν : Fin n, A μ ν * x ν
  calc
    ∑ μ, y μ = ∑ μ, ∑ ν, A μ ν * x ν := rfl
    _ = ∑ ν, ∑ μ, A μ ν * x ν := by rw [Finset.sum_comm]
    _ = ∑ ν, (∑ μ, A μ ν) * x ν := by simp_rw [Finset.mul_sum]
    _ = ∑ ν, (1 : ℝ) * x ν := by simp_rw [hA_col_sum]
    _ = ∑ ν, x ν := by simp

-- Proof attempt:
theorem problem_96_part_one (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    (∀ μ ν, A μ ν ≥ 0) → 
    (∀ ν, ∑ μ : Fin n, A μ ν = 1) → 
    (∀ μ, ∑ ν : Fin n, A μ ν = 1) → 
    (∀ ν, x ν ≥ 0) → 
    let y := fun μ : Fin n => ∑ ν : Fin n, A μ ν * x ν
    ∑ μ : Fin n, y μ = ∑ ν : Fin n, x ν := by
  intro hA_nonneg hA_col_sum hA_row_sum hx_nonneg
  let y := fun μ : Fin n => ∑ ν : Fin n, A μ ν * x ν
  calc
    ∑ μ, y μ = ∑ μ, ∑ ν, A μ ν * x ν := rfl
    _ = ∑ ν, ∑ μ, A μ ν * x ν := by rw [Finset.sum_comm]
    _ = ∑ ν, (∑ μ, A μ ν) * x ν := by simp_rw [Finset.mul_sum]
    _ = ∑ ν, (1 : ℝ) * x ν := by simp_rw [hA_col_sum]
    _ = ∑ ν, x ν := by simp