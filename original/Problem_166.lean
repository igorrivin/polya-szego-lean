/-
Polya-Szego Problem 166
Part One, Chapter 4

Original problem:
Let $\varphi_{n}(x)$ and $\psi_{n}(x)$ denote the polynomials of degree $n, n= 0,1,2, \ldots$ defined by the formulas\\
$\varphi_{0}(x)=1, \quad \varphi_{n}^{\prime}(x)=\varphi_{n-1}(x), \quad \varphi_{n}(0)=0$,\\
$\psi_{0}(x)=1, \quad \psi_{n}(x+1)-\psi_{n}(x)=\psi_{n-1}(x), \quad \psi_{n}(0)=0, \quad n=1,2,3, \ldots$\\
Find the two sums $\varphi(x)$ and $\psi(x)$,

$$
\begin{aligned}
& \varphi(x)=\varphi_{0}(x)+\varphi_{1}(x)+\cdots+\varphi_{n}(x)+\cdots \\
& \psi(x)=\psi_{0}(x)+\psi_{\mathrm{

Formalization notes: -- We formalize the statement about intervals (x_k, y_k) containing (x_{k+1}, y_{k+1})
-- where x_n = y_n * exp(-1/(12n)) and y_n = n! * n^(-n - 1/2) * exp(n)
-- The statement means: x_{k+1} > x_k and y_{k+1} < y_k for all k ≥ 1
-/

import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Intervals.Basic

-- Formalization notes:
-- We formalize the statement about intervals (x_k, y_k) containing (x_{k+1}, y_{k+1})
-- where x_n = y_n * exp(-1/(12n)) and y_n = n! * n^(-n - 1/2) * exp(n)
-- The statement means: x_{k+1} > x_k and y_{k+1} < y_k for all k ≥ 1

theorem problem_166_interval_nesting (k : ℕ) (hk : k ≥ 1) :
    let y_n : ℕ → ℝ := fun n => (Nat.factorial n : ℝ) * ((n : ℝ) ^ (-(n : ℝ) - 1/2)) * Real.exp n
    let x_n : ℕ → ℝ := fun n => y_n n * Real.exp (-1/(12 * n))
    in x_n (k + 1) > x_n k ∧ y_n (k + 1) < y_n k := by
  sorry

-- Proof attempt:
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Intervals.Basic

theorem problem_166_interval_nesting (k : ℕ) (hk : k ≥ 1) :
    let y_n : ℕ → ℝ := fun n => (Nat.factorial n : ℝ) * ((n : ℝ) ^ (-(n : ℝ) - 1/2)) * Real.exp n
    let x_n : ℕ → ℝ := fun n => y_n n * Real.exp (-1/(12 * n))
    in x_n (k + 1) > x_n k ∧ y_n (k + 1) < y_n k := by
  let y_n : ℕ → ℝ := fun n => (Nat.factorial n : ℝ) * ((n : ℝ) ^ (-(n : ℝ) - 1/2)) * Real.exp n
  let x_n : ℕ → ℝ := fun n => y_n n * Real.exp (-1/(12 * n))
  have hk_pos : (k : ℝ) > 0 := by exact_mod_cast Nat.pos_of_ne_zero (by linarith)
  have hk1_pos : (k + 1 : ℝ) > 0 := by norm_cast; linarith
  
  constructor
  · -- Proof that x_{k+1} > x_k
    simp [x_n, y_n]
    rw [mul_lt_mul_right (Real.exp_pos _)]
    have : (k + 1 : ℝ) ^ (k + 1 + 1/2) / (k : ℝ) ^ (k + 1/2) = 
           (1 + 1/k) ^ (k + 1/2) * (k + 1) / Real.sqrt (k + 1) := by
      rw [← Real.rpow_add hk_pos, ← Real.rpow_add hk1_pos]
      field_simp [hk_pos.ne', hk1_pos.ne']
      rw [← Real.rpow_nat_cast, ← Real.rpow_mul (by positivity)]
      congr 2
      · ring
      · ring_nf; rw [add_comm _ (1/2), ← add_assoc]; congr
        field_simp; ring
    rw [this, Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
    field_simp [hk_pos.ne', hk1_pos.ne']
    rw [mul_comm _ (Real.exp 1), ← Real.exp_add, add_comm _ (1 : ℝ)]
    have : Real.exp (-(1 / (12 * (k + 1))) + 1 / (12 * k) + 1) = 
           Real.exp (1 + 1/(12*k*(k+1)))) := by
      congr
      field_simp [hk_pos.ne', hk1_pos.ne']
      ring
    rw [this]
    apply mul_lt_mul_of_pos_left _ (by positivity)
    have : (1 + 1/k) ^ (k + 1/2) * (k + 1) / Real.sqrt (k + 1) < Real.exp (1 + 1/(12*k*(k+1))) := by
      refine (Real.stirling_inequality (k + 1)).trans_le' ?_
      refine le_of_eq ?_
      congr 2
      · field_simp [hk_pos.ne']; ring
      · field_simp [hk_pos.ne', hk1_pos.ne']; ring
    exact this
  · -- Proof that y_{k+1} < y_k
    simp [y_n]
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
    field_simp [hk_pos.ne', hk1_pos.ne']
    rw [mul_comm _ (Real.exp 1), ← Real.exp_add, add_comm _ (1 : ℝ)]
    have : (k + 1 : ℝ) ^ (k + 1 + 1/2) / (k : ℝ) ^ (k + 1/2) = 
           (1 + 1/k) ^ (k + 1/2) * (k + 1) / Real.sqrt (k + 1) := by
      rw [← Real.rpow_add hk_pos, ← Real.rpow_add hk1_pos]
      field_simp [hk_pos.ne', hk1_pos.ne']
      rw [← Real.rpow_nat_cast, ← Real.rpow_mul (by positivity)]
      congr 2
      · ring
      · ring_nf; rw [add_comm _ (1/2), ← add_assoc]; congr
        field_simp; ring
    rw [this]
    apply mul_lt_mul_of_pos_left _ (by positivity)
    exact Real.stirling_inequality (k + 1)