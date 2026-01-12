/-
Polya-Szego Problem 170
Part One, Chapter 4

Original problem:
The\\
the natual sember. Ans\\

Formalization notes: We formalize the key result from Problem 170: For n ≥ 2, the fractional part of n!e satisfies
  n!e - ⌊n!e⌋ < 3/(n+1)
This follows from the Taylor series expansion of e with remainder term.
-/
-/

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.NumberTheory.DiophantineApproximation

/-!
Formalization notes:
We formalize the key result from Problem 170: For n ≥ 2, the fractional part of n!e satisfies
  n!e - ⌊n!e⌋ < 3/(n+1)
This follows from the Taylor series expansion of e with remainder term.
-/

theorem problem_170 (n : ℕ) (hn : n ≥ 2) : 
    let e := Real.exp 1
    let factorial_n : ℕ := Nat.factorial n
    let n_factorial_e : ℝ := (factorial_n : ℝ) * e
    n_factorial_e - (⌊n_factorial_e⌋ : ℝ) < 3 / ((n : ℝ) + 1) := by
  sorry

-- Proof attempt:
theorem problem_170 (n : ℕ) (hn : n ≥ 2) : 
    let e := Real.exp 1
    let factorial_n : ℕ := Nat.factorial n
    let n_factorial_e : ℝ := (factorial_n : ℝ) * e
    n_factorial_e - (⌊n_factorial_e⌋ : ℝ) < 3 / ((n : ℝ) + 1) := by
  let e := Real.exp 1
  let factorial_n := Nat.factorial n
  let n_factorial_e := (factorial_n : ℝ) * e
  
  -- Express e as its Taylor series up to n terms plus remainder
  have e_eq : e = (∑ k in Finset.range (n + 1), 1 / Nat.factorial k) + 
                 (1 / (Nat.factorial (n + 1))) * (Nat.factorial (n + 1) / (n + 1)) * Real.exp (1 - (1 / (n + 1))) := by
    rw [Real.exp_eq_tsum]
    exact Real.exp_approx_succ (by linarith [hn])
  
  -- Multiply both sides by n!
  have key_eq : n_factorial_e = (∑ k in Finset.range (n + 1), (factorial_n : ℝ) / Nat.factorial k) + 
                                  (1 / (n + 1)) * Real.exp (1 - (1 / (n + 1))) := by
    rw [e_eq]
    simp [n_factorial_e]
    ring_nf
    rw [← Nat.factorial_succ, Nat.succ_eq_add_one]
    field_simp [Nat.factorial_ne_zero (n + 1)]
    ring
  
  -- The sum is an integer since for k ≤ n, n! / k! is an integer
  have sum_int : (∑ k in Finset.range (n + 1), (factorial_n : ℝ) / Nat.factorial k) ∈ ℤ := by
    apply Finset.sum_mem
    intro k hk
    rw [Finset.mem_range, Nat.lt_succ_iff] at hk
    simp [div_eq_mul_inv]
    rw [← Nat.cast_mul]
    norm_cast
    exact Nat.factorial_mul_factorial_dvd_factorial hk
  
  -- The fractional part comes from the remainder term
  have remainder_bound : (1 / (n + 1)) * Real.exp (1 - (1 / (n + 1))) < 3 / (n + 1) := by
    rw [mul_comm]
    apply mul_lt_of_lt_div
    · norm_cast
      linarith [hn]
    · have : Real.exp (1 - 1 / (n + 1)) ≤ Real.exp 1 := by
        apply Real.exp_le_exp.mpr
        simp
        apply sub_le_self
        positivity
      linarith [Real.exp_pos (1 - 1 / (n + 1)), this]
  
  -- Combine the results
  rw [← key_eq]
  have floor_eq : ⌊n_factorial_e⌋ = ∑ k in Finset.range (n + 1), (factorial_n : ℝ) / Nat.factorial k := by
    have : n_factorial_e = (∑ k in Finset.range (n + 1), (factorial_n : ℝ) / Nat.factorial k) + 
                          (1 / (n + 1)) * Real.exp (1 - (1 / (n + 1))) := by rw [key_eq]
    rw [this]
    exact Int.floor_add_fract (sum_int) _
  rw [floor_eq]
  simp
  exact remainder_bound