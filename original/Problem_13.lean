/-
Polya-Szego Problem 13
Part Three, Chapter 1

Original problem:
We put\\
s -uvided into three\\
i. Suppose that the

Lee segment. (The - of the variables variable $t$ signify $=6 e^{-i t}$.\\
s functions of the le $t$ is represented onents of velocity ve radius vector.\\
e $n$-th term $\frac{z^{n}}{n!}$ of\\
$P_{0}(z)=z, \quad P_{n}(z)=z\left(1-\frac{z^{2}}{1^{2}}\right)\left(1-\frac{z^{2}}{2^{2}}\right)\left(1-\frac{z^{2}}{3^{2}}\right) \cdots\left(1-\frac{z^{2}}{n^{2}}\right)$,

$$
n=1,2,3, \ldots
$$

For what values of $z$ is $\left|P_{n}(z)\right|$ large

Formalization notes: -- We define P_n(z) as given in the problem: P_0(z) = z, 
-- P_n(z) = z ∏_{k=1}^n (1 - z^2/k^2) for n ≥ 1
-- The theorem characterizes where |P_n(z)| is strictly greater than |P_m(z)| for all m ≠ n
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sine

-- Formalization notes:
-- We define P_n(z) as given in the problem: P_0(z) = z, 
-- P_n(z) = z ∏_{k=1}^n (1 - z^2/k^2) for n ≥ 1
-- The theorem characterizes where |P_n(z)| is strictly greater than |P_m(z)| for all m ≠ n

open Complex
open Real

-- Define the partial products P_n(z)
noncomputable def P : ℕ → ℂ → ℂ
  | 0, z => z
  | n+1, z => P n z * (1 - z^2 / ((n+1 : ℂ)^2))

-- Alternative direct definition for clarity
noncomputable def P' (n : ℕ) (z : ℂ) : ℂ :=
  z * ∏ k in Finset.range n, (1 - z^2 / ((k+1 : ℂ)^2))

-- The main theorem: For z ≠ 0 and not on certain boundaries,
-- |P_n(z)| is maximal when z lies in the region R_n between lemniscates L_n and L_{n+1}
theorem problem_13_part1 (n : ℕ) (z : ℂ) (hz : z ≠ 0) :
    -- Define the lemniscates L_n: |z^2 - n^2| = n^2
    let L (k : ℕ) : Set ℂ := {w | Complex.abs (w^2 - (k : ℂ)^2) = (k : ℝ)^2}
    -- Define the region R_n: between L_n and L_{n+1} (for n ≥ 1)
    -- R_0 is inside L_1
    let R (k : ℕ) : Set ℂ :=
      if k = 0 then {w | Complex.abs (w^2 - 1) < 1}
      else {w | Complex.abs (w^2 - (k : ℂ)^2) > (k : ℝ)^2 ∧ 
                Complex.abs (w^2 - ((k+1 : ℂ))^2) < ((k+1 : ℝ))^2}
    -- If z is in R_n, then |P_n(z)| > |P_m(z)| for all m ≠ n
    z ∈ R n → ∀ m : ℕ, m ≠ n → Complex.abs (P n z) > Complex.abs (P m z) := by
  sorry

-- Additional theorem about the angular region where the sequence |P_n(z)| is eventually increasing
theorem problem_13_part2 (z : ℂ) :
    -- Outside the angular region -π/4 < arg z < π/4 and 3π/4 < arg z < 5π/4 (and z ≠ 0),
    -- |P_n(z)| increases monotonically with n
    let angular_region : Set ℂ := {w | w ≠ 0 ∧ 
        ((Complex.arg w > -π/4 ∧ Complex.arg w < π/4) ∨
         (Complex.arg w > 3*π/4 ∧ Complex.arg w < 5*π/4))}
    z ∉ angular_region → ∀ n : ℕ, Complex.abs (P n z) ≤ Complex.abs (P (n+1) z) := by
  sorry

-- Theorem about equality on boundaries
theorem problem_13_part3 (n : ℕ) (z : ℂ) :
    -- On the boundary between R_n and R_{n+1}, |P_n(z)| = |P_{n+1}(z)| 
    -- and both are greater than other partial products
    let boundary (k : ℕ) : Set ℂ := 
      {w | Complex.abs (w^2 - ((k+1 : ℂ))^2) = ((k+1 : ℝ))^2}
    z ∈ boundary n → 
    Complex.abs (P n z) = Complex.abs (P (n+1) z) ∧
    ∀ m : ℕ, m ≠ n → m ≠ n+1 → Complex.abs (P n z) > Complex.abs (P m z) := by
  sorry

-- Proof attempt:
theorem problem_13_part1 (n : ℕ) (z : ℂ) (hz : z ≠ 0) :
    let L (k : ℕ) : Set ℂ := {w | Complex.abs (w^2 - (k : ℂ)^2) = (k : ℝ)^2}
    let R (k : ℕ) : Set ℂ :=
      if k = 0 then {w | Complex.abs (w^2 - 1) < 1}
      else {w | Complex.abs (w^2 - (k : ℂ)^2) > (k : ℝ)^2 ∧ 
                Complex.abs (w^2 - ((k+1 : ℂ))^2) < ((k+1 : ℝ))^2}
    z ∈ R n → ∀ m : ℕ, m ≠ n → Complex.abs (P n z) > Complex.abs (P m z) := by
  intro L R hzR m hmn
  simp [P, P'] at *
  cases' n with n
  · -- Case n = 0
    simp [R] at hzR
    cases' m with m
    · contradiction
    · simp [P, P']
      rw [Finset.prod_range_succ]
      simp [Complex.abs.map_mul]
      have : Complex.abs (1 - z^2 / ((m + 1 : ℂ)^2)) < 1 := by
        have := hzR
        rw [← Complex.abs.map_div, ← mul_lt_mul_right (by positivity : 0 < (m+1 : ℝ)^2)]
        field_simp
        rw [← Complex.abs.map_mul, ← Complex.abs.map_sub, mul_comm, ← sub_lt_iff_lt_add']
        convert this using 2
        ring_nf
        simp
        ring
      refine mul_lt_mul_of_pos_left ?_ (Complex.abs.pos hz)
      clear hz hzR
      induction' m with k ih
      · simp [this]
      · rw [Finset.prod_range_succ, Complex.abs.map_mul]
        exact mul_lt_one_of_nonneg_of_lt_one_left (by positivity) ih this.le this
  · -- Case n ≥ 1
    simp [R] at hzR
    cases' m with m
    · -- Case m = 0
      simp [P, P']
      rw [Finset.prod_range_succ]
      simp [Complex.abs.map_mul]
      have : Complex.abs (1 - z^2 / ((n + 1 : ℂ)^2)) < 1 := by
        have := hzR.2
        rw [← Complex.abs.map_div, ← mul_lt_mul_right (by positivity : 0 < (n+1 : ℝ)^2)]
        field_simp
        rw [← Complex.abs.map_mul, ← Complex.abs.map_sub, mul_comm, ← sub_lt_iff_lt_add']
        convert this using 2
        ring_nf
        simp
        ring
      refine mul_lt_mul_of_pos_left ?_ (Complex.abs.pos hz)
      clear hz hzR
      induction' n with k ih
      · simp [this]
      · rw [Finset.prod_range_succ, Complex.abs.map_mul]
        exact mul_lt_one_of_nonneg_of_lt_one_left (by positivity) ih this.le this
    · -- Case m ≥ 1
      simp [P, P']
      rw [Finset.prod_range_succ, Finset.prod_range_succ, Complex.abs.map_mul, Complex.abs.map_mul]
      refine mul_lt_mul' ?_ ?_ (by simp) (Complex.abs.pos hz)
      · -- Compare the products
        have h1 : ∀ k < n, Complex.abs (1 - z^2 / ((k + 1 : ℂ)^2)) > 1 := by
          intro k hk
          have := hzR.1
          rw [← Complex.abs.map_div, ← mul_lt_mul_right (by positivity : 0 < (k+1 : ℝ)^2)]
          field_simp
          rw [← Complex.abs.map_mul, ← Complex.abs.map_sub, mul_comm, ← lt_sub_iff_add_lt']
          convert this using 2
          ring_nf
          simp
          ring
        have h2 : ∀ k ≥ n, Complex.abs (1 - z^2 / ((k + 1 : ℂ)^2)) < 1 := by
          intro k hk
          have := hzR.2
          rw [← Complex.abs.map_div, ← mul_lt_mul_right (by positivity : 0 < (k+1 : ℝ)^2)]
          field_simp
          rw [← Complex.abs.map_mul, ← Complex.abs.map_sub, mul_comm, ← sub_lt_iff_lt_add']
          convert this using 2
          ring_nf
          simp
          ring
        -- Now compare the products based on whether m < n or m > n
        by_cases hm : m < n
        · have := h1 m.succ (Nat.lt_succ_of_lt hm)
          refine (Finset.prod_lt_prod' (fun k _ ↦ by positivity) ?_).le
          intro k hk
          exact (h1 k (hk.trans_le (Nat.le_of_lt_succ hm))).le
        · push_neg at hm
          have := h2 m.succ (hm.trans (Nat.le_succ _))
          refine (Finset.prod_lt_prod' (fun k _ ↦ by positivity) ?_).le
          intro k hk
          exact (h2 k (hk.trans_le hm)).le
      · -- Compare the last factors
        by_cases hm : m < n
        · exact h1 m.succ (Nat.lt_succ_of_lt hm)
        · push_neg at hm
          exact h2 m.succ (hm.trans (Nat.le_succ _))