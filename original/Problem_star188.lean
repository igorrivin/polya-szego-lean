/-
Polya-Szego Problem *188
Part One, Chapter 4

Original problem:
Show that

$$
\frac{S_{k}^{k}}{z^{k+1}}+\frac{S_{k}^{k+1}}{z^{k+2}}+\cdots+\frac{S_{k}^{n}}{z^{n+1}}+\cdots=\frac{1}{z(z-1)(z-2) \cdots(z-k)} .
$$

Formalization notes: -- 1. We formalize the equality of power series (formal power series identity)
-- 2. Sₖⁿ represents Stirling numbers of the second kind S(n,k) = {n k}
-- 3. The series is considered as a formal power series in z⁻¹
-- 4. We use Complex z since the formula holds for complex z outside integer poles
-- 5. The series converges for |z| > k (outside a disk)
-/

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Analysis.Calculus.Series

open Complex
open Set
open Filter

-- Formalization notes:
-- 1. We formalize the equality of power series (formal power series identity)
-- 2. Sₖⁿ represents Stirling numbers of the second kind S(n,k) = {n k}
-- 3. The series is considered as a formal power series in z⁻¹
-- 4. We use Complex z since the formula holds for complex z outside integer poles
-- 5. The series converges for |z| > k (outside a disk)

theorem problem_188_part_one_chapter_4 (k : ℕ) :
    let S : ℕ → ℕ → ℝ := fun n k => if n < k then 0 else stirling2 n k
    HaveConvergentSeries := 
      ∀ z : ℂ, |z| > (k : ℝ) → 
        HasSum (λ n : ℕ ↦ (S (n + k) k : ℂ) / (z : ℂ) ^ (n + k + 1)) 
               (1 / (∏ i : ℕ in Finset.range (k + 1), (z - (i : ℂ))))) := by
  sorry

-- Proof attempt:
theorem problem_188_part_one_chapter_4 (k : ℕ) :
    let S : ℕ → ℕ → ℝ := fun n k => if n < k then 0 else stirling2 n k
    ∀ z : ℂ, |z| > (k : ℝ) → 
        HasSum (λ n : ℕ ↦ (S (n + k) k : ℂ) / (z : ℂ) ^ (n + k + 1)) 
               (1 / (∏ i : ℕ in Finset.range (k + 1), (z - (i : ℂ))))) := by
  intro S z hz
  induction k with
  | zero =>
    simp [S, Finset.range_one, Finset.prod_empty]
    have : (1 : ℂ) = (1 : ℂ) / z * z := by field_simp; ring
    rw [this]
    refine HasSum.smul_const ?_ z
    simp [one_div]
    exact hasSum_geometric_of_norm_lt_1 (by simpa using hz)
  | succ k ih =>
    -- Key steps:
    -- 1. Rewrite the goal using the recurrence relation for Stirling numbers
    -- 2. Factor out (z - k) from the denominator
    -- 3. Apply the inductive hypothesis
    have hk : (k : ℝ) < |z| := by linarith [show (k : ℝ) < (k + 1 : ℝ) by norm_num]
    have hz_ne : z ≠ k := by
      intro h; rw [h] at hz; simp at hz; linarith
    have hz_ne' : ∀ i ∈ Finset.range (k + 1), z ≠ i := by
      intro i hi
      rw [Finset.mem_range] at hi
      intro h
      rw [h] at hz
      have : |(i : ℂ)| = i := by simp
      rw [this] at hz
      linarith [show i ≤ k by linarith]
    
    -- Rewrite the denominator product
    have prod_eq : ∏ i in Finset.range (k + 2), (z - i) = (z - (k + 1)) * ∏ i in Finset.range (k + 1), (z - i) := by
      rw [Finset.range_succ, Finset.prod_insert (Finset.not_mem_range_self)]
    
    -- Main proof
    rw [show (k + 1 : ℝ) = ↑k + 1 by norm_num] at hz
    rw [prod_eq, one_div_mul_one_div, ← mul_div_assoc, ← div_eq_mul_inv]
    
    -- Apply the inductive hypothesis
    have := ih z hk
    simp [S] at this ⊢
    
    -- Rewrite the sum using the Stirling recurrence
    have stirling_rec : ∀ n, S (n + k + 1) (k + 1) = S (n + k) k + (k + 1) * S (n + k) (k + 1) := by
      intro n
      simp [S]
      rw [stirling2_succ_succ, Nat.cast_add, Nat.cast_mul]
      split_ifs with h₁ h₂ h₃ <;> try simp [S] at *
      · linarith
      · linarith
      · linarith
    
    -- Transform the sum
    refine HasSum.even_mul_iff ?_ hz_ne |>.mp ?_
    · apply mul_comm
    · convert_to HasSum (fun n => (S (n + k) k : ℂ) / z ^ (n + k + 1) + (k + 1) * S (n + k) (k + 1) / z ^ (n + k + 1)) 
                        (1 / ∏ i in Finset.range (k + 1), (z - i)) using 1
      · ext n
        rw [← add_div, stirling_rec n, Nat.cast_add, Nat.cast_mul]
        congr 2
        rw [← add_assoc, add_comm 1 n, add_assoc]
      · exact HasSum.add this (HasSum.smul_const (ih z hk) (k + 1 : ℂ))