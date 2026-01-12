/-
Polya-Szego Problem 185.1
Part One, Chapter 4

Original problem:
Construct a sequence of real numbers $a_{1}, a_{2}, \ldots, a_{n}, \ldots$ so that the series

$$
a_{1}^{l}+a_{2}^{l}+\cdots+a_{n}^{l}+\cdots
$$

diverges for $l=\overline{5}$, but converges when $l$ is any odd positive integer different from $\overline{0}$.\\
185.2 (continued). Let the set of all odd positive integers be divided (arbitrarily) into two complementary subsets $C$ and $D$ (having no element in common). Show that there exists a sequence of real numbers $a_{1}, a_{2}, \ldots, a_{n}, 

Formalization notes: 1. **Key Concepts Captured:**
   - Part 185.1: Formalizes existence of a sequence `a : ℕ → ℝ` with:
     - `¬ Summable fun n => (a n)^5` (diverges for l = 5)
     - `∀ l, l.Odd → l > 0 → l ≠ 5 → Summable fun n => (a n)^l` (converges for all other odd positive integers)
-/

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.PSeries
import Mathlib.Data.Nat.Parity
import Mathlib.Data.Set.Pairwise

/-!
  Formalizing Problem 185 from Polya-Szego's "Problems and Theorems in Analysis"

  We formalize the existence of sequences of real numbers with prescribed convergence 
  properties for series of powers.
  
  For Part 185.1: ∃ sequence where Σ a_n^5 diverges but Σ a_n^l converges 
  for all odd positive integers l ≠ 5.
  
  For Part 185.2: For any partition (C, D) of odd positive integers into 
  disjoint sets, ∃ sequence where Σ a_n^l converges for l ∈ C and diverges for l ∈ D.
-/

open Set
open Filter
open Finset
open BigOperators

/-- Problem 185.1: Existence of a sequence where Σ a_n^5 diverges but Σ a_n^l 
    converges for all odd positive integers l ≠ 5. -/
theorem exists_sequence_convergence_specific_l : 
    ∃ (a : ℕ → ℝ), 
      (¬ Summable fun n : ℕ => (a n) ^ (5 : ℕ)) ∧ 
      (∀ (l : ℕ), (l : ℕ).Odd → l > 0 → l ≠ 5 → Summable fun n : ℕ => (a n) ^ (l : ℕ)) := by
  sorry

/-- Problem 185.2: For any partition of odd positive integers into two disjoint sets,
    there exists a sequence where the series Σ a_n^l converges for l in one set
    and diverges for l in the other set. -/
theorem exists_sequence_for_partition (C D : Set ℕ) 
    (hC : ∀ n ∈ C, n.Odd ∧ n > 0) (hD : ∀ n ∈ D, n.Odd ∧ n > 0)
    (hdisj : Disjoint C D) (hunion : ∀ n, (n.Odd ∧ n > 0) → (n ∈ C ∨ n ∈ D)) : 
    ∃ (a : ℕ → ℝ), 
      (∀ l ∈ C, Summable fun n : ℕ => (a n) ^ (l : ℕ)) ∧ 
      (∀ l ∈ D, ¬ Summable fun n : ℕ => (a n) ^ (l : ℕ)) ∧
      (∀ l ∉ C ∪ D, True) := by
  sorry

-- Proof attempt:
theorem exists_sequence_convergence_specific_l : 
    ∃ (a : ℕ → ℝ), 
      (¬ Summable fun n : ℕ => (a n) ^ (5 : ℕ)) ∧ 
      (∀ (l : ℕ), (l : ℕ).Odd → l > 0 → l ≠ 5 → Summable fun n : ℕ => (a n) ^ (l : ℕ)) := by
  let a : ℕ → ℝ := fun n => 
    let m := (n / 10) + 1
    if n % 10 < 5 then (1:ℝ) / (m ^ (1/5)) else (-2:ℝ) / (m ^ (1/5))
  
  have h_a_def : ∀ n, a n = 
    let m := (n / 10) + 1
    if n % 10 < 5 then m ^ (-(1/5)) else -2 * m ^ (-(1/5)) := by
    intro n
    simp [a, ← one_div]
    rw [div_eq_mul_inv]
  
  refine ⟨a, ?_, ?_⟩
  · -- Show Σ a_n^5 diverges
    have : Summable (fun n => (a n)^5) ↔ Summable (fun m => 5 * (1:ℝ) / (m:ℝ)) := by
      apply summable_congr
      intro n
      rw [h_a_def n]
      let m := (n / 10) + 1
      have h_m_pos : 0 < (m:ℝ) := by norm_cast; exact Nat.succ_pos _
      cases' (n % 10 < 5) with h
      · simp [h]
        rw [← one_div, rpow_nat_cast, rpow_neg h_m_pos.le, rpow_one_div h_m_pos.ne']
        field_simp
      · simp [h]
        rw [neg_mul_pow, pow_bit1_neg, ← one_div, rpow_nat_cast, rpow_neg h_m_pos.le, 
            rpow_one_div h_m_pos.ne']
        field_simp
        ring
    rw [this]
    simp only [div_eq_mul_inv]
    have : ¬Summable (fun m => (5:ℝ) * m⁻¹) := by
      apply Summable.not_of_not_summable_norm
      simp only [norm_mul, norm_inv, norm_eq_abs, abs_of_pos (by norm_num : 0 < (5:ℝ)), 
                 abs_inv, Real.norm_eq_abs, mul_inv_rev]
      exact Real.not_summable_nat_inv
    exact this
  · -- Show Σ a_n^l converges for odd l ≠ 5
    intro l hl_odd hl_pos hl_ne5
    have h_l_ge1 : 1 ≤ l := Nat.pos_iff_one_le.mp hl_pos
    have h_l_ge3 : 3 ≤ l := by
      cases' h_l_ge1.lt_or_eq with h h
      · cases' h; case refl => cases hl_odd
      · cases' h; case refl => cases hl_ne5 (by decide)
      · exact Nat.succ_le_succ (Nat.succ_le_succ h)
    
    apply summable_of_isBigO_nat
    have : (fun n => (a n)^l) =O[atTop] (fun n => n ^ (-(l/5))) := by
      rw [Asymptotics.isBigO_iff]
      refine ⟨3, ?_⟩
      intro n hn
      rw [h_a_def n]
      let m := (n / 10) + 1
      have h_m_ge : m ≥ n / 10 := by simp [m]; exact Nat.le_add_left _ _
      cases' (n % 10 < 5) with h
      · simp [h]
        rw [norm_mul, norm_eq_abs, abs_one, one_mul, norm_inv, norm_rpow_of_nonneg]
        · rw [← rpow_neg (by positivity : 0 ≤ (m:ℝ)), ← one_div]
          refine le_trans ?_ (rpow_le_rpow_of_nonpos (by positivity) h_m_ge (by linarith))
          simp only [inv_le_inv, Nat.cast_le]
          exact Nat.div_le_self n 10
        · positivity
      · simp [h]
        rw [norm_mul, norm_eq_abs, abs_neg, abs_two, norm_mul, norm_eq_abs, abs_one, 
            norm_inv, norm_rpow_of_nonneg]
        · rw [mul_assoc, ← rpow_neg (by positivity : 0 ≤ (m:ℝ)), ← one_div]
          refine le_trans ?_ (rpow_le_rpow_of_nonpos (by positivity) h_m_ge (by linarith))
          simp only [inv_le_inv, Nat.cast_le]
          exact Nat.div_le_self n 10
        · positivity
    refine this.trans ?_
    simp only [Real.norm_eq_abs]
    have h_conv : l / 5 > 1 := by
      have : l > 5 := by
        cases' Nat.lt_or_eq_of_le h_l_ge3 with h h
        · cases' h; case refl => cases hl_ne5 (by decide)
        · cases' h; case refl => cases hl_ne5 (by decide)
        · exact h
      rw [← Nat.cast_lt (α := ℚ), ← div_lt_iff (by norm_num : (0:ℚ) < 5)]
      norm_cast
    exact summable_one_div_nat_pow.mpr h_conv