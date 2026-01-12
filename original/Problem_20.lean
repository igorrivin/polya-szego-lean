/-
Polya-Szego Problem 20
Part One, Chapter 4

Original problem:
Assume that the function $f(x)$ is monotone on the interval $(0,1)$.\\

Formalization notes: -- 1. We formalize the inequality for monotone increasing functions on (0,1)
-- 2. We use the Riemann integral (since the book uses Riemann integration)
-- 3. The function f is assumed to be integrable on [0,1] (implied by monotonicity on open interval)
-- 4. The sum uses division of [0,1] into n equal subintervals
-- 5. We include the integrability hypothesis explicitly since Lean requires it
-/

import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.Calculus.FundamentalTheoremOfCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral

-- Formalization notes:
-- 1. We formalize the inequality for monotone increasing functions on (0,1)
-- 2. We use the Riemann integral (since the book uses Riemann integration)
-- 3. The function f is assumed to be integrable on [0,1] (implied by monotonicity on open interval)
-- 4. The sum uses division of [0,1] into n equal subintervals
-- 5. We include the integrability hypothesis explicitly since Lean requires it

theorem problem_20_inequality {f : ℝ → ℝ} (hf : MonotoneOn f (Set.Ioo (0 : ℝ) 1)) 
    (hint : ∀ a b : ℝ, 0 ≤ a → b ≤ 1 → IntervalIntegrable f volume a b) (n : ℕ) (hn : n ≥ 1) :
    (∫ x in (0 : ℝ)..(1 - 1/(n : ℝ)), f x) ≤ 
    ((∑ k in Finset.Icc 1 (n-1), f (k/(n : ℝ))) / (n : ℝ)) ∧
    ((∑ k in Finset.Icc 1 (n-1), f (k/(n : ℝ))) / (n : ℝ)) ≤ ∫ x in (1/(n : ℝ))..(1 : ℝ), f x := by
  sorry

-- Proof attempt:
theorem problem_20_inequality {f : ℝ → ℝ} (hf : MonotoneOn f (Set.Ioo (0 : ℝ) 1)) 
    (hint : ∀ a b : ℝ, 0 ≤ a → b ≤ 1 → IntervalIntegrable f volume a b) (n : ℕ) (hn : n ≥ 1) :
    (∫ x in (0 : ℝ)..(1 - 1/(n : ℝ)), f x) ≤ 
    ((∑ k in Finset.Icc 1 (n-1), f (k/(n : ℝ))) / (n : ℝ)) ∧
    ((∑ k in Finset.Icc 1 (n-1), f (k/(n : ℝ))) / (n : ℝ)) ≤ ∫ x in (1/(n : ℝ))..(1 : ℝ), f x := by
  have n_pos : (n : ℝ) > 0 := by exact_mod_cast Nat.pos_of_ne_zero (Nat.not_eq_zero_of_lt hn)
  have hk : ∀ k ∈ Finset.Icc 1 (n-1), (k : ℝ)/n ∈ Set.Icc (1/n) (1 - 1/n) := by
    intro k hk
    simp at hk
    constructor
    · rw [div_le_iff n_pos]
      exact_mod_cast hk.1
    · rw [le_sub_iff_add_le', add_comm, ← le_sub_iff_add_le', one_div, div_le_iff n_pos]
      norm_cast
      exact hk.2
  
  -- Left inequality
  have left_ineq : (∫ x in (0 : ℝ)..(1 - 1/(n : ℝ)), f x) ≤ 
                  ((∑ k in Finset.Icc 1 (n-1), f (k/(n : ℝ))) / (n : ℝ)) := by
    let a := 0
    let b := 1 - 1/(n : ℝ)
    have hab : a ≤ b := by
      rw [sub_nonneg]
      exact one_div_le_one_of_le n_pos (by exact_mod_cast hn)
    
    rw [← sub_nonneg, ← integral_const (1/n), ← integral_sum]
    · apply integral_sub_le_integral_of_monotone_on hf
      · exact hint _ _ (le_refl _) hab
      · exact intervalIntegrable_const
      · intro x hx
        rw [Set.mem_Ioo] at hx
        have hx' : x ∈ Set.Ioo (0 : ℝ) 1 := ⟨hx.1, lt_of_lt_of_le hx.2 hab⟩
        refine ⟨hx.1, hx.2⟩
      · intro x hx
        rw [Set.mem_Ioo] at hx
        have k := Nat.floor (x * n)
        have hk1 : k ∈ Finset.Icc 1 (n-1) := by
          refine ⟨Nat.one_le_floor_of_one_le ?_, Nat.floor_le_of_le ?_⟩
          · rw [← div_le_iff n_pos]
            exact hx.1.le
          · rw [← le_sub_iff_add_le', add_comm, ← le_sub_iff_add_le', one_div]
            exact hx.2.le
        have hk2 : k/(n : ℝ) ≤ x ∧ x < (k + 1)/(n : ℝ) := by
          constructor
          · rw [div_le_iff n_pos]
            exact Nat.floor_le (x * n)
          · rw [lt_div_iff n_pos]
            exact Nat.lt_floor_add_one _
        exact hf ⟨hk2.1, hk2.2.trans_lt (by rw [div_lt_iff n_pos]; linarith)⟩ hx' (hk k hk1).2
    
    · simp [Finset.card_Icc, Nat.sub_zero]
      field_simp [n_pos]
      ring
  
  -- Right inequality
  have right_ineq : ((∑ k in Finset.Icc 1 (n-1), f (k/(n : ℝ))) / (n : ℝ)) ≤ 
                   ∫ x in (1/(n : ℝ))..(1 : ℝ), f x := by
    let a := 1/(n : ℝ)
    let b := 1
    have hab : a ≤ b := by
      apply one_div_le_one_of_le n_pos
      exact_mod_cast hn
    
    rw [← sub_nonneg, ← integral_sum, ← integral_const (1/n)]
    · apply integral_le_integral_sub_of_monotone_on hf
      · exact hint _ _ (le_refl _) hab
      · exact intervalIntegrable_const
      · intro x hx
        rw [Set.mem_Ioo] at hx
        have hx' : x ∈ Set.Ioo (0 : ℝ) 1 := ⟨hx.1.trans_lt (by positivity), hx.2⟩
        refine ⟨hx.1, hx.2⟩
      · intro x hx
        rw [Set.mem_Ioo] at hx
        have k := Nat.ceil (x * n) - 1
        have hk1 : k ∈ Finset.Icc 1 (n-1) := by
          refine ⟨Nat.one_le_floor_of_one_le ?_, Nat.floor_le_of_le ?_⟩
          · rw [← div_le_iff n_pos]
            exact hx.1.le
          · rw [← le_sub_iff_add_le', add_comm, ← le_sub_iff_add_le', one_div]
            exact hx.2.le
        have hk2 : k/(n : ℝ) < x ∧ x ≤ (k + 1)/(n : ℝ) := by
          constructor
          · rw [lt_div_iff n_pos]
            exact Nat.sub_one_lt_floor _
          · rw [div_le_iff n_pos]
            exact Nat.ceil_le _
        exact hf hx' ⟨hk2.1, hk2.2.trans_lt (by rw [div_lt_iff n_pos]; linarith)⟩ (hk k hk1).1
    
    · simp [Finset.card_Icc, Nat.sub_zero]
      field_simp [n_pos]
      ring
  
  exact ⟨left_ineq, right_ineq⟩