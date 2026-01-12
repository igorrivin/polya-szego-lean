/-
Polya-Szego Problem 106
Part One, Chapter 3

Original problem:
A convergent sequence has either a maximum or a minimum or both.

The following propositions show that even the most extravagant sequences behave occasionally like good mannered sequences, i.e. they show some feature of monotone sequences.\\

Formalization notes: -- We formalize the key part of Problem 106 from Polya-Szego:
-- For a continuous function f on [0, 2π] and any positive integer n,
-- the integral ∫₀²π f(x)|sin n x| dx can be expressed as a sum
-- where each term involves an intermediate value f_{νn} of f on
-- subintervals [(ν-1)(2π/n), ν(2π/n)], multiplied by the integral of |sin n x|
-- over that subinterval.
-- This captures the essence of Fejér's method from the citation.
-/

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral

-- Formalization notes:
-- We formalize the key part of Problem 106 from Polya-Szego:
-- For a continuous function f on [0, 2π] and any positive integer n,
-- the integral ∫₀²π f(x)|sin n x| dx can be expressed as a sum
-- where each term involves an intermediate value f_{νn} of f on
-- subintervals [(ν-1)(2π/n), ν(2π/n)], multiplied by the integral of |sin n x|
-- over that subinterval.
-- This captures the essence of Fejér's method from the citation.

theorem problem_106_feier_integral_decomposition (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc (0 : ℝ) (2 * π))) 
    (n : ℕ) (hn : n > 0) :
    ∃ (f_val : ℕ → ℝ), ∀ (ν : ℕ), ν ∈ Finset.Icc 1 n → 
    let a := (ν - 1 : ℝ) * (2 * π) / n
    let b := (ν : ℝ) * (2 * π) / n
    f_val ν ∈ Set.Icc (sInf (f '' Set.Icc a b)) (sSup (f '' Set.Icc a b)) ∧
    ∫ x in (0:ℝ)..(2 * π), f x * |Real.sin (n * x)| = 
      ∑ ν in Finset.Icc 1 n, 
        f_val ν * ∫ x in a..b, |Real.sin (n * x)| := by
  sorry

-- Proof attempt:
theorem problem_106_feier_integral_decomposition (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc (0 : ℝ) (2 * π))) 
    (n : ℕ) (hn : n > 0) :
    ∃ (f_val : ℕ → ℝ), ∀ (ν : ℕ), ν ∈ Finset.Icc 1 n → 
    let a := (ν - 1 : ℝ) * (2 * π) / n
    let b := (ν : ℝ) * (2 * π) / n
    f_val ν ∈ Set.Icc (sInf (f '' Set.Icc a b)) (sSup (f '' Set.Icc a b)) ∧
    ∫ x in (0:ℝ)..(2 * π), f x * |Real.sin (n * x)| = 
      ∑ ν in Finset.Icc 1 n, 
        f_val ν * ∫ x in a..b, |Real.sin (n * x)| := by
  -- First, split the integral into n subintervals
  have h_split : ∫ x in (0:ℝ)..(2 * π), f x * |Real.sin (n * x)| = 
      ∑ ν in Finset.Icc 1 n, ∫ x in ((ν - 1 : ℝ) * (2 * π) / n)..(ν * (2 * π) / n), f x * |Real.sin (n * x)| := by
    have h_partition : ∀ x ∈ Set.Icc 0 (2 * π), x ∈ ⋃ ν ∈ Finset.Icc 1 n, Set.Icc ((ν - 1) * (2 * π) / n) (ν * (2 * π) / n) := by
      intro x hx
      simp only [Finset.mem_Icc, Set.mem_iUnion]
      obtain ⟨ν, hν⟩ := exists_nat_mul_le_of_le hn (le_refl n) (by linarith [hx.1, hx.2]) 
      use ν
      have hν' : ν ∈ Finset.Icc 1 n := by
        simp [Finset.mem_Icc]
        refine ⟨Nat.one_le_of_lt hn, hν.1⟩
      refine ⟨hν', ?_⟩
      simp [Set.mem_Icc]
      constructor
      · apply div_le_of_nonneg_of_le_mul (by positivity) hx.1
        rw [mul_comm]
        exact Nat.cast_le.2 hν.1
      · apply le_div_of_nonneg_of_mul_le (by positivity) hx.2
        rw [mul_comm]
        exact Nat.cast_le.2 hν.1
    refine intervalIntegral.integral_eq_sum_of_partition ?_ h_partition
    exact ContinuousOn.mul hf (Continuous.continuousOn (Continuous.abs (Real.continuous_sin.comp (continuous_const.mul continuous_id))))
  
  -- For each subinterval, apply the mean value theorem for integrals
  choose f_val hf_val using fun ν (hν : ν ∈ Finset.Icc 1 n) => by
    let a := (ν - 1 : ℝ) * (2 * π) / n
    let b := (ν : ℝ) * (2 * π) / n
    have h_ab : a ≤ b := by
      simp only [a, b]
      apply div_le_div_of_nonneg_right (by nlinarith) (by positivity)
    have h_cont : ContinuousOn f (Set.Icc a b) := by
      refine ContinuousOn.mono hf ?_
      refine Set.Icc_subset_Icc ?_ ?_
      · simp [a]
        apply div_nonneg
        · apply mul_nonneg
          · simp; linarith [Finset.mem_Icc.1 hν].1
          · norm_num
        · positivity
      · simp [b]
        apply div_le_of_nonneg_of_le_mul (by positivity)
        · exact mul_le_mul_of_nonneg_left (by linarith [Finset.mem_Icc.1 hν].2) (by norm_num)
    have h_integrable : IntervalIntegrable (fun x => |Real.sin (n * x)|) volume a b := by
      apply Continuous.intervalIntegrable
      exact Continuous.abs (Real.continuous_sin.comp (continuous_const.mul continuous_id))
    obtain ⟨ξ, hξ⟩ := ContinuousOn.exists_integral_eq_mul (hf := h_cont) (hg := fun x => |Real.sin (n * x)|)
      (hg_cont := Continuous.continuousOn (Continuous.abs (Real.continuous_sin.comp (continuous_const.mul continuous_id))))
      (hg_nonneg := fun x _ => abs_nonneg _) h_integrable
    refine ⟨ξ, ?_⟩
    exact ⟨hξ.1, hξ.2⟩

  -- Combine the results
  refine ⟨f_val, fun ν hν => ?_⟩
  let a := (ν - 1 : ℝ) * (2 * π) / n
  let b := (ν : ℝ) * (2 * π) / n
  refine ⟨(hf_val ν hν).1, ?_⟩
  rw [h_split]
  congr 1
  apply Finset.sum_congr rfl
  intro μ hμ
  rw [(hf_val μ hμ).2]
  ring