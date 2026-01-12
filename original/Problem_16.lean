/-
Polya-Szego Problem 16
Part Three, Chapter 1

Original problem:
A polynomial of the form

$$
z^{n}-p_{1} z^{n-1}-p_{2} z^{n-2}-\cdots-p_{n-1} z-p_{n},
$$

where $p_{1} \geqq 0, p_{2} \geqq 0, \ldots, p_{n} \geqq 0, p_{1}+p_{2}+\cdots+p_{n}>0$, has just one positive zero.\\

Formalization notes: -- We formalize the statement about polynomials with nonnegative coefficients having exactly one positive root.
-- The polynomial is: z^n - p₁z^(n-1) - p₂z^(n-2) - ... - pₙ
-- Conditions: pᵢ ≥ 0 for all i, and ∑ pᵢ > 0
-- Conclusion: The polynomial has exactly one positive real root.
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic
import Mathlib.Data.Polynomial.Basic
import Mathlib.Data.Polynomial.Degree
import Mathlib.Data.Polynomial.Eval

-- Formalization notes:
-- We formalize the statement about polynomials with nonnegative coefficients having exactly one positive root.
-- The polynomial is: z^n - p₁z^(n-1) - p₂z^(n-2) - ... - pₙ
-- Conditions: pᵢ ≥ 0 for all i, and ∑ pᵢ > 0
-- Conclusion: The polynomial has exactly one positive real root.

theorem problem_16 (n : ℕ) (p : ℕ → ℝ) (hp_nonneg : ∀ i, 1 ≤ i → i ≤ n → p i ≥ 0) 
    (hp_sum_pos : ∑ i in Finset.Icc 1 n, p i > 0) :
    ∃! (ζ : ℝ), ζ > 0 ∧ 
      (∑ k : ℕ in Finset.range (n + 1), 
        ((Polynomial.monomial (n : ℕ) (1 : ℝ)) - 
          ∑ i in Finset.Icc 1 n, Polynomial.monomial (n - i) (p i))).eval ζ = 0 := by
  sorry

-- Proof attempt:
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic
import Mathlib.Data.Polynomial.Basic
import Mathlib.Data.Polynomial.Degree
import Mathlib.Data.Polynomial.Eval

theorem problem_16 (n : ℕ) (p : ℕ → ℝ) (hp_nonneg : ∀ i, 1 ≤ i → i ≤ n → p i ≥ 0) 
    (hp_sum_pos : ∑ i in Finset.Icc 1 n, p i > 0) :
    ∃! (ζ : ℝ), ζ > 0 ∧ 
      (∑ k : ℕ in Finset.range (n + 1), 
        ((Polynomial.monomial (n : ℕ) (1 : ℝ)) - 
          ∑ i in Finset.Icc 1 n, Polynomial.monomial (n - i) (p i))).eval ζ = 0 := by
  let f : ℝ → ℝ := fun z ↦ 1 - ∑ i in Finset.Icc 1 n, p i * z^(-i)
  let poly := (Polynomial.monomial n 1) - ∑ i in Finset.Icc 1 n, Polynomial.monomial (n - i) (p i)
  
  have hf_eq : ∀ z > 0, poly.eval z = z^n * f z := by
    intro z hz
    simp [Polynomial.eval_sub, Polynomial.eval_monomial, Polynomial.eval_finset_sum]
    rw [← mul_sum]
    simp_rw [Polynomial.eval_monomial]
    simp only [Nat.cast_id]
    have : ∀ i ∈ Finset.Icc 1 n, z ^ (n - i) = z ^ n * z ^ (-i) := by
      intro i hi
      rw [← zpow_nat_cast, ← zpow_nat_cast, ← zpow_nat_cast, ← zpow_add₀ (ne_of_gt hz)]
      simp [Nat.sub_add_cancel (Finset.mem_Icc.mp hi).2]
    simp_rw [this]
    ring_nf
    rw [mul_sub, mul_one]
  
  have hf_cont : ∀ {z}, z > 0 → ContinuousAt f z := by
    intro z hz
    refine ContinuousAt.sub ?_ ?_
    · exact continuousAt_const
    · apply ContinuousAt.finset_sum (Finset.Icc 1 n)
      intro i hi
      refine ContinuousAt.mul ?_ ?_
      · exact continuousAt_const
      · exact continuousAt_zpow (-i) (Or.inr (ne_of_gt hz))
  
  have hf_lim0 : Tendsto f atTop (𝓝 1) := by
    refine Tendsto.sub tendsto_const_nhds ?_
    simp only [sub_self]
    apply Tendsto.congr' _ (tendsto_finset_sum _ fun i hi ↦ tendsto_const_nhds.mul (tendsto_zpow_atTop_zero (by linarith [Finset.mem_Icc.mp hi].1)))
    apply eventually_atTop.2
    refine ⟨1, fun z hz ↦ ?_⟩
    congr
    ext i
    simp [zpow_neg, inv_zpow (le_of_lt hz)]
  
  have hf_lim_infty : Tendsto f (𝓝[>] 0) (𝓝 (-∞)) := by
    refine Tendsto.sub tendsto_const_nhds ?_
    simp only [sub_zero]
    have : Tendsto (fun z ↦ ∑ i in Finset.Icc 1 n, p i * z ^ (-i)) (𝓝[>] 0) atTop := by
      apply Tendsto.congr' _ (tendsto_finset_sum _ fun i hi ↦ 
        Tendsto.const_mul_atTop (hp_nonneg i (Finset.mem_Icc.mp hi).1 (Finset.mem_Icc.mp hi).2) 
        (tendsto_zpow_neg_atTop (Finset.mem_Icc.mp hi).1)))
      filter_upwards [self_mem_nhdsWithin] with z hz
      congr
      ext i
      simp [zpow_neg, inv_zpow (le_of_lt hz)]
    simpa using this
  
  have hf_mono : StrictMonoOn f (Set.Ioi 0) := by
    apply StrictMonoOn.sub_const
    refine strictMonoOn_finset_sum (Finset.Icc 1 n) fun i hi ↦ ?_
    refine StrictMonoOn.const_mul (hp_nonneg i (Finset.mem_Icc.mp hi).1 (Finset.mem_Icc.mp hi).2) ?_
    refine strictMonoOn_zpow_neg (Finset.mem_Icc.mp hi).1
  
  obtain ⟨ζ, hζ_pos, hζ_root⟩ := IntermediateValue_Ioo (by linarith) 
    (hf_lim_infty.mono_left nhdsWithin_le_nhds) hf_lim0 
    (show ∃ x y, x ∈ Set.Ioi 0 ∧ y ∈ Set.Ioi 0 ∧ x < y ∧ f x < f y from 
      ⟨1, 2, by norm_num, by norm_num, by norm_num, hf_mono (by norm_num) (by norm_num) (by norm_num)⟩)
  
  refine ⟨ζ, hζ_pos, ?_, fun ζ' hζ' hζ'_root ↦ ?_⟩
  · rw [hf_eq ζ hζ_pos, mul_eq_zero]
    right
    exact hζ_root
  
  · have hζ'_eq := congr_arg (· * ζ' ^ n) hζ'_root
    simp [hf_eq ζ' hζ'.1] at hζ'_eq
    have := hf_mono.eq_iff_eq (Set.mem_Ioi.mpr hζ_pos) (Set.mem_Ioi.mpr hζ'.1)
    rw [← hζ_root, hζ'_eq] at this
    exact this.1