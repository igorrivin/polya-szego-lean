/-
Polya-Szego Problem 83
Part One, Chapter 2

Original problem:
Assume that the function $f(x)$, defined on $\left[x_{1}, x_{2}\right]$ is properly integrable and that it has a positive lower bound. The function

$$
\psi(t)=\left(\frac{1}{x_{2}-x_{1}} \int_{x_{1}}^{x_{2}}[f(x)]^{t} d x\right)^{\frac{1}{t}}
$$

is non-decreasing for all $t$. Compute

$$
\psi(-\infty), \quad \psi(-1), \quad \psi(0), \quad \psi(1), \quad \psi(+\infty) .
$$

For $\psi(0)$ see 82. In computing $\psi(-\infty)$ and $\psi(\infty)$ assume that $f(x)$ is continuous.\\

Formalization notes: -- 1. We formalize the monotonicity property of ψ(t)
-- 2. We compute the limits at t → -∞, t → -1, t → 0, t → 1, and t → ∞
-- 3. For ψ(0), we use the limit as t → 0 (geometric mean)
-- 4. For ψ(±∞), we assume f is continuous to get min/max
-- 5. We work with ℝ≥0-valued f since it has positive lower bound
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Analysis.Calculus.MeanInequalities

-- Formalization notes:
-- 1. We formalize the monotonicity property of ψ(t)
-- 2. We compute the limits at t → -∞, t → -1, t → 0, t → 1, and t → ∞
-- 3. For ψ(0), we use the limit as t → 0 (geometric mean)
-- 4. For ψ(±∞), we assume f is continuous to get min/max
-- 5. We work with ℝ≥0-valued f since it has positive lower bound

open Real
open Set
open Filter
open scoped Topology

variable {x₁ x₂ : ℝ} (hlt : x₁ < x₂)

theorem problem_83_part1 {f : ℝ → ℝ≥0} (hf_int : IntervalIntegrable f volume x₁ x₂)
    (h_lower_bound : ∃ c > 0, ∀ x ∈ Set.Icc x₁ x₂, c ≤ f x) :
    let ψ : ℝ → ℝ := fun t => 
      if t = 0 then Real.exp ((1 / (x₂ - x₁)) * ∫ x in x₁..x₂, Real.log (f x : ℝ))
      else (((x₂ - x₁)⁻¹ * ∫ x in x₁..x₂, (f x : ℝ) ^ t) ^ (t⁻¹ : ℝ))
    in MonotoneOn ψ (Set.univ : Set ℝ) := by
  sorry

theorem problem_83_limits {f : ℝ → ℝ≥0} (hf_cont : ContinuousOn f (Set.Icc x₁ x₂))
    (hf_int : IntervalIntegrable f volume x₁ x₂) 
    (h_lower_bound : ∃ c > 0, ∀ x ∈ Set.Icc x₁ x₂, c ≤ f x) :
    let ψ : ℝ → ℝ := fun t => 
      if t = 0 then Real.exp ((1 / (x₂ - x₁)) * ∫ x in x₁..x₂, Real.log (f x : ℝ))
      else (((x₂ - x₁)⁻¹ * ∫ x in x₁..x₂, (f x : ℝ) ^ t) ^ (t⁻¹ : ℝ))
    in
    have hlt' : x₂ - x₁ > 0 := by linarith
    have h_min_max : ∃ xmin xmax, xmin ∈ Set.Icc x₁ x₂ ∧ xmax ∈ Set.Icc x₁ x₂ ∧
      (∀ x ∈ Set.Icc x₁ x₂, f xmin ≤ f x) ∧ (∀ x ∈ Set.Icc x₁ x₂, f x ≤ f xmax) := by
      exact IsCompact.exists_isMinOn_isMaxOn (isCompact_Icc) (hf_cont.mono isClosed_Icc.subset_continuousOn)
        ⟨x₁, left_mem_Icc.mpr (le_refl _)⟩ ⟨x₂, right_mem_Icc.mpr (le_refl _)⟩
    rcases h_min_max with ⟨xmin, xmax, hxmin, hxmax, hmin, hmax⟩
    have hpos : 0 < f xmin := by
      rcases h_lower_bound with ⟨c, hc_pos, hc⟩
      exact lt_of_lt_of_eq hc_pos (by simpa using hc xmin hxmin)
    have ψ_neg_infty : Tendsto ψ atBot (𝓝 (f xmin : ℝ)) := by
      -- ψ(-∞) = min f(x)
      sorry
    have ψ_neg_one : ψ (-1) = ((x₂ - x₁)⁻¹ * ∫ x in x₁..x₂, (f x : ℝ)⁻¹)⁻¹ := by
      -- ψ(-1) = harmonic mean
      simp [ψ, show (-1 : ℝ)⁻¹ = -1 by norm_num]
    have ψ_zero : ψ 0 = Real.exp ((1 / (x₂ - x₁)) * ∫ x in x₁..x₂, Real.log (f x : ℝ)) := by
      -- ψ(0) = geometric mean (limit as t→0)
      simp [ψ]
    have ψ_one : ψ 1 = (x₂ - x₁)⁻¹ * ∫ x in x₁..x₂, f x := by
      -- ψ(1) = arithmetic mean
      simp [ψ, show (1 : ℝ)⁻¹ = 1 by norm_num]
    have ψ_infty : Tendsto ψ atTop (𝓝 (f xmax : ℝ)) := by
      -- ψ(∞) = max f(x)
      sorry
    ⟨ψ_neg_infty, ψ_neg_one, ψ_zero, ψ_one, ψ_infty⟩

-- Proof attempt:
theorem problem_83_part1 {f : ℝ → ℝ≥0} (hf_int : IntervalIntegrable f volume x₁ x₂)
    (h_lower_bound : ∃ c > 0, ∀ x ∈ Set.Icc x₁ x₂, c ≤ f x) :
    let ψ : ℝ → ℝ := fun t => 
      if t = 0 then Real.exp ((1 / (x₂ - x₁)) * ∫ x in x₁..x₂, Real.log (f x : ℝ))
      else (((x₂ - x₁)⁻¹ * ∫ x in x₁..x₂, (f x : ℝ) ^ t) ^ (t⁻¹ : ℝ))
    in MonotoneOn ψ (Set.univ : Set ℝ) := by
  intro t s hts htu hsu
  have hlt' : x₂ - x₁ > 0 := by linarith
  rcases h_lower_bound with ⟨c, hc_pos, hc⟩
  have hf_pos : ∀ x ∈ Icc x₁ x₂, 0 < (f x : ℝ) := fun x hx => 
    lt_of_lt_of_eq hc_pos (by simpa using hc x hx)
  
  by_cases ht0 : t = 0
  · -- Case when t = 0 (geometric mean)
    simp [ψ, ht0]
    have hs0 : s = 0 ∨ s ≠ 0 := by exact eq_or_ne s 0
    cases hs0 with
    | inl hs0 => simp [hs0]
    | inr hs0 =>
      simp [ψ, hs0]
      have hs_pos : 0 < s := by linarith [hts]
      apply Real.exp_monotone
      rw [← Real.log_rpow (by positivity)]
      apply le_trans _ (holder_mean_log_le hlt' hf_int hf_pos hs_pos)
      simp [holder_mean, ψ, hs0, hs_pos]
  
  · -- Case when t ≠ 0
    simp [ψ, ht0]
    by_cases hs0 : s = 0
    · -- Case when s = 0 (geometric mean)
      simp [ψ, hs0]
      have ht_pos : t < 0 ∨ 0 < t := by exact Ne.lt_or_lt ht0
      cases ht_pos with
      | inl ht_neg =>
        apply Real.exp_monotone
        rw [← Real.log_rpow (by positivity)]
        apply le_trans (holder_mean_log_le hlt' hf_int hf_pos (by linarith [ht_neg]))
        simp [holder_mean, ψ, hs0]
      | inr ht_pos =>
        apply Real.exp_monotone
        rw [← Real.log_rpow (by positivity)]
        apply le_trans (holder_mean_log_le hlt' hf_int hf_pos ht_pos)
        simp [holder_mean, ψ, hs0]
    
    · -- Case when s ≠ 0
      simp [ψ, hs0]
      have ht_pos : t < 0 ∨ 0 < t := by exact Ne.lt_or_lt ht0
      have hs_pos : s < 0 ∨ 0 < s := by exact Ne.lt_or_lt hs0
      cases ht_pos with
      | inl ht_neg =>
        cases hs_pos with
        | inl hs_neg =>
          -- Both negative case
          have := holder_mean_monotone hlt' hf_int hf_pos hs_neg ht_neg hts
          simp [holder_mean] at this
          exact this
        | inr hs_pos =>
          -- Negative to positive case
          have := holder_mean_monotone hlt' hf_int hf_pos hs_pos ht_neg (by linarith)
          simp [holder_mean] at this
          exact this
      | inr ht_pos =>
        cases hs_pos with
        | inl hs_neg =>
          -- Positive to negative case (shouldn't happen by hts)
          linarith
        | inr hs_pos =>
          -- Both positive case
          have := holder_mean_monotone hlt' hf_int hf_pos hs_pos ht_pos hts
          simp [holder_mean] at this
          exact this