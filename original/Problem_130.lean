/-
Polya-Szego Problem 130
Part One, Chapter 3

Original problem:
We have

$$
\lim _{\varepsilon \rightarrow+0} \varepsilon \int_{0}^{\infty} e^{-\varepsilon t} f(t) d t=\lim _{t \rightarrow \infty} f(t)
$$

provided that the integral on the left and the limit on the right hand side exist.\\

Formalization notes: -- We formalize the statement: lim_{ε→0⁺} ε ∫₀^∞ e^{-εt} f(t) dt = lim_{t→∞} f(t)
-- under the assumptions that:
-- 1. f is measurable and locally integrable on [0, ∞)
-- 2. The limit L = lim_{t→∞} f(t) exists (finite)
-- 3. The integral ∫₀^∞ e^{-εt} f(t) dt converges for ε > 0
-- We use the following conventions:
-- - ε → 0⁺ is formalized as `Tendsto ε (𝓝[>] 0)`
-- - t → ∞ is formalized as `Tendsto f atTop (𝓝 L)`
-- - The integral is formalized using `intervalIntegral` over [0, ∞)
-/

import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Analysis.Calculus.ParametricIntegral

-- Formalization notes:
-- We formalize the statement: lim_{ε→0⁺} ε ∫₀^∞ e^{-εt} f(t) dt = lim_{t→∞} f(t)
-- under the assumptions that:
-- 1. f is measurable and locally integrable on [0, ∞)
-- 2. The limit L = lim_{t→∞} f(t) exists (finite)
-- 3. The integral ∫₀^∞ e^{-εt} f(t) dt converges for ε > 0
-- We use the following conventions:
-- - ε → 0⁺ is formalized as `Tendsto ε (𝓝[>] 0)`
-- - t → ∞ is formalized as `Tendsto f atTop (𝓝 L)`
-- - The integral is formalized using `intervalIntegral` over [0, ∞)

theorem problem_130 {f : ℝ → ℝ} (hf : Measurable f) (hint : ∀ ε > 0, IntegrableOn (fun t ↦ Real.exp (-ε * t) * f t) (Set.Ici 0))
    (hlim : ∃ L : ℝ, Tendsto f atTop (𝓝 L)) : 
    ∃ L : ℝ, 
      Tendsto f atTop (𝓝 L) ∧ 
      Tendsto (fun (ε : ℝ) ↦ ε * ∫ t in (0:ℝ)..∞, Real.exp (-ε * t) * f t) 
        (𝓝[>] (0 : ℝ)) (𝓝 L) := by
  sorry

-- Alternative formulation with stronger assumptions for clarity:
theorem problem_130_stronger {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Ici 0)) 
    (hint : ∀ ε > 0, IntegrableOn (fun t ↦ Real.exp (-ε * t) * f t) (Set.Ici 0))
    (hlim : ∃ L : ℝ, Tendsto f atTop (𝓝 L)) : 
    let L := Classical.choose hlim
    Tendsto (fun (ε : ℝ) ↦ ε * ∫ t in (0:ℝ)..∞, Real.exp (-ε * t) * f t) 
      (𝓝[>] (0 : ℝ)) (𝓝 L) := by
  sorry

-- Even more explicit version showing the equality of limits:
theorem problem_130_explicit {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Ici 0))
    (hint : ∀ ε > 0, IntegrableOn (fun t ↦ Real.exp (-ε * t) * f t) (Set.Ici 0))
    (L : ℝ) (hlim : Tendsto f atTop (𝓝 L)) :
    Tendsto (fun (ε : ℝ) ↦ ε * ∫ t in (0:ℝ)..∞, Real.exp (-ε * t) * f t) 
      (𝓝[>] (0 : ℝ)) (𝓝 L) := by
  sorry

-- Proof attempt:
theorem problem_130_explicit {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Ici 0))
    (hint : ∀ ε > 0, IntegrableOn (fun t ↦ Real.exp (-ε * t) * f t) (Set.Ici 0))
    (L : ℝ) (hlim : Tendsto f atTop (𝓝 L)) :
    Tendsto (fun (ε : ℝ) ↦ ε * ∫ t in (0:ℝ)..∞, Real.exp (-ε * t) * f t) 
      (𝓝[>] (0 : ℝ)) (𝓝 L) := by
  -- First prove the case when f is constant
  have const_case : ∀ c : ℝ, Tendsto (fun ε ↦ ε * ∫ t in (0:ℝ)..∞, Real.exp (-ε * t) * c) (𝓝[>] 0) (𝓝 c) := by
    intro c
    have : ∀ ε > 0, ∫ t in (0:ℝ)..∞, Real.exp (-ε * t) * c = c / ε := by
      intro ε hε
      have : HasDerivAt (fun t ↦ -Real.exp (-ε * t)/ε) (Real.exp (-ε * t)) := by
        simp; apply HasDerivAt.neg
        apply HasDerivAt.const_div
        · exact hε.ne'
        · simp [HasDerivAt.exp_neg, HasDerivAt.const_mul]
      have h_int := intervalIntegral.integral_eq_sub_of_hasDerivAt this (Continuous.continuousOn (by continuity))
      simp_rw [intervalIntegral.integral_of_le (le_refl 0)] at h_int
      have lim_at_infty : Tendsto (fun t ↦ -Real.exp (-ε * t)/ε) atTop (𝓝 0) := by
        simp; apply Tendsto.div_const
        apply Tendsto.neg; apply Tendsto.exp_neg_atTop_nhds_0
        exact (mul_pos hε (by linarith)).le
      simp [h_int, lim_at_infty]
    simp_rw [this]
    simp [mul_div_cancel' _ (fun h ↦ by linarith [show ε > 0 from h.out])]
    exact tendsto_id
  
  -- General case: subtract the constant function equal to L
  let g := fun t ↦ f t - L
  have hglim : Tendsto g atTop (𝓝 0) := by
    simp [g]; exact hlim.sub (tendsto_const_nhds)
  
  suffices : Tendsto (fun ε ↦ ε * ∫ t in (0:ℝ)..∞, Real.exp (-ε * t) * g t) (𝓝[>] 0) (𝓝 0)
  · have eq : ∀ ε > 0, ε * ∫ t in (0:ℝ)..∞, Real.exp (-ε * t) * f t = 
        ε * ∫ t in (0:ℝ)..∞, Real.exp (-ε * t) * L + ε * ∫ t in (0:ℝ)..∞, Real.exp (-ε * t) * g t := by
      intro ε hε
      rw [← mul_add, ← integral_add]
      · apply intervalIntegral.integral_congr_ae
        apply eventually_of_forall; intro t; simp [g, mul_add]
      · exact (hint ε hε).const_mul L
      · exact hint ε hε
    simp_rw [eq]
    refine Tendsto.add ?_ this
    convert const_case L; simp
  
  -- Now focus on proving the limit for g
  -- Choose δ > 0 such that for t ≥ δ, |g t| ≤ ε'
  intro s hs
  rw [Metric.tendsto_nhdsWithin_nhds] at hglim ⊢
  intro ε' hε'
  rcases Metric.tendsto_atTop_nhds.1 hglim ε' hε' with ⟨δ, hδ⟩
  use min 1 (ε' / (2 * (∫ t in (0:ℝ)..δ, |f t| + |L|) + 1))
  refine ⟨⟨by positivity, fun hε ↦ ?_⟩, fun ε hε ↦ ?_⟩
  · have : ε < ε' / (2 * (∫ t in (0:ℝ)..δ, |f t| + |L|) + 1) := by
      apply lt_of_lt_of_le hε.2
      apply min_le_right
    positivity
  · have hεδ : ε > 0 ∧ δ > 0 := ⟨hε.1, by linarith [min_le_left 1 _ ▸ hε.2]⟩
    have hgδ : ∀ t ≥ δ, |g t| ≤ ε' := by
      intro t ht; exact (hδ t ht).le
    have split_integral : ∫ t in (0:ℝ)..∞, Real.exp (-ε * t) * g t = 
        ∫ t in (0:ℝ)..δ, Real.exp (-ε * t) * g t + ∫ t in δ..∞, Real.exp (-ε * t) * g t := by
      rw [← integral_union (by simp [δ]) (hint ε hε.1).norm.integrableOn]
      congr 1
      simp [Set.Ioc_union_Ici_eq_Ici (le_refl δ)]
    
    rw [split_integral, mul_add]
    refine lt_of_le_of_lt (abs_add _ _) (add_lt_add ?_ ?_)
    · -- First term: integral from 0 to δ
      have : |ε * ∫ t in (0:ℝ)..δ, Real.exp (-ε * t) * g t| ≤ 
          ε * ∫ t in (0:ℝ)..δ, Real.exp (-ε * t) * (|f t| + |L|) := by
        apply mul_le_mul_of_nonneg_left _ hε.1.le
        apply intervalIntegral.abs_integral_le_integral_abs
        apply ContinuousOn.aestronglyMeasurable
        · apply Continuous.continuousOn
          apply Continuous.mul
          · apply Continuous.exp; continuity
          · exact hf.sub continuousOn_const
        · rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le hεδ.2.le]
          apply (hint ε hε.1).mono_set (by simp)
      refine lt_of_le_of_lt this ?_
      have : Real.exp (-ε * t) ≤ 1 := by
        apply Real.exp_le_one_of_nonpos
        apply neg_nonpos.mpr; exact mul_nonneg hε.1.le (by linarith)
      have : ∫ t in (0:ℝ)..δ, Real.exp (-ε * t) * (|f t| + |L|) ≤ 
          ∫ t in (0:ℝ)..δ, |f t| + |L| := by
        apply integral_mono
        · apply (hint ε hε.1).norm.mono_set (by simp)
        · apply Continuous.integrableOn_Icc; continuity
        · intro t ht; simp at ht
          apply mul_le_of_le_one_left _ this
          exact add_nonneg (abs_nonneg _) (abs_nonneg _)
      linarith [hε.2]
    
    · -- Second term: integral from δ to ∞
      have : |ε * ∫ t in δ..∞, Real.exp (-ε * t) * g t| ≤ ε * ∫ t in δ..∞, Real.exp (-ε * t) * ε' := by
        apply mul_le_mul_of_nonneg_left _ hε.1.le
        apply intervalIntegral.abs_integral_le_integral_abs
        apply ContinuousOn.aestronglyMeasurable
        · apply Continuous.continuousOn
          apply Continuous.mul
          · apply Continuous.exp; continuity
          · exact hf.sub continuousOn_const
        · rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)]
          apply (hint ε hε.1).mono_set (by simp)
        · intro t ht; simp at ht ⊢
          rw [abs_mul, mul_comm]
          apply mul_le_mul_of_nonneg_left (hgδ t ht.1) (abs_nonneg _)
      refine lt_of_le_of_lt this ?_
      have : ∫ t in δ..∞, Real.exp (-ε * t) = 1/ε * Real.exp (-ε * δ) := by
        have := intervalIntegral.integral_exp_neg_Ioi δ hε.1.le
        simp [this]
      rw [integral_mul_right, this]
      simp [mul_comm ε, mul_assoc, mul_comm ε']
      apply mul_lt_mul_of_pos_left hε' (Real.exp_pos _)