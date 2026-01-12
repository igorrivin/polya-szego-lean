/-
Polya-Szego Problem *226
Part One, Chapter 5

Original problem:
Add to the assumptions of $\mathbf{2 2 3}$ that $f(x, y)>0$. Then

$$
\lim _{n \rightarrow \infty}\left[\int_{a}^{a^{\prime}}\left(\int_{b}^{b^{\prime}}[f(x, y)]^{n} d y\right)^{-1} d x\right]^{-\frac{1}{n}}=\min _{x} \max _{y} f(x, y)
$$

Formalization notes: -- We formalize the limit statement from Polya-Szego Problem 226.
-- Assumptions:
-- 1. f : ℝ × ℝ → ℝ is continuous on [a, a'] × [b, b']
-- 2. f(x, y) > 0 everywhere on this rectangle
-- 3. The integrals are Riemann integrals over intervals
-- The theorem states that the limit equals min_{x ∈ [a,a']} max_{y ∈ [b,b']} f(x, y)
-/

import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.Bochner
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

-- Formalization notes:
-- We formalize the limit statement from Polya-Szego Problem 226.
-- Assumptions:
-- 1. f : ℝ × ℝ → ℝ is continuous on [a, a'] × [b, b']
-- 2. f(x, y) > 0 everywhere on this rectangle
-- 3. The integrals are Riemann integrals over intervals
-- The theorem states that the limit equals min_{x ∈ [a,a']} max_{y ∈ [b,b']} f(x, y)

theorem problem_226 {a a' b b' : ℝ} (ha : a ≤ a') (hb : b ≤ b') 
    (f : ℝ × ℝ → ℝ) (hf_cont : ContinuousOn f (Set.uIcc (a, b) (a', b'))) 
    (hf_pos : ∀ (x : ℝ) (y : ℝ), x ∈ Set.Icc a a' → y ∈ Set.Icc b b' → f (x, y) > 0) :
    Filter.Tendsto (λ (n : ℕ) => 
      (∫ x in a..a', ((∫ y in b..b', (f (x, y)) ^ n) : ℝ)⁻¹) ^ (-(n : ℝ)⁻¹))
      Filter.atTop (𝓝 (⨅ x ∈ Set.Icc a a', ⨆ y ∈ Set.Icc b b', f (x, y))) := by
  sorry

-- Proof attempt:
theorem problem_226 {a a' b b' : ℝ} (ha : a ≤ a') (hb : b ≤ b') 
    (f : ℝ × ℝ → ℝ) (hf_cont : ContinuousOn f (Set.uIcc (a, b) (a', b'))) 
    (hf_pos : ∀ (x : ℝ) (y : ℝ), x ∈ Set.Icc a a' → y ∈ Set.Icc b b' → f (x, y) > 0) :
    Filter.Tendsto (λ (n : ℕ) => 
      (∫ x in a..a', ((∫ y in b..b', (f (x, y)) ^ n) : ℝ)⁻¹) ^ (-(n : ℝ)⁻¹))
      Filter.atTop (𝓝 (⨅ x ∈ Set.Icc a a', ⨆ y ∈ Set.Icc b b', f (x, y))) := by
  let φ (x : ℝ) := ⨆ y ∈ Set.Icc b b', f (x, y)
  have hφ_cont : ContinuousOn φ (Set.Icc a a') := by
    apply ContinuousOn.sup_supr
    · intro x hx
      have : Set.Icc b b' = Set.uIcc b b' := Set.uIcc_of_le hb
      rw [this]
      exact (hf_cont.comp continuousOn_id.prod continuousOn_const).continuousOn_snd hx
    · intro x hx y hy
      exact hf_pos x y hx hy
  have hφ_pos : ∀ x ∈ Set.Icc a a', φ x > 0 := by
    intro x hx
    obtain ⟨y, hy⟩ := (isCompact_Icc (b := b')).exists_isMaxOn (Set.nonempty_Icc.mpr hb) 
      (ContinuousOn.mono (hf_cont.comp continuousOn_id.prod continuousOn_const) 
        (by simp [Set.prod_subset_iff]) (x, ·) hx).continuousOn
    exact hf_pos x y hx hy.1
  
  -- Main proof steps
  have key : ∀ x ∈ Set.Icc a a', Filter.Tendsto (λ n => (∫ y in b..b', (f (x, y))^n) ^ (-(n : ℝ)⁻¹)) 
      Filter.atTop (𝓝 (φ x)) := by
    intro x hx
    have h_cont : ContinuousOn (f x) (Set.Icc b b') := by
      exact ContinuousOn.comp hf_cont continuousOn_const.prod continuousOn_id (by simp [hx.1, hx.2])
    have h_pos : ∀ y ∈ Set.Icc b b', f (x, y) > 0 := fun y hy => hf_pos x y hx hy
    convert tendsto_integral_pow_essSup_inv (μ := volume.restrict (Set.Icc b b')) 
      (hf := h_cont.aemeasurable) (h_pos := fun y hy => h_pos y hy) using 1
    · simp only [intervalIntegral.integral_of_le hb, Measure.restrict_apply measurableSet_Icc, 
        Set.univ_inter, volume_Icc]
    · simp [φ, essSup_eq_sSup_ae (h_cont.aemeasurable), sSup_eq_iSup, 
        Measure.ae_restrict_eq volume measurableSet_Icc, eventually_principal]
  
  let I (n : ℕ) := (∫ x in a..a', ((∫ y in b..b', (f (x, y))^n))⁻¹) ^ (-(n : ℝ)⁻¹)
  suffices : Filter.Tendsto (λ n => (∫ x in a..a', (φ x)^(-n)) ^ (-(n : ℝ)⁻¹)) Filter.atTop 
      (𝓝 (⨅ x ∈ Set.Icc a a', φ x))
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le ?_ this ?_ ?_
    · refine eventually_of_forall (fun n => ?_)
      refine Real.rpow_le_rpow_of_nonpos (by positivity) (intervalIntegral.integral_le_integral 
        (fun x hx => ?_) (by norm_num; linarith [(@one_le_nat_cast ℝ _ n).mpr n.one_le_two])) 
        (by norm_num; linarith [(@one_le_nat_cast ℝ _ n).mpr n.one_le_two])
      refine inv_le_inv_of_le (by positivity) ?_
      exact integral_pow_le_sup_pow (μ := volume.restrict (Set.Icc b b')) 
        (hf := (hf_cont.comp continuousOn_const.prod continuousOn_id).continuousOn_snd hx) 
        (fun y hy => hf_pos x y hx hy)
    · refine eventually_of_forall (fun n => ?_)
      refine Real.rpow_le_rpow_of_nonpos (by positivity) (intervalIntegral.integral_le_integral 
        (fun x hx => ?_) (by norm_num; linarith [(@one_le_nat_cast ℝ _ n).mpr n.one_le_two])) 
        (by norm_num; linarith [(@one_le_nat_cast ℝ _ n).mpr n.one_le_two])
      refine inv_le_inv_of_le (by positivity) ?_
      exact integral_pow_le_sup_pow (μ := volume.restrict (Set.Icc b b')) 
        (hf := (hf_cont.comp continuousOn_const.prod continuousOn_id).continuousOn_snd hx) 
        (fun y hy => hf_pos x y hx hy)
  
  -- Final step using the key lemma
  convert tendsto_integral_pow_essInf_inv (μ := volume.restrict (Set.Icc a a')) 
    (hf := hφ_cont.aemeasurable) (h_pos := fun x hx => hφ_pos x hx) using 1
  · simp only [intervalIntegral.integral_of_le ha, Measure.restrict_apply measurableSet_Icc, 
      Set.univ_inter, volume_Icc]
  · simp [essInf_eq_sInf_ae (hφ_cont.aemeasurable), sInf_eq_iInf, 
      Measure.ae_restrict_eq volume measurableSet_Icc, eventually_principal]