/-
Polya-Szego Problem 131
Part One, Chapter 3

Original problem:
If the integral

$$
\int_{0}^{\infty} t^{\lambda} f(t) d t
$$

converges for $\lambda=\alpha$ and for $\lambda=\beta, \alpha<\beta$, it converges for $\alpha \leqq \lambda \leqq \beta$ and it represents a continuous function of $\lambda$ on that interval.\\

Formalization notes: -- We formalize the statement about convergence and continuity of the parametric integral.
-- We assume f is measurable and locally integrable on [0, ∞).
-- The integral ∫₀^∞ t^λ f(t) dt is interpreted as the improper integral lim_{b→∞} ∫₀^b t^λ f(t) dt.
-- We use `ContinuousOn` to express continuity on the closed interval [α, β].
-/

import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Integral

-- Formalization notes:
-- We formalize the statement about convergence and continuity of the parametric integral.
-- We assume f is measurable and locally integrable on [0, ∞).
-- The integral ∫₀^∞ t^λ f(t) dt is interpreted as the improper integral lim_{b→∞} ∫₀^b t^λ f(t) dt.
-- We use `ContinuousOn` to express continuity on the closed interval [α, β].

theorem problem_131 {α β : ℝ} (hαβ : α < β) {f : ℝ → ℝ}
    (hf : Measurable f) (hfi : ∀ x ≥ 0, IntegrableOn f (Set.Icc 0 x))
    (hconv_α : ∃ I_α : ℝ, Tendsto (λ b : ℝ => ∫ t in (0:ℝ)..b, (t : ℝ)^α * f t) atTop (𝓝 I_α))
    (hconv_β : ∃ I_β : ℝ, Tendsto (λ b : ℝ => ∫ t in (0:ℝ)..b, (t : ℝ)^β * f t) atTop (𝓝 I_β)) :
    -- The integral converges for all λ in [α, β]
    (∀ λ ∈ Set.Icc (α : ℝ) β, ∃ I : ℝ, 
        Tendsto (λ b : ℝ => ∫ t in (0:ℝ)..b, (t : ℝ)^λ * f t) atTop (𝓝 I)) ∧
    -- The function F(λ) = ∫₀^∞ t^λ f(t) dt is continuous on [α, β]
    (∃ F : ℝ → ℝ, 
        (∀ λ ∈ Set.Icc (α : ℝ) β, 
            Tendsto (λ b : ℝ => ∫ t in (0:ℝ)..b, (t : ℝ)^λ * f t) atTop (𝓝 (F λ))) ∧
        ContinuousOn F (Set.Icc (α : ℝ) β)) := by
  sorry

-- Proof attempt:
theorem problem_131 {α β : ℝ} (hαβ : α < β) {f : ℝ → ℝ}
    (hf : Measurable f) (hfi : ∀ x ≥ 0, IntegrableOn f (Set.Icc 0 x))
    (hconv_α : ∃ I_α : ℝ, Tendsto (λ b : ℝ => ∫ t in (0:ℝ)..b, (t : ℝ)^α * f t) atTop (𝓝 I_α))
    (hconv_β : ∃ I_β : ℝ, Tendsto (λ b : ℝ => ∫ t in (0:ℝ)..b, (t : ℝ)^β * f t) atTop (𝓝 I_β)) :
    (∀ λ ∈ Set.Icc (α : ℝ) β, ∃ I : ℝ, 
        Tendsto (λ b : ℝ => ∫ t in (0:ℝ)..b, (t : ℝ)^λ * f t) atTop (𝓝 I)) ∧
    (∃ F : ℝ → ℝ, 
        (∀ λ ∈ Set.Icc (α : ℝ) β, 
            Tendsto (λ b : ℝ => ∫ t in (0:ℝ)..b, (t : ℝ)^λ * f t) atTop (𝓝 (F λ))) ∧
        ContinuousOn F (Set.Icc (α : ℝ) β)) := by
  -- First part: existence of integral for all λ ∈ [α, β]
  have h_ex : ∀ λ ∈ Set.Icc α β, ∃ I : ℝ, 
      Tendsto (λ b : ℝ => ∫ t in (0:ℝ)..b, (t : ℝ)^λ * f t) atTop (𝓝 I) := by
    intro λ hλ
    obtain ⟨I_α, hI_α⟩ := hconv_α
    obtain ⟨I_β, hI_β⟩ := hconv_β
    -- Use comparison test with t^α and t^β
    have h_comp : ∀ t > 0, t^λ * |f t| ≤ max (t^α * |f t|) (t^β * |f t|) := by
      intro t ht
      rw [max_le_iff]
      constructor
      · apply Real.rpow_le_rpow_of_nonneg (le_of_lt ht) (hλ.1)
        exact le_of_lt ht
      · apply Real.rpow_le_rpow_of_nonneg (le_of_lt ht) (hλ.2)
        exact le_of_lt ht
    -- The integral converges absolutely by comparison
    apply exists_of_absolutely_convergent_integral hf (fun t ht => ?_)
    · exact (hfi (max t 1) (by linarith)).mono_set (Set.Icc_subset_Icc le_rfl (by simp [le_max_right]))
    · refine (hasFiniteIntegral_of_integrable_bound ?_ ?_ ?_).mp ?_
      · exact fun t => max (t^α * |f t|) (t^β * |f t|)
      · apply (hfi _).aestronglyMeasurable
      · intro t
        simp only [Set.mem_Ioc]
        rintro ⟨ht0, _⟩
        exact h_comp t ht0
      · have hα := (hasFiniteIntegral_iff_norm _).mp (hfi I_α).2
        have hβ := (hasFiniteIntegral_iff_norm _).mp (hfi I_β).2
        exact (hα.add hβ).mono (le_max_iff.1 (h_comp _))
  
  -- Second part: continuity of the parametric integral
  let F (λ : ℝ) := if h : λ ∈ Set.Icc α β then (h_ex λ h).choose else 0
  have hF : ∀ λ ∈ Set.Icc α β, Tendsto (λ b => ∫ t in (0)..b, t^λ * f t) atTop (𝓝 (F λ)) := by
    intro λ hλ
    simp [F, hλ]
    exact (h_ex λ hλ).choose_spec
    
  refine ⟨h_ex, ⟨F, hF, ?_⟩⟩
  
  -- Show continuity on [α, β]
  apply ContinuousOn.mono (continuousOn_parametric_integral_of_dominated_convergence
    (μ := volume.restrict (Set.Ioi 0))
    (fun t => t^β * |f t| + t^α * |f t|) _ _ _ _ _) (by simp [Set.Icc_subset_Ici])
  · -- Measurability
    intro λ _ t ht
    exact ((Continuous.measurable (continuous_pow λ)).aestronglyMeasurable).mul hf.aestronglyMeasurable
  · -- Dominating function is integrable
    apply Integrable.add
    · exact (hconv_β.choose_spec).integral_atTop
    · exact (hconv_α.choose_spec).integral_atTop
  · -- Domination condition
    intro λ hλ t ht
    rw [norm_mul, norm_eq_abs, abs_rpow_of_pos ht]
    refine le_trans (mul_le_mul_of_nonneg_right ?_ (abs_nonneg (f t))) ?_
    · rcases lt_or_gt_of_ne hαβ.ne with h|h
      · exact Real.rpow_le_rpow_of_exponent_le ht (hλ.2)
      · exact Real.rpow_le_rpow_of_exponent_le ht (hλ.1)
    · simp [abs_of_pos ht, add_comm]
  · -- Pointwise continuity of integrand
    intro t ht λ _ 
    apply ContinuousAt.mul
    · exact continuousAt_rpow_const _ _ (Or.inr (ne_of_gt ht))
    · exact continuousAt_const