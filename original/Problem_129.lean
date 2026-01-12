/-
Polya-Szego Problem 129
Part One, Chapter 3

Original problem:
Let $x$ be a fixed point of the interval $[a, b]$ considered in $\mathbf{1 2 8}$. In order that

$$
\lim _{n \rightarrow \infty} \int_{a}^{b} p_{n}(t) f(t) d t=f(x)
$$

holds for all functions $f(t)$ continuous on $[a, b]$ it is necessary and sufficient that

$$
\lim _{n \rightarrow \infty}\left(\int_{a}^{x-\varepsilon} p_{n}(t) d t+\int_{x+\varepsilon}^{b} p_{n}(t) d t\right)=0
$$

for all positive values of $\varepsilon$ for which $a<x-\varepsilon<x+\varepsilon<b$ (if $x=a$ or $x=b$ the first 

Formalization notes: -- We formalize the necessary and sufficient condition for the convergence of
-- ∫ p_n(t) f(t) dt to f(x) for all continuous f.
-- We assume p_n : ℝ → ℝ are integrable functions on [a, b] with ∫ p_n = 1
-- The condition involves integrals over intervals excluding an ε-neighborhood of x
-/

import Mathlib.Analysis.Calculus.Integral.FTC
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Topology.Instances.Real

open Real
open Set
open Filter
open MeasureTheory
open IntervalIntegral

-- Formalization notes:
-- We formalize the necessary and sufficient condition for the convergence of
-- ∫ p_n(t) f(t) dt to f(x) for all continuous f.
-- We assume p_n : ℝ → ℝ are integrable functions on [a, b] with ∫ p_n = 1
-- The condition involves integrals over intervals excluding an ε-neighborhood of x

theorem problem_129 {a b x : ℝ} (hab : a ≤ b) (hx : x ∈ Set.Icc a b) 
    {p : ℕ → ℝ → ℝ} (hp_integrable : ∀ n, IntervalIntegrable (p n) volume a b)
    (hp_norm_one : ∀ n, ∫ t in a..b, p n t = 1) :
    (∀ f : ℝ → ℝ, ContinuousOn f (Set.Icc a b) → 
        Tendsto (λ n => ∫ t in a..b, p n t * f t) atTop (𝓝 (f x))) ↔
    (∀ ε > 0, (hε₁ : a ≤ x - ε) → (hε₂ : x + ε ≤ b) → 
        Tendsto (λ n => ∫ t in a..(x - ε), p n t + ∫ t in (x + ε)..b, p n t) 
                atTop (𝓝 0)) := by
  sorry

-- Proof attempt:
theorem problem_129 {a b x : ℝ} (hab : a ≤ b) (hx : x ∈ Set.Icc a b) 
    {p : ℕ → ℝ → ℝ} (hp_integrable : ∀ n, IntervalIntegrable (p n) volume a b)
    (hp_norm_one : ∀ n, ∫ t in a..b, p n t = 1) :
    (∀ f : ℝ → ℝ, ContinuousOn f (Set.Icc a b) → 
        Tendsto (λ n => ∫ t in a..b, p n t * f t) atTop (𝓝 (f x))) ↔
    (∀ ε > 0, (hε₁ : a ≤ x - ε) → (hε₂ : x + ε ≤ b) → 
        Tendsto (λ n => ∫ t in a..(x - ε), p n t + ∫ t in (x + ε)..b, p n t) 
                atTop (𝓝 0)) := by
  constructor
  · -- Necessary direction
    intro h f_conv ε hε hε₁ hε₂
    let f := fun t => if t ∈ Icc (x - ε) (x + ε) then 0 else 1
    have f_cont : ContinuousOn f (Icc a b) := by
      apply continuousOn_if
      · exact isClosed_Icc
      · exact continuousOn_const
      · exact continuousOn_const
      · intro t ht ht'
        simp at ht'
        exact (ht'.2 (mem_Icc.1 ht).1).elim
    specialize h f f_cont
    have : f x = 0 := by simp [mem_Icc.2 ⟨by linarith, by linarith⟩]
    rw [this] at h
    have eq : ∫ t in a..b, p n t * f t = ∫ t in a..(x - ε), p n t + ∫ t in (x + ε)..b, p n t := by
      rw [intervalIntegral.integral_of_le hab, integral_if (hp_integrable n) f_cont.intervalIntegrable]
      simp only [integral_const, smul_eq_mul, mul_one, mul_zero, add_zero, zero_add]
      rw [← integral_union (Ioc_disjoint_Ioc_singleton (x - ε) (x + ε)) 
          (hp_integrable n).mono_set Ioc_subset_Icc_self
          (hp_integrable n).mono_set Ioc_subset_Icc_self]
      congr
      rw [Ioc_union_Ioc_eq_Ioc hε₁ hε₂, ← Icc_diff_Icc_same hε₁ hε₂]
      exact Ioc_union_Ioc_same (by linarith) (by linarith)
    simp_rw [eq] at h
    exact h
  · -- Sufficient direction
    intro h f f_cont
    rw [Metric.tendsto_nhds]
    intro δ hδ
    obtain ⟨ε, hε, hεx⟩ : ∃ ε > 0, ∀ t ∈ Icc a b, |t - x| ≤ ε → |f t - f x| ≤ δ/2 := by
      exact UniformContinuousOn.continuousOn_iff.mp f_cont.uniformContinuousOn x hx δ (half_pos hδ)
    obtain ⟨hε₁, hε₂⟩ : a ≤ x - ε ∧ x + ε ≤ b := by
      cases' hx with hxa hxb
      refine ⟨?_, ?_⟩
      · exact le_trans hxa (by linarith [hε])
      · exact le_trans (by linarith [hε]) hxb
    specialize h ε hε hε₁ hε₂
    rw [Metric.tendsto_nhds] at h
    obtain ⟨N, hN⟩ := h (δ/2) (half_pos hδ)
    refine ⟨N, fun n hn => ?_⟩
    have eq : ∫ t in a..b, p n t * f t - f x = 
        ∫ t in a..b, p n t * (f t - f x) := by
      rw [← integral_sub (hp_integrable n).mul_continuousOn f_cont.intervalIntegrable,
          ← integral_mul_const, hp_norm_one, one_mul, sub_self]
    rw [eq]
    have split : ∫ t in a..b, p n t * (f t - f x) = 
        ∫ t in a..(x - ε), p n t * (f t - f x) + 
        ∫ t in (x - ε)..(x + ε), p n t * (f t - f x) + 
        ∫ t in (x + ε)..b, p n t * (f t - f x) := by
      rw [← integral_add_adjacent_intervals (hp_integrable n).mono_set (hp_integrable n).mono_set,
          ← integral_add_adjacent_intervals (hp_integrable n).mono_set (hp_integrable n).mono_set]
      · simp
      · exact hε₁
      · exact hε₂
    rw [split]
    have bound : |∫ t in a..(x - ε), p n t * (f t - f x) + ∫ t in (x + ε)..b, p n t * (f t - f x)| ≤ δ/2 := by
      have : ∫ t in a..(x - ε), p n t * (f t - f x) + ∫ t in (x + ε)..b, p n t * (f t - f x) = 
          (f x - f x) * (∫ t in a..(x - ε), p n t + ∫ t in (x + ε)..b, p n t) := by
        rw [sub_self, zero_mul, integral_mul_const, integral_mul_const, add_mul, mul_zero]
      rw [this, norm_zero]
      exact le_of_lt (hN n hn)
    have bound2 : |∫ t in (x - ε)..(x + ε), p n t * (f t - f x)| ≤ δ/2 := by
      refine abs_integral_le_integral_abs.trans ?_
      refine integral_le_integral_of_le (by linarith) (fun t ht => ?_)
      rw [abs_mul]
      refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
      rw [abs_of_nonneg ?_]
      · exact hεx t (Ioc_subset_Icc_self ht) (le_of_lt (abs_lt.1 (Ioc_subset_uIoc ht)).2)
      · rw [← integral_sub (hp_integrable n).mono_set (hp_integrable n).mono_set,
            hp_norm_one, ← integral_union (Ioc_disjoint_Ioc_singleton (x - ε) (x + ε)) 
            (hp_integrable n).mono_set (hp_integrable n).mono_set]
        simp [integral_const, smul_eq_mul, mul_one]
        rw [Ioc_union_Ioc_eq_Ioc hε₁ hε₂]
        exact le_trans (norm_integral_le_integral_norm _) (integral_le_integral_of_le (by linarith) (fun _ _ => norm_nonneg _))
    rw [← sub_zero (f x)]
    simp_rw [← norm_sub_le_iff]
    calc |∫ t in a..(x - ε), p n t * (f t - f x) + ∫ t in (x - ε)..(x + ε), p n t * (f t - f x) + 
           ∫ t in (x + ε)..b, p n t * (f t - f x)| 
        ≤ |∫ t in a..(x - ε), p n t * (f t - f x) + ∫ t in (x + ε)..b, p n t * (f t - f x)| + 
          |∫ t in (x - ε)..(x + ε), p n t * (f t - f x)| := abs_add _ _
    _ ≤ δ/2 + δ/2 := add_le_add bound bound2
    _ = δ := by ring