/-
Polya-Szego Problem 291
Part Three, Chapter 6

Original problem:
Let $f(z)$ be a regular function and $|f(z)|<1$ in the unit disk $|z|<1$; in addition let $f(z)$ be regular at $z=1$ and $f(0)=0, f(1)=1$. Then $f^{\prime}(1)$ must be real and $f^{\prime}(1) \geqq 1$.\\

Formalization notes: -- We formalize the key conclusion: f'(1) is real and ≥ 1
-- We assume:
-- 1. f is holomorphic on the open unit disk 𝔻
-- 2. |f(z)| < 1 for all z ∈ 𝔻
-- 3. f has a removable singularity at z = 1 (is "regular" there)
-- 4. f(0) = 0 and f(1) = 1
-- The conclusion: deriv f 1 is real and ≥ 1
-/

import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Calculus.Deriv

-- Formalization notes:
-- We formalize the key conclusion: f'(1) is real and ≥ 1
-- We assume:
-- 1. f is holomorphic on the open unit disk 𝔻
-- 2. |f(z)| < 1 for all z ∈ 𝔻
-- 3. f has a removable singularity at z = 1 (is "regular" there)
-- 4. f(0) = 0 and f(1) = 1
-- The conclusion: deriv f 1 is real and ≥ 1

open Complex
open Metric
open Set

theorem problem_291 (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (h_bound : ∀ z, ‖z‖ < 1 → ‖f z‖ < 1)
    (h_regular_at_one : ∃ g : ℂ → ℂ, AnalyticAt ℂ g 1 ∧ EqOn f g (ball (0 : ℂ) 1))
    (h_f0 : f 0 = 0) (h_f1 : f 1 = 1) :
    ∃ (c : ℝ), deriv f 1 = c ∧ 1 ≤ c := by
  sorry

-- Proof attempt:
theorem problem_291 (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (h_bound : ∀ z, ‖z‖ < 1 → ‖f z‖ < 1)
    (h_regular_at_one : ∃ g : ℂ → ℂ, AnalyticAt ℂ g 1 ∧ EqOn f g (ball (0 : ℂ) 1))
    (h_f0 : f 0 = 0) (h_f1 : f 1 = 1) :
    ∃ (c : ℝ), deriv f 1 = c ∧ 1 ≤ c := by
  -- First establish the Schwarz lemma condition
  have h_schwarz : ∀ z ∈ ball (0 : ℂ) 1, ‖f z‖ ≤ ‖z‖ := by
    intro z hz
    exact Complex.abs_le_abs_of_mapsTo_ball hf h_bound h_f0 z hz
  
  -- Extract the analytic continuation at 1
  obtain ⟨g, hg_analytic, hg_eq⟩ := h_regular_at_one
  
  -- Show f is differentiable at 1 via the analytic continuation
  have h_diff_at_1 : DifferentiableAt ℂ f 1 := by
    refine DifferentiableAt.congr_of_eventuallyEq ?_ hg_eq
    exact hg_analytic.differentiableAt
  
  -- Consider real z approaching 1 from below
  let z : ℕ → ℝ := fun n => 1 - (1/(n+1))
  have hz_lt1 : ∀ n, ‖(z n : ℂ)‖ < 1 := by
    intro n
    simp [z]
    norm_num
    exact Nat.succ_pos n
  have hz_tendsto : Tendsto z atTop (𝓝 1) := by
    simp [z]
    exact tendsto_one_sub_div_atTop_nhds_0_nat.comp tendsto_nat_cast_atTop_atTop
  
  -- For each zₙ, we have |(1 - f zₙ)/(1 - zₙ)| ≥ 1
  have h_ratio_ge_one : ∀ n, 1 ≤ ‖(1 - f (z n : ℂ)) / (1 - (z n : ℂ))‖ := by
    intro n
    have hzn : z n ∈ ball (0 : ℂ) 1 := by
      rw [mem_ball_zero_iff]
      exact hz_lt1 n
    have hzn_ne1 : z n ≠ 1 := by simp [z]
    rw [norm_div, norm_sub_left, norm_sub_left, ← h_f1]
    simp only [norm_one]
    have := h_schwarz (z n : ℂ) hzn
    rw [norm_sub_left, norm_one] at this
    have : ‖f (z n : ℂ)‖ ≤ ‖(z n : ℂ)‖ := this
    rw [norm_eq_abs, norm_eq_abs, ← abs_ofReal (z n), abs_ofReal, abs_ofReal] at this
    have : abs (f (z n : ℂ)) ≤ z n := by simpa using this
    rw [← sub_pos] at this
    have : 1 - z n ≤ 1 - abs (f (z n : ℂ)) := by linarith
    rw [← norm_eq_abs, ← norm_eq_abs]
    refine (div_le_div_of_le_left zero_le_one (sub_pos.mpr ?_) this).trans_eq ?_
    · exact_mod_cast hzn_ne1.symm
    · simp [norm_eq_abs, abs_ofReal]
  
  -- Take the limit to get |f'(1)| ≥ 1
  have h_deriv_norm : 1 ≤ ‖deriv f 1‖ := by
    have := tendsto.norm h_ratio_ge_one
    have : Tendsto (fun n => ‖(1 - f (z n : ℂ)) / (1 - (z n : ℂ))‖) atTop (𝓝 ‖deriv f 1‖) := by
      refine Tendsto.comp (continuous_norm.tendsto _) ?_
      have : deriv f 1 = deriv g 1 := by
        symm
        apply Filter.EventuallyEq.deriv_eq
        apply hg_eq.eventuallyEq_of_mem
        exact isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr (by norm_num))
      rw [this]
      exact hg_analytic.hasDerivAt_deriv.tendsto_nhds (by simp)
    exact ge_of_tendsto' this h_ratio_ge_one
  
  -- Show f'(1) is real and ≥ 1
  have h_deriv_real : deriv f 1 ∈ ℝ := by
    have : deriv f 1 = deriv g 1 := by
      symm
      apply Filter.EventuallyEq.deriv_eq
      apply hg_eq.eventuallyEq_of_mem
      exact isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr (by norm_num))
    rw [this]
    exact hg_analytic.continuousAt.deriv_im_zero (by simp)
  
  refine ⟨deriv f 1, rfl, ?_⟩
  rw [← norm_of_real (deriv f 1), Real.norm_eq_abs, abs_of_nonneg]
  · exact h_deriv_norm
  · rwa [← h_deriv_real]