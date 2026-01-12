/-
Polya-Szego Problem 320
Part Three, Chapter 6

Original problem:
Consider a regular harmonic function in the disk $|z|<R$. We denote by $A(r)$ its maximum on the circle $|z|=r, r<R$. When $0<r_{1}<r_{2}<r_{3}<R$ we have

$$
A\left(r_{2}\right) \leqq \frac{\log r_{2}-\log r_{1}}{\log r_{3}-\log r_{1}} A\left(r_{3}\right)+\frac{\log r_{3}-\log r_{2}}{\log r_{3}-\log r_{1}} A\left(r_{1}\right)
$$

i.e. $A(r)$ is a convex function of $\log \gamma$.\\

Formalization notes: -- We formalize the statement about harmonic functions on a disk and the convexity of A(r) in log(r)
-- A(r) is defined as the maximum of |u(z)| on the circle |z| = r
-- The inequality expresses that A(r) is a convex function of log(r)
-/

import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Convex.Function

-- Formalization notes:
-- We formalize the statement about harmonic functions on a disk and the convexity of A(r) in log(r)
-- A(r) is defined as the maximum of |u(z)| on the circle |z| = r
-- The inequality expresses that A(r) is a convex function of log(r)

open Complex
open Metric
open Set
open Real

theorem problem_320 (R : ℝ) (hR : 0 < R) (u : ℂ → ℝ) (hu : HarmonicOn u (ball (0 : ℂ) R)) 
    (A : ℝ → ℝ) (hA : ∀ r, 0 < r → r < R → A r = sSup (u '' (sphere (0 : ℂ) r))) :
    ∀ (r₁ r₂ r₃ : ℝ), 0 < r₁ → r₁ < r₂ → r₂ < r₃ → r₃ < R → 
    A r₂ ≤ ((Real.log r₂ - Real.log r₁) / (Real.log r₃ - Real.log r₁)) * A r₃ + 
           ((Real.log r₃ - Real.log r₂) / (Real.log r₃ - Real.log r₁)) * A r₁ := by
  sorry

-- Proof attempt:
theorem problem_320 (R : ℝ) (hR : 0 < R) (u : ℂ → ℝ) (hu : HarmonicOn u (ball (0 : ℂ) R)) 
    (A : ℝ → ℝ) (hA : ∀ r, 0 < r → r < R → A r = sSup (u '' (sphere (0 : ℂ) r))) :
    ∀ (r₁ r₂ r₃ : ℝ), 0 < r₁ → r₁ < r₂ → r₂ < r₃ → r₃ < R → 
    A r₂ ≤ ((Real.log r₂ - Real.log r₁) / (Real.log r₃ - Real.log r₁)) * A r₃ + 
           ((Real.log r₃ - Real.log r₂) / (Real.log r₃ - Real.log r₁)) * A r₁ := by
  intro r₁ r₂ r₃ hr₁ hr₁₂ hr₂₃ hr₃
  have h₁₃ : Real.log r₁ < Real.log r₃ := by
    apply Real.log_lt_log
    all_goals positivity
  have hα : ∃ α, A r₁ + α * Real.log r₁ = A r₃ + α * Real.log r₃ := by
    refine ⟨(A r₃ - A r₁)/(Real.log r₁ - Real.log r₃), ?_⟩
    field_simp [h₁₃.ne']
    ring
  obtain ⟨α, hα⟩ := hα
  let v : ℂ → ℝ := fun z => u z + α * Real.log (abs z)
  have hv : HarmonicOn v (annulus (0 : ℂ) r₁ r₃) := by
    apply HarmonicOn.add hu
    refine (harmonicOn_log_abs _).mono ?_
    simp [annulus, mem_ball, norm_eq_abs]
    intro z hz
    exact ne_of_gt hz.1
    intro z hz
    exact lt_of_lt_of_le hz.2 hr₃.le
  have h_max : ∀ z ∈ annulus (0 : ℂ) r₁ r₃, v z ≤ max (A r₁ + α * Real.log r₁) (A r₃ + α * Real.log r₃) := by
    have := harmonicOn_abs_max hv (isCompact_annulus r₁ r₃) (isClosed_annulus r₁ r₃).closure_subset_ball
    intro z hz
    refine le_trans (le_csSup this ?_) (le_max_left _ _)
    refine ⟨z, hz, ?_⟩
    simp [v]
  have h_eq : A r₁ + α * Real.log r₁ = A r₃ + α * Real.log r₃ := hα
  rw [h_eq] at h_max
  specialize h_max
  have hr₂ : r₁ < r₂ ∧ r₂ < r₃ := ⟨hr₁₂, hr₂₃⟩
  have hz : ∃ z ∈ sphere (0 : ℂ) r₂, u z = A r₂ := by
    have := isCompact_sphere (0 : ℂ) r₂
    have hne : (sphere (0 : ℂ) r₂).Nonempty := by simp [hr₂.1.le]
    obtain ⟨z, hz, hmax⟩ := IsCompact.exists_isMaxOn this hne (hu.continuousOn.mono (sphere_subset_ball hr₂.2.le))
    refine ⟨z, hz, ?_⟩
    rw [hA r₂ hr₂.1 hr₂.2]
    exact csSup_eq_of_isCompact_of_isMaxOn this hne hmax
  obtain ⟨z, hz, huz⟩ := hz
  specialize h_max z ⟨hr₂.1.trans_le (by rw [mem_sphere_zero_iff_norm, hz]; rfl), hr₂.2.trans_le (by rw [mem_sphere_zero_iff_norm, hz]; rfl)⟩
  rw [v, huz, mem_sphere_zero_iff_norm] at hz
  simp_rw [hz, Real.norm_eq_abs, abs_of_pos hr₂.1] at h_max
  rw [hα] at h_max
  have : Real.log r₂ = ((Real.log r₂ - Real.log r₁) / (Real.log r₃ - Real.log r₁)) * Real.log r₃ + 
                     ((Real.log r₃ - Real.log r₂) / (Real.log r₃ - Real.log r₁)) * Real.log r₁ := by
    field_simp [h₁₃.ne']
    ring
  rw [this] at h_max
  simp_rw [mul_add, add_mul, ← mul_assoc] at h_max
  rw [le_add_iff_nonneg_right] at h_max
  convert h_max using 1 <;> field_simp [h₁₃.ne'] <;> ring