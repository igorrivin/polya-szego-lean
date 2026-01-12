/-
Polya-Szego Problem 268
Part Three, Chapter 6

Original problem:
We assume that the function $f(z)$ is regular in the simply connected region $|z|>R . M(r)$ denotes the maximum of $|f(z)|$ on the circle $|z|=r, r>R$. Then $M(r)$ is also the maximum of $|f(z)|$ for $|z| \geqq r$ and $M(r)$ is monotone decreasing unless $f(z)$ is a constant.\\

Formalization notes: -- We formalize the statement about the maximum modulus principle for functions
-- regular in the exterior domain |z| > R.
-- We assume f is holomorphic on {z | |z| > R} (with possible isolated singularity at ∞)
-- M(r) = max_{|z|=r} |f(z)| for r > R
-- The theorem states:
-- 1. M(r) = max_{|z| ≥ r} |f(z)|
-- 2. M(r) is monotone decreasing in r unless f is constant
-/

import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Real

-- Formalization notes:
-- We formalize the statement about the maximum modulus principle for functions
-- regular in the exterior domain |z| > R.
-- We assume f is holomorphic on {z | |z| > R} (with possible isolated singularity at ∞)
-- M(r) = max_{|z|=r} |f(z)| for r > R
-- The theorem states:
-- 1. M(r) = max_{|z| ≥ r} |f(z)|
-- 2. M(r) is monotone decreasing in r unless f is constant

open Complex
open Metric
open Set
open Filter

theorem problem_268 (R : ℝ) (hR : 0 < R) (f : ℂ → ℂ) 
    (hf : DifferentiableOn ℂ f {z | R < |z|}) :
    let M : ℝ → ℝ := fun r => sSup (|f| '' (sphere (0 : ℂ) r))
    in (∀ r, r > R → M r = sSup (|f| '' {z | r ≤ |z|})) ∧
       (∀ r₁ r₂, R < r₁ → r₁ ≤ r₂ → M r₂ ≤ M r₁) ∧
       (¬∀ r₁ r₂, R < r₁ → r₁ ≤ r₂ → M r₂ ≤ M r₁ → f = Function.const ℂ (f 1)) := by
  sorry

-- Proof attempt:
theorem problem_268 (R : ℝ) (hR : 0 < R) (f : ℂ → ℂ) 
    (hf : DifferentiableOn ℂ f {z | R < |z|}) :
    let M : ℝ → ℝ := fun r => sSup (|f| '' (sphere (0 : ℂ) r))
    in (∀ r, r > R → M r = sSup (|f| '' {z | r ≤ |z|})) ∧
       (∀ r₁ r₂, R < r₁ → r₁ ≤ r₂ → M r₂ ≤ M r₁) ∧
       (¬∀ r₁ r₂, R < r₁ → r₁ ≤ r₂ → M r₂ ≤ M r₁ → f = Function.const ℂ (f 1)) := by
  set M := fun r => sSup (|f| '' (sphere (0 : ℂ) r)) with hM_def
  constructor
  · intro r hr
    have h₁ : IsCompact (sphere (0 : ℂ) r) := isCompact_sphere _ _
    have h₂ : (sphere (0 : ℂ) r).Nonempty := by
      simp only [nonempty_sphere, norm_zero, Ne.def, hr, not_false_eq_true]
    have h₃ : ContinuousOn (|f|) (sphere (0 : ℂ) r) := by
      refine ContinuousOn.comp (continuous_abs.continuousOn) ?_ (mapsTo_image _ _)
      exact hf.continuousOn.mono (by simp [hr.le, sphere_subset_closedBall])
    obtain ⟨z, hz, hmax⟩ := h₁.exists_forall_ge h₂ h₃
    rw [hM_def, ← hmax]
    apply le_antisymm
    · apply csSup_le ((nonempty_sphere.mpr hr).image _)
      intro y hy
      obtain ⟨w, hw, rfl⟩ := hy
      exact le_max_of_le_right (hmax w hw)
    · refine le_csSup ?_ (mem_image_of_mem _ hz)
      apply BddAbove.image (h₁.bddAbove_continuousOn h₃)
  constructor
  · intro r₁ r₂ hr₁ hr₂
    rw [hM_def, hM_def]
    have h₁ : {z | r₂ ≤ |z|} ⊆ {z | r₁ ≤ |z|} := by
      intro z hz; exact le_trans hr₂ hz
    apply csSup_mono
    · exact (nonempty_sphere.mpr hr₂).image _
    · exact (nonempty_sphere.mpr hr₁).image _
    · apply Set.image_subset _ (sphere_subset_closedBall.trans h₁)
    · apply BddAbove.image (isCompact_sphere _ _).bddAbove_continuousOn
      exact ContinuousOn.comp (continuous_abs.continuousOn) 
        (hf.continuousOn.mono (by simp [hr₁.le, sphere_subset_closedBall])) 
        (mapsTo_image _ _)
  · intro h
    let f_const := Function.const ℂ (f 1)
    by_contra hc
    push_neg at hc
    obtain ⟨z, hz⟩ := hc
    have hd : DifferentiableOn ℂ (f - f_const) {w | R < |w|} := by
      apply DifferentiableOn.sub hf
      exact differentiableOn_const _
    have h_nonconst : ¬∀ w, R < |w| → f w = f 1 := by
      intro h'; apply hz; exact h' 1 (by simp [hR])
    obtain ⟨w, hwR, hw⟩ : ∃ w, R < |w| ∧ f w ≠ f 1 := by
      push_neg at h_nonconst; exact h_nonconst
    set r := max R (|w| + 1) with hr_def
    have hr : R < r := by simp [hr_def, hR, lt_add_one (|w|)]
    have hwr : |w| < r := by simp [hr_def, lt_add_one (|w|)]
    have := h r (|w|) hr (by linarith) (by simp [hM_def])
    have h_eq : f = f_const := this
    apply hw
    exact h_eq.symm ▸ rfl