/-
Polya-Szego Problem 239
Part Three, Chapter 5

Original problem:
Let the ff in the disk $\mid z<$ for $|z|<R$, i.e. $\left|z_{1}\right|<R, \mid z_{2}<R$

The factor $\frac{1}{2}$ can m sition geometrically\\

Formalization notes: -- We formalize the inequality |f'(0)| * R ≤ (1/2) * D(f) for holomorphic functions on a disk,
-- where D(f) = sup_{|z| < R} |f(z) - f(-z)|.
-- We also include the equality case for linear functions.
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

-- Formalization notes:
-- We formalize the inequality |f'(0)| * R ≤ (1/2) * D(f) for holomorphic functions on a disk,
-- where D(f) = sup_{|z| < R} |f(z) - f(-z)|.
-- We also include the equality case for linear functions.

open Complex
open Metric
open Set

theorem problem_239 (R : ℝ) (hR : 0 < R) (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (ball (0 : ℂ) R)) :
    let D := sSup (Set.range fun (z : ℂ) => ‖f z - f (-z)‖) in
    let a₁ := deriv f 0 in
    ‖a₁‖ * R ≤ (1/2 : ℝ) * D := by
  sorry

-- Equality case for linear functions
theorem problem_239_linear_case (R : ℝ) (hR : 0 < R) (a₀ a₁ : ℂ) :
    let f := fun (z : ℂ) => a₀ + a₁ * z in
    let D := sSup (Set.range fun (z : ℂ) => ‖f z - f (-z)‖) in
    D = 2 * ‖a₁‖ * R := by
  sorry

-- Proof attempt:
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.CircleIntegral

open Complex Metric Set Real
open scoped Real NNReal

theorem problem_239 (R : ℝ) (hR : 0 < R) (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (ball (0 : ℂ) R)) :
    let D := sSup (Set.range fun (z : ℂ) => ‖f z - f (-z)‖) in
    let a₁ := deriv f 0 in
    ‖a₁‖ * R ≤ (1/2 : ℝ) * D := by
  let D := sSup (Set.range fun (z : ℂ) => ‖f z - f (-z)‖)
  let a₁ := deriv f 0
  have hD : 0 ≤ D := by
    apply le_csSup
    · use ‖f 0 - f (-0)‖
      simp only [Set.mem_range, exists_apply_eq_apply]
    · exact Real.sSup_nonneg _ (by simp only [Set.mem_range, forall_apply_eq_imp_iff', norm_nonneg, forall_const])
  
  have hf' : ∀ r ∈ Ioo (0 : ℝ) R, DifferentiableOn ℂ f (closedBall 0 r) :=
    fun r hr => hf.mono (closedBall_subset_ball hr.2)
  
  have key : ∀ r ∈ Ioo (0 : ℝ) R, ‖a₁‖ * r ≤ (1/2) * D := by
    intro r hr
    have hcr : ContinuousOn (fun z ↦ f z - f (-z)) (sphere (0 : ℂ) r) := by
      refine (hf' r hr).continuousOn.sub ?_
      refine (hf' r hr).comp continuousOn_neg ?_
      intro z hz
      simp only [mem_closedBall, norm_neg] at hz ⊢
      exact hz
    have h_int : a₁ = (2 * π * r * I)⁻¹ • ∮ z in C(0, r), (f z - f (-z)) / z ^ 2 := by
      have h1 := (hf' r hr).hasFPowerSeriesOnBall hR
      simp only [deriv_fpowerSeries0, normedAddCommGroup_eq_zero] at h1
      rw [h1]
      simp only [one_mul, Nat.factorial_one, Nat.cast_one, inv_one]
    rw [h_int, norm_smul, norm_inv, norm_mul, norm_eq_abs, abs_ofReal, norm_eq_abs, abs_two, abs_mul, abs_pi,
      norm_eq_abs, abs_I, mul_one, ← mul_assoc, ← mul_assoc, inv_mul_eq_div, div_mul_eq_mul_div, mul_comm (‖_‖)]
    apply div_le_of_nonneg_of_le_mul (by positivity) (by positivity)
    rw [mul_assoc, ← mul_assoc (1/2 : ℝ)]
    refine (norm_circleIntegral_le_two_pi_mul_norm _ _ ?_).trans ?_
    · exact hcr.div (continuousOn_id.pow _) fun z hz => pow_ne_zero _ (circleIntegral.integrand_ne hr.1.ne' hz)
    · refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      refine (norm_div_le _ _).trans ?_
      refine (div_le_of_nonneg_of_le_mul (by positivity) (norm_nonneg _) ?_).trans ?_
      · exact (le_csSup (Real.isBounded_iff_bddBelow_bddAbove.2 ⟨⟨0, fun _ ⟨z, hz⟩ => hz ▸ norm_nonneg _⟩, 
          ⟨D, fun y ⟨z, hz⟩ => hz ▸ le_sSup ⟨‖f z - f (-z)‖, by simp⟩⟩⟩) ⟨r, mem_sphere_iff_norm.2 hr.1.le⟩)
      · simp only [norm_pow, norm_eq_abs, abs_ofReal, hr.1.le, rpow_nat_cast, pow_two, mul_inv_le_iff hr.1]
        exact le_of_eq (by ring)
  
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have : ‖a₁‖ * R - ‖a₁‖ * ε ≤ (1/2) * D := by
    rcases exists_between (lt_min hR hε) with ⟨r, hr, hrε⟩
    have : ‖a₁‖ * r ≤ (1/2) * D := key r ⟨hr.1, hr.2.trans hR⟩
    rw [← sub_le_iff_le_add]
    refine (mul_le_mul_of_nonneg_left (sub_le_sub_left hrε.2 _) (norm_nonneg _)).trans ?_
    rw [mul_sub, ← this]
    exact sub_le_sub_left (mul_le_mul_of_nonneg_left hrε.1.le (norm_nonneg _)) _
  linarith

theorem problem_239_linear_case (R : ℝ) (hR : 0 < R) (a₀ a₁ : ℂ) :
    let f := fun (z : ℂ) => a₀ + a₁ * z in
    let D := sSup (Set.range fun (z : ℂ) => ‖f z - f (-z)‖) in
    D = 2 * ‖a₁‖ * R := by
  let f := fun (z : ℂ) => a₀ + a₁ * z
  let D := sSup (Set.range fun (z : ℂ) => ‖f z - f (-z)‖)
  have hf : ∀ z, f z - f (-z) = 2 * a₁ * z := by intro z; simp [f, ← mul_assoc, mul_comm (a₁ : ℂ) z]
  simp_rw [hf, norm_mul, norm_eq_abs, abs_two, abs_ofReal]
  have : (fun z => ‖f z - f (-z)‖) = fun z => 2 * ‖a₁‖ * ‖z‖ := by ext z; simp [norm_mul]
  rw [this]
  have : Set.range (fun z => 2 * ‖a₁‖ * ‖z‖) = (fun x => 2 * ‖a₁‖ * x) '' Set.range (‖·‖ : ℂ → ℝ) := by
    simp [Set.range_comp]
  rw [this, ← image_ball_zero_eq_ball_zero hR, Real.sSup_image_ball_zero_eq hR (by positivity)]
  ring