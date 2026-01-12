/-
Polya-Szego Problem 167
Part One, Chapter 4

Original problem:
Le1\\
ag as the 1\\

Formalization notes: -- We formalize a version of Cauchy's integral theorem for functions multiplied by log(z) or z^k
-- The domain D is assumed to be simply connected and not containing 0
-- The contour γ is assumed to be piecewise smooth and contained in D
-- The conclusion is that the contour integrals vanish
-/

import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Polynomial
import Mathlib.Analysis.SpecialFunctions.Log.Basic

-- Formalization notes:
-- We formalize a version of Cauchy's integral theorem for functions multiplied by log(z) or z^k
-- The domain D is assumed to be simply connected and not containing 0
-- The contour γ is assumed to be piecewise smooth and contained in D
-- The conclusion is that the contour integrals vanish

open Complex
open Set
open scoped Real

theorem problem_167_part_one (D : Set ℂ) (hD : IsOpen D) (hD_simply_conn : SimplyConnected D) 
    (hD_no_zero : (0 : ℂ) ∉ D) (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f D) 
    (γ : ℝ → ℂ) (hγ : Path γ) (hγ_smooth : PiecewiseSmooth γ) 
    (hγ_range : range γ ⊆ D) (hγ_closed : γ 0 = γ 1) (k : ℕ) :
    (∮ z in γ, f z * Real.log (Complex.abs z) + f z * Real.arg z * I) = 0 ∧
    (∮ z in γ, z ^ k * f z) = 0 := by
  sorry

-- Proof attempt:
theorem problem_167_part_one (D : Set ℂ) (hD : IsOpen D) (hD_simply_conn : SimplyConnected D) 
    (hD_no_zero : (0 : ℂ) ∉ D) (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f D) 
    (γ : ℝ → ℂ) (hγ : Path γ) (hγ_smooth : PiecewiseSmooth γ) 
    (hγ_range : range γ ⊆ D) (hγ_closed : γ 0 = γ 1) (k : ℕ) :
    (∮ z in γ, f z * Real.log (Complex.abs z) + f z * Real.arg z * I) = 0 ∧
    (∮ z in γ, z ^ k * f z) = 0 := by
  constructor
  · -- First integral: f(z) * log z
    let g : ℂ → ℂ := fun z ↦ f z * (Real.log (Complex.abs z) + Real.arg z * I)
    have hg_diff : DifferentiableOn ℂ g D := by
      refine DifferentiableOn.mul hf ?_
      apply DifferentiableOn.add
      · exact (differentiableOn_real_log.comp differentiableOn_norm hD_no_zero).ofRestrictScalars ℂ
      · exact (differentiableOn_arg.mul_const I).comp differentiableOn_id hD_no_zero
    exact CauchyIntegralTheorem.cauchy_integral_theorem hD hD_simply_conn g hg_diff γ hγ_smooth hγ_range hγ_closed
  · -- Second integral: z^k * f(z)
    let h : ℂ → ℂ := fun z ↦ z ^ k * f z
    have hh_diff : DifferentiableOn ℂ h D := by
      refine DifferentiableOn.mul ?_ hf
      exact differentiableOn_pow k
    exact CauchyIntegralTheorem.cauchy_integral_theorem hD hD_simply_conn h hh_diff γ hγ_smooth hγ_range hγ_closed