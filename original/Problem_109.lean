/-
Polya-Szego Problem 109
Part One, Chapter 3

Original problem:
The functi

Is satisfied if and\\
$a<\xi<b$.\\

Formalization notes: -- We formalize a version of: If f is holomorphic on an open set containing [a,b] ⊂ ℝ,
-- and Re(f'(z)) > 0 for all z in [a,b], then the argument of f is strictly increasing
-- on [a,b]. More precisely, for a ≤ x < y ≤ b, we have arg(f(y)) > arg(f(x)).
-- We work modulo 2π and use the principal value of the argument.
-/

import Mathlib.Analysis.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Complex.Log

-- Formalization notes:
-- We formalize a version of: If f is holomorphic on an open set containing [a,b] ⊂ ℝ,
-- and Re(f'(z)) > 0 for all z in [a,b], then the argument of f is strictly increasing
-- on [a,b]. More precisely, for a ≤ x < y ≤ b, we have arg(f(y)) > arg(f(x)).
-- We work modulo 2π and use the principal value of the argument.

theorem problem_109 {a b : ℝ} (hab : a < b) {f : ℂ → ℂ} 
    (hf : DifferentiableOn ℂ f (Set.uIcc (a : ℂ) (b : ℂ))) 
    (hpos : ∀ z, z ∈ Set.uIcc (a : ℂ) (b : ℂ)) → 0 < (deriv f z).re) :
    ∀ (x y : ℝ) (hx : a ≤ x) (hy : y ≤ b) (hlt : x < y), 
    Real.Angle.toReal (Complex.arg (f y)) > Real.Angle.toReal (Complex.arg (f x)) := by
  sorry

-- Proof attempt:
theorem problem_109 {a b : ℝ} (hab : a < b) {f : ℂ → ℂ} 
    (hf : DifferentiableOn ℂ f (Set.uIcc (a : ℂ) (b : ℂ))) 
    (hpos : ∀ z, z ∈ Set.uIcc (a : ℂ) (b : ℂ) → 0 < (deriv f z).re) :
    ∀ (x y : ℝ) (hx : a ≤ x) (hy : y ≤ b) (hlt : x < y), 
    Real.Angle.toReal (Complex.arg (f y)) > Real.Angle.toReal (Complex.arg (f x)) := by
  intro x y hx hy hlt
  let γ : ℝ → ℂ := fun t ↦ ↑t
  have hγ : ∀ t, γ t ∈ Set.uIcc (a : ℂ) (b : ℂ) := by
    intro t
    simp [γ, Set.uIcc_of_le (by linarith [hx, hy] : a ≤ b)]
    constructor <;> linarith [hx, hy]
  have hcont : ContinuousOn γ (Set.Icc x y) := continuous_ofReal.continuousOn
  have hdiff : DifferentiableOn ℝ γ (Set.Ioo x y) := differentiable_ofReal.differentiableOn
  let F : ℝ → ℂ := f ∘ γ
  have hF_diff : DifferentiableOn ℝ F (Set.Ioo x y) := 
    hf.comp hdiff fun t ht => hγ t
  
  -- Main calculation using the argument principle
  have harg_diff : ∀ t ∈ Set.Ioo x y, HasDerivAt (fun t ↦ Complex.arg (F t)) 
      ((deriv f (γ t)).re / (F t).re) t := by
    intro t ht
    have hF_ne_zero : F t ≠ 0 := by
      sorry -- Need to show f doesn't vanish on [a,b], but this isn't given in the theorem
    have hderiv : HasDerivAt F (deriv f (γ t) * 1) t := by
      have := hF_diff.hasDerivAt (Set.mem_Ioo.mp ht)
      rw [deriv_ofReal] at this
      exact this
    simp [F] at hderiv
    convert Complex.hasDerivAt_arg hF_ne_zero using 1
    rw [Complex.deriv_arg]
    field_simp [hF_ne_zero]
    simp [← Complex.mul_re, deriv_ofReal, mul_one]
    exact hpos (γ t) (hγ t)
  
  -- Apply mean value theorem to the argument function
  let g : ℝ → ℝ := fun t ↦ Real.Angle.toReal (Complex.arg (F t))
  have hg_diff : ∀ t ∈ Set.Ioo x y, HasDerivAt g ((deriv f (γ t)).re / (F t).re) t := by
    intro t ht
    have := harg_diff t ht
    apply HasDerivAt.congr_of_eventuallyEq this
    simp [g]
    exact Filter.eventuallyEq_of_mem (self_mem_nhdsWithin.mpr ht) fun _ ↦ rfl
  
  have hg_cont : ContinuousOn g (Set.Icc x y) := by
    refine ContinuousOn.comp (f := Complex.arg) (g := F) ?_ hF_diff.continuousOn
    exact Complex.continuous_arg.comp_continuousOn (hf.continuousOn.mono (Set.uIcc_subset_setOf (hγ ·)))
  
  have hg_diff' : ∀ t ∈ Set.Ioo x y, HasDerivAt g ((deriv f (γ t)).re / (F t).re) t := hg_diff
  
  obtain ⟨ξ, hξ, hMVT⟩ := exists_hasDerivAt_eq_slope g hlt hg_cont hg_diff'
  have hpos' : 0 < (deriv f (γ ξ)).re := hpos (γ ξ) (hγ ξ)
  have hF_re_pos : 0 < (F ξ).re := by
    sorry -- Need to show Re(f(z)) > 0 on [a,b], but this isn't given in the theorem
  have : 0 < (deriv f (γ ξ)).re / (F ξ).re := by positivity
  rw [hMVT] at this
  linarith