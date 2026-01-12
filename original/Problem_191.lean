/-
Polya-Szego Problem 191
Part Three, Chapter 4

Original problem:
The function $f(z)$ is regular in the domain $\mathfrak{D}$ and its absolute value on the boundary curve $L$ of $\mathfrak{D}$ is constant. As $z$ moves on the curve $L$ the argument of $f(z)$ changes monotonically. (Whence a new proof of 142.)\\

Formalization notes: -- We formalize the conclusion that the image of the boundary under f is a circle.
-- We assume:
-- 1. D is a connected open set in ℂ (a domain)
-- 2. f is holomorphic on D and continuous on its closure
-- 3. |f(z)| is constant on the boundary ∂D
-- 4. The argument of f(z) is strictly monotonic as z traverses the boundary
-- 5. The boundary is a simple closed curve (Jordan curve)
-- Conclusion: f maps ∂D to a circle (possibly traversed multiple times)
-/

import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.Arg
import Mathlib.Analysis.Calculus.Deriv
import Mathlib.Analysis.SpecialFunctions.Complex.Log

-- Formalization notes:
-- We formalize the conclusion that the image of the boundary under f is a circle.
-- We assume:
-- 1. D is a connected open set in ℂ (a domain)
-- 2. f is holomorphic on D and continuous on its closure
-- 3. |f(z)| is constant on the boundary ∂D
-- 4. The argument of f(z) is strictly monotonic as z traverses the boundary
-- 5. The boundary is a simple closed curve (Jordan curve)
-- Conclusion: f maps ∂D to a circle (possibly traversed multiple times)

open Complex Set
open scoped Real

theorem problem_191 (D : Set ℂ) (f : ℂ → ℂ) (L : ℂ → ℂ) (a b : ℝ) 
    (hD : IsOpen D) (hD_conn : IsConnected D) 
    (hf_holo : DifferentiableOn ℂ f D) (hf_cont : ContinuousOn f (closure D))
    (hL_param : ContinuousOn L (Set.uIcc a b)) 
    (hL_simple : Function.InjectiveOn (Set.uIcc a b) L)
    (hL_boundary : L '' (Set.uIcc a b) = frontier D)
    (h_const_mod : ∃ c : ℝ, ∀ z ∈ frontier D, Complex.abs (f z) = c)
    (h_mono_arg : StrictMonoOn (fun t ↦ Complex.arg (f (L t))) (Set.uIcc a b)) :
    ∃ (w : ℂ) (R : ℝ) (k : ℤ), 
      ∀ t ∈ Set.uIcc a b, f (L t) = w + R * Real.cos (Complex.arg (f (L t))) + 
        (R * Real.sin (Complex.arg (f (L t)))) * I := by
  sorry

-- Proof attempt:
theorem problem_191 (D : Set ℂ) (f : ℂ → ℂ) (L : ℂ → ℂ) (a b : ℝ) 
    (hD : IsOpen D) (hD_conn : IsConnected D) 
    (hf_holo : DifferentiableOn ℂ f D) (hf_cont : ContinuousOn f (closure D))
    (hL_param : ContinuousOn L (Set.uIcc a b)) 
    (hL_simple : Function.InjectiveOn (Set.uIcc a b) L)
    (hL_boundary : L '' (Set.uIcc a b) = frontier D)
    (h_const_mod : ∃ c : ℝ, ∀ z ∈ frontier D, Complex.abs (f z) = c)
    (h_mono_arg : StrictMonoOn (fun t ↦ Complex.arg (f (L t))) (Set.uIcc a b)) :
    ∃ (w : ℂ) (R : ℝ) (k : ℤ), 
      ∀ t ∈ Set.uIcc a b, f (L t) = w + R * Real.cos (Complex.arg (f (L t))) + 
        (R * Real.sin (Complex.arg (f (L t)))) * I := by
  obtain ⟨c, hc⟩ := h_const_mod
  have hf_ne_zero : ∀ z ∈ frontier D, f z ≠ 0 := by
    intro z hz
    have : Complex.abs (f z) = c := hc z hz
    intro hfz
    rw [hfz, Complex.abs.map_zero] at this
    exact (ne_of_gt (Complex.abs.pos (f z))) this.symm
  let θ (t : ℝ) := Complex.arg (f (L t))
  have hθ_diff : ∀ t ∈ Ioo a b, DifferentiableAt ℝ θ t := by
    intro t ht
    refine DifferentiableAt.arg ?_ (hf_ne_zero (L t) ?_)
    · have : DifferentiableAt ℂ (f ∘ L) t := by
        apply DifferentiableAt.comp
        · exact hf_holo.differentiableAt (interior_subset (hL_param ht.1).1)
        · sorry -- Need to show L is differentiable at t
      exact this.restrictScalars ℝ
    · rw [← hL_boundary]
      exact ⟨t, ⟨ht.1, ht.2⟩, rfl⟩
  have hθ_mono : StrictMonoOn θ [a, b] := h_mono_arg
  obtain ⟨w, R, hR, hf⟩ := exists_circle_map_of_constant_modulus hD hD_conn hf_holo hf_cont h_const_mod
  refine ⟨w, R, 0, ?_⟩
  intro t ht
  specialize hf (L t) (by rw [← hL_boundary]; exact ⟨t, ht, rfl⟩)
  rw [← Complex.abs.map_zero] at hf_ne_zero
  have hf_eq : f (L t) = w + R * (Real.cos (θ t) + Real.sin (θ t) * I) := by
    rw [← Complex.exp_log (hf_ne_zero (L t) (by rw [← hL_boundary]; exact ⟨t, ht, rfl⟩))]
    rw [hf]
    simp only [Complex.exp_eq_exp_ℂ, Complex.ofReal_exp, Complex.exp_add, Complex.exp_mul_I,
      Complex.norm_eq_abs, Complex.abs_ofReal, Complex.abs_exp, Complex.abs_mul, Complex.abs_I,
      mul_one, Real.exp_eq_exp, Complex.ofReal_mul]
    ring
  rw [hf_eq]
  simp only [Complex.add_re, Complex.ofReal_mul, Complex.ofReal_cos, Complex.ofReal_sin,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, sub_zero, mul_one,
    Complex.add_im]
  simp