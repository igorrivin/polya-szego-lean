/-
Polya-Szego Problem 307
Part Three, Chapter 6

Original problem:
Let $f(z)$ be regular for $|z|<R$;

$$
\mathscr{G}(r)=e^{\frac{1}{2 \pi} \int_{0}^{2 \pi} \log \left|f\left(r e^{i \vartheta}\right)\right| d \vartheta}
$$

denotes the geometric mean of $|f(z)|$ on the circle $|z|=r, r<R$. The function $\mathfrak{G}(r)$ is monotone increasing with $r$ and a convex function of $\log r$ (in the wide sense).\\

Formalization notes: -- 1. We formalize the key properties of the geometric mean function 𝓖(r)
-- 2. We assume f is holomorphic on the open disk of radius R
-- 3. We define 𝓖(r) as the geometric mean of |f(z)| on |z| = r
-- 4. We prove 𝓖(r) is monotone increasing and log-convex in log r
-- 5. The book's solution suggests working with log 𝓖(r) directly
-/

import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral

-- Formalization notes:
-- 1. We formalize the key properties of the geometric mean function 𝓖(r)
-- 2. We assume f is holomorphic on the open disk of radius R
-- 3. We define 𝓖(r) as the geometric mean of |f(z)| on |z| = r
-- 4. We prove 𝓖(r) is monotone increasing and log-convex in log r
-- 5. The book's solution suggests working with log 𝓖(r) directly

open Complex
open Real
open Set
open IntervalIntegral
open MeasureTheory

variable {f : ℂ → ℂ} {R : ℝ} (hR : 0 < R)

-- Helper definition for the geometric mean
noncomputable def geometricMean (f : ℂ → ℂ) (r : ℝ) : ℝ :=
  Real.exp ((1 / (2 * π)) * ∫ θ in (0 : ℝ)..(2 * π), Real.log (Complex.abs (f (r * exp (θ * I)))))

-- Main theorem capturing the properties of 𝓖(r)
theorem problem_307 (hf : DifferentiableOn ℂ f (ball (0 : ℂ) R)) (hr : 0 < r) (hr' : r < R) :
    let 𝓖 := geometricMean f r
    -- Monotonicity: if 0 < r₁ ≤ r₂ < R, then 𝓖(r₁) ≤ 𝓖(r₂)
    (∀ r₁ r₂, 0 < r₁ → r₁ ≤ r₂ → r₂ < R → geometricMean f r₁ ≤ geometricMean f r₂) ∧
    -- Convexity of log 𝓖 as a function of log r
    (ConvexOn ℝ (Set.Ioo 0 R) fun r : ℝ => Real.log (geometricMean f r)) ∧
    -- Alternative formulation: log 𝓖 is convex in log r
    (ConvexOn ℝ (Set.Ioo (-∞) (Real.log R)) fun x : ℝ => 
      Real.log (geometricMean f (Real.exp x))) := by
  sorry

-- Additional theorem capturing the formula from the book's solution
-- when f has zeros z₁, ..., zₙ in |z| ≤ r and f(0) = 1
theorem problem_307_formula (hf : DifferentiableOn ℂ f (ball (0 : ℂ) R)) (hf0 : f 0 = 1)
    (hz : ∀ z ∈ closedBall (0 : ℂ) r, f z = 0 → z ≠ 0) (hr_pos : 0 < r) (hr_lt : r < R) :
    let zeros := {z : ℂ | z ∈ closedBall (0 : ℂ) r ∧ f z = 0}
    let n := (zeros.filter (λ z => z ≠ 0)).card
    Real.log (geometricMean f r) = 
      n * Real.log r - ∑ z in (zeros.filter (λ z => z ≠ 0)).toFinset, Real.log (Complex.abs z) := by
  sorry

-- Proof attempt:
theorem problem_307 (hf : DifferentiableOn ℂ f (ball (0 : ℂ) R)) (hr : 0 < r) (hr' : r < R) :
    let 𝓖 := geometricMean f r
    (∀ r₁ r₂, 0 < r₁ → r₁ ≤ r₂ → r₂ < R → geometricMean f r₁ ≤ geometricMean f r₂) ∧
    (ConvexOn ℝ (Set.Ioo 0 R) fun r : ℝ => Real.log (geometricMean f r)) ∧
    (ConvexOn ℝ (Set.Ioo (-∞) (Real.log R)) fun x : ℝ => 
      Real.log (geometricMean f (Real.exp x))) := by
  let 𝓖 := geometricMean f
  have hf' : ∀ r (hr : r ∈ Ioo 0 R), ContinuousOn (fun z => f z) (sphere (0 : ℂ) r) := by
    intro r hr
    apply DifferentiableOn.continuousOn
    apply hf.mono
    simp [closedBall_subset_ball hr.2]
  
  have log𝓖_eq : ∀ r ∈ Ioo 0 R, log (𝓖 r) = (1 / (2 * π)) * ∫ θ in (0 : ℝ)..(2 * π), log (abs (f (r * exp (θ * I)))) := by
    intro r hr
    simp [𝓖, geometricMean]
    rw [Real.exp_log]
    apply mul_pos
    · apply div_pos; norm_num; apply mul_pos; norm_num; exact Real.pi_pos
    · apply intervalIntegral_pos_of_integrable_on_of_nonneg
      · apply Continuous.intervalIntegrable
        apply Continuous.mul
        · continuity
        · apply Continuous.comp continuous_ofReal
          apply Continuous.log
          apply Continuous.comp continuous_abs
          exact (hf' r hr).comp (continuous_mul_right _)
      · intro θ hθ
        apply log_nonneg
        apply one_le_iff_ne_zero.2
        intro h
        have : abs (f (r * exp (θ * I))) = 0 := by rw [h, abs_zero]
        simp at this
        exact this
  
  have log𝓖_smooth : ∀ r ∈ Ioo 0 R, ContDiffAt ℝ ⊤ (fun r => log (𝓖 r)) r := by
    intro r hr
    rw [log𝓖_eq r hr]
    apply ContDiffAt.const_mul
    apply intervalIntegral_contDiffAt
    · apply isOpen_Ioo
    · intro r' hr' θ hθ
      apply ContDiffAt.log
      · apply ContDiffAt.comp
        apply ContDiffAt.abs
        apply ContDiffAt.comp
        · exact hf.differentiableAt (ball_subset_ball (le_of_lt hr'.2) (mem_ball_zero_iff.2 hr'.1))
        · apply ContDiffAt.mul
          exact contDiffAt_id
          exact contDiffAt_const
      · apply one_le_iff_ne_zero.2
        intro h
        have : abs (f (r' * exp (θ * I))) = 0 := by rw [h, abs_zero]
        simp at this
        exact this
  
  have log𝓖_deriv : ∀ r ∈ Ioo 0 R, HasDerivAt (fun r => log (𝓖 r)) 
      ((1 / (2 * π)) * ∫ θ in (0 : ℝ)..(2 * π), (1 / r) * re (deriv f (r * exp (θ * I)) * exp (θ * I) / f (r * exp (θ * I)))) r := by
    intro r hr
    have := log𝓖_smooth r hr
    rw [log𝓖_eq r hr]
    apply HasDerivAt.const_mul
    apply hasDerivAt_integral_of_interval_deriv (u := fun θ => log (abs (f (r * exp (θ * I)))))
    · exact fun θ hθ => ContinuousAt.log (Continuous.continuousAt (continuous_abs.comp (hf' r hr).continuousAt_iff.2 hθ))
          (one_le_abs_iff.mpr (hf' r hr (mem_sphere_zero_iff.mpr (le_refl r)) hθ))
    · intro θ hθ
      apply HasDerivAt.log
      · exact (hf.differentiableAt (ball_subset_ball (le_of_lt hr.2) (mem_ball_zero_iff.2 hr.1))).hasDerivAt.comp θ
            (HasDerivAt.mul_const (hasDerivAt_id θ) _)
      · exact one_le_abs_iff.mpr (hf' r hr (mem_sphere_zero_iff.mpr (le_refl r)) hθ)
  
  have log𝓖_mono : ∀ r₁ r₂, 0 < r₁ → r₁ ≤ r₂ → r₂ < R → 𝓖 r₁ ≤ 𝓖 r₂ := by
    intro r₁ r₂ hr₁ hle hr₂
    refine' Real.exp_le_exp.2 _
    rw [log𝓖_eq r₁ ⟨hr₁, lt_of_le_of_lt hle hr₂⟩, log𝓖_eq r₂ ⟨lt_of_lt_of_le hr₁ hle, hr₂⟩]
    apply mul_le_mul_of_nonneg_left
    · apply integral_mono_on
      · exact Continuous.intervalIntegrable (Continuous.log.comp (continuous_abs.comp (hf' r₁ _))) 
      · exact Continuous.intervalIntegrable (Continuous.log.comp (continuous_abs.comp (hf' r₂ _)))
      · exact interval_subset_interval le_rfl le_rfl
      · intro θ hθ
        apply log_monotone
        apply abs_le_abs_of_abs_le
        apply hf.abs_subharmonic (ball_mem_nhds _ (lt_of_lt_of_le hr₁ hle)) (ball_subset_ball (le_of_lt hr₂))
        exact mem_ball_zero_iff.2 (lt_of_lt_of_le hr₁ hle)
    · apply div_nonneg; norm_num; exact le_of_lt Real.pi_pos
  
  have log𝓖_convex : ConvexOn ℝ (Ioo 0 R) (fun r => log (𝓖 r)) := by
    apply ConvexOn.mono (convex_Ioo 0 R)
    · intro r hr
      rw [log𝓖_eq r hr]
      exact (log𝓖_smooth r hr).differentiableAt.differentiableWithinAt
    · intro r hr
      have := log𝓖_deriv r hr
      simp at this
      sorry -- Missing the second derivative calculation for full convexity proof
  
  have log𝓖_exp_convex : ConvexOn ℝ (Ioo (-∞) (log R)) (fun x => log (𝓖 (exp x))) := by
    sorry -- Follows from log𝓖_convex by composition with exp
  
  exact ⟨log𝓖_mono, log𝓖_convex, log𝓖_exp_convex⟩