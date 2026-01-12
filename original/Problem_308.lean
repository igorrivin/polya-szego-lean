/-
Polya-Szego Problem 308
Part Three, Chapter 6

Original problem:
The function $f(z)$ is supposed to be regular for $|z|<R$ and not a constant. We put

$$
I(r)=\frac{1}{2 \pi} \int_{0}^{2 \pi}\left|f\left(r e^{i \vartheta}\right)\right| d \vartheta, \quad r<R
$$

The function $I(r)$ is monotone increasing with $r$ and $\log I(r)$ is a convex function of $\log r$. [299, 304.]\\

Formalization notes: -- We formalize two main properties of the mean integral I(r):
-- 1. I(r) is monotone increasing in r
-- 2. log I(r) is a convex function of log r
-- We assume f is holomorphic on the open disk of radius R and non-constant.
-- The integral I(r) is defined as the average of |f(z)| on the circle |z| = r.
-/

import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Convex.Slope
import Mathlib.MeasureTheory.Integral.IntervalIntegral

-- Formalization notes:
-- We formalize two main properties of the mean integral I(r):
-- 1. I(r) is monotone increasing in r
-- 2. log I(r) is a convex function of log r
-- We assume f is holomorphic on the open disk of radius R and non-constant.
-- The integral I(r) is defined as the average of |f(z)| on the circle |z| = r.

open Complex
open Real
open Set
open MeasureTheory
open intervalIntegral

theorem problem_308 (R : ℝ) (hR : 0 < R) (f : ℂ → ℂ) 
    (hf : DifferentiableOn ℂ f (ball (0 : ℂ) R)) (hconst : ¬ ∀ z ∈ ball (0 : ℂ) R, f z = f 0) :
    let I : ℝ → ℝ := fun r => 
      if hr : 0 ≤ r ∧ r < R then
        (1 / (2 * π)) * ∫ θ in (0)..(2 * π), Complex.abs (f (⟨r, 0⟩ * exp (θ * I))) 
      else 0
    in
    ∃ I_fun : ℝ → ℝ, 
      (∀ r, 0 ≤ r → r < R → I_fun r = I r) ∧
      -- I(r) is monotone increasing
      (∀ r1 r2, 0 ≤ r1 → r1 ≤ r2 → r2 < R → I_fun r1 ≤ I_fun r2) ∧
      -- log I(r) is convex in log r
      (∀ r1 r2 r3 : ℝ, 0 < r1 → r1 < r2 → r2 < r3 → r3 < R → 
        let x1 := Real.log r1
        let x2 := Real.log r2
        let x3 := Real.log r3
        let y1 := Real.log (I_fun r1)
        let y2 := Real.log (I_fun r2)
        let y3 := Real.log (I_fun r3)
        in (x3 - x2) * y1 + (x2 - x1) * y3 ≤ (x3 - x1) * y2) := by
  sorry

-- Proof attempt:
set_option maxHeartbeats 400000
theorem problem_308 (R : ℝ) (hR : 0 < R) (f : ℂ → ℂ) 
    (hf : DifferentiableOn ℂ f (ball (0 : ℂ) R)) (hconst : ¬ ∀ z ∈ ball (0 : ℂ) R, f z = f 0) :
    let I : ℝ → ℝ := fun r => 
      if hr : 0 ≤ r ∧ r < R then
        (1 / (2 * π)) * ∫ θ in (0)..(2 * π), Complex.abs (f (⟨r, 0⟩ * exp (θ * I))) 
      else 0
    in
    ∃ I_fun : ℝ → ℝ, 
      (∀ r, 0 ≤ r → r < R → I_fun r = I r) ∧
      (∀ r1 r2, 0 ≤ r1 → r1 ≤ r2 → r2 < R → I_fun r1 ≤ I_fun r2) ∧
      (∀ r1 r2 r3 : ℝ, 0 < r1 → r1 < r2 → r2 < r3 → r3 < R → 
        let x1 := Real.log r1
        let x2 := Real.log r2
        let x3 := Real.log r3
        let y1 := Real.log (I_fun r1)
        let y2 := Real.log (I_fun r2)
        let y3 := Real.log (I_fun r3)
        in (x3 - x2) * y1 + (x2 - x1) * y3 ≤ (x3 - x1) * y2) := by
  let I_fun := fun r => if 0 ≤ r ∧ r < R then I r else 0
  use I_fun
  refine ⟨fun r hr hRr => by simp [I_fun, hr, hRr], ?_, ?_⟩
  · -- Monotonicity
    intro r1 r2 hr1 hr1r2 hr2R
    simp only [I_fun]
    split_ifs with h1 h2
    · have hsub : ball (0 : ℂ) R ⊆ ball 0 R := subset_rfl
      have h1' : r1 ∈ Ioc 0 R := ⟨h1.1, hr1r2.trans_lt h2.2⟩
      have h2' : r2 ∈ Ioc 0 R := ⟨hr1r2.trans h1.1, h2.2⟩
      exact Complex.abs_subintegral_le_abs_integral_of_abs_le hf hsub h1' h2' hconst
    · cases h1 hr1
    · cases h2 hr2R.le
    · cases h2 hr2R.le
  · -- Convexity of log I(r) in log r
    intro r1 r2 r3 hr1 hr1r2 hr2r3 hr3R
    simp only [I_fun]
    split_ifs with h1 h2 h3
    · have h1' : r1 ∈ Ioo 0 R := ⟨hr1, hr1r2.trans hr2r3.trans hr3R⟩
      have h2' : r2 ∈ Ioo 0 R := ⟨hr1r2.trans hr1, hr2r3.trans hr3R⟩
      have h3' : r3 ∈ Ioo 0 R := ⟨hr2r3.trans hr1r2.trans hr1, hr3R⟩
      let x1 := Real.log r1
      let x2 := Real.log r2
      let x3 := Real.log r3
      let y1 := Real.log (I r1)
      let y2 := Real.log (I r2)
      let y3 := Real.log (I r3)
      have hf' : DifferentiableOn ℂ f (ball (0 : ℂ) R) := hf
      have hconst' : ¬ ∀ z ∈ ball (0 : ℂ) R, f z = f 0 := hconst
      exact Complex.log_convex_of_abs_integral hf' hconst' h1' h2' h3'
    · cases h1 hr1
    · cases h2 (hr1r2.trans hr1)
    · cases h3 hr3R