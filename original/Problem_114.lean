/-
Polya-Szego Problem 114
Part Three, Chapter 3

Original problem:
The function $w=\log (1+z)$ maps the disk $|z|=1$ onto an infinite domain contained in the strip $-\frac{\pi}{2}<\Im w<\frac{\pi}{2}$. Its support function (defined only for $-\frac{\pi}{2} \leqq \varphi \leqq \frac{\pi}{2}$ ) is

$$
h(\varphi)=\cos \varphi \cdot \log (2 \cos \varphi)+\varphi \sin \varphi .
$$

\begin{enumerate}
  \setcounter{enumi}{114}
  \item The function $w=\frac{2}{i} \arcsin i z$ maps the disk $|z| \leqq 1$ onto a finite convex domain which has two corners and lies in the 

Formalization notes: We formalize the statement that the function f(z) = (2/i) * arcsin(i*z) maps the closed unit disk
to a convex domain contained in the horizontal strip -π ≤ Im(w) ≤ π.
-/

import Mathlib.Analysis.Complex.Conformal
import Mathlib.Analysis.Convex.Support
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arcsine

/-!
Formalization notes:
We formalize the statement that the function f(z) = (2/i) * arcsin(i*z) maps the closed unit disk
to a convex domain contained in the horizontal strip -π ≤ Im(w) ≤ π.

Key components:
1. f : ℂ → ℂ is defined as f(z) = (2/i) * Complex.arcsin (i * z)
2. The image of the closed unit disk under f is convex
3. The image is contained in the strip {w | -π ≤ w.im ∧ w.im ≤ π}
4. The boundary of this image has two corners (points of non-differentiability)

Note: We use `SetLike` notation for the unit disk and strip.
-/

open Complex Set
open scoped ComplexConjugate

noncomputable section

theorem problem_114_mapping_properties :
    let f : ℂ → ℂ := fun z => (2 / I) * arcsin (I * z)
    let unitDisk : Set ℂ := {z | ‖z‖ ≤ 1}
    let horizontalStrip : Set ℂ := {w | -π ≤ w.im ∧ w.im ≤ π}
    Convex ℝ (f '' unitDisk) ∧ f '' unitDisk ⊆ horizontalStrip := by
  sorry

/-!
Additional formalization for the support function aspect:
The problem mentions that for certain φ, the support function equals that of the point πi.
We formalize this relationship for the relevant sector.
-/

theorem problem_114_support_function :
    let f : ℂ → ℂ := fun z => (2 / I) * arcsin (I * z)
    let unitDisk : Set ℂ := {z | ‖z‖ ≤ 1}
    let D := f '' unitDisk
    let h_D : ℝ → ℝ := fun φ => sInf {r | ∀ w ∈ D, re (w * exp (-I * φ)) ≤ r}
    let h_point : ℝ → ℝ := fun φ => re ((π * I) * exp (-I * φ))
    ∀ φ, π/4 ≤ φ ∧ φ ≤ 3*π/4 → h_D φ = h_point φ := by
  sorry

-- Proof attempt:
theorem problem_114_mapping_properties :
    let f : ℂ → ℂ := fun z => (2 / I) * arcsin (I * z)
    let unitDisk : Set ℂ := {z | ‖z‖ ≤ 1}
    let horizontalStrip : Set ℂ := {w | -π ≤ w.im ∧ w.im ≤ π}
    Convex ℝ (f '' unitDisk) ∧ f '' unitDisk ⊆ horizontalStrip := by
  intro f unitDisk horizontalStrip
  constructor
  · -- First prove the image is convex
    apply Convex.is_linear_image
    · show IsLinearMap ℂ f
      refine' ⟨fun z w => by simp [f, mul_add, add_mul], fun c z => by simp [f, mul_assoc]⟩
    · exact convex_unit_ball
  · -- Then prove the image is contained in the horizontal strip
    intro w hw
    obtain ⟨z, hz, rfl⟩ := hw
    simp [f, norm_eq_abs] at hz
    have h_arcsin_bounds : -π/2 ≤ (arcsin (I * z)).re ∧ (arcsin (I * z)).re ≤ π/2 := by
      apply arcsin_re_le_pi_div_two
      apply neg_pi_div_two_le_arcsin_re
      rw [← norm_eq_abs, ← norm_mul]
      simp [norm_eq_abs, hz]
    simp [horizontalStrip, mul_comm (2 / I), ← mul_assoc]
    have : (2 / I * arcsin (I * z)).im = 2 * (arcsin (I * z)).re := by
      rw [mul_comm, ← re_ofReal_mul_I]
      simp [ofReal_mul_re, ofReal_mul_im, mul_comm]
    rw [this]
    constructor
    · linarith [h_arcsin_bounds.1]
    · linarith [h_arcsin_bounds.2]