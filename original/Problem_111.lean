/-
Polya-Szego Problem 111
Part One, Chapter 3

Original problem:
If $f(x)$ an properly integrably\\

Formalization notes: -- We formalize: If f is analytic on a neighborhood of the closed disk |z| ≤ r,
-- and the image f(|z|=r) is star-shaped with respect to two points a and b,
-- then it is star-shaped with respect to any convex combination λa + μb.
-- The key condition is Re[z * f'(z) * conj(f(z) - w)] > 0 for w in the convex hull.
-/

import Mathlib.Analysis.Complex.Analytic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

-- Formalization notes:
-- We formalize: If f is analytic on a neighborhood of the closed disk |z| ≤ r,
-- and the image f(|z|=r) is star-shaped with respect to two points a and b,
-- then it is star-shaped with respect to any convex combination λa + μb.
-- The key condition is Re[z * f'(z) * conj(f(z) - w)] > 0 for w in the convex hull.

theorem problem_111 {f : ℂ → ℂ} {r : ℝ} (hr : 0 < r) 
    (hf : AnalyticOn ℂ f (Metric.closedBall (0 : ℂ) r)) :
    -- If f is analytic on closed disk of radius r
    let S := {w : ℂ | ∀ z : ℂ, Complex.abs z = r → 
      ∃ (t : ℝ) (ht : 0 ≤ t) (hz_diff : DifferentiableAt ℂ f z), 
      t * (z * deriv f z * conj (f z - w)).re > 0}
    -- S is the set of points w.r.t. which the image is star-shaped
    in Convex ℝ S := by
  -- The set S is convex
  sorry

-- Proof attempt:
intro w₁ w₂ hw₁ hw₂ λ μ hλ hμ hλμ
simp only [Set.mem_setOf_eq] at hw₁ hw₂ ⊢
intro z hz
obtain ⟨t₁, ht₁, hz_diff₁, h₁⟩ := hw₁ z hz
obtain ⟨t₂, ht₂, hz_diff₂, h₂⟩ := hw₂ z hz
have hz_diff : DifferentiableAt ℂ f z := hz_diff₁
use (λ * t₁ + μ * t₂)
constructor
· apply add_nonneg (mul_nonneg hλ ht₁) (mul_nonneg hμ ht₂)
· exact hz_diff
· have : conj (f z - (λ • w₁ + μ • w₂)) = λ • conj (f z - w₁) + μ • conj (f z - w₂) := by
    simp only [sub_add, sub_smul, smul_sub, ← Complex.conj_smul, Complex.conj_conj]
    ring_nf
  rw [this, ← mul_add, deriv f z, mul_assoc, mul_assoc, ← Complex.re_add]
  have h₁' := h₁
  have h₂' := h₂
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, neg_mul, sub_neg_eq_add] at h₁ h₂ ⊢
  rw [← mul_assoc, ← mul_assoc] at h₁ h₂ ⊢
  calc 
    (λ * t₁ + μ * t₂) * (z * deriv f z * (λ * conj (f z - w₁) + μ * conj (f z - w₂))).re
      = (λ * t₁ + μ * t₂) * (λ * (z * deriv f z * conj (f z - w₁)).re + μ * (z * deriv f z * conj (f z - w₂)).re) := by
        simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, neg_mul, sub_neg_eq_add]
        ring
    _ = λ * t₁ * (λ * (z * deriv f z * conj (f z - w₁)).re) + μ * t₂ * (μ * (z * deriv f z * conj (f z - w₂)).re)
          + λ * t₁ * (μ * (z * deriv f z * conj (f z - w₂)).re) + μ * t₂ * (λ * (z * deriv f z * conj (f z - w₁)).re) := by ring
    _ > 0 := by
      apply add_pos_of_pos_of_nonneg
      · apply add_pos_of_pos_of_nonneg
        · rw [mul_assoc, mul_assoc, ← mul_assoc λ t₁, mul_comm t₁ λ]
          rw [mul_assoc, mul_assoc]
          exact mul_pos (mul_pos hλ hλ) (mul_pos ht₁ h₁')
        · exact mul_nonneg (mul_nonneg hλ hμ) (mul_nonneg ht₁ h₂')
      · apply add_nonneg
        · exact mul_nonneg (mul_nonneg hμ hλ) (mul_nonneg ht₂ h₁')
        · rw [mul_assoc, mul_assoc, ← mul_assoc μ t₂, mul_comm t₂ μ]
          rw [mul_assoc, mul_assoc]
          exact mul_pos (mul_pos hμ hμ) (mul_pos ht₂ h₂')