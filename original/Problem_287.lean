/-
Polya-Szego Problem 287
Part Three, Chapter 6

Original problem:
We assume that the function $f(z)$ is regular, has positive real part for $|z|<1$ and that $f(0)$ is real. Then we have

$$
\begin{aligned}
f(0) \frac{1-|z|}{1+|z|} & \leqq \Re f(z) \leqq f(0) \frac{1+|z|}{1-|z|}, \quad|\Im f(z)| \leqq f(0) \frac{2|z|}{1-|z|^{2}} \\
& f(0) \frac{1-|z|}{1+|z|} \leqq|f(z)| \leqq f(0) \frac{1+|z|}{1-|z|}, \quad 0<|z|<1
\end{aligned}
$$

There is equality only if

$$
f(z)=w_{0} \frac{1+e^{i x} z}{1-e^{i x} z}, \quad \quad w_{0}, \alpha \text { real, } w_{0}>0
$$

\b

Formalization notes: -- We formalize Problem 287 and Problem 288 from Polya-Szego.
-- Problem 287: For f holomorphic on the unit disk with positive real part and f(0) real,
-- we have bounds on Re(f), Im(f), and |f|.
-- Problem 288: Special case when |Re(f)| < 1 and f(0) = 0, with stronger bounds.
-/

import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

-- Formalization notes:
-- We formalize Problem 287 and Problem 288 from Polya-Szego.
-- Problem 287: For f holomorphic on the unit disk with positive real part and f(0) real,
-- we have bounds on Re(f), Im(f), and |f|.
-- Problem 288: Special case when |Re(f)| < 1 and f(0) = 0, with stronger bounds.

open Complex
open Set
open Metric

-- Problem 287: Main inequalities for functions with positive real part
theorem problem_287 {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (hpos : ∀ z, ‖z‖ < 1 → 0 < re (f z)) (hreal : im (f 0) = 0) (hz : ℂ) (hz_mem : z ∈ ball (0 : ℂ) 1) :
    let r := ‖z‖ in
    let a := re (f 0) in
    a * (1 - r) / (1 + r) ≤ re (f z) ∧
    re (f z) ≤ a * (1 + r) / (1 - r) ∧
    |im (f z)| ≤ a * (2 * r) / (1 - r ^ 2) ∧
    a * (1 - r) / (1 + r) ≤ ‖f z‖ ∧
    ‖f z‖ ≤ a * (1 + r) / (1 - r) := by
  sorry

-- Problem 288: Special case with |Re(f)| < 1 and f(0) = 0
theorem problem_288 {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (hbounded : ∀ z, ‖z‖ < 1 → |re (f z)| < 1) (hzero : f 0 = 0) (hz : ℂ) (hz_mem : z ∈ ball (0 : ℂ) 1 \ {0}) :
    let r := ‖z‖ in
    |re (f z)| ≤ (4 / π) * Real.arctan r ∧
    |im (f z)| ≤ (2 / π) * Real.log ((1 + r) / (1 - r)) := by
  sorry

-- Problem 289: Oscillation bounds for functions on disks
theorem problem_289 {R r : ℝ} (hR_pos : 0 < R) (hr_nonneg : 0 ≤ r) (hr_lt : r < R)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (ball (0 : ℂ) R))
    (Δ : ℝ) (hΔ : ∀ z₁ z₂, ‖z₁‖ < R → ‖z₂‖ < R → |re (f z₁) - re (f z₂)| < Δ) :
    ∀ z₁ z₂, ‖z₁‖ ≤ r → ‖z₂‖ ≤ r →
      |re (f z₁) - re (f z₂)| ≤ (4 * Δ / π) * Real.arctan (r / R) ∧
      |im (f z₁) - im (f z₂)| ≤ (2 * Δ / π) * Real.log ((R + r) / (R - r)) := by
  sorry

-- Proof attempt:
theorem problem_287 {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (hpos : ∀ z, ‖z‖ < 1 → 0 < re (f z)) (hreal : im (f 0) = 0) (hz : ℂ) (hz_mem : z ∈ ball (0 : ℂ) 1) :
    let r := ‖z‖ in
    let a := re (f 0) in
    a * (1 - r) / (1 + r) ≤ re (f z) ∧
    re (f z) ≤ a * (1 + r) / (1 - r) ∧
    |im (f z)| ≤ a * (2 * r) / (1 - r ^ 2) ∧
    a * (1 - r) / (1 + r) ≤ ‖f z‖ ∧
    ‖f z‖ ≤ a * (1 + r) / (1 - r) := by
  let r := ‖z‖
  let a := re (f 0)
  have hr : r < 1 := by simpa using hz_mem
  have hr' : 0 ≤ r := norm_nonneg z
  have a_pos : 0 < a := hpos 0 (by simp [zero_lt_one])
  
  -- Apply the conformal mapping approach
  let φ : ℂ → ℂ := fun ζ => ζ
  let ψ : ℂ → ℂ := fun ζ => a * (1 + ζ) / (1 - ζ)
  
  -- Construct the composition g = ψ⁻¹ ∘ f ∘ φ
  let g : ℂ → ℂ := fun z => (f z - a) / (f z + a)
  
  have hg_diff : DifferentiableOn ℂ g (ball (0 : ℂ) 1) := by
    refine DifferentiableOn.div (hf.sub (differentiableOn_const _)) 
      (hf.add (differentiableOn_const _)) ?_
    intro z hz
    apply ne_of_gt
    rw [add_re, add_im, ← Complex.ext_iff]
    constructor
    · exact (hpos z hz).le
    · rw [add_im, (differentiableOn_const _).eqOn (by simp) hz |>.self_of_mem hz, zero_add]
  
  have hg_bounded : MapsTo g (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) := by
    intro z hz
    simp only [mem_ball_zero_iff, norm_lt_one_iff]
    have fz_pos : 0 < re (f z) := hpos z hz
    have fz_ne_neg_a : f z ≠ -a := by
      contrapose! fz_pos
      rw [fz_pos, neg_re]
      exact neg_lt_zero.mpr a_pos
    rw [← norm_lt_one_iff]
    refine lt_of_le_of_ne (norm_sub_le _ _) (ne_of_apply_ne norm ?_)
    simp [g, div_ne_zero (sub_ne_zero_of_ne (ne_of_gt fz_pos)) (add_ne_zero.mpr ⟨fz_ne_neg_a, rfl⟩)]
  
  have hg0 : g 0 = 0 := by
    simp [g, hreal, hzero]
    rw [← Complex.ext_iff]
    simp [hreal]
  
  -- Apply Schwarz lemma to g
  have hg_norm : ∀ z, ‖z‖ < 1 → ‖g z‖ ≤ ‖z‖ := by
    intro z hz
    apply DifferentiableOn.le_of_ball hg_diff hg_bounded hg0 z hz
  
  -- Now translate back to f
  have hf_expr : f z = a * (1 + g z) / (1 - g z) := by
    have : 1 - g z ≠ 0 := by
      contrapose! hr
      rw [norm_eq_zero] at hr
      have := hg_norm z hz_mem
      rw [hr] at this
      exact absurd (by simp [this]) zero_ne_one
    field_simp [g, this]
    ring
  
  -- Extract real and imaginary parts
  have re_fz : re (f z) = a * (1 - ‖g z‖^2) / ‖1 - g z‖^2 := by
    rw [hf_expr, div_re]
    simp only [one_re, one_im, mul_re, add_re, sub_re]
    rw [← norm_sq_eq_abs]
    ring_nf
    simp [norm_sq]
  
  have im_fz : im (f z) = a * (2 * im (g z)) / ‖1 - g z‖^2 := by
    rw [hf_expr, div_im]
    simp only [one_re, one_im, mul_im, add_im, sub_im]
    ring_nf
  
  -- Main inequalities
  have hg_norm' : ‖g z‖ ≤ r := hg_norm z hz_mem
  
  -- First inequality: lower bound on Re(f z)
  have h1 : a * (1 - r) / (1 + r) ≤ re (f z) := by
    rw [re_fz]
    have hdenom_pos : 0 < ‖1 - g z‖^2 := by positivity
    refine (div_le_div_of_le hdenom_pos ?_).trans (div_le_div_of_le_left ?_ hdenom_pos ?_)
    · refine le_trans ?_ (sub_le_sub_left (pow_le_pow_left (norm_nonneg _) hg_norm' 2) 1)
      rw [← mul_div_right_comm, ← mul_div_right_comm]
      refine mul_le_mul_of_nonneg_left ?_ a_pos.le
      rw [sub_le_sub_iff_left, ← mul_sub_one]
      refine mul_le_mul_of_nonneg_right ?_ (by linarith [hg_norm'])
      linarith [hg_norm']
    · positivity
    · rw [← norm_sub, norm_sub_rev]
      calc ‖1 - g z‖^2 ≤ (1 + ‖g z‖)^2 := by gcongr; apply norm_sub_le
      _ ≤ (1 + r)^2 := by gcongr
  
  -- Second inequality: upper bound on Re(f z)
  have h2 : re (f z) ≤ a * (1 + r) / (1 - r) := by
    rw [re_fz]
    refine (div_le_div_of_le (by positivity) ?_).trans ?_
    · refine le_trans (sub_le_sub_left (pow_le_pow_left (norm_nonneg _) hg_norm' 2) 1) ?_
      rw [← mul_div_right_comm, ← mul_div_right_comm]
      refine mul_le_mul_of_nonneg_left ?_ a_pos.le
      rw [sub_le_sub_iff_left, ← mul_add_one]
      refine mul_le_mul_of_nonneg_right ?_ (by linarith [hg_norm'])
      linarith [hg_norm']
    · rw [← norm_sub, norm_sub_rev]
      refine (pow_le_pow_left (norm_nonneg _) ?_ 2).trans ?_
      · exact norm_sub_le _ _
      · gcongr
        linarith [hg_norm']
  
  -- Third inequality: bound on Im(f z)
  have h3 : |im (f z)| ≤ a * (2 * r) / (1 - r ^ 2) := by
    rw [im_fz, abs_div, abs_mul, abs_of_nonneg (by positivity), abs_two]
    refine (div_le_div_of_le (by positivity) ?_).trans ?_
    · refine mul_le_mul_of_nonneg_left ?_ a_pos.le
      rw [mul_assoc]
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      exact (abs_im_le_abs (g z)).trans (hg_norm z hz_mem)
    · rw [← norm_sub, norm_sub_rev]
      refine (pow_le_pow_left (norm_nonneg _) ?_ 2).trans ?_
      · exact norm_sub_le _ _
      · have : ‖g z‖^2 ≤ r^2 := pow_le_pow_left (norm_nonneg _) hg_norm' 2
        linarith
  
  -- Fourth inequality: lower bound on |f z|
  have h4 : a * (1 - r) / (1 + r) ≤ ‖f z‖ := by
    refine le_trans ?_ (Complex.abs_re_le_abs (f z))
    exact h1
  
  -- Fifth inequality: upper bound on |f z|
  have h5 : ‖f z‖ ≤ a * (1 + r) / (1 - r) := by
    rw [hf_expr, norm_div, norm_mul]
    refine (div_le_div_of_le (norm_pos_iff.mpr ?_) ?_).trans ?_
    · exact sub_ne_zero_of_ne (ne_of_gt (norm_lt_one_iff.mpr (hg_norm z hz_mem)))
    · refine mul_le_mul_of_nonneg_left ?_ a_pos.le
      rw [norm_add, norm_one]
      exact add_le_add_left (hg_norm z hz_mem) _
    · refine div_le_div_of_le_left (by positivity) ?_ ?_
      · exact norm_sub_pos_iff.mpr (ne_of_gt (norm_lt_one_iff.mpr (hg_norm z hz_mem)))
      · rw [norm_sub, norm_one]
        exact le_sub_iff_add_le.mpr (add_le_add_right (hg_norm z hz_mem) _)
  
  exact ⟨h1, h2, h3, h4, h5⟩