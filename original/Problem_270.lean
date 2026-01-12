/-
Polya-Szego Problem 270
Part Three, Chapter 6

Original problem:
Suppose that $f(z)$ is a polynomial of degree $n$ and that

$$
|f(z)| \leqq M
$$

on the real interval $-1 \leqq z \leqq 1$. Then we have

$$
|f(z)| \leqq M(a+b)^{n}
$$

for any $z$ outside this interval; $a$ and $b$ are the semi-axes of the ellipse through $z$ and with foci -1 and 1 . What does the proposition imply for $z \rightarrow \infty$ ?\\

Formalization notes: -- We formalize the key inequality |f(z)| ≤ M(a+b)^n for z outside [-1,1]
-- where a and b are semi-axes of the ellipse through z with foci at -1 and 1.
-- For the limit case z → ∞, we formalize the corollary about the leading coefficient.
-/

import Mathlib.Analysis.Complex.Polynomial
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.Convex.Complex
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Data.Complex.Basic

-- Formalization notes:
-- We formalize the key inequality |f(z)| ≤ M(a+b)^n for z outside [-1,1]
-- where a and b are semi-axes of the ellipse through z with foci at -1 and 1.
-- For the limit case z → ∞, we formalize the corollary about the leading coefficient.

open Complex
open Polynomial
open Set

/-- The ellipse with foci at -1 and 1 passing through z. -/
noncomputable def ellipseSemiAxes (z : ℂ) : ℝ × ℝ :=
  let r := Complex.abs (z + 1) + Complex.abs (z - 1)
  let a := r / 2
  let b := Real.sqrt ((r/2)^2 - 1)
  (a, b)

theorem problem_270_part1 {f : ℂ[X]} (hf : f.degree = f.natDegree) (hn : f.natDegree > 0) 
    (M : ℝ) (hM : 0 ≤ M) (h_bound : ∀ x : ℝ, -1 ≤ x → x ≤ 1 → ‖f.eval (x : ℂ)‖ ≤ M) :
    ∀ (z : ℂ), ‖z.re‖ > 1 → 
    let (a, b) := ellipseSemiAxes z
    ‖f.eval z‖ ≤ M * ((a + b) ^ f.natDegree) := by
  sorry

theorem problem_270_part2 {f : ℂ[X]} (hf : f.degree = f.natDegree) (hn : f.natDegree > 0) 
    (M : ℝ) (hM : 0 ≤ M) (h_bound : ∀ x : ℝ, -1 ≤ x → x ≤ 1 → ‖f.eval (x : ℂ)‖ ≤ M) :
    let leading_coeff := f.leadingCoeff
    ‖leading_coeff‖ ≤ M * (2 ^ f.natDegree) := by
  sorry

-- Alternative formulation focusing on the key inequality
theorem problem_270_inequality {f : ℂ[X]} (hdeg : f.natDegree = n) 
    (M : ℝ) (h_bound : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → ‖f.eval (x : ℂ)‖ ≤ M) 
    (z : ℂ) (hz : ‖z.re‖ > 1) :
    let r := Complex.abs (z + 1) + Complex.abs (z - 1)
    let a := r / 2
    let b := Real.sqrt ((r/2)^2 - 1)
    ‖f.eval z‖ ≤ M * ((a + b) ^ n) := by
  sorry

-- Corollary for z → ∞ (leading coefficient bound)
theorem problem_270_corollary {f : ℂ[X]} (hdeg : f.natDegree = n) (hn : n > 0)
    (M : ℝ) (h_bound : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → ‖f.eval (x : ℂ)‖ ≤ M) :
    ‖f.leadingCoeff‖ ≤ M * (2 ^ n) := by
  sorry

-- Proof attempt:
theorem problem_270_part1 {f : ℂ[X]} (hf : f.degree = f.natDegree) (hn : f.natDegree > 0) 
    (M : ℝ) (hM : 0 ≤ M) (h_bound : ∀ x : ℝ, -1 ≤ x → x ≤ 1 → ‖f.eval (x : ℂ)‖ ≤ M) :
    ∀ (z : ℂ), ‖z.re‖ > 1 → 
    let (a, b) := ellipseSemiAxes z
    ‖f.eval z‖ ≤ M * ((a + b) ^ f.natDegree) := by
  intro z hz
  let (a, b) := ellipseSemiAxes z
  let r := Complex.abs (z + 1) + Complex.abs (z - 1)
  have hr : r ≥ 2 := by
    have h1 : Complex.abs (z + 1) ≥ ‖(z + 1).re‖ := Complex.abs_re_le_abs _
    have h2 : Complex.abs (z - 1) ≥ ‖(z - 1).re‖ := Complex.abs_re_le_abs _
    rw [← Real.norm_eq_abs, ← Real.norm_eq_abs] at h1 h2
    have hz' : 1 < ‖z.re‖ := hz
    rw [add_re, one_re] at h1
    rw [sub_re, one_re] at h2
    linarith
  have hab : a = r / 2 ∧ b = Real.sqrt ((r/2)^2 - 1) := ⟨rfl, rfl⟩
  have hb_nonneg : 0 ≤ b := by rw [hab.2]; apply Real.sqrt_nonneg
  have hab_eq : a + b = (r + Real.sqrt (r^2 - 4)) / 2 := by
    rw [hab.1, hab.2]
    ring_nf
    rw [← Real.sqrt_mul (by linarith : 0 ≤ r^2 - 4) (1/4)]
    field_simp
    ring_nf
  -- Key Bernstein-Riesz inequality
  have main_ineq : ‖f.eval z‖ ≤ M * (a + b) ^ f.natDegree := by
    sorry -- This would require the full Bernstein-Riesz proof
  exact main_ineq

theorem problem_270_part2 {f : ℂ[X]} (hf : f.degree = f.natDegree) (hn : f.natDegree > 0) 
    (M : ℝ) (hM : 0 ≤ M) (h_bound : ∀ x : ℝ, -1 ≤ x → x ≤ 1 → ‖f.eval (x : ℂ)‖ ≤ M) :
    let leading_coeff := f.leadingCoeff
    ‖leading_coeff‖ ≤ M * (2 ^ f.natDegree) := by
  let n := f.natDegree
  let c := f.leadingCoeff
  -- Take limit as z → ∞
  have lim : Filter.Tendsto (fun z : ℂ => ‖f.eval z‖ / ‖z‖ ^ n) Filter.atTop (𝓝 ‖c‖) := by
    convert Polynomial.tendsto_norm_atTop_div_norm_atTop_pow f hn
    simp [leadingCoeff]
  -- For large z, apply part1 and take limit
  have h : ∀ᶠ z in Filter.atTop, ‖f.eval z‖ ≤ M * (2 ^ n) * ‖z‖ ^ n := by
    refine Filter.eventually_atTop.2 ⟨1, fun z hz => ?_⟩
    have hz' : ‖z.re‖ > 1 := by
      have : ‖z‖ ≥ ‖z.re‖ := Complex.norm_re_le_norm z
      linarith
    let (a, b) := ellipseSemiAxes z
    have hab : a + b ≤ ‖z‖ + 1 := by
      calc a + b = (Complex.abs (z + 1) + Complex.abs (z - 1)) / 2 + Real.sqrt _ := by
          simp [ellipseSemiAxes]
      _ ≤ (‖z‖ + 1 + ‖z‖ + 1) / 2 + Real.sqrt _ := by gcongr; simp [Complex.norm_add_le]
      _ ≤ ‖z‖ + 1 + Real.sqrt ((‖z‖ + 1)^2 - 1) := by ring_nf; gcongr
      _ ≤ ‖z‖ + 1 + (‖z‖ + 1) := by
          gcongr
          apply Real.sqrt_le_le'
          nlinarith
      _ = 2 * ‖z‖ + 2 := by ring
      _ ≤ 2 * ‖z‖ + 2 * ‖z‖ := by gcongr; linarith [hz]
      _ = 4 * ‖z‖ := by ring
    have := problem_270_part1 hf hn M hM h_bound z hz'
    refine le_trans this ?_
    gcongr
    refine le_trans hab ?_
    have : ‖z‖ ≥ 1 := by linarith
    nlinarith
  have lim' : Filter.Tendsto (fun z => M * (2 ^ n)) Filter.atTop (𝓝 (M * (2 ^ n))) :=
    Filter.Tendsto.const_mul _ (Filter.tendsto_const_nhds)
  convert le_of_tendsto_of_tendsto' lim lim' h
  simp [mul_comm]

theorem problem_270_inequality {f : ℂ[X]} (hdeg : f.natDegree = n) 
    (M : ℝ) (h_bound : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → ‖f.eval (x : ℂ)‖ ≤ M) 
    (z : ℂ) (hz : ‖z.re‖ > 1) :
    let r := Complex.abs (z + 1) + Complex.abs (z - 1)
    let a := r / 2
    let b := Real.sqrt ((r/2)^2 - 1)
    ‖f.eval z‖ ≤ M * ((a + b) ^ n) := by
  have hf : f.degree = f.natDegree := Polynomial.degree_eq_natDegree (by rw [hdeg]; exact Nat.pos_of_ne_zero (by intro h; rw [h] at hn; exact hn rfl))
  exact problem_270_part1 hf (by rw [hdeg]; exact hn) M (by linarith [h_bound 0 (by simp) (by simp)]) h_bound z hz

theorem problem_270_corollary {f : ℂ[X]} (hdeg : f.natDegree = n) (hn : n > 0)
    (M : ℝ) (h_bound : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → ‖f.eval (x : ℂ)‖ ≤ M) :
    ‖f.leadingCoeff‖ ≤ M * (2 ^ n) := by
  have hf : f.degree = f.natDegree := Polynomial.degree_eq_natDegree (by rw [hdeg]; exact hn)
  exact problem_270_part2 hf hn M (by linarith [h_bound 0 (by simp) (by simp)]) h_bound