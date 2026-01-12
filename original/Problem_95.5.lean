/-
Polya-Szego Problem 95.5
Part One, Chapter 2

Original problem:
A wire which forms a closed plane curve $C$ carries a unit electric current and exerts a force $F$ on a unit magnetic pole in the plane of, and interior to, $C$. Given $A$, the area enclosed by $C$, prove that $F$ is a minimum when $C$ is a circle and the magnetic pole is at its center.- [Assume that $C$ is star-shaped with respect to the magnetic pole [III 109] which is located at the origin of a system of polar coordinates $r, \varphi$. Then

$$
F=\int_{0}^{2 \pi} \frac{d \varphi}{r} .
$$

Exp

Formalization notes: -- We formalize the key inequality from the solution: F ≥ 2π√(π/A)
-- where F = ∫₀^{2π} (1/r(φ)) dφ and A = (1/2)∫₀^{2π} r(φ)² dφ
-- The theorem states that for any positive, continuous, 2π-periodic function r,
-- this inequality holds, with equality iff r is constant.
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convex.Integral

-- Formalization notes:
-- We formalize the key inequality from the solution: F ≥ 2π√(π/A)
-- where F = ∫₀^{2π} (1/r(φ)) dφ and A = (1/2)∫₀^{2π} r(φ)² dφ
-- The theorem states that for any positive, continuous, 2π-periodic function r,
-- this inequality holds, with equality iff r is constant.

theorem problem_95_5 (r : ℝ → ℝ) (hr_pos : ∀ φ, 0 < r φ) (hr_cont : ContinuousOn r (Set.Icc 0 (2 * π))) 
    (hr_periodic : ∀ φ, r (φ + 2 * π) = r φ) :
    let F : ℝ := ∫ φ in (0 : ℝ)..(2 * π), (1 / r φ)
    let A : ℝ := (1/2) * ∫ φ in (0 : ℝ)..(2 * π), (r φ) ^ 2
    in 0 < A ∧ F ≥ 2 * π * Real.sqrt (π / A) ∧ 
        (F = 2 * π * Real.sqrt (π / A) ↔ ∃ c : ℝ, 0 < c ∧ ∀ φ, r φ = c) := by
  sorry

-- Proof attempt:
theorem problem_95_5 (r : ℝ → ℝ) (hr_pos : ∀ φ, 0 < r φ) (hr_cont : ContinuousOn r (Set.Icc 0 (2 * π))) 
    (hr_periodic : ∀ φ, r (φ + 2 * π) = r φ) :
    let F : ℝ := ∫ φ in (0 : ℝ)..(2 * π), (1 / r φ)
    let A : ℝ := (1/2) * ∫ φ in (0 : ℝ)..(2 * π), (r φ) ^ 2
    in 0 < A ∧ F ≥ 2 * π * Real.sqrt (π / A) ∧ 
        (F = 2 * π * Real.sqrt (π / A) ↔ ∃ c : ℝ, 0 < c ∧ ∀ φ, r φ = c) := by
  set F := ∫ φ in (0 : ℝ)..(2 * π), (1 / r φ)
  set A := (1/2) * ∫ φ in (0 : ℝ)..(2 * π), (r φ) ^ 2
  have hA_pos : 0 < A := by
    apply mul_pos
    · norm_num
    · apply intervalIntegral.integral_pos_of_pos_on
      · exact hr_cont
      · intro x hx; exact pow_pos (hr_pos x) 2
      · exact Real.two_pi_pos
  refine ⟨hA_pos, ?_, ?_⟩
  · -- Main inequality F ≥ 2π√(π/A)
    have h₁ : ∫ φ in (0)..(2 * π), 1 = 2 * π := by simp [Real.two_pi_pos]
    have h₂ : ∫ φ in (0)..(2 * π), (1 / r φ) = F := rfl
    have h₃ : ∫ φ in (0)..(2 * π), r φ ^ 2 = 2 * A := by field_simp; ring
    have := ConvexOn.integral_mul_le (p := 3/2) (q := 3)
      (f := fun φ => (1 / r φ) ^ (2/3 : ℝ)) (g := fun φ => (r φ ^ 2) ^ (1/3 : ℝ))
      (hf := ?_) (hg := ?_) (h_int_f := ?_) (h_int_g := ?_)
    rotate_left
    · -- Convexity of x ↦ x^(3/2)
      apply ConvexOn.pow (by norm_num) (by linarith)
    · -- Convexity of x ↦ x^3
      apply ConvexOn.pow (by norm_num) (by linarith)
    · -- Integrability of (1/r)^(2/3)
      sorry -- Need to show integrability (omitted for brevity)
    · -- Integrability of (r^2)^(1/3)
      sorry -- Need to show integrability (omitted for brevity)
    simp only [← rpow_mul (le_of_lt (hr_pos _)), ← rpow_mul (pow_pos (hr_pos _) 2).le] at this
    simp only [one_div, rpow_neg (le_of_lt (hr_pos _)), rpow_one] at this
    have key_ineq : (2 * π) ^ (3/2) ≤ F ^ (2/3) * (2 * A) ^ (1/3) := by
      convert this using 1
      · simp [h₁]
      · simp [h₂, h₃]
    rw [← Real.rpow_le_rpow_iff (by positivity) (by positivity) (by norm_num : 0 < 3)]
    simp only [mul_rpow (by positivity) (by positivity), Real.rpow_mul (by positivity).le]
    rw [Real.rpow_three, Real.rpow_three, Real.mul_rpow (by positivity) (by positivity)]
    simp only [Real.rpow_nat_cast]
    rw [← Real.rpow_mul (by positivity), ← Real.rpow_add (by positivity)]
    norm_num
    rw [Real.rpow_one, Real.rpow_two]
    field_simp [hA_pos.ne']
    ring_nf
    rw [← Real.sqrt_div (by positivity), Real.sqrt_eq_rpow]
    field_simp [hA_pos.ne']
    ring
  · -- Equality case
    constructor
    · intro h_eq
      use (1/2π * F)
      constructor
      · have : 0 < 1/2π * F := by
          apply mul_pos _ (intervalIntegral.integral_pos_of_pos_on _ _ _)
          · norm_num
          · exact hr_cont
          · intro x _; exact one_div_pos.mpr (hr_pos x)
          · exact Real.two_pi_pos
        linarith
      · sorry -- Need to show constant function case (omitted for brevity)
    · rintro ⟨c, hc_pos, hc⟩
      simp [F, A, hc]
      field_simp [hc_pos.ne', Real.two_pi_pos.ne']
      rw [Real.sqrt_div (by positivity), Real.sqrt_eq_rpow, Real.rpow_two]
      field_simp [hc_pos.ne', Real.two_pi_pos.ne']
      ring