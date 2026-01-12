/-
Polya-Szego Problem 94.2
Part One, Chapter 2

Original problem:
Let $E$ denote the area of the surface of an ellipsoid with semiaxes $a, b, c$ and prove that

$$
\frac{4 \pi(b c+c a+a b)}{3} \leqq E \leqq \frac{4 \pi\left(a^{2}+b^{2}+c^{2}\right)}{3} .
$$

[Derive, or take for granted, that

$$
E=\iint\left(b^{2} c^{2} \xi^{2}+c^{2} a^{2} \eta^{2}+a^{2} b^{2} \zeta^{2}\right)^{1 / 2} d \omega:
$$

the integration is extended over the surface of the unit sphere of which $(\xi, \eta, \zeta)$ is a point,

$$
\xi^{2}+\eta^{2}+\zeta^{2}=1
$$

and do the s\\
94.3 

Formalization notes: -- We formalize the inequality for the surface area E of an ellipsoid with semi-axes a, b, c > 0
-- The exact formula for E is given as an integral over the unit sphere S²
-- We assume a, b, c are positive real numbers
-- The theorem states: (4π/3)(bc + ca + ab) ≤ E ≤ (4π/3)(a² + b² + c²)
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Geometry.Manifold.Integral

open Real
open MeasureTheory
open Set

-- Formalization notes:
-- We formalize the inequality for the surface area E of an ellipsoid with semi-axes a, b, c > 0
-- The exact formula for E is given as an integral over the unit sphere S²
-- We assume a, b, c are positive real numbers
-- The theorem states: (4π/3)(bc + ca + ab) ≤ E ≤ (4π/3)(a² + b² + c²)

theorem ellipsoid_surface_area_inequality (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (4 * π / 3) * (b * c + c * a + a * b) ≤ 
    (∫∫ in (sphere (0 : ℝ × ℝ × ℝ) 1), 
      Real.sqrt ((b^2 * c^2) * ξ.1.1^2 + (c^2 * a^2) * ξ.1.2^2 + (a^2 * b^2) * ξ.2^2) ∂(surfaceMeasureOnSphere ℝ 2)) ∧
    (∫∫ in (sphere (0 : ℝ × ℝ × ℝ) 1), 
      Real.sqrt ((b^2 * c^2) * ξ.1.1^2 + (c^2 * a^2) * ξ.1.2^2 + (a^2 * b^2) * ξ.2^2) ∂(surfaceMeasureOnSphere ℝ 2)) ≤ 
    (4 * π / 3) * (a^2 + b^2 + c^2) := by
  sorry

-- Proof attempt:
theorem ellipsoid_surface_area_inequality (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (4 * π / 3) * (b * c + c * a + a * b) ≤ 
    (∫∫ in (sphere (0 : ℝ × ℝ × ℝ) 1), 
      Real.sqrt ((b^2 * c^2) * ξ.1.1^2 + (c^2 * a^2) * ξ.1.2^2 + (a^2 * b^2) * ξ.2^2) ∂(surfaceMeasureOnSphere ℝ 2)) ∧
    (∫∫ in (sphere (0 : ℝ × ℝ × ℝ) 1), 
      Real.sqrt ((b^2 * c^2) * ξ.1.1^2 + (c^2 * a^2) * ξ.1.2^2 + (a^2 * b^2) * ξ.2^2) ∂(surfaceMeasureOnSphere ℝ 2)) ≤ 
    (4 * π / 3) * (a^2 + b^2 + c^2) := by
  let E := ∫∫ in (sphere (0 : ℝ × ℝ × ℝ) 1), 
    Real.sqrt ((b^2 * c^2) * ξ.1.1^2 + (c^2 * a^2) * ξ.1.2^2 + (a^2 * b^2) * ξ.2^2) ∂(surfaceMeasureOnSphere ℝ 2)
  have h_sphere : ∫∫ in (sphere (0 : ℝ × ℝ × ℝ) 1), 1 ∂(surfaceMeasureOnSphere ℝ 2) = 4 * π := by
    simp [surfaceArea_sphere]
  have h_xi : ∫∫ in (sphere (0 : ℝ × ℝ × ℝ) 1), ξ.1.1^2 ∂(surfaceMeasureOnSphere ℝ 2) = 4 * π / 3 := by
    have := integral_sphere_symmetry (fun x => x.1.1^2) (by continuity)
    simp [this, h_sphere]
  have h_eta : ∫∫ in (sphere (0 : ℝ × ℝ × ℝ) 1), ξ.1.2^2 ∂(surfaceMeasureOnSphere ℝ 2) = 4 * π / 3 := by
    have := integral_sphere_symmetry (fun x => x.1.2^2) (by continuity)
    simp [this, h_sphere]
  have h_zeta : ∫∫ in (sphere (0 : ℝ × ℝ × ℝ) 1), ξ.2^2 ∂(surfaceMeasureOnSphere ℝ 2) = 4 * π / 3 := by
    have := integral_sphere_symmetry (fun x => x.2^2) (by continuity)
    simp [this, h_sphere]
  
  constructor
  · -- Lower bound
    have : ∀ x ∈ sphere (0 : ℝ × ℝ × ℝ) 1, 
      Real.sqrt ((b^2 * c^2) * x.1.1^2 + (c^2 * a^2) * x.1.2^2 + (a^2 * b^2) * x.2^2) ≥ 
      b * c * x.1.1^2 + c * a * x.1.2^2 + a * b * x.2^2 := by
      intro x hx
      simp [sphere_zero_one] at hx
      have := hx
      rw [← Real.sqrt_mul_self (b * c * x.1.1^2 + c * a * x.1.2^2 + a * b * x.2^2)]
      · apply Real.sqrt_le_sqrt
        rw [sq_sqrt (by positivity)]
        apply le_of_eq
        ring_nf
        rw [this]
        ring
      · positivity
    apply le_trans (integral_mono (by positivity) (by continuity) (by continuity) this)
    simp [h_xi, h_eta, h_zeta]
    ring
  · -- Upper bound
    have : ∀ x ∈ sphere (0 : ℝ × ℝ × ℝ) 1, 
      Real.sqrt ((b^2 * c^2) * x.1.1^2 + (c^2 * a^2) * x.1.2^2 + (a^2 * b^2) * x.2^2) ≤ 
      Real.sqrt (a^2 + b^2 + c^2) * Real.sqrt (x.1.1^2 + x.1.2^2 + x.2^2) := by
      intro x hx
      simp [sphere_zero_one] at hx
      rw [hx, Real.sqrt_one, mul_one]
      apply Real.sqrt_le_sqrt
      rw [← hx]
      apply le_of_eq
      ring
    apply le_trans (integral_mono (by positivity) (by continuity) (by continuity) this)
    simp [h_sphere]
    ring_nf
    rw [Real.sqrt_mul_self (by positivity)]
    ring