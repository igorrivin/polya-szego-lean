/-
Polya-Szego Problem 136
Part One, Chapter 3

Original problem:
Every continuous function that is periodic with period $2 \pi$ can be uniformly approximated by trigonometric polynomials [VI, § 2] to any assigned degree of accuracy. (Weierstrass' approximation theorem.)\\

Formalization notes: -- We formalize Weierstrass' trigonometric approximation theorem for continuous
-- periodic functions on ℝ with period 2π. The theorem states that such functions
-- can be uniformly approximated by trigonometric polynomials.
-- We use `AddCircle (2 * π)` to represent ℝ/(2πℤ), the circle of circumference 2π.
-- `TrigonometricPolynomial f` means f is a finite linear combination of
-- functions x ↦ cos(n*x) and x ↦ sin(n*x) for n ∈ ℕ.
-/

import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.InnerProductSpace.L2Space
import Mathlib.MeasureTheory.Integral.Periodic
import Mathlib.Topology.ContinuousFunction.Algebra

-- Formalization notes:
-- We formalize Weierstrass' trigonometric approximation theorem for continuous
-- periodic functions on ℝ with period 2π. The theorem states that such functions
-- can be uniformly approximated by trigonometric polynomials.
-- We use `AddCircle (2 * π)` to represent ℝ/(2πℤ), the circle of circumference 2π.
-- `TrigonometricPolynomial f` means f is a finite linear combination of
-- functions x ↦ cos(n*x) and x ↦ sin(n*x) for n ∈ ℕ.

open Real
open Complex
open Set
open Filter
open scoped Real
open scoped BigOperators

theorem weierstrass_trig_approx (f : C(AddCircle (2 * π), ℂ)) (ε : ℝ) (hε : ε > 0) :
    ∃ (P : C(AddCircle (2 * π), ℂ)) (_ : TrigonometricPolynomial P), 
    ∀ (x : AddCircle (2 * π)), ‖f x - P x‖ ≤ ε := by
  sorry

-- Proof attempt:
theorem weierstrass_trig_approx (f : C(AddCircle (2 * π), ℂ)) (ε : ℝ) (hε : ε > 0) :
    ∃ (P : C(AddCircle (2 * π), ℂ)) (_ : TrigonometricPolynomial P), 
    ∀ (x : AddCircle (2 * π)), ‖f x - P x‖ ≤ ε := by
  -- The trigonometric polynomials form a subalgebra of C(AddCircle (2 * π), ℂ)
  have subalg : Subalgebra ℂ C(AddCircle (2 * π), ℂ) := 
    TrigonometricPolynomial.subalgebra
  -- This subalgebra separates points
  have separates : Subalgebra.SeparatesPoints ℂ subalg :=
    TrigonometricPolynomial.subalgebra_separatesPoints
  -- It contains the constant functions
  have const : (algebraMap ℂ C(AddCircle (2 * π), ℂ)) '' Set.univ ⊆ subalg := by
    simp [TrigonometricPolynomial.algebraMap_mem]
  -- Apply the complex version of Stone-Weierstrass theorem
  refine StoneWeierstrass.exists_mem_subalgebra_norm_lt 
    (isCompact_univ : IsCompact (Set.univ : Set (AddCircle (2 * π)))) 
    subalg separates const f hε