/-
Polya-Szego Problem 135
Part One, Chapter 3

Original problem:
Every function defined and continuous on the finite interval $[a, b]$ can be approximated uniformly on $[a, b]$ by polynomials to any degree of accuracy. (Weierstrass' approximation theorem.)\\

Formalization notes: -- 1. We formalize the Weierstrass approximation theorem for continuous functions on [a, b]
-- 2. We use `ContinuousMap` to represent continuous functions on `Set.Icc a b`
-- 3. The theorem states that for any ε > 0, there exists a polynomial p such that
--    for all x in [a, b], |f x - p x| < ε
-- 4. This is the uniform approximation version using the sup norm
-- 5. We use `Polynomial ℝ` for real polynomials
-/

import Mathlib.Analysis.SpecialFunctions.Polynomials
import Mathlib.Analysis.Weierstrass.Approximation
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.ContinuousFunction.Algebra
import Mathlib.Topology.ContinuousFunction.Weierstrass

-- Formalization notes:
-- 1. We formalize the Weierstrass approximation theorem for continuous functions on [a, b]
-- 2. We use `ContinuousMap` to represent continuous functions on `Set.Icc a b`
-- 3. The theorem states that for any ε > 0, there exists a polynomial p such that
--    for all x in [a, b], |f x - p x| < ε
-- 4. This is the uniform approximation version using the sup norm
-- 5. We use `Polynomial ℝ` for real polynomials

theorem problem_135 (a b : ℝ) (hab : a ≤ b) (f : C(Set.Icc a b, ℝ)) (ε : ℝ) (hε : 0 < ε) :
    ∃ p : Polynomial ℝ, ∀ x ∈ Set.Icc a b, ‖f x - p.eval x‖ < ε := by
  -- This follows directly from `ContinuousMap.exists_polynomial_approx_of_compact`
  -- or `PolynomialFunctions.stoneWeierstrass` in Mathlib
  exact ContinuousMap.exists_polynomial_approx_of_compact (by
    intro x hx
    exact ⟨x, hx, rfl⟩) f hε

-- Proof attempt:
theorem problem_135 (a b : ℝ) (hab : a ≤ b) (f : C(Set.Icc a b, ℝ)) (ε : ℝ) (hε : 0 < ε) :
    ∃ p : Polynomial ℝ, ∀ x ∈ Set.Icc a b, ‖f x - p.eval x‖ < ε := by
  exact ContinuousMap.exists_polynomial_approx_of_compact (by
    intro x hx
    exact ⟨x, hx, rfl⟩) f hε