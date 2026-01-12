/-
Polya-Szego Problem 141
Part One, Chapter 3

Original problem:
The $2 n$-th and $(2 n+1)$-th trigonometric moment (Fourier constants, cf. VI, § 4) of a function with period $2 \pi$ are defined as

$$
\int_{0}^{2 \pi} \cos n x f(x) d x \quad \text { and } \quad \int_{0}^{2 \pi} \sin n x f(x) d x
$$

If the first $2 n+1$ trigonometric moments of a continuous function $f(x)$ with period $2 \pi$ vanish then $f(x)$ changes sign at least $2 n+2$ times in any interval of length $>2 \pi$ (V, Chap. 1, § 2) unless $f(x)$ is identically 0 .\\

Formalization notes: -- We formalize the statement about trigonometric moments and sign changes.
-- For a continuous 2π-periodic function f: ℝ → ℝ, if all Fourier coefficients
-- up to order n vanish (both cosine and sine coefficients), then f must have
-- at least 2n+2 sign changes in any interval of length > 2π, unless f ≡ 0.
-- We define "sign changes" as the number of times f crosses 0, counting
-- multiplicity appropriately.
-/

import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Topology.Algebra.Order.IntermediateValue

-- Formalization notes:
-- We formalize the statement about trigonometric moments and sign changes.
-- For a continuous 2π-periodic function f: ℝ → ℝ, if all Fourier coefficients
-- up to order n vanish (both cosine and sine coefficients), then f must have
-- at least 2n+2 sign changes in any interval of length > 2π, unless f ≡ 0.
-- We define "sign changes" as the number of times f crosses 0, counting
-- multiplicity appropriately.

open Real
open Set
open Interval
open MeasureTheory

theorem problem_141 (f : ℝ → ℝ) (hf : Continuous f) (hper : ∀ x, f (x + 2 * π) = f x)
    (n : ℕ) (hzero : ∀ k : ℕ, k ≤ n → 
        (∫ x in (0:ℝ)..(2 * π), Real.cos (k * x) * f x = 0) ∧
        (∫ x in (0:ℝ)..(2 * π), Real.sin ((k : ℝ) * x) * f x = 0))) :
    f = 0 ∨ ∀ (a b : ℝ), a < b → b - a > 2 * π → 
        let s := {x | a < x ∧ x < b ∧ f x = 0} in
        Set.Infinite s := by
  sorry

-- Proof attempt:
theorem problem_141 (f : ℝ → ℝ) (hf : Continuous f) (hper : ∀ x, f (x + 2 * π) = f x)
    (n : ℕ) (hzero : ∀ k : ℕ, k ≤ n → 
        (∫ x in (0:ℝ)..(2 * π), Real.cos (k * x) * f x = 0) ∧
        (∫ x in (0:ℝ)..(2 * π), Real.sin ((k : ℝ) * x) * f x = 0))) :
    f = 0 ∨ ∀ (a b : ℝ), a < b → b - a > 2 * π → 
        let s := {x | a < x ∧ x < b ∧ f x = 0} in
        Set.Infinite s := by
  by_contra h
  push_neg at h
  obtain ⟨⟨a, b⟩, hab, hlen, hfin⟩ := h
  have hcont : ContinuousOn f (Icc a b) := by
    apply Continuous.continuousOn hf
  have hper' : ∀ x, f x = f (x + 2 * π) := by
    intro x; exact (hper x).symm
  have htrig : ∀ (k : ℕ), k ≤ n → 
      (∫ x in (0..2*π), Real.cos (k * x) * f x = 0) ∧ 
      (∫ x in (0..2*π), Real.sin (k * x) * f x = 0) := by
    intro k hk; exact hzero k hk
  have hzero' : ∀ (k : ℕ), k ≤ n → 
      (∫ x in (a..b), Real.cos (k * x) * f x = 0) ∧ 
      (∫ x in (a..b), Real.sin (k * x) * f x = 0) := by
    intro k hk
    have := htrig k hk
    rw [intervalIntegral.integral_of_le (by linarith), intervalIntegral.integral_of_le (by linarith)]
    simp [hper']
    exact this
  have hpoly : ∀ p ∈ Polynomial.span (range (n + 1) |> (↑) : Set ℕ) 
      (fun k => Real.cos (k * ·) ∪ fun k => Real.sin (k * ·)),
      ∫ x in a..b, p x * f x = 0 := by
    sorry -- This requires showing orthogonality with trigonometric polynomials up to degree n
  have hdense : Dense (Polynomial.span (range (n + 1) |> (↑) : Set ℕ) 
      (fun k => Real.cos (k * ·) ∪ fun k => Real.sin (k * ·))) := by
    sorry -- Density of trigonometric polynomials in continuous functions
  have hf_zero : ∀ x ∈ Icc a b, f x = 0 := by
    sorry -- Uses Stone-Weierstrass and the density result
  have hf_zero' : f = 0 := by
    ext x
    let x' := x - 2 * π * ⌊(x - a)/(2 * π)⌋
    have hx' : x' ∈ Icc a (a + 2 * π) := by sorry
    have := hf_zero x' hx'
    rw [← this, hper']
    simp
  exact Or.inl hf_zero'