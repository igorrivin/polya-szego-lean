/-
Polya-Szego Problem 108
Part One, Chapter 3

Original problem:
If $j(x)$ is p\\
(x) are every wh\\

Formalization notes: -- This formalizes a typical problem from Polya-Szego Chapter 3 on power series.
-- We formalize: If a power series converges absolutely at a point on its boundary,
-- then it converges uniformly on the closed disk up to that boundary point.
-- This is a reasonable interpretation of what might appear as Problem 108
-- based on the context of problems 106-107.
-/

-- Imports for analysis: Real numbers, power series, and sequences
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Complex.Exponential

-- Formalization notes: 
-- This formalizes a typical problem from Polya-Szego Chapter 3 on power series.
-- We formalize: If a power series converges absolutely at a point on its boundary,
-- then it converges uniformly on the closed disk up to that boundary point.
-- This is a reasonable interpretation of what might appear as Problem 108
-- based on the context of problems 106-107.

open Complex
open scoped ComplexConjugate

theorem problem_108 :
    -- For a formal power series f centered at 0 with complex coefficients
    ∀ (f : ℂ → ℂ) (R : ℝ) (z₀ : ℂ), 
    -- Positive radius of convergence
    0 < R → 
    -- z₀ is on the boundary (|z₀| = R)
    Complex.abs z₀ = R →
    -- The power series converges absolutely at z₀
    (Summable fun (n : ℕ) => Complex.abs (f.coeff n * z₀^n)) →
    -- Then it converges uniformly on the closed ball of radius R
    ∀ (ε : ℝ), 0 < ε → 
    ∃ (N : ℕ), ∀ (n ≥ N) (z : ℂ), Complex.abs z ≤ R → 
    Complex.abs (∑ k in Finset.range n, f.coeff k * z^k - ∑ k in Finset.range n, f.coeff k * z₀^k) < ε := by
  sorry

-- Proof attempt:
theorem problem_108 :
    ∀ (f : ℂ → ℂ) (R : ℝ) (z₀ : ℂ), 
    0 < R → 
    Complex.abs z₀ = R →
    (Summable fun (n : ℕ) => Complex.abs (f.coeff n * z₀^n)) →
    ∀ (ε : ℝ), 0 < ε → 
    ∃ (N : ℕ), ∀ (n ≥ N) (z : ℂ), Complex.abs z ≤ R → 
    Complex.abs (∑ k in Finset.range n, f.coeff k * z^k - ∑ k in Finset.range n, f.coeff k * z₀^k) < ε := by
  intro f R z₀ hR hz₀ hsum ε hε
  -- First show the tail of the series is uniformly small
  have hCauchy := Summable.cauchy_summable (fun n => Complex.abs (f.coeff n * z₀^n)) hsum
  rw [Metric.cauchySeq_iff] at hCauchy
  specialize hCauchy ε hε
  obtain ⟨N, hN⟩ := hCauchy
  use N
  intro n hn z hz
  -- Rewrite the difference of partial sums as a single sum
  simp only [Finset.sum_sub_distrib]
  rw [← Finset.sum_sub_distrib]
  -- Apply triangle inequality to the sum
  have hbound : Complex.abs (∑ k in Finset.range n, f.coeff k * (z^k - z₀^k)) ≤ 
                 ∑ k in Finset.range n, Complex.abs (f.coeff k * (z^k - z₀^k)) := by
    exact Complex.abs.sum_le_sum _ _
  -- Show each term is bounded by |f.coeff k| * |z₀^k|
  have hterm : ∀ k, Complex.abs (f.coeff k * (z^k - z₀^k)) ≤ 
                Complex.abs (f.coeff k * z₀^k) := by
    intro k
    rw [Complex.abs_mul, Complex.abs_mul]
    refine mul_le_mul le_rfl ?_ (Complex.abs.nonneg _) (Complex.abs.nonneg _)
    have hzk : Complex.abs z ≤ Complex.abs z₀ := by rw [hz₀]; exact hz
    exact Complex.abs_pow_le_pow_abs_of_abs_le hzk k
  -- Combine the bounds
  refine lt_of_le_of_lt hbound ?_
  refine lt_of_le_of_lt (Finset.sum_le_sum fun k _ => hterm k) ?_
  -- Now use the Cauchy condition
  specialize hN n N hn (le_refl N)
  simp only [dist_eq_norm, norm_eq_abs, sub_zero] at hN
  exact hN