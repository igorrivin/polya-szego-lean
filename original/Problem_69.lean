/-
Polya-Szego Problem 69
Part One, Chapter 2

Original problem:
Let the function $f(x)$ be defined and properly integrable on the interval $\left[x_{1}, x_{2}\right]$ and let $f(x)$ have a positive lower bound. Then

$$
\frac{x_{2}-x_{1}}{\int_{x_{1}}^{x_{2}} \frac{d x}{f(x)}} \leqq e^{\frac{1}{x_{2}-x_{1}}} \int_{x_{1}}^{x_{2}} \log f(x) d x . \frac{1}{x_{2}-x_{1}} \int_{x_{1}}^{x_{2}} f(x) d x
$$

or, with the notation just defined,

$$
\mathfrak{H}(f) \leqq \mathfrak{G}(f) \leqq \mathfrak{U}(f) .
$$

\begin{enumerate}
  \setcounter{enumi}{69}
  \item Supp

Formalization notes: -- We formalize the result about convex functions: 
-- For a mid-point convex function φ (strictly or non-strictly), 
-- we get the general arithmetic mean inequality for n points.
-- We capture both strict (<) and non-strict (≤) versions.
-- The theorem assumes φ : ℝ → ℝ, though the interval could be generalized.
-/

-- Imports for convex functions and inequalities
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.SpecificFunctions
import Mathlib.Data.Real.Basic

-- Formalization notes:
-- We formalize the result about convex functions: 
-- For a mid-point convex function φ (strictly or non-strictly), 
-- we get the general arithmetic mean inequality for n points.
-- We capture both strict (<) and non-strict (≤) versions.
-- The theorem assumes φ : ℝ → ℝ, though the interval could be generalized.

theorem problem_70_strict_convex (φ : ℝ → ℝ) 
    (hconvex_strict : ∀ (t₁ t₂ : ℝ), t₁ ≠ t₂ → φ ((t₁ + t₂) / 2) < (φ t₁ + φ t₂) / 2)
    (t : Fin n → ℝ) (hne : ∃ i j, i ≠ j ∧ t i ≠ t j) :
    φ ((∑ i, t i) / n) < (∑ i, φ (t i)) / n := by
  sorry

theorem problem_70_convex {m M : ℝ} (hmM : m ≤ M) (φ : ℝ → ℝ)
    (hconvex : ∀ (t₁ t₂ : ℝ), m ≤ t₁ → t₁ ≤ M → m ≤ t₂ → t₂ ≤ M → t₁ ≠ t₂ → 
        φ ((t₁ + t₂) / 2) ≤ (φ t₁ + φ t₂) / 2)
    (t : Fin n → ℝ) (ht : ∀ i, m ≤ t i ∧ t i ≤ M) :
    φ ((∑ i, t i) / n) ≤ (∑ i, φ (t i)) / n := by
  sorry

-- Proof attempt:
theorem problem_70_strict_convex (φ : ℝ → ℝ) 
    (hconvex_strict : ∀ (t₁ t₂ : ℝ), t₁ ≠ t₂ → φ ((t₁ + t₂) / 2) < (φ t₁ + φ t₂) / 2)
    (t : Fin n → ℝ) (hne : ∃ i j, i ≠ j ∧ t i ≠ t j) :
    φ ((∑ i, t i) / n) < (∑ i, φ (t i)) / n := by
  have : StrictConvexOn ℝ Set.univ φ := by
    refine strictConvexOn_univ_of_midpoint_strict φ fun x y hxy => ?_
    exact hconvex_strict x y hxy
  exact StrictConvexOn.map_average_lt this t hne