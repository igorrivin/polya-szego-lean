/-
Polya-Szego Problem 298
Part Three, Chapter 6

Original problem:
We assume that the function $f(z)$ is regular and bounded in the half-plane $\Re z>0$ and vanishes at the points $z_{1}, z_{2}, z_{3}, \ldots$ outside the unit disk in the half-plane, i.e. $\left|z_{n}\right|>1, \Re z_{n}>0, n=1,2,3, \ldots$ Then the sum of the series

$$
\Re \frac{1}{z_{1}}+\Re \frac{1}{z_{2}}+\Re \frac{1}{z_{3}}+\cdots
$$

is finite or else $f(z) \equiv 0$.

\begin{enumerate}
  \setcounter{enumi}{298}
  \item The sum of the absolute values of several analytic functions attains

Formalization notes: -- We formalize the maximum principle for the sum of absolute values of analytic functions.
-- The theorem states that for analytic functions f₁,...,fₙ on a domain D, the function
-- φ(z) = ∑|fᵢ(z)| attains its maximum on the boundary ∂D, unless all fᵢ are constant.
-- We use `IsMaxOn` to express that the maximum is attained on the boundary.
-/

import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.HalfPlane

open Complex
open Set
open scoped ComplexConjugate

-- Formalization notes:
-- We formalize the maximum principle for the sum of absolute values of analytic functions.
-- The theorem states that for analytic functions f₁,...,fₙ on a domain D, the function
-- φ(z) = ∑|fᵢ(z)| attains its maximum on the boundary ∂D, unless all fᵢ are constant.
-- We use `IsMaxOn` to express that the maximum is attained on the boundary.

theorem problem_300 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {D : Set ℂ} (hD : IsOpen D) (hD_conn : IsConnected D) 
    {f : Fin n → ℂ → E} (hf : ∀ i, DifferentiableOn ℂ (f i) D) :
    let φ : ℂ → ℝ := fun z => ∑ i : Fin n, ‖f i z‖
    let boundary := frontier D
    IsMaxOn φ (closure D) boundary := by
  intro φ boundary
  sorry

-- Formalization notes for the stronger version (300 continued):
-- This states that if the maximum is attained in the interior, then all functions are constant.
-- We use `IsPreconnected` for the domain and `Set.interior` for the interior points.

theorem problem_300_continued {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {D : Set ℂ} (hD : IsOpen D) (hD_conn : IsPreconnected D)
    {f : Fin n → ℂ → E} (hf : ∀ i, DifferentiableOn ℂ (f i) D) :
    let φ : ℂ → ℝ := fun z => ∑ i : Fin n, ‖f i z‖
    let M := sSup (φ '' D)
    (∃ z ∈ interior D, φ z = M) → (∀ i, ∃ c : E, f i = Function.const ℂ c) := by
  intro φ M h
  sorry

-- Proof attempt:
theorem problem_300 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {D : Set ℂ} (hD : IsOpen D) (hD_conn : IsConnected D) 
    {f : Fin n → ℂ → E} (hf : ∀ i, DifferentiableOn ℂ (f i) D) :
    let φ : ℂ → ℝ := fun z => ∑ i : Fin n, ‖f i z‖
    let boundary := frontier D
    IsMaxOn φ (closure D) boundary := by
  intro φ boundary
  apply IsMaxOn.of_subset_closure
  · intro z hz
    have hφ : DifferentiableOn ℂ (fun w => ∑ i, ‖f i w‖) D := by
      intro w hw
      apply DifferentiableOn.sum
      intro i _
      exact (hf i).norm.differentiableAt hw |>.differentiableWithinAt
    exact Complex.norm_le_norm_of_isMaxOn hD hD_conn hφ hz
  · exact frontier_subset_closure