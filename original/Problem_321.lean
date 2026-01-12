/-
Polya-Szego Problem 321
Part Three, Chapter 6

Original problem:
Deduce Hadamard's three circle theorem 304 from 320 and vice versa $\mathbf{3 2 0}$ from Hadamard's three circle theorem.

\begin{enumerate}
  \setcounter{enumi}{321}
  \item Let $\alpha$ be given, $0<\alpha<\frac{\pi}{2}$. The function $f(z)$ is assumed to be regular in the sector $-\alpha \leqq \vartheta \leqq \alpha\left(z=r e^{i \vartheta}\right)$. In addition $f(z)$ has the\\
following propert\\
(1) there exis\\
(2)\\
(i.e. on the bour $|f(z)| \leqq 1$ holds ii
\end{enumerate}

Proof: Let i

Formalization notes: We formalize Problem 321 from Polya-Szego:
Let α ∈ (0, π/2). Suppose f is analytic in the sector S = {z | arg z ∈ [-α, α]} 
and satisfies:
1. ∃ A, B > 0 such that ∀ z ∈ S, |f(z)| < A * exp(B * |z|)
2. On the boundary rays (arg z = ±α), |f(z)| ≤ 1
Then ∀ z ∈ S, |f(z)| ≤ 1.
-/

import Mathlib.Analysis.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.Complex.PhragmenLindelof

/-!
Formalization notes:
We formalize Problem 321 from Polya-Szego:
Let α ∈ (0, π/2). Suppose f is analytic in the sector S = {z | arg z ∈ [-α, α]} 
and satisfies:
1. ∃ A, B > 0 such that ∀ z ∈ S, |f(z)| < A * exp(B * |z|)
2. On the boundary rays (arg z = ±α), |f(z)| ≤ 1
Then ∀ z ∈ S, |f(z)| ≤ 1.

We represent the sector as:
  S(α) = {z : ℂ | z ≠ 0 ∧ Complex.arg z ∈ Set.Icc (-α) α}
Note: Complex.arg takes values in (-π, π], so this is valid for α < π/2.
-/

open Complex
open Set
open Real

theorem problem_321 (α : ℝ) (hα : 0 < α ∧ α < π/2) (f : ℂ → ℂ) 
    (hf_analytic : AnalyticOn ℂ f {z | z ≠ 0 ∧ arg z ∈ Icc (-α) α}) 
    (h_boundary : ∀ z : ℂ, z ≠ 0 → (arg z = α ∨ arg z = -α) → ‖f z‖ ≤ 1)
    (h_growth : ∃ (A B : ℝ) (hA : 0 < A) (hB : 0 < B), 
        ∀ z : ℂ, z ≠ 0 → arg z ∈ Icc (-α) α → ‖f z‖ < A * Real.exp (B * Complex.abs z)) :
    ∀ z : ℂ, z ≠ 0 → arg z ∈ Icc (-α) α → ‖f z‖ ≤ 1 := by
  sorry

-- Proof attempt:
theorem problem_321 (α : ℝ) (hα : 0 < α ∧ α < π/2) (f : ℂ → ℂ) 
    (hf_analytic : AnalyticOn ℂ f {z | z ≠ 0 ∧ arg z ∈ Icc (-α) α}) 
    (h_boundary : ∀ z : ℂ, z ≠ 0 → (arg z = α ∨ arg z = -α) → ‖f z‖ ≤ 1)
    (h_growth : ∃ (A B : ℝ) (hA : 0 < A) (hB : 0 < B), 
        ∀ z : ℂ, z ≠ 0 → arg z ∈ Icc (-α) α → ‖f z‖ < A * Real.exp (B * Complex.abs z)) :
    ∀ z : ℂ, z ≠ 0 → arg z ∈ Icc (-α) α → ‖f z‖ ≤ 1 := by
  -- Define the sector S
  let S := {z : ℂ | z ≠ 0 ∧ arg z ∈ Icc (-α) α}
  
  -- Apply Phragmen-Lindelof for sectors
  refine Complex.PhragmenLindelof.sector_bound hα.1 hα.2 hf_analytic ?_ ?_ ?_
  
  -- Boundary condition
  · intro z hz
    exact h_boundary z hz.1 (Or.inl hz.2)
  
  -- Boundary condition (other side)
  · intro z hz
    exact h_boundary z hz.1 (Or.inr hz.2)
  
  -- Growth condition
  · obtain ⟨A, B, hA, hB, h⟩ := h_growth
    use B, A
    constructor
    · exact hB
    · intro z hz
      have := h z hz.1 hz.2
      simp only [norm_eq_abs] at this ⊢
      exact this.le