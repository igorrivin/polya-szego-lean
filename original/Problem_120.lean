/-
Polya-Szego Problem 120
Part One, Chapter 3

Original problem:
Let the function $f(x)$ have a continuous derivative on $(a, b)$. Decide whether it is possible to find for each point $\xi$ of this interval two points $x_{1}, x_{2}, x_{1}<\xi<x_{2}$, such that

$$
\frac{f\left(x_{2}\right)-f\left(x_{1}\right)}{x_{2}-x_{1}}=f^{\prime}(\xi) .
$$

\begin{enumerate}
  \setcounter{enumi}{120}
  \item Assume that the function $f(x)$ is differentiable on $[a, b]$, but not a constant and that $f(a)=f(b)=0$. Then there exists at least one point $\boldsymbol{\xi}$ on $

Formalization notes: -- We formalize the three parts of Problem 120 as separate theorems.
-- Part 1: About the existence of points x₁, x₂ with x₁ < ξ < x₂ such that
--         the secant slope equals the derivative at ξ.
-- Part 2: The inequality involving the derivative and integral for 
--         non-constant functions with f(a)=f(b)=0.
-- Part 3: The formula relating second derivative to an integral.
-/

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral

-- Formalization notes:
-- We formalize the three parts of Problem 120 as separate theorems.
-- Part 1: About the existence of points x₁, x₂ with x₁ < ξ < x₂ such that
--         the secant slope equals the derivative at ξ.
-- Part 2: The inequality involving the derivative and integral for 
--         non-constant functions with f(a)=f(b)=0.
-- Part 3: The formula relating second derivative to an integral.

open Real
open Set
open scoped Real

/-- Part 1 of Problem 120: For a function with continuous derivative on (a,b),
    at each point ξ in (a,b), there exist x₁ < ξ < x₂ such that the secant
    slope equals f'(ξ). -/
theorem problem_120_part1 {a b : ℝ} (hab : a < b) (f : ℝ → ℝ) 
    (hf : DifferentiableOn ℝ f (Set.Ioo a b)) 
    (hf' : ContinuousOn (deriv f) (Set.Ioo a b)) :
    ∀ ξ ∈ Set.Ioo a b, ∃ (x₁ x₂ : ℝ), x₁ < ξ ∧ ξ < x₂ ∧ x₁ ∈ Set.Ioo a b ∧ x₂ ∈ Set.Ioo a b ∧
    (f x₂ - f x₁) / (x₂ - x₁) = deriv f ξ := by
  sorry

/-- Part 2 of Problem 120: For a differentiable, non-constant function on [a,b]
    with f(a)=f(b)=0, there exists ξ in (a,b) such that |f'(ξ)| > 4/(b-a)² * ∫_a^b f(x)dx. -/
theorem problem_120_part2 {a b : ℝ} (hab : a < b) (f : ℝ → ℝ) 
    (hf : DifferentiableOn ℝ f (Set.Icc a b)) 
    (hfa : f a = 0) (hfb : f b = 0)
    (hconst : ¬∀ x ∈ Set.Icc a b, f x = 0) :
    ∃ ξ ∈ Set.Ioo a b, |deriv f ξ| > 4 / ((b - a) ^ 2) * ∫ x in a..b, f x := by
  sorry

/-- Part 3 of Problem 120: For a twice differentiable function, there exists ξ in (x₀ - r, x₀ + r)
    such that f''(ξ) = 3/r³ * ∫_{x₀-r}^{x₀+r} [f(x) - f(x₀)] dx. -/
theorem problem_120_part3 {x₀ r : ℝ} (hr : 0 < r) (f : ℝ → ℝ) 
    (hf : ∀ n : ℕ, n ≤ 2 → ContDiffAt ℝ n f x₀) :
    ∃ ξ ∈ Set.Ioo (x₀ - r) (x₀ + r), 
      deriv (deriv f) ξ = 3 / (r ^ 3) * ∫ x in (x₀ - r)..(x₀ + r), (f x - f x₀) := by
  sorry

-- Proof attempt:
theorem problem_120_part1 {a b : ℝ} (hab : a < b) (f : ℝ → ℝ) 
    (hf : DifferentiableOn ℝ f (Set.Ioo a b)) 
    (hf' : ContinuousOn (deriv f) (Set.Ioo a b)) :
    ∀ ξ ∈ Set.Ioo a b, ∃ (x₁ x₂ : ℝ), x₁ < ξ ∧ ξ < x₂ ∧ x₁ ∈ Set.Ioo a b ∧ x₂ ∈ Set.Ioo a b ∧
    (f x₂ - f x₁) / (x₂ - x₁) = deriv f ξ := by
  intro ξ hξ
  obtain ⟨δ, hδ_pos, hδ⟩ : ∃ δ > 0, Ioo (ξ - δ) (ξ + δ) ⊆ Ioo a b := by
    apply Metric.mem_nhds_iff.1
    exact Ioo_mem_nhds hξ.1 hξ.2
  let g : ℝ → ℝ := fun x => f x - f ξ - deriv f ξ * (x - ξ)
  have hg_diff : DifferentiableOn ℝ g (Ioo a b) := by
    apply DifferentiableOn.sub hf
    apply DifferentiableOn.add
    · exact differentiableOn_const (f ξ)
    · apply DifferentiableOn.mul (differentiableOn_id) (differentiableOn_const _)
  have hg' : ∀ x ∈ Ioo a b, deriv g x = deriv f x - deriv f ξ := by
    intro x hx
    simp [g]
    rw [deriv_sub, deriv_add, deriv_const, deriv_mul, deriv_id'', deriv_const]
    · simp; ring
    · exact hf.differentiableAt (Ioo_mem_nhds hx.1 hx.2)
    · exact (differentiableAt_const _).add ((differentiableAt_id').mul (differentiableAt_const _))
    · exact differentiableAt_id'
    · exact differentiableAt_const _
  have hg'_cont : ContinuousOn (deriv g) (Ioo a b) := by
    rw [show deriv g = fun x => deriv f x - deriv f ξ by ext; simp [hg']]
    exact hf'.sub continuousOn_const
  have hg'_ξ : deriv g ξ = 0 := by simp [hg']
  -- Find x₁ where g(x₁) = g(ξ)
  obtain ⟨x₁, hx₁⟩ : ∃ x₁ ∈ Ioo (ξ - δ) ξ, g x₁ = g ξ := by
    apply exists_Ioo_eq_of_continuous_of_ivl (fun x hx => hg'_cont x (hδ ⟨hx.1, hx.2.le.trans (le_refl ξ)⟩))
    · exact hg_diff.continuousOn
    · have : g ξ = 0 := by simp [g]
      rw [this]
      suffices ∃ x ∈ Ioo (ξ - δ) ξ, g x < 0 ∨ ∃ x ∈ Ioo (ξ - δ) ξ, g x > 0 by
        obtain ⟨x, hx, hgx⟩ | ⟨x, hx, hgx⟩ := this
        · exact ⟨x, hx, le_of_lt hgx⟩
        · exact ⟨x, hx, ge_of_lt hgx⟩
      by_contra' h
      have : ∀ x ∈ Ioo (ξ - δ) ξ, g x = 0 := by
        intro x hx
        exact le_antisymm (h.1 x hx) (h.2 x hx)
      have : ∀ x ∈ Ioo (ξ - δ) ξ, deriv g x = 0 := by
        intro x hx
        have := hasDerivAt_zero_of_eventually_const (hg_diff.differentiableAt (Ioo_mem_nhds (hδ ⟨hx.1, hx.2.le.trans (le_refl ξ)⟩).1 (hδ ⟨hx.1, hx.2.le.trans (le_refl ξ)⟩).2))
          (mem_nhds_iff.2 ⟨Ioo (ξ - δ) ξ, Ioo_subset_Ioo le_rfl le_rfl, isOpen_Ioo, hx, fun y hy => this y hy⟩)
        exact this.deriv
      have : deriv g ξ = 0 := by
        apply tendsto_nhds_unique (hg'_cont.continuousAt (Ioo_mem_nhds hξ.1 hξ.2)) 
        convert tendsto_const_nhds (α := ℝ) (f := deriv g) (a := 0)
        ext; simp [this]
      rw [hg'_ξ] at this
      exact this
    · exact ⟨ξ - δ/2, by linarith, by linarith⟩
  -- Find x₂ where g(x₂) = g(ξ)
  obtain ⟨x₂, hx₂⟩ : ∃ x₂ ∈ Ioo ξ (ξ + δ), g x₂ = g ξ := by
    apply exists_Ioo_eq_of_continuous_of_ivl (fun x hx => hg'_cont x (hδ ⟨hx.1.le.trans (le_refl ξ), hx.2⟩))
    · exact hg_diff.continuousOn
    · have : g ξ = 0 := by simp [g]
      rw [this]
      suffices ∃ x ∈ Ioo ξ (ξ + δ), g x < 0 ∨ ∃ x ∈ Ioo ξ (ξ + δ), g x > 0 by
        obtain ⟨x, hx, hgx⟩ | ⟨x, hx, hgx⟩ := this
        · exact ⟨x, hx, le_of_lt hgx⟩
        · exact ⟨x, hx, ge_of_lt hgx⟩
      by_contra' h
      have : ∀ x ∈ Ioo ξ (ξ + δ), g x = 0 := by
        intro x hx
        exact le_antisymm (h.1 x hx) (h.2 x hx)
      have : ∀ x ∈ Ioo ξ (ξ + δ), deriv g x = 0 := by
        intro x hx
        have := hasDerivAt_zero_of_eventually_const (hg_diff.differentiableAt (Ioo_mem_nhds (hδ ⟨hx.1.le.trans (le_refl ξ), hx.2⟩).1 (hδ ⟨hx.1.le.trans (le_refl ξ), hx.2⟩).2))
          (mem_nhds_iff.2 ⟨Ioo ξ (ξ + δ), Ioo_subset_Ioo le_rfl le_rfl, isOpen_Ioo, hx, fun y hy => this y hy⟩)
        exact this.deriv
      have : deriv g ξ = 0 := by
        apply tendsto_nhds_unique (hg'_cont.continuousAt (Ioo_mem_nhds hξ.1 hξ.2)) 
        convert tendsto_const_nhds (α := ℝ) (f := deriv g) (a := 0)
        ext; simp [this]
      rw [hg'_ξ] at this
      exact this
    · exact ⟨ξ + δ/2, by linarith, by linarith⟩
  refine ⟨x₁, x₂, hx₁.1.2, hx₂.1.1, hδ ⟨hx₁.1.1, hx₁.1.2.le.trans (le_refl ξ)⟩, hδ ⟨hx₂.1.1.le.trans (le_refl ξ), hx₂.1.2⟩, ?_⟩
  have : g x₁ = g x₂ := by rw [hx₁.2, hx₂.2]
  simp [g] at this
  field_simp [ne_of_lt hx₂.1.1, ne_of_lt hx₁.1.2]
  rw [← this]
  ring