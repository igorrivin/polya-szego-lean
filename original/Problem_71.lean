/-
Polya-Szego Problem 71
Part One, Chapter 2

Original problem:
Suppose that the function $f(x)$ is properly integrable on the interval $\left[x_{1}, x_{2}\right]$ and $m \leqq f(x) \leqq M$ and, furthermore, that $\varphi(t)$ is defined and convex on the interval $[m, M]$. Then we have the inequality

$$
\varphi\left(\frac{1}{x_{2}-x_{1}} \int_{x_{1}}^{x_{2}} f(x) d x\right) \leqq \frac{1}{x_{2}-x_{1}} \int_{x_{1}}^{x_{2}} \varphi[f(x)] d x
$$

\begin{enumerate}
  \setcounter{enumi}{71}
  \item Suppose that the function $\varphi(t)$ is defined on the interv

Formalization notes: -- 1. We formalize Jensen's inequality for integrals: for a convex function φ and integrable f,
--    φ(⨍ f) ≤ ⨍ φ ∘ f where ⨍ denotes the average over an interval
-- 2. We use `ConvexOn` to express that φ is convex on [m, M]
-- 3. We use `intervalIntegrable` to express proper integrability on [x₁, x₂]
-- 4. The average integral is defined as (x₂ - x₁)⁻¹ * ∫_{x₁}^{x₂} f(x) dx
-- 5. We assume x₁ < x₂ to avoid division by zero
-/

import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Calculus.MeanInequalities
import Mathlib.MeasureTheory.Integral.IntervalIntegral

-- Formalization notes:
-- 1. We formalize Jensen's inequality for integrals: for a convex function φ and integrable f,
--    φ(⨍ f) ≤ ⨍ φ ∘ f where ⨍ denotes the average over an interval
-- 2. We use `ConvexOn` to express that φ is convex on [m, M]
-- 3. We use `intervalIntegrable` to express proper integrability on [x₁, x₂]
-- 4. The average integral is defined as (x₂ - x₁)⁻¹ * ∫_{x₁}^{x₂} f(x) dx
-- 5. We assume x₁ < x₂ to avoid division by zero

theorem problem_71 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {x₁ x₂ : ℝ} (hx : x₁ < x₂) {m M : ℝ} (hmM : m ≤ M)
    {f : ℝ → ℝ} (hf : IntervalIntegrable f MeasureTheory.volume x₁ x₂)
    (hf_range : ∀ x, x ∈ Set.Icc (x₁ : ℝ) x₂ → f x ∈ Set.Icc m M)
    {φ : ℝ → ℝ} (hφ : ConvexOn ℝ (Set.Icc m M) φ) :
    φ (((x₂ - x₁)⁻¹ : ℝ) • ∫ x in x₁..x₂, f x) ≤ 
      ((x₂ - x₁)⁻¹ : ℝ) • ∫ x in x₁..x₂, φ (f x) := by
  sorry

-- Proof attempt:
theorem problem_71 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {x₁ x₂ : ℝ} (hx : x₁ < x₂) {m M : ℝ} (hmM : m ≤ M)
    {f : ℝ → ℝ} (hf : IntervalIntegrable f MeasureTheory.volume x₁ x₂)
    (hf_range : ∀ x, x ∈ Set.Icc (x₁ : ℝ) x₂ → f x ∈ Set.Icc m M)
    {φ : ℝ → ℝ} (hφ : ConvexOn ℝ (Set.Icc m M) φ) :
    φ (((x₂ - x₁)⁻¹ : ℝ) • ∫ x in x₁..x₂, f x) ≤ 
      ((x₂ - x₁)⁻¹ : ℝ) • ∫ x in x₁..x₂, φ (f x) := by
  -- The average integral is in the convex set [m, M]
  have avg_mem : ((x₂ - x₁)⁻¹ • ∫ x in x₁..x₂, f x) ∈ Set.Icc m M := by
    refine Set.mem_Icc.mpr ⟨?_, ?_⟩
    · -- Lower bound
      have : m ≤ (x₂ - x₁)⁻¹ • ∫ x in x₁..x₂, f x := by
        rw [smul_eq_mul, ← div_eq_inv_mul]
        apply intervalIntegral.average_le_of_le_integral hx hf (fun x hx ↦ (hf_range x hx).1)
      exact this
    · -- Upper bound
      have : (x₂ - x₁)⁻¹ • ∫ x in x₁..x₂, f x ≤ M := by
        rw [smul_eq_mul, ← div_eq_inv_mul]
        apply intervalIntegral.integral_le_average_of_le hx hf (fun x hx ↦ (hf_range x hx).2)
      exact this
  
  -- Apply Jensen's inequality for integrals
  apply ConvexOn.map_average_le hφ
  · exact hx
  · exact hf
  · intro x hx
    exact hf_range x hx
  · exact avg_mem