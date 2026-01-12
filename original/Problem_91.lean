/-
Polya-Szego Problem 91
Part One, Chapter 2

Original problem:
The function $f(x)$ is defined on $\left[x_{1}, x_{2}\right]$, properly integrable and strictly positive. We introduce

$$
\mathfrak{M}_{\varkappa}(f)=\left(\int_{x_{1}}^{x_{2}}[f(x)]^{\varkappa} d x\right)^{\frac{1}{\varkappa}} .
$$

Let $g(x)$ be a function with the same properties as $f(x)$. Then we have

$$
\mathcal{M}_{\varkappa}(f+g) \leqq \text { or } \geqq \mathcal{M}_{\varkappa}(f)+\mathcal{M}_{\varkappa}(g),
$$

according as $\varkappa \geqq 1$ or $\varkappa \leqq 1$.\\

Formalization notes: -- 1. We formalize the Minkowski inequality for integrals on a closed interval
-- 2. f and g are positive integrable functions on [a, b]
-- 3. 𝔐_κ(f) is defined as (∫_a^b (f(x))^κ dx)^(1/κ) for κ ≠ 0
-- 4. For κ = 0, we would need the geometric mean, but the problem focuses on κ ≥ 1 or κ ≤ 1
-- 5. We assume κ > 0 to avoid issues with negative powers and integrability
-- 6. The inequality direction reverses at κ = 1 (Minkowski vs reverse Minkowski)
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral

-- Formalization notes:
-- 1. We formalize the Minkowski inequality for integrals on a closed interval
-- 2. f and g are positive integrable functions on [a, b]
-- 3. 𝔐_κ(f) is defined as (∫_a^b (f(x))^κ dx)^(1/κ) for κ ≠ 0
-- 4. For κ = 0, we would need the geometric mean, but the problem focuses on κ ≥ 1 or κ ≤ 1
-- 5. We assume κ > 0 to avoid issues with negative powers and integrability
-- 6. The inequality direction reverses at κ = 1 (Minkowski vs reverse Minkowski)

theorem problem_91 (a b : ℝ) (hab : a ≤ b) (κ : ℝ) (hκ_pos : 0 < κ) 
    (f g : ℝ → ℝ) (hf_pos : ∀ x, x ∈ Set.Icc a b → 0 < f x) (hg_pos : ∀ x, x ∈ Set.Icc a b → 0 < g x)
    (hf_int : IntervalIntegrable f MeasureTheory.volume a b)
    (hg_int : IntervalIntegrable g MeasureTheory.volume a b) :
    let Mκ (h : ℝ → ℝ) := (∫ x in a..b, (h x) ^ κ) ^ (1/κ) in
    if κ ≥ 1 then
      Mκ (f + g) ≤ Mκ f + Mκ g
    else if κ ≤ 1 then
      Mκ (f + g) ≥ Mκ f + Mκ g
    else True := by
  sorry

-- Proof attempt:
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral

theorem problem_91 (a b : ℝ) (hab : a ≤ b) (κ : ℝ) (hκ_pos : 0 < κ) 
    (f g : ℝ → ℝ) (hf_pos : ∀ x, x ∈ Set.Icc a b → 0 < f x) (hg_pos : ∀ x, x ∈ Set.Icc a b → 0 < g x)
    (hf_int : IntervalIntegrable f MeasureTheory.volume a b)
    (hg_int : IntervalIntegrable g MeasureTheory.volume a b) :
    let Mκ (h : ℝ → ℝ) := (∫ x in a..b, (h x) ^ κ) ^ (1/κ) in
    if κ ≥ 1 then
      Mκ (f + g) ≤ Mκ f + Mκ g
    else if κ ≤ 1 then
      Mκ (f + g) ≥ Mκ f + Mκ g
    else True := by
  intro Mκ
  simp only
  split_ifs with hκ_ge1 hκ_le1
  · -- Case κ ≥ 1: Apply Minkowski's inequality
    have h_int : ∀ h : ℝ → ℝ, IntervalIntegrable (fun x ↦ (h x) ^ κ) MeasureTheory.volume a b := by
      intro h
      refine IntervalIntegrable.rpow_const ?_ hκ_pos.le
      exact hf_int
    have hf_pos' : ∀ x ∈ Set.Icc a b, 0 ≤ f x := fun x hx ↦ (hf_pos x hx).le
    have hg_pos' : ∀ x ∈ Set.Icc a b, 0 ≤ g x := fun x hx ↦ (hg_pos x hx).le
    have h_add_pos : ∀ x ∈ Set.Icc a b, 0 ≤ f x + g x := fun x hx ↦ add_nonneg (hf_pos' x hx) (hg_pos' x hx)
    have h_add_int : IntervalIntegrable (fun x ↦ (f x + g x) ^ κ) MeasureTheory.volume a b := by
      refine IntervalIntegrable.rpow_const ?_ hκ_pos.le
      exact IntervalIntegrable.add hf_int hg_int
    rw [Mκ, Mκ, Mκ]
    refine Real.rpow_le_rpow ?_ ?_ (by linarith [hκ_pos])
    · exact intervalIntegral.integral_rpow_le_add_rpow hab hκ_ge1 hf_pos' hg_pos' hf_int hg_int
    · exact integral_nonneg fun x ↦ Real.rpow_nonneg (h_add_pos x (Set.mem_Icc_of_Ioo hab x.2))
  · -- Case κ ≤ 1: Apply reverse Minkowski inequality
    have h_int : ∀ h : ℝ → ℝ, IntervalIntegrable (fun x ↦ (h x) ^ κ) MeasureTheory.volume a b := by
      intro h
      refine IntervalIntegrable.rpow_const ?_ hκ_pos.le
      exact hf_int
    have hf_pos' : ∀ x ∈ Set.Icc a b, 0 ≤ f x := fun x hx ↦ (hf_pos x hx).le
    have hg_pos' : ∀ x ∈ Set.Icc a b, 0 ≤ g x := fun x hx ↦ (hg_pos x hx).le
    have h_add_pos : ∀ x ∈ Set.Icc a b, 0 ≤ f x + g x := fun x hx ↦ add_nonneg (hf_pos' x hx) (hg_pos' x hx)
    have h_add_int : IntervalIntegrable (fun x ↦ (f x + g x) ^ κ) MeasureTheory.volume a b := by
      refine IntervalIntegrable.rpow_const ?_ hκ_pos.le
      exact IntervalIntegrable.add hf_int hg_int
    rw [Mκ, Mκ, Mκ]
    refine Real.rpow_le_rpow ?_ ?_ (by linarith [hκ_pos])
    · exact intervalIntegral.add_rpow_le_integral_rpow hab hκ_le1 hf_pos' hg_pos' hf_int hg_int
    · exact integral_nonneg fun x ↦ Real.rpow_nonneg (h_add_pos x (Set.mem_Icc_of_Ioo hab x.2))
  · -- Trivial case
    trivial