/-
Polya-Szego Problem 85
Part One, Chapter 2

Original problem:
The functions $f(x)$ and $g(x)$ are properly integrable over the interval $\left[x_{1}, x_{2}\right]$ and strictly positive. Then\\
i.e.

$$
e^{\frac{1}{x_{2}-x_{1}} \int_{x_{1}}^{x_{2}} \log [f(x)+g(x)] d x} \geqq e^{\frac{1}{x_{2}-x_{1}} \int_{x_{1}}^{x_{2}} \log f(x) d x}+e^{\frac{1}{x_{1}-x_{2}} \int_{x_{1}}^{x_{2}} \log g(x) d x},
$$

$$
\mathscr{G}(f+g) \geqq \mathscr{G}(f)+\mathscr{G}(g) .
$$

\begin{enumerate}
  \setcounter{enumi}{85}
  \item The functions $f_{1}(x), f_{2}(x), \ldots, f_

Formalization notes: We formalize Problem 85 from Polya-Szego Part One, Chapter 2:
For properly integrable, strictly positive functions f and g on [x₁, x₂],
the geometric mean of (f + g) is at least the sum of geometric means of f and g.
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Analysis.Convex.Jensen

/- Formalization notes:
We formalize Problem 85 from Polya-Szego Part One, Chapter 2:
For properly integrable, strictly positive functions f and g on [x₁, x₂],
the geometric mean of (f + g) is at least the sum of geometric means of f and g.

Specifically, we formalize:
  exp(⨍_{x₁}^{x₂} log(f(x) + g(x)) dx) ≥ exp(⨍_{x₁}^{x₂} log(f(x)) dx) + exp(⨍_{x₁}^{x₂} log(g(x)) dx)
where ⨍ denotes the average integral: (1/(x₂ - x₁)) ∫_{x₁}^{x₂}

We use `intervalIntegral` for integration over intervals and require f, g to be positive
and integrable on [a, b] with a < b.
-/

open Real
open scoped Interval

theorem problem_85 {a b : ℝ} (hab : a < b) {f g : ℝ → ℝ} 
    (hf_int : IntervalIntegrable f volume a b) (hg_int : IntervalIntegrable g volume a b)
    (hf_pos : ∀ x, x ∈ Set.uIcc a b → f x > 0) (hg_pos : ∀ x, x ∈ Set.uIcc a b → g x > 0) :
    Real.exp ((1 / (b - a)) * ∫ x in a..b, Real.log (f x + g x)) ≥
    Real.exp ((1 / (b - a)) * ∫ x in a..b, Real.log (f x)) + 
    Real.exp ((1 / (b - a)) * ∫ x in a..b, Real.log (g x)) := by
  sorry

-- Proof attempt:
theorem problem_85 {a b : ℝ} (hab : a < b) {f g : ℝ → ℝ} 
    (hf_int : IntervalIntegrable f volume a b) (hg_int : IntervalIntegrable g volume a b)
    (hf_pos : ∀ x, x ∈ Set.uIcc a b → f x > 0) (hg_pos : ∀ x, x ∈ Set.uIcc a b → g x > 0) :
    Real.exp ((1 / (b - a)) * ∫ x in a..b, Real.log (f x + g x)) ≥
    Real.exp ((1 / (b - a)) * ∫ x in a..b, Real.log (f x)) + 
    Real.exp ((1 / (b - a)) * ∫ x in a..b, Real.log (g x)) := by
  -- First, define the average integrals
  let I₁ := (1 / (b - a)) * ∫ x in a..b, Real.log (f x)
  let I₂ := (1 / (b - a)) * ∫ x in a..b, Real.log (g x)
  let I := (1 / (b - a)) * ∫ x in a..b, Real.log (f x + g x)
  
  -- Show that the integrals exist
  have hf_log_int : IntervalIntegrable (fun x => Real.log (f x)) volume a b := by
    refine IntervalIntegrable.log hf_int ?_
    intro x hx
    exact hf_pos x hx
  have hg_log_int : IntervalIntegrable (fun x => Real.log (g x)) volume a b := by
    refine IntervalIntegrable.log hg_int ?_
    intro x hx
    exact hg_pos x hx
  have hfg_log_int : IntervalIntegrable (fun x => Real.log (f x + g x)) volume a b := by
    refine IntervalIntegrable.log (hf_int.add hg_int) ?_
    intro x hx
    exact add_pos (hf_pos x hx) (hg_pos x hx)
  
  -- Apply Jensen's inequality for the concave log function
  have hJensen : I ≥ Real.log (Real.exp I₁ + Real.exp I₂) := by
    let μ : Measure ℝ := volume.restrict (Ι a b)
    have hμ : IsProbabilityMeasure μ := by
      constructor
      simp [Measure.restrict_apply MeasurableSet.univ, volume_univ, Ioc_measure]
      field_simp [hab.ne']
    have h_log_concave : ConcaveOn ℝ (Set.Ioi 0) Real.log := concaveOn_log
    have h_fg_pos : ∀ x ∈ Ι a b, f x + g x > 0 := fun x hx => add_pos (hf_pos x hx) (hg_pos x hx)
    
    -- Rewrite integrals as expectations
    have : I = ∫ x, Real.log (f x + g x) ∂μ := by
      simp [μ, I, intervalIntegral.integral_of_le hab.le]
      congr
      ext x
      simp [Set.indicator_apply, Set.mem_Ioc, hab]
    rw [this]
    
    have : Real.exp I₁ + Real.exp I₂ = ∫ x, f x ∂μ + ∫ x, g x ∂μ := by
      simp [μ, I₁, I₂, intervalIntegral.integral_of_le hab.le]
      congr <;> ext x <;> simp [Set.indicator_apply, Set.mem_Ioc, hab]
    rw [this]
    
    -- Apply Jensen's inequality
    refine (h_log_concave.le_integral hμ _).trans ?_
    · intro x hx
      exact h_fg_pos x hx
    · exact (integrable_add hf_int hg_int).congr (by simp [μ])
    simp only [← exp_log (add_pos (exp_pos I₁) (exp_pos I₂))]
    exact log_le_log (exp_pos _) (by positivity)
  
  -- Exponentiate both sides to get the final result
  refine (Real.exp_monotone hJensen).trans_eq ?_
  simp only [Real.exp_log (add_pos (Real.exp_pos I₁) (Real.exp_pos I₂))]