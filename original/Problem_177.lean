/-
Polya-Szego Problem 177
Part One, Chapter 4

Original problem:
For $0<\sigma<1, \xi \neq 0$ the series

$$
\frac{\sin 1^{\sigma} \xi}{1^{\varrho}}+\frac{\sin 2^{\sigma} \xi}{2^{\varrho}}+\frac{\sin 3^{\sigma} \xi}{3^{\varrho}}+\cdots+\frac{\sin n^{\sigma} \xi}{n^{\varrho}}+\cdots
$$

is absolutely convergent if and only if $\varrho>1$.\\

Formalization notes: We formalize the statement:
"For 0 < σ < 1, ξ ≠ 0, the series ∑_{n=1}^∞ sin(n^σ ξ)/n^ϱ is absolutely convergent if and only if ϱ > 1."
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic

/- Formalization notes:

We formalize the statement:
"For 0 < σ < 1, ξ ≠ 0, the series ∑_{n=1}^∞ sin(n^σ ξ)/n^ϱ is absolutely convergent if and only if ϱ > 1."

Mathematical details:
- We use `hσpos : 0 < σ` and `hσlt1 : σ < 1` for 0 < σ < 1
- We use `hξ_ne_zero : ξ ≠ 0` for ξ ≠ 0
- Absolute convergence is formalized using `Summable (abs ∘ (λ n ↦ Real.sin ((n:ℝ)^σ * ξ) / (n:ℝ)^ϱ))`
- Since the sum is from n=1 to ∞, we use `Finset.sum` over `Finset.Icc 1 N` and take the limit as N → ∞
- However, for the theorem statement, we use `Summable` which handles infinite sums
- Note: The book uses ϱ for the exponent, which we write as `r` in Lean
- We assume σ and r are real numbers, ξ is a real number

Caution: The original problem statement uses "absolutely convergent" in the classical sense,
which corresponds to Summable of the absolute values in Mathlib.
-/

theorem problem_177 (σ r ξ : ℝ) (hσpos : 0 < σ) (hσlt1 : σ < 1) (hξ_ne_zero : ξ ≠ 0) :
    (Summable fun (n : ℕ) ↦ |Real.sin (((n : ℝ) ^ σ) * ξ) / ((n : ℝ) ^ r)|) ↔ r > 1 := by
  sorry

-- Alternative formulation using explicit series notation:
theorem problem_177_alt (σ r ξ : ℝ) (hσpos : 0 < σ) (hσlt1 : σ < 1) (hξ_ne_zero : ξ ≠ 0) :
    (∀ (f : ℕ → ℝ), f = (fun n ↦ Real.sin (((n.succ : ℝ) ^ σ) * ξ) / ((n.succ : ℝ) ^ r)) →
      Summable fun n ↦ abs (f n)) ↔ r > 1 := by
  sorry

-- Proof attempt:
theorem problem_177 (σ r ξ : ℝ) (hσpos : 0 < σ) (hσlt1 : σ < 1) (hξ_ne_zero : ξ ≠ 0) :
    (Summable fun (n : ℕ) ↦ |Real.sin (((n : ℝ) ^ σ) * ξ) / ((n : ℝ) ^ r)|) ↔ r > 1 := by
  constructor
  · intro h
    -- Show that if the series converges, then r > 1
    have h_upper_bound : ∃ C > 0, ∀ n ≥ 1, |Real.sin ((n : ℝ) ^ σ * ξ)| / (n : ℝ) ^ r ≤ C / n ^ r := by
      refine ⟨1, by norm_num, fun n _ ↦ ?_⟩
      simp only [one_div]
      rw [mul_comm]
      apply mul_le_of_le_one_left (by positivity)
      exact abs_sin_le_one _
    
    -- Compare with the p-series
    have h_comp := summable_of_nonneg_of_le (fun n ↦ by positivity) 
      (fun n ↦ h_upper_bound.2 n (by linarith)) h
    simp only [← summable_abs_iff, ← one_div] at h_comp
    exact (Real.summable_nat_rpow_inv.1 h_comp).2
  · intro hr
    -- Show that if r > 1, the series converges
    apply Summable.of_norm
    have h_sin_bound : ∃ C > 0, ∀ n ≥ 1, |Real.sin ((n : ℝ) ^ σ * ξ)| ≤ C * (n : ℝ) ^ σ := by
      refine ⟨|ξ|, abs_pos.mpr hξ_ne_zero, fun n _ ↦ ?_⟩
      rw [← mul_one (n : ℝ) ^ σ]
      exact abs_sin_mul_le (n ^ σ) ξ
    obtain ⟨C, hCpos, hC⟩ := h_sin_bound
    have h_bound : ∀ n ≥ 1, |Real.sin ((n : ℝ) ^ σ * ξ)| / (n : ℝ) ^ r ≤ C / (n : ℝ) ^ (r - σ) := by
      intro n hn
      rw [div_le_div_right (by positivity)]
      exact hC n hn
    apply Summable.of_nonneg_of_le (fun n ↦ by positivity) h_bound
    exact Real.summable_nat_rpow_inv.mpr (by linarith [hr])