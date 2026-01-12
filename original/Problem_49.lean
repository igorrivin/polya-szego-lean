/-
Polya-Szego Problem 49
Part One, Chapter 4

Original problem:
Prove the existence of

$$
\lim _{n \rightarrow \infty} \frac{\sqrt[n]{n!}}{n}
$$

in a way different from I 69 and that the limit is equal to the geometric mean of $f(x)=x$ on the interval $[0,1]$, i.e. $=\frac{1}{e}$.\\

Formalization notes: We formalize Problem 49 from Polya-Szego's "Problems and Theorems in Analysis":
1. The existence of lim_{n→∞} (n!)^{1/n}/n
2. That this limit equals 1/e (the geometric mean of f(x)=x on [0,1])
-/

import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/- Formalization notes:
We formalize Problem 49 from Polya-Szego's "Problems and Theorems in Analysis":
1. The existence of lim_{n→∞} (n!)^{1/n}/n
2. That this limit equals 1/e (the geometric mean of f(x)=x on [0,1])

We break this into two parts:
- First, prove the limit exists
- Second, prove it equals 1/e

The geometric mean of f(x)=x on [0,1] is exp(∫₀¹ ln x dx) = exp(-1) = 1/e
-/

open Real
open Filter
open scoped Topology

/-- The limit of (n!)^{1/n}/n as n → ∞ exists. -/
theorem problem_49_part1 : ∃ L : ℝ, Tendsto (λ n : ℕ ↦ ((Nat.factorial n) ^ (1/(n : ℝ)) / (n : ℝ))) atTop (𝓝 L) := by
  sorry

/-- The limit of (n!)^{1/n}/n as n → ∞ equals 1/e. -/
theorem problem_49_part2 : Tendsto (λ n : ℕ ↦ ((Nat.factorial n) ^ (1/(n : ℝ)) / (n : ℝ))) atTop (𝓝 (Real.exp (-1))) := by
  sorry

/-- Alternative formulation using Stirling's approximation approach -/
theorem problem_49_combined : 
    Tendsto (λ n : ℕ ↦ ((Nat.factorial n) ^ (1/(n : ℝ)) / (n : ℝ))) atTop (𝓝 (Real.exp (-1))) := by
  sorry

/-- The geometric mean of f(x)=x on [0,1] is 1/e -/
theorem geometric_mean_of_x_on_01 : 
    Real.exp (∫ x in (0:ℝ)..1, Real.log x) = Real.exp (-1) := by
  calc
    Real.exp (∫ x in (0:ℝ)..1, Real.log x) = Real.exp (-1) := by
      have : ∫ x in (0:ℝ)..1, Real.log x = -1 := by
        refine integral_log_one ?_
        exact by norm_num
      rw [this]
    _ = Real.exp (-1) := rfl

-- Proof attempt:
theorem problem_49_part1 : ∃ L : ℝ, Tendsto (λ n : ℕ ↦ ((Nat.factorial n) ^ (1/(n : ℝ)) / (n : ℝ))) atTop (𝓝 L) := by
  have h := tendsto_log_stirling
  have h' : Tendsto (fun n : ℕ => (log (Nat.factorial n) - (n * log n - n)) / n) atTop (𝓝 0) := by
    refine Tendsto.congr' ?_ h
    filter_upwards [Filter.eventually_ne_atTop 0] with n hn
    simp [Nat.cast_ne_zero.mpr hn]
  have h'' : Tendsto (fun n : ℕ => (log (Nat.factorial n) / n) - log n + 1) atTop (𝓝 0) := by
    simp_rw [div_sub', add_sub_assoc]
    refine Tendsto.sub ?_ tendsto_const_nhds
    refine Tendsto.div ?_ ?_ tendsto_nat_cast_atTop_atTop
    · simp_rw [mul_comm]
      exact tendsto_log_stirling
    · exact tendsto_nat_cast_atTop_atTop
  have h''' : Tendsto (fun n : ℕ => log ((Nat.factorial n) ^ (1/(n:ℝ)) / n)) atTop (𝓝 (-1)) := by
    simp_rw [log_div, log_pow, one_div, mul_comm _ (log _)]
    convert h'' using 1
    ring
  exact ⟨exp (-1), Tendsto.exp h'''⟩