/-
Polya-Szego Problem 175
Part One, Chapter 4

Original problem:
Suppose that $a>0,0<\sigma<1$. The sequence

$$
x_{n}=a n^{\sigma}-\left[a n^{\sigma}\right]
$$

is equidistributed on the interval $[0,1]$.\\

Formalization notes: -- 1. We formalize equidistribution using `Tendsto` with the sequence of measures
--    `(1/(n+1)) * ∑_{k=0}^n δ_{x_k}` converging to Lebesgue measure on [0,1]
-- 2. `a > 0` and `0 < σ < 1` are explicit hypotheses
-- 3. `x_n = a * n^σ - ⌊a * n^σ⌋` gives the fractional part
-- 4. We use `Real.log` for the logarithm in the solution context
-- 5. The solution reference to Problem 173 about convergence/divergence is not formalized here
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Constructions.Prod.Integral
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.NumberTheory.Equidistribution.Basic

-- Formalization notes:
-- 1. We formalize equidistribution using `Tendsto` with the sequence of measures
--    `(1/(n+1)) * ∑_{k=0}^n δ_{x_k}` converging to Lebesgue measure on [0,1]
-- 2. `a > 0` and `0 < σ < 1` are explicit hypotheses
-- 3. `x_n = a * n^σ - ⌊a * n^σ⌋` gives the fractional part
-- 4. We use `Real.log` for the logarithm in the solution context
-- 5. The solution reference to Problem 173 about convergence/divergence is not formalized here

theorem problem_175 (a : ℝ) (σ : ℝ) (ha : a > 0) (hσ : σ ∈ Set.Ioo (0 : ℝ) 1)) :
    EquidistribOn (fun n : ℕ => a * (n : ℝ) ^ σ - ⌊a * (n : ℝ) ^ σ⌋) 
    (Set.Icc (0 : ℝ) 1) := by
  sorry

-- Proof attempt:
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Constructions.Prod.Integral
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.NumberTheory.Equidistribution.Basic

open Filter Asymptotics Metric MeasureTheory Real Set Topology

theorem problem_175 (a : ℝ) (σ : ℝ) (ha : a > 0) (hσ : σ ∈ Set.Ioo (0 : ℝ) 1)) :
    EquidistribOn (fun n : ℕ => a * (n : ℝ) ^ σ - ⌊a * (n : ℝ) ^ σ⌋) 
    (Set.Icc (0 : ℝ) 1) := by
  rw [equidistribOn_iff_vanishing_of_fourierCoeff]
  intro k hk
  simp only [ne_eq, Int.cast_eq_zero, Int.natAbs_eq_zero] at hk
  have hk_ne_zero : k ≠ 0 := hk
  clear hk
  simp only [Function.comp_apply, fourierCoeff_eq_sum_sub_floor]
  
  -- Main estimate using Weyl's criterion
  have : Tendsto (fun N : ℕ ↦ (1 / (N + 1)) * ∑ n in Finset.range (N + 1), Complex.exp (2 * π * Complex.I * k * (a * (n : ℝ) ^ σ)))
    atTop (𝓝 0) := by
    apply tendsto_zero_weyl_criterion_of_exponent_lt_one
    · exact ha
    · exact hσ.1
    · exact hσ.2
    · exact Int.cast_ne_zero.mpr hk_ne_zero
  
  -- Convert the complex exponential to trigonometric form
  have : ∀ n, Complex.exp (2 * π * Complex.I * k * (a * (n : ℝ) ^ σ)) = 
    Complex.ofReal' (Real.cos (2 * π * k * a * (n : ℝ) ^ σ)) + 
    Complex.I * Complex.ofReal' (Real.sin (2 * π * k * a * (n : ℝ) ^ σ)) := by
    intro n
    simp [Complex.exp_mul_I, mul_assoc]
  
  -- Show the imaginary part tends to zero
  have im_tendsto : Tendsto (fun N : ℕ ↦ (1 / (N + 1)) * ∑ n in Finset.range (N + 1), 
    Real.sin (2 * π * k * a * (n : ℝ) ^ σ)) atTop (𝓝 0) := by
    convert (tendsto_zero_weyl_criterion_of_exponent_lt_one ha hσ.1 hσ.2 hk_ne_zero).im
    ext N
    simp [← Complex.ext_iff, this]
  
  -- Show the real part tends to zero
  have re_tendsto : Tendsto (fun N : ℕ ↦ (1 / (N + 1)) * ∑ n in Finset.range (N + 1), 
    Real.cos (2 * π * k * a * (n : ℝ) ^ σ)) atTop (𝓝 0) := by
    convert (tendsto_zero_weyl_criterion_of_exponent_lt_one ha hσ.1 hσ.2 hk_ne_zero).re
    ext N
    simp [← Complex.ext_iff, this]
  
  -- Combine to show the original sum tends to zero
  convert this using 1
  ext N
  congr
  funext n
  simp [this]