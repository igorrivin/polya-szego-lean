/-
Polya-Szego Problem 176
Part One, Chapter 4

Original problem:
Let $a>0, \sigma>1$. The numbers

$$
x_{n}=a(\log n)^{\sigma}-\left[a(\log n)^{\sigma}\right]
$$

are equidistributed on $[0,1]$.\\

Formalization notes: -- 1. We formalize equidistribution using `Tendsto` with the sequence of measures
--    (1/N) * ∑_{n=1}^N δ_{x_n} converging weakly to Lebesgue measure on [0,1]
-- 2. The notation [x] means the floor/entier function, which we write as `⌊x⌋`
-- 3. We use `Real.log` for natural logarithm
-- 4. The condition σ > 1 is expressed as `hσ : σ > 1`
-- 5. The sequence x_n is defined for n ≥ 1, so we use `n : ℕ` and `hn : n ≥ 1`
-- 6. We use `Set.mem_Icc` to express that values are in [0,1]
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Constructions.Prod.Basic
import Mathlib.NumberTheory.Equidistribution.Basic

-- Formalization notes:
-- 1. We formalize equidistribution using `Tendsto` with the sequence of measures
--    (1/N) * ∑_{n=1}^N δ_{x_n} converging weakly to Lebesgue measure on [0,1]
-- 2. The notation [x] means the floor/entier function, which we write as `⌊x⌋`
-- 3. We use `Real.log` for natural logarithm
-- 4. The condition σ > 1 is expressed as `hσ : σ > 1`
-- 5. The sequence x_n is defined for n ≥ 1, so we use `n : ℕ` and `hn : n ≥ 1`
-- 6. We use `Set.mem_Icc` to express that values are in [0,1]

open Set
open scoped BigOperators

theorem problem_176 (a : ℝ) (σ : ℝ) (ha : a > 0) (hσ : σ > 1) :
    Tendsto (fun (N : ℕ) => (1/(N : ℝ)) • ∑ n in Finset.range N, 
      MeasureTheory.Measure.dirac (a * (Real.log (n + 1)) ^ σ - ⌊a * (Real.log (n + 1)) ^ σ⌋))
      atTop (𝓝 (MeasureTheory.Measure.restrict volume (Icc (0 : ℝ) 1))) := by
  sorry

-- Proof attempt:
theorem problem_176 (a : ℝ) (σ : ℝ) (ha : a > 0) (hσ : σ > 1) :
    Tendsto (fun (N : ℕ) => (1/(N : ℝ)) • ∑ n in Finset.range N, 
      MeasureTheory.Measure.dirac (a * (Real.log (n + 1)) ^ σ - ⌊a * (Real.log (n + 1)) ^ σ⌋))
      atTop (𝓝 (MeasureTheory.Measure.restrict volume (Icc (0 : ℝ) 1))) := by
  -- Apply Weyl's equidistribution criterion
  apply MeasureTheory.equidistributed_iff_forall_exp_integral_eq_zero.2
  intro k hk
  -- The case k = 0 is trivial, so we assume k ≠ 0
  have hk_ne_zero : k ≠ 0 := by simpa using hk
  -- We need to show the limit of the exponential sums is zero
  simp only [MeasureTheory.Measure.dirac_apply, smul_eq_mul, Finset.sum_mul, one_div,
    MeasureTheory.Measure.restrict_apply, MeasurableSet.univ, MeasureTheory.Measure.univ_toOuterMeasure,
    OuterMeasure.coe_univ, mul_one, Set.mem_Icc, Function.comp_apply]
  -- The exponential sum can be rewritten using the fractional part
  have : ∀ n, a * (Real.log (n + 1)) ^ σ - ⌊a * (Real.log (n + 1)) ^ σ⌋ = Int.fract (a * (Real.log (n + 1)) ^ σ) := by
    intro n
    rw [Int.fract]
    ring
  simp_rw [this]
  -- Now apply Weyl's criterion for the fractional part
  have : Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ n in Finset.range N, Complex.exp (2 * π * Complex.I * k * Int.fract (a * (Real.log (n + 1)) ^ σ))) atTop (𝓝 0) := by
    refine' tendsto_zero_iff_norm_tendsto_zero.2 _
    -- The key step is to show that the sequence (a (log (n+1))^σ) is uniformly distributed modulo 1
    -- This follows from the fact that (log n)^σ is uniformly distributed modulo 1 for σ > 1
    -- We use the general result about uniform distribution of sequences with sufficient growth
    apply tendsto_zero_of_sum_exp_two_pi_mul_fract_growth
    · exact ha
    · exact hσ
    · exact hk_ne_zero
  simpa [← Complex.ofReal_mul, ← mul_assoc, ← Complex.ofReal_inv, ← Complex.ofReal_nat_cast]