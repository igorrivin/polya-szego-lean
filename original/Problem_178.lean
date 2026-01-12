/-
Polya-Szego Problem 178
Part One, Chapter 4

Original problem:
Suppose that the square roots of the natural numbers $1,2,3, \ldots$ are written up one below the other in an infinite array. Examine the digits at the $j$-th decimal place (to the right of the decimal point), $j \geqq 1$. Each digit $0,1,2, \ldots, 9$ appears on the average equally often. More precisely: let $v_{g}(n)$ denote the number of those integers $\leqq n$ whose square roots show a $g$ at the $j$-th decimal place. Then

$$
\lim _{n \rightarrow \infty} \frac{v_{g}(n)}{n}=\frac{1}{10}, \q

Formalization notes: -- We formalize the statement about decimal digits in square roots of natural numbers.
-- For each j ≥ 1 (decimal position after decimal point) and digit g ∈ {0,...,9},
-- let v_g(n) = number of k ≤ n such that the j-th decimal digit of √k is g.
-- The theorem states: lim_{n→∞} v_g(n)/n = 1/10 for each digit g.
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Digits
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Asymptotics.Asymptotics

-- Formalization notes:
-- We formalize the statement about decimal digits in square roots of natural numbers.
-- For each j ≥ 1 (decimal position after decimal point) and digit g ∈ {0,...,9},
-- let v_g(n) = number of k ≤ n such that the j-th decimal digit of √k is g.
-- The theorem states: lim_{n→∞} v_g(n)/n = 1/10 for each digit g.

theorem problem_178_digit_distribution_square_roots (j : ℕ) (hj : j ≥ 1) (g : ℕ) (hg : g ≤ 9) :
    Tendsto (λ (n : ℕ) => 
      ((Finset.range (n + 1)).filter (λ k => 
        let sqrt_k := Real.sqrt (k : ℝ)
        let decimal_expansion := Real.digits 10 (sqrt_k - ⌊sqrt_k⌋) (by norm_num)
        -- Get the j-th digit (0-indexed, so we use j-1 since j ≥ 1)
        let digit := decimal_expansion.get? (j - 1)
        digit = some g
      )).card / (n : ℝ)) 
      atTop (𝓝 (1/10 : ℝ)) := by
  sorry

-- Proof attempt:
import Mathlib.NumberTheory.Equidistribution.Real

open Filter Real Set

theorem problem_178_digit_distribution_square_roots (j : ℕ) (hj : j ≥ 1) (g : ℕ) (hg : g ≤ 9) :
    Tendsto (λ (n : ℕ) => 
      ((Finset.range (n + 1)).filter (λ k => 
        let sqrt_k := Real.sqrt (k : ℝ)
        let decimal_expansion := Real.digits 10 (sqrt_k - ⌊sqrt_k⌋) (by norm_num)
        let digit := decimal_expansion.get? (j - 1)
        digit = some g
      )).card / (n : ℝ)) 
      atTop (𝓝 (1/10 : ℝ)) := by
  -- The key idea is that (√n) is uniformly distributed mod 1
  have uniform_dist : Equidistributed (fun n : ℕ => Real.sqrt n) := by
    apply Equidistributed.of_vanDerCorput (fun n => Real.sqrt n)
    intro q hq
    -- The van der Corput condition holds for square roots
    -- This is a deep result from analytic number theory
    exact Real.tendsto_sum_sqrt_fourier hq

  -- Convert equidistribution to digit distribution
  let I : Set ℝ := Ico (g / 10^j) ((g + 1) / 10^j)
  have hI : volume I = 1/10^j := by
    rw [Real.volume_Ico]
    field_simp [pow_ne_zero j (by norm_num : (10:ℝ) ≠ 0)]
    ring

  -- The fractional parts are equidistributed
  have lim := uniform_dist.tendsto_preimage_Ico volume_Ico_ae_restrict (n + 1)
  simp_rw [fract_eq_self.mpr (by simp [sqrt_nonneg]), ← Nat.cast_succ] at lim

  -- Need to relate the digit condition to the interval I
  have digit_event (k : ℕ) :
    (Real.digits 10 (fract (Real.sqrt k)) (by norm_num)).get? (j - 1) = some g ↔
    fract (Real.sqrt k) ∈ I := by
    rw [← Real.digits_eq_floor (by norm_num) (fract_nonneg _), Option.get?_eq_some]
    refine ⟨fun ⟨h₁, h₂⟩ => ?_, fun h => ?_⟩
    · rw [mem_Ico]
      have := Real.digits_lt (by norm_num) (fract_lt_one _)
      refine ⟨?_, ?_⟩
      · rw [← h₁, ← Real.digits_div_pow_eq (by norm_num) (j-1) (fract_nonneg _)]
        exact div_nonneg (Nat.cast_nonneg _) (pow_nonneg (by norm_num) _)
      · rw [← h₁, ← Real.digits_div_pow_eq (by norm_num) (j-1) (fract_nonneg _)]
        exact div_lt_one (pow_pos (by norm_num) _)
    · rw [mem_Ico] at h
      refine ⟨?_, Nat.lt_succ_iff.mpr ?_⟩
      · rw [Real.digits_div_pow_eq (by norm_num) (j-1) (fract_nonneg _)]
        exact le_of_lt h.2
      · exact Real.digits_len_le (by norm_num) (fract_nonneg _)

  -- Now we can rewrite our limit
  have : (fun n => ((Finset.range (n + 1)).filter (λ k => fract (Real.sqrt k) ∈ I)).card / (n : ℝ)) =ᶠ[atTop]
         (fun n => ((Finset.range (n + 1)).filter (λ k => (Real.digits 10 (fract (Real.sqrt k)) _).get? (j - 1) = some g)).card / (n : ℝ)) :=
    eventually_of_forall fun n => by congr; ext k; rw [digit_event]

  -- The result follows from equidistribution and the measure of I
  rw [tendsto_congr this]
  convert uniform_dist.tendsto_preimage_Ico volume_Ico_ae_restrict (n + 1) using 1
  · simp [hI]
  · field_simp [pow_ne_zero j (by norm_num : (10:ℝ) ≠ 0)]
    rw [← mul_one_div, mul_assoc, mul_one_div, mul_comm (1/10:ℝ), ← mul_assoc]
    congr
    norm_num