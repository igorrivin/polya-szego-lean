/-
Polya-Szego Problem 4
Part One, Chapter 4

Original problem:
Construct the lower and the upper sum for the function $\frac{1}{x}$ on the interval $[a, b]$ with the points of division in geometric progression, $a>0$. Find the limit as $n$ becomes infinite.\\

Formalization notes: -- We formalize the lower and upper Riemann sums for f(x) = 1/x on [a,b] with partition points
-- in geometric progression: x_k = a * (b/a)^{k/n} for k = 0,...,n
-- The lower sum uses infimum on each subinterval [x_{k-1}, x_k]
-- The upper sum uses supremum on each subinterval [x_{k-1}, x_k]
-- We then prove both sums converge to ∫_a^b 1/x dx = log(b) - log(a) as n → ∞
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic

-- Formalization notes:
-- We formalize the lower and upper Riemann sums for f(x) = 1/x on [a,b] with partition points
-- in geometric progression: x_k = a * (b/a)^{k/n} for k = 0,...,n
-- The lower sum uses infimum on each subinterval [x_{k-1}, x_k]
-- The upper sum uses supremum on each subinterval [x_{k-1}, x_k]
-- We then prove both sums converge to ∫_a^b 1/x dx = log(b) - log(a) as n → ∞

open Real
open Set
open Filter
open scoped Topology

theorem problem_4 (a b : ℝ) (ha : 0 < a) (hb : a < b) :
    Tendsto (λ (n : ℕ) => 
      let q := Real.rpow (b/a) ((n : ℝ)⁻¹) in
      Finset.sum (Finset.range n) (λ ν => 
        (a * q^(ν : ℝ)) * (q - 1) / (a * q^(ν + 1 : ℝ)))) atTop (𝓝 (Real.log b - Real.log a)) ∧
    Tendsto (λ (n : ℕ) => 
      let q := Real.rpow (b/a) ((n : ℝ)⁻¹) in
      Finset.sum (Finset.range n) (λ ν => 
        (a * q^(ν : ℝ)) * (q - 1) / (a * q^(ν : ℝ)))) atTop (𝓝 (Real.log b - Real.log a)) := by
  sorry

-- Proof attempt:
theorem problem_4 (a b : ℝ) (ha : 0 < a) (hb : a < b) :
    Tendsto (λ (n : ℕ) => 
      let q := Real.rpow (b/a) ((n : ℝ)⁻¹) in
      Finset.sum (Finset.range n) (λ ν => 
        (a * q^(ν : ℝ)) * (q - 1) / (a * q^(ν + 1 : ℝ)))) atTop (𝓝 (Real.log b - Real.log a)) ∧
    Tendsto (λ (n : ℕ) => 
      let q := Real.rpow (b/a) ((n : ℝ)⁻¹) in
      Finset.sum (Finset.range n) (λ ν => 
        (a * q^(ν : ℝ)) * (q - 1) / (a * q^(ν : ℝ)))) atTop (𝓝 (Real.log b - Real.log a)) := by
  have hab : 0 < b/a := by linarith [ha, hb]
  have hq : ∀ n, 0 < Real.rpow (b/a) ((n : ℝ)⁻¹) := fun n => Real.rpow_pos_of_pos hab _
  have hq1 : ∀ n, Real.rpow (b/a) ((n : ℝ)⁻¹) ≠ 1 := by
    intro n hn
    have := Real.rpow_eq_one_iff_of_pos hab ((n : ℝ)⁻¹) (by simp)
    simp [hn] at this
    exact (ne_of_lt hb).symm this.1
  constructor
  · -- Upper sum case
    simp_rw [div_eq_mul_inv, mul_assoc, ← mul_pow, mul_comm (a * _), mul_assoc, 
             mul_comm _ (q - 1), ← mul_assoc, mul_div_cancel _ (hq _), mul_one]
    simp_rw [← div_eq_mul_inv, div_div, mul_div_cancel _ (hq _)]
    simp_rw [div_self (ne_of_gt (hq _)), mul_one, sub_one]
    have : ∀ n, (Finset.range n).sum (λ ν => (1 - 1) / (Real.rpow (b/a) ((n : ℝ)⁻¹))) = 
                 n * (Real.rpow (b/a) ((n : ℝ)⁻¹) - 1) := by
      intro n
      simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    simp_rw [this]
    have : (fun n : ℕ => n * (Real.rpow (b/a) ((n : ℝ)⁻¹) - 1)) = 
           (fun n : ℕ => (Real.log (b/a)) * ((Real.log (b/a))⁻¹ * n * (Real.rpow (b/a) ((n : ℝ)⁻¹) - 1))) := by
      ext n
      rw [mul_assoc, ← mul_assoc _ _ (Real.log (b/a)), inv_mul_cancel, one_mul]
      exact (Real.log_ne_zero_of_ne_one (ne_of_gt hab) (ne_of_lt (div_lt_one_of_lt hb))).symm
    rw [this]
    apply Tendsto.mul_const
    refine Tendsto.congr' ?_ (tendsto_const_div_atTop_nhds_0_nat (Real.log (b/a)))
    apply eventually_of_forall
    intro n
    rw [mul_comm, mul_assoc, inv_mul_cancel]
    exact (Real.log_ne_zero_of_ne_one (ne_of_gt hab) (ne_of_lt (div_lt_one_of_lt hb))).symm
  · -- Lower sum case
    simp_rw [div_eq_mul_inv, mul_assoc, ← mul_pow, mul_comm (a * _), mul_assoc, 
             mul_comm _ (q - 1), ← mul_assoc, mul_div_cancel _ (hq _), mul_one]
    simp_rw [← div_eq_mul_inv, div_div, mul_div_cancel _ (hq _)]
    simp_rw [div_self (ne_of_gt (hq _)), mul_one, sub_one]
    have : ∀ n, (Finset.range n).sum (λ ν => (1 - 1)) = n * (Real.rpow (b/a) ((n : ℝ)⁻¹) - 1) := by
      intro n
      simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    simp_rw [this]
    have : (fun n : ℕ => n * (Real.rpow (b/a) ((n : ℝ)⁻¹) - 1)) = 
           (fun n : ℕ => (Real.log (b/a)) * ((Real.log (b/a))⁻¹ * n * (Real.rpow (b/a) ((n : ℝ)⁻¹) - 1))) := by
      ext n
      rw [mul_assoc, ← mul_assoc _ _ (Real.log (b/a)), inv_mul_cancel, one_mul]
      exact (Real.log_ne_zero_of_ne_one (ne_of_gt hab) (ne_of_lt (div_lt_one_of_lt hb))).symm
    rw [this]
    apply Tendsto.mul_const
    refine Tendsto.congr' ?_ (tendsto_const_div_atTop_nhds_0_nat (Real.log (b/a)))
    apply eventually_of_forall
    intro n
    rw [mul_comm, mul_assoc, inv_mul_cancel]
    exact (Real.log_ne_zero_of_ne_one (ne_of_gt hab) (ne_of_lt (div_lt_one_of_lt hb))).symm