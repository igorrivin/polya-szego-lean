/-
Polya-Szego Problem 88
Part One, Chapter 2

Original problem:
If the following conditions are satisfied:

$$
b_{n}>0, \quad \sum_{n=0}^{\infty} b_{n} \text { divergent }, \quad \lim _{n \rightarrow \infty} \frac{a_{0}+a_{1}+a_{2}+\cdots+a_{n}}{b_{0}+b_{1}+b_{2}+\cdots+b_{n}}=s,
$$

then

$$
\lim _{t \rightarrow 1-0} \frac{a_{0}+a_{1} t+a_{2} t^{2}+\cdots+a_{n} t^{n}+\cdots}{b_{0}+b_{1} t+b_{2} t^{2}+\cdots+b_{n} t^{n}+\cdots}=s,
$$

provided that the series in the denominator converges for $|t|<1$.\\

Formalization notes: -- We formalize the statement about Abel summability for ratio of power series.
-- We assume:
-- 1. b_n > 0 for all n
-- 2. ∑ b_n diverges (sum over ℕ)
-- 3. The Cesàro-like limit of partial sums ratio equals s
-- 4. The denominator power series converges for |t| < 1
-- Then the Abel limit of the ratio of power series equals s.
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Summability.Abel
import Mathlib.Analysis.Asymptotics.Asymptotics

-- Formalization notes:
-- We formalize the statement about Abel summability for ratio of power series.
-- We assume:
-- 1. b_n > 0 for all n
-- 2. ∑ b_n diverges (sum over ℕ)
-- 3. The Cesàro-like limit of partial sums ratio equals s
-- 4. The denominator power series converges for |t| < 1
-- Then the Abel limit of the ratio of power series equals s.

theorem problem_88 {a b : ℕ → ℝ} (hb_pos : ∀ n, 0 < b n) 
    (hb_divergent : ¬Summable b) 
    (h_limit : Tendsto (λ n => (∑ i in Finset.range (n+1), a i) / (∑ i in Finset.range (n+1), b i)) 
      atTop (𝓝 s)) 
    (h_conv_radius : HasSum (λ n : ℕ => b n * (1/2 : ℝ) ^ n) (∑' n : ℕ, b n * (1/2 : ℝ) ^ n)) :
    Tendsto (λ t : ℝ => 
      if h : ‖t‖ < 1 then 
        (∑' n : ℕ, a n * t ^ n) / (∑' n : ℕ, b n * t ^ n)
      else 0)
      (𝓝[<] 1) (𝓝 s) := by
  sorry

-- Proof attempt:
theorem problem_88 {a b : ℕ → ℝ} (hb_pos : ∀ n, 0 < b n) 
    (hb_divergent : ¬Summable b) 
    (h_limit : Tendsto (λ n => (∑ i in Finset.range (n+1), a i) / (∑ i in Finset.range (n+1), b i)) 
      atTop (𝓝 s)) 
    (h_conv_radius : HasSum (λ n : ℕ => b n * (1/2 : ℝ) ^ n) (∑' n : ℕ, b n * (1/2 : ℝ) ^ n)) :
    Tendsto (λ t : ℝ => 
      if h : ‖t‖ < 1 then 
        (∑' n : ℕ, a n * t ^ n) / (∑' n : ℕ, b n * t ^ n)
      else 0)
      (𝓝[<] 1) (𝓝 s) := by
  -- First establish that the denominator tends to infinity
  have hB_tendsto : Tendsto (λ n => ∑ i in Finset.range n, b i) atTop atTop := by
    apply tendsto_atTop_of_nonneg_of_nonneg_sum hb_divergent
    · intro n; exact Finset.sum_nonneg (fun i _ => le_of_lt (hb_pos i))
    · intro n; exact hb_pos n
  
  -- Apply Abel's theorem for the numerator and denominator
  have h_abel_a : Tendsto (λ t => ∑' n, a n * t ^ n) (𝓝[<] 1) (𝓝 s * ∞) := by
    refine' tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ _
    · apply tendsto_tsum_Abel_atTop_of_summable_on_Ioo
      · intro n; exact mem_Ioo.mpr ⟨by linarith, by linarith⟩
      · exact h_limit
      · exact hB_tendsto
    · intro t ht
      simp only [mem_setOf_eq, mem_Iio]
      exact ht
  
  have h_abel_b : Tendsto (λ t => ∑' n, b n * t ^ n) (𝓝[<] 1) atTop := by
    refine' tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ _
    · apply tendsto_tsum_Abel_atTop_of_summable_on_Ioo
      · intro n; exact mem_Ioo.mpr ⟨by linarith, by linarith⟩
      · simp only [div_one]
        apply tendsto_const_nhds.congr'
        filter_upwards [Filter.eventually_ge_atTop 0] with n hn
        simp [Finset.sum_range_one, hb_pos 0]
      · exact hB_tendsto
    · intro t ht
      simp only [mem_setOf_eq, mem_Iio]
      exact ht
  
  -- Now handle the ratio
  refine' Tendsto.congr' _ ((tendsto_congr' _).mp (Filter.Tendsto.div h_abel_a h_abel_b _))
  · filter_upwards [self_mem_nhdsWithin] with t ht
    simp [ht]
  · filter_upwards [self_mem_nhdsWithin] with t ht
    simp [ht]
    rw [mul_comm, mul_div_assoc, div_self (ne_of_gt (tsum_pos (fun n => mul_pos (hb_pos n) (pow_pos (by linarith [ht]) _)))), 
        mul_one]
  · simp only [ne_eq, not_false_eq_true]