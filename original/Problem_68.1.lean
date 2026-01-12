/-
Polya-Szego Problem 68.1
Part One, Chapter 2

Original problem:
The numbers $a_{0}, a_{1}, a_{2}, \ldots$ are positive and

$$
\lim _{n \rightarrow \infty} \frac{a_{n+1}}{a_{n}}=p
$$

Then $\lim _{n \rightarrow \infty} \sqrt[n]{a_{n}}$ exists also and has the same value $p$.\\

Formalization notes: -- We formalize the statement: If (a_n) is a sequence of positive real numbers
-- and lim_{n→∞} a_{n+1}/a_n = p, then lim_{n→∞} (a_n)^{(1/n)} = p.
-- This is a classic result about the relationship between the ratio test
-- and the root test for sequences.
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Sequences

-- Formalization notes:
-- We formalize the statement: If (a_n) is a sequence of positive real numbers
-- and lim_{n→∞} a_{n+1}/a_n = p, then lim_{n→∞} (a_n)^{(1/n)} = p.
-- This is a classic result about the relationship between the ratio test
-- and the root test for sequences.

theorem problem_68_1 {a : ℕ → ℝ} (ha_pos : ∀ n, 0 < a n) (p : ℝ) 
    (hlim : Filter.Tendsto (λ n => a (n + 1) / a n) Filter.atTop (𝓝 p)) :
    Filter.Tendsto (λ n => Real.rpow (a n) ((n : ℝ)⁻¹)) Filter.atTop (𝓝 p) := by
  sorry

-- Proof attempt:
theorem problem_68_1 {a : ℕ → ℝ} (ha_pos : ∀ n, 0 < a n) (p : ℝ) 
    (hlim : Filter.Tendsto (λ n => a (n + 1) / a n) Filter.atTop (𝓝 p)) :
    Filter.Tendsto (λ n => Real.rpow (a n) ((n : ℝ)⁻¹)) Filter.atTop (𝓝 p) := by
  -- First convert the nth root to exponential form
  suffices : Filter.Tendsto (λ n => (a n) ^ ((n : ℝ)⁻¹)) Filter.atTop (𝓝 p)
  · simp [Real.rpow_def_of_pos (ha_pos _), ← Real.exp_log (ha_pos _)] at this ⊢
    exact this

  -- Key idea: express aₙ as a product of ratios (aₖ₊₁/aₖ) from k=0 to n-1
  have hprod : ∀ n, a n = a 0 * ∏ k in Finset.range n, (a (k+1) / a k) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.prod_range_succ, ← ih, mul_assoc, mul_div_cancel' _ (ha_pos _).ne']

  -- Rewrite the limit using the product expression
  rw [show (a n) ^ ((n : ℝ)⁻¹) = (a 0 ^ ((n : ℝ)⁻¹)) * (∏ k in Finset.range n, (a (k+1) / a k)) ^ ((n : ℝ)⁻¹) 
        by rw [hprod, mul_rpow (ha_pos 0).le (Finset.prod_nonneg (fun k _ => div_nonneg (ha_pos _).le (ha_pos _).le)), 
              Finset.prod_range_eq_mul_prod_erase_zero _ n]]

  -- The first term tends to 1 since a₀^(1/n) → 1
  have h1 : Filter.Tendsto (λ n => a 0 ^ ((n : ℝ)⁻¹)) Filter.atTop (𝓝 1) := by
    refine Real.tendsto_rpow_atTop_nhds_zero_of_norm_lt_one ?_
    simp only [norm_one, one_lt_one_iff, false_or]
    exact Or.inr (by norm_num)

  -- The second term is the geometric mean of the ratios
  have h2 : Filter.Tendsto (λ n => (∏ k in Finset.range n, (a (k+1) / a k)) ^ ((n : ℝ)⁻¹)) Filter.atTop (𝓝 p) := by
    -- Convert to exp of average of logs
    rw [← Real.exp_log (Finset.prod_pos (fun k _ => div_pos (ha_pos _) (ha_pos _))), 
        Real.exp_log (Finset.prod_pos (fun k _ => div_pos (ha_pos _) (ha_pos _)))]
    simp_rw [Real.rpow_def_of_pos (Finset.prod_pos (fun k _ => div_pos (ha_pos _) (ha_pos _))), 
             ← Real.exp_mul, ← Real.exp_add]
    have := Real.tendsto_exp_nhds_0_nhds_1
    -- The average of logs tends to log p
    have : Filter.Tendsto (λ n => (n : ℝ)⁻¹ * ∑ k in Finset.range n, Real.log (a (k+1) / a k)) Filter.atTop (𝓝 (Real.log p)) := by
      refine Tendsto.mul_const (Real.log p) ?_
      exact tendsto_inv_atTop_zero.comp tendsto_nat_cast_atTop_atTop
      convert hlim.comp (Real.tendsto_log_nhds_within_0 (by simp [ha_pos, ne_of_gt]))
      ext n
      simp
    exact Real.continuous_exp.tendsto _ |>.comp this

  -- Combine the two limits using multiplication
  convert h1.mul h2 using 1
  · ext n
    ring
  · simp