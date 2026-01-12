/-
Polya-Szego Problem 148
Part One, Chapter 4

Original problem:
The number $\frac{2}{3}$ is enveloped by the series
$$
\frac{3}{4}+\frac{1}{4}-\frac{3}{8}-\frac{1}{8}+\frac{3}{16}+\frac{1}{16}-\frac{3}{32}-\frac{1}{32}+\cdots
$$
but not in the strict sense.\\
149 ${ }^{1}$. Plot the first seven terms of the series
$$
e^{i}=1+\frac{i}{1!}-\frac{1}{2!}-\frac{i}{3!}+\frac{1}{4!}+\frac{i}{5!}-\frac{1}{6!}-\cdots
$$
successively as complex numbers and compute so the value of $e^{i}$ to three decimals.\\

Formalization notes: 1. We define the series as a function from ℕ to ℝ
2. The nth term a_n is: 
   - For even n = 2k: sign * 3/2^(k+1) where sign alternates every two terms
   - For odd n = 2k+1: sign * 1/2^(k+1) where sign alternates every two terms
3. "Envelops" means the sequence of partial sums s_n converges to 2/3, 
   and s_n alternates above and below 2/3, but not strictly (some partial sums might equal 2/3)
4. We'll prove the series converges to 2/3 and analyze the oscillation pattern
-/
-/

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic

/-!
Problem 148 from Polya-Szego's "Problems and Theorems in Analysis"

The series: 3/4 + 1/4 - 3/8 - 1/8 + 3/16 + 1/16 - 3/32 - 1/32 + ...
envelops 2/3 but not in the strict sense.

Formalization notes:
1. We define the series as a function from ℕ to ℝ
2. The nth term a_n is: 
   - For even n = 2k: sign * 3/2^(k+1) where sign alternates every two terms
   - For odd n = 2k+1: sign * 1/2^(k+1) where sign alternates every two terms
3. "Envelops" means the sequence of partial sums s_n converges to 2/3, 
   and s_n alternates above and below 2/3, but not strictly (some partial sums might equal 2/3)
4. We'll prove the series converges to 2/3 and analyze the oscillation pattern
-/

/-- The terms of the series in Problem 148 -/
def problem148_term (n : ℕ) : ℝ :=
  let k := n / 2
  let sign : ℝ := if (n / 2) % 2 = 0 then 1 else -1
  if n % 2 = 0 then sign * (3 : ℝ) / ((2 : ℝ) ^ (k + 1))
  else sign * (1 : ℝ) / ((2 : ℝ) ^ (k + 1))

/-- The partial sums of the series -/
def problem148_partial_sum (N : ℕ) : ℝ :=
  ∑ n in Finset.range N, problem148_term n

/-- The series converges to 2/3 -/
theorem problem148_converges : Filter.Tendsto problem148_partial_sum Filter.atTop (𝓝 (2/3 : ℝ)) := by
  sorry

/-- The partial sums oscillate around 2/3 -/
theorem problem148_envelops : 
    ∃ (f : ℕ → Prop), 
      (∀ n, f n → problem148_partial_sum n ≥ (2/3 : ℝ)) ∧
      (∀ n, ¬f n → problem148_partial_sum n ≤ (2/3 : ℝ)) ∧
      (∀ n, ∃ m ≥ n, f m) ∧
      (∀ n, ∃ m ≥ n, ¬f m) := by
  sorry

/-- The enveloping is not strict: some partial sums equal 2/3 -/
theorem problem148_not_strict_enveloping : 
    ∃ n : ℕ, problem148_partial_sum n = (2/3 : ℝ) := by
  sorry

-- Proof attempt:
theorem problem148_converges : Filter.Tendsto problem148_partial_sum Filter.atTop (𝓝 (2/3 : ℝ)) := by
  -- We'll group terms in pairs and show the partial sums converge to 2/3
  have h_tendsto : Filter.Tendsto (fun N ↦ ∑ n in Finset.range (2*N), problem148_term n) 
      Filter.atTop (𝓝 (2/3 : ℝ)) := by
    simp only [problem148_partial_sum]
    have h_pair : ∀ k, problem148_term (2*k) + problem148_term (2*k+1) = 
        (if k % 2 = 0 then 1 else -1) * (1/2)^(k+1) := by
      intro k
      simp [problem148_term]
      split_ifs with h1 h2 h3
      · ring_nf; simp [pow_succ]
      · ring_nf; simp [pow_succ]
      · ring_nf; simp [pow_succ]
      · ring_nf; simp [pow_succ]
    simp_rw [Finset.sum_range_add, h_pair]
    -- This is now an alternating geometric series
    have : (2/3 : ℝ) = ∑' k, (if k % 2 = 0 then 1 else -1) * (1/2)^(k+1) := by
      have : ∑' k, ((-1 : ℝ)^k) * (1/2)^(k+1) = (1/2) * ∑' k, (-1/2)^k := by
        simp_rw [mul_comm _ (1/2), ←mul_assoc, ←pow_mul, ←neg_eq_neg_one_mul, tsum_mul_right]
      rw [this]
      have : ∑' k, (-1/2)^k = (1 : ℝ)/(1 - (-1/2)) := by
        apply tsum_geometric_of_abs_lt_1; norm_num
      rw [this]; norm_num; ring
    rw [←this]
    apply HasSum.tendsto_sum_nat
    exact hasSum_ite_alternating_geometric (by norm_num) (by norm_num)
  
  -- Now extend to all partial sums, not just even-length ones
  refine tendsto_atTop_of_eventually_const_add_one h_tendsto ?h
  intro n
  simp [problem148_partial_sum]
  rw [Finset.sum_range_succ]
  have : problem148_term n = 0 := by
    cases n.even_or_odd with
    | inl h => 
      simp [problem148_term, h, Nat.mod_eq_zero_of_dvd h]
      split_ifs <;> field_simp
    | inr h =>
      simp [problem148_term, h, Nat.mod_add_mod]
      split_ifs <;> field_simp
  simp [this]