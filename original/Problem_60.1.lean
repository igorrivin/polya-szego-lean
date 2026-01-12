/-
Polya-Szego Problem 60.1
Part One, Chapter 1

Original problem:
Show that

$$
\lim _{q \rightarrow 1}\left[\begin{array}{l}
n \\
k
\end{array}\right]=\binom{n}{k} .
$$

Cf. 10.\\

Formalization notes: -- 1. We formalize the q-binomial coefficient [n choose k]_q as `qBinomial n k q`
-- 2. The limit is taken as q → 1 from both sides
-- 3. We use the standard binomial coefficient `Nat.choose n k` for the right side
-- 4. The theorem states that as q approaches 1, the q-binomial coefficient converges to the ordinary binomial coefficient
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic

-- Formalization notes:
-- 1. We formalize the q-binomial coefficient [n choose k]_q as `qBinomial n k q`
-- 2. The limit is taken as q → 1 from both sides
-- 3. We use the standard binomial coefficient `Nat.choose n k` for the right side
-- 4. The theorem states that as q approaches 1, the q-binomial coefficient converges to the ordinary binomial coefficient

theorem problem_60_1 (n k : ℕ) (hk : k ≤ n) : 
    Tendsto (fun (q : ℝ) => Real.qBinomial n k q) (𝓝 1) (𝓝 (Nat.choose n k)) := by
  sorry

-- Proof attempt:
theorem problem_60_1 (n k : ℕ) (hk : k ≤ n) : 
    Tendsto (fun (q : ℝ) => Real.qBinomial n k q) (𝓝 1) (𝓝 (Nat.choose n k)) := by
  rw [Real.qBinomial]
  simp only [Nat.cast_id]
  have : ∀ i ∈ Finset.range k, Tendsto (fun q : ℝ => (1 - q ^ (n - i)) / (1 - q ^ (i + 1))) (𝓝 1) (𝓝 ((n - i) / (i + 1))) := by
    intro i hi
    have n_pos : 0 < n - i := Nat.sub_pos_of_lt (Nat.lt_of_le_of_lt (Nat.le_of_lt (Finset.mem_range.1 hi)) hk)
    have k_pos : 0 < i + 1 := by linarith [Finset.mem_range.1 hi]
    rw [show (n - i : ℝ) / (i + 1 : ℝ) = (n - i) / (i + 1) by simp]
    refine Tendsto.div (?_ : Tendsto (fun q => 1 - q ^ (n - i)) (𝓝 1) (𝓝 (1 - 1 ^ (n - i)))) 
                      (?_ : Tendsto (fun q => 1 - q ^ (i + 1)) (𝓝 1) (𝓝 (1 - 1 ^ (i + 1)))) 
                      ?_ ?_
    · refine Tendsto.sub tendsto_const_nhds ?_
      refine Continuous.tendsto (fun q => q ^ (n - i)) 1 ?_
      exact continuous_pow (n - i)
    · refine Tendsto.sub tendsto_const_nhds ?_
      refine Continuous.tendsto (fun q => q ^ (i + 1)) 1 ?_
      exact continuous_pow (i + 1)
    · simp [sub_ne_zero, ne_of_gt (Nat.cast_pos.mpr n_pos)]
    · simp [sub_ne_zero, ne_of_gt (Nat.cast_pos.mpr k_pos)]
  have := Tendsto.finset_prod (Finset.range k) (fun i _ => this i (by simp [hk])) 
  simp only [one_pow, sub_self, Nat.cast_zero, zero_div, div_zero, mul_zero, add_zero] at this
  convert this using 1
  simp [Nat.choose_eq_factorial_div_factorial hk, div_eq_mul_inv]
  ring