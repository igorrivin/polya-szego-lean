/-
Polya-Szego Problem 12
Part Three, Chapter 1

Original problem:
For what values of $z$ is the absolute value of the $n$-th term of the series

$$
\begin{aligned}
& 1+\frac{z}{1}+\frac{z(z-1)}{1 \cdot 2}+\frac{z(z-1)(z-2)}{1 \cdot 2 \cdot 3}+\cdots+ \\
& +\frac{z(z-1) \cdots(z-n+1)}{1 \cdot 2 \cdots n}+\cdots=\sum_{n=0}^{\infty}\binom{z}{n}
\end{aligned}
$$

(binomial series for $(1+t)^{z}$ with $t=1$ and complex $z$ ) larger than the absolute value of any other term of this series ? $n=0,1,2, \ldots$\\

Formalization notes: -- We formalize the condition for which the absolute value of the n-th term
-- of the binomial series (1+1)^z = ∑_{n=0}^∞ binom(z,n) is maximal.
-- The problem asks: For complex z, find when |binom(z,n)| ≥ |binom(z,k)| for all k.
-- We'll state this as: ∃ n such that ∀ k, |Complex.binomial z n| ≥ |Complex.binomial z k|
-- Note: Complex.binomial is defined for complex z and natural n in Mathlib4.
-/

import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Complex.Basic

-- Formalization notes:
-- We formalize the condition for which the absolute value of the n-th term
-- of the binomial series (1+1)^z = ∑_{n=0}^∞ binom(z,n) is maximal.
-- The problem asks: For complex z, find when |binom(z,n)| ≥ |binom(z,k)| for all k.
-- We'll state this as: ∃ n such that ∀ k, |Complex.binomial z n| ≥ |Complex.binomial z k|
-- Note: Complex.binomial is defined for complex z and natural n in Mathlib4.

theorem problem_12_part_three_chapter_one (z : ℂ) :
    ∃ (n : ℕ), ∀ (k : ℕ), Complex.abs (Complex.binomial z n) ≥ Complex.abs (Complex.binomial z k) := by
  sorry

-- Proof attempt:
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Complex.Basic

theorem problem_12_part_three_chapter_one (z : ℂ) :
    ∃ (n : ℕ), ∀ (k : ℕ), Complex.abs (Complex.binomial z n) ≥ Complex.abs (Complex.binomial z k) := by
  -- The sequence |binom(z, n)| tends to 0 as n → ∞
  have tendsto_zero : Tendsto (fun n : ℕ ↦ Complex.abs (Complex.binomial z n)) atTop (𝓝 0) := by
    simp [Complex.binomial]
    apply Complex.tendsto_norm_zero.comp (tendsto_cobounded.mono_left atTop_le_cofinite)
  
  -- Since the sequence tends to 0, it's eventually bounded by |binom(z, 0)|
  obtain ⟨N, hN⟩ : ∃ N, ∀ n ≥ N, Complex.abs (Complex.binomial z n) ≤ Complex.abs (Complex.binomial z 0) :=
    Metric.tendsto_atTop.1 tendsto_zero (Complex.abs (Complex.binomial z 0)) (by norm_num) |>.imp fun N hN n hn ↦ hN n hn
  
  -- Consider the finite set {0, ..., N-1} where the maximum must be attained
  let s : Finset ℕ := Finset.range N
  have hs : s.Nonempty := by simp [N.zero_le]
  
  -- Get the maximum value in this finite set
  obtain ⟨n, hn⟩ : ∃ n ∈ s, ∀ k ∈ s, Complex.abs (Complex.binomial z k) ≤ Complex.abs (Complex.binomial z n) :=
    Finset.exists_max_image s (fun k ↦ Complex.abs (Complex.binomial z k)) hs
  
  -- Show this n works for all k
  use n
  intro k
  by_cases hk : k < N
  · -- Case k < N: maximum in the finite set
    exact hn k (Finset.mem_range.2 hk)
  · -- Case k ≥ N: bounded by |binom(z, 0)| which is ≤ |binom(z, n)|
    have : k ≥ N := Nat.le_of_not_lt hk
    refine le_trans (hN k this) ?_
    exact hn 0 (Finset.mem_range.2 (N.zero_le.trans_lt (Nat.lt_succ_self N)))