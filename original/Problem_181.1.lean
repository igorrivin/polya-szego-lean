/-
Polya-Szego Problem 181.1
Part One, Chapter 4

Original problem:
Assume that
\end{enumerate}

$$
a_{i 1}+a_{i 2}+\cdots+a_{i n}+\cdots=s_{i}
$$

converges for $i=1,2,3, \ldots$, define $U_{i}$ as the least upper bound of

$$
\left|a_{i 1}+a_{i 2}+\cdots+a_{i n}\right|, \quad n=1,2,3, \ldots,
$$

and assume that

$$
U_{1}+U_{2}+\cdots+U_{n}+\cdots
$$

converges. Then the series\\
(*) $\quad a_{11}+a_{12}+a_{21}+a_{13}+a_{22}+a_{31}+\cdots+a_{1 n}+a_{2, n-1}+\cdots$, which you obtain by arranging the numbers in the array

$$
\begin{aligned}
& a_{11} a_{12} a_{1

Formalization notes: -- 1. We formalize the problem about convergence of a diagonal summation of a double sequence
-- 2. We assume:
--    - For each i, the series ∑_{j=1}^∞ a_{i,j} converges to s_i
--    - U_i = sup_{n} |∑_{j=1}^n a_{i,j}|
--    - ∑_{i=1}^∞ U_i converges
-- 3. The conclusion: The diagonal sum ∑_{k=1}^∞ (∑_{i+j=k+1} a_{i,j}) converges to ∑_{i=1}^∞ s_i
-- 4. We use Finset for finite sums and Filter for limits
-- 5. The diagonal ordering is: a11, a12, a21, a13, a22, a31, a14, a23, a32, a41, ...
-/

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Summability.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Instances.Real

-- Formalization notes:
-- 1. We formalize the problem about convergence of a diagonal summation of a double sequence
-- 2. We assume:
--    - For each i, the series ∑_{j=1}^∞ a_{i,j} converges to s_i
--    - U_i = sup_{n} |∑_{j=1}^n a_{i,j}|
--    - ∑_{i=1}^∞ U_i converges
-- 3. The conclusion: The diagonal sum ∑_{k=1}^∞ (∑_{i+j=k+1} a_{i,j}) converges to ∑_{i=1}^∞ s_i
-- 4. We use Finset for finite sums and Filter for limits
-- 5. The diagonal ordering is: a11, a12, a21, a13, a22, a31, a14, a23, a32, a41, ...

theorem problem_181_1 {a : ℕ → ℕ → ℝ} (ha_converges : ∀ i, ∃ s : ℝ, Tendsto (λ n ↦ ∑ j in Finset.range n, a i j) atTop (𝓝 s))
    (U : ℕ → ℝ) (hU_def : ∀ i, U i = ⨆ n : ℕ, |∑ j in Finset.range n, a i j|)
    (hU_summable : Summable U) : 
    ∃ S : ℝ, 
    Tendsto (λ M ↦ ∑ k in Finset.range M, 
      ∑ m in Finset.range k, a (m + 1) (k - m)) atTop (𝓝 S) ∧
    S = ∑' i, Classical.choose (ha_converges i) := by
  sorry

-- Proof attempt:
theorem problem_181_1 {a : ℕ → ℕ → ℝ} (ha_converges : ∀ i, ∃ s : ℝ, Tendsto (λ n ↦ ∑ j in Finset.range n, a i j) atTop (𝓝 s))
    (U : ℕ → ℝ) (hU_def : ∀ i, U i = ⨆ n : ℕ, |∑ j in Finset.range n, a i j|)
    (hU_summable : Summable U) : 
    ∃ S : ℝ, 
    Tendsto (λ M ↦ ∑ k in Finset.range M, 
      ∑ m in Finset.range k, a (m + 1) (k - m)) atTop (𝓝 S) ∧
    S = ∑' i, Classical.choose (ha_converges i) := by
  -- Define s_i as the limit of the series for each i
  let s : ℕ → ℝ := fun i ↦ Classical.choose (ha_converges i)
  have hs : ∀ i, Tendsto (λ n ↦ ∑ j in Finset.range n, a i j) atTop (𝓝 (s i)) := 
    fun i ↦ Classical.choose_spec (ha_converges i)
  
  -- Show |s_i| ≤ U_i for each i
  have h_s_bound : ∀ i, |s i| ≤ U i := by
    intro i
    rw [hU_def i]
    apply ciSup_le
    intro n
    have := hs i
    have h := tendsto_nhds_unique this (tendsto_const_nhds (x := ∑ j in Finset.range n, a i j))
    simp at h
    rw [← h]
    exact le_ciSup (bddAbove_range_sum_of_summable hU_def hU_summable i) n

  -- Show sum of s_i is absolutely convergent
  have h_s_summable : Summable s := by
    apply Summable.of_norm_bounded U hU_summable h_s_bound

  -- Define the diagonal sum function
  let S_M := fun M ↦ ∑ k in Finset.range M, ∑ m in Finset.range k, a (m + 1) (k - m)

  -- Define the partial sums of s_i
  let T_N := fun N ↦ ∑ i in Finset.range N, s i

  -- Show T_N converges to ∑' i, s i
  have hT : Tendsto T_N atTop (𝓝 (∑' i, s i)) := by
    simp [T_N]
    exact h_s_summable.hasSum.tendsto_sum_nat

  -- Main proof: show S_M converges to same limit as T_N
  refine ⟨∑' i, s i, ?_⟩
  constructor
  · -- Show S_M converges to ∑' i, s i
    apply tendsto_nhds_of_cauchySeq_of_subseq hT
    · -- Cauchy sequence for S_M
      apply cauchySeq_of_summable_norm
      convert hU_summable using 1
      ext i
      rw [hU_def i]
      simp
    · -- Subsequence argument
      intro ε hε
      obtain ⟨N, hN⟩ := cauchySeq_finset_iff_vanishing.1 h_s_summable.cauchySeq_finset ε hε
      use N
      intro M hMN
      have h_sum_diff : |S_M M - T_N N| ≤ ∑ i in Finset.range N, U i - ∑ i in Finset.range N, s i + 
                        ∑ i in Finset.range N, |∑ j in Finset.range (M - i), a i j - s i| := by
        sorry -- This would require more detailed calculation
      -- The rest would involve showing each term is small
      sorry -- Additional technical details would go here
  · rfl