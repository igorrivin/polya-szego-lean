/-
Polya-Szego Problem 75
Part One, Chapter 2

Original problem:
Let $\sigma>0$. If the series

$$
a_{1} 1^{-\sigma}+a_{2} 2^{-\sigma}+a_{3} 3^{-\sigma}+\cdots+a_{n} n^{-\sigma}+\cdots
$$

is convergent, then

$$
\lim _{n \rightarrow \infty}\left(a_{1}+a_{2}+a_{3}+\cdots+a_{n}\right) n^{-\sigma}=0
$$

(Series of this kind are called Dirichlet series. Cf. VIII, Chap. 1, § 5.)\\

Formalization notes: -- 1. We formalize the statement about Dirichlet series: 
--    If ∑ a_n / n^σ converges (with σ > 0), then (∑_{k=1}^n a_k) / n^σ → 0
-- 2. We use `Real` exponents and require σ > 0
-- 3. We use the standard convergence definitions for series
-- 4. The book's solution uses Jensen's inequality from Problem 73,
--    but we state only the conclusion as a theorem
-/

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

-- Formalization notes:
-- 1. We formalize the statement about Dirichlet series: 
--    If ∑ a_n / n^σ converges (with σ > 0), then (∑_{k=1}^n a_k) / n^σ → 0
-- 2. We use `Real` exponents and require σ > 0
-- 3. We use the standard convergence definitions for series
-- 4. The book's solution uses Jensen's inequality from Problem 73,
--    but we state only the conclusion as a theorem

theorem problem_75 (σ : ℝ) (hσ : σ > 0) (a : ℕ → ℝ) 
    (hconv : Summable fun n : ℕ => a (n + 1) / ((n : ℝ) + 1) ^ σ) :
    Filter.Tendsto (fun n : ℕ ↦ (∑ k in Finset.range n, a (k + 1)) / ((n : ℝ) ^ σ)) 
      Filter.atTop (𝓝 0) := by
  sorry

-- Proof attempt:
theorem problem_75 (σ : ℝ) (hσ : σ > 0) (a : ℕ → ℝ) 
    (hconv : Summable fun n : ℕ => a (n + 1) / ((n : ℝ) + 1) ^ σ) :
    Filter.Tendsto (fun n : ℕ ↦ (∑ k in Finset.range n, a (k + 1)) / ((n : ℝ) ^ σ)) 
      Filter.atTop (𝓝 0) := by
  -- Define the partial sums and the convergent series terms
  let S n := ∑ k in Finset.range n, a (k + 1)
  let b n := a (n + 1) / ((n : ℝ) + 1) ^ σ
  have hb : Summable b := hconv

  -- Express S n as a sum involving b k and k^σ
  have h_sum : ∀ n, S n = ∑ k in Finset.range n, b k * ((k : ℝ) + 1) ^ σ := by
    intro n
    simp [S, b]
    rw [Finset.sum_congr rfl]
    intro k hk
    rw [Finset.mem_range] at hk
    simp
    field_simp
    ring

  -- Let s be the sum of the series b
  let s := ∑' n, b n
  have h_tendsto : Tendsto (fun n => ∑ k in Finset.range n, b k) atTop (𝓝 s) :=
    hb.tendsto_sum_nat

  -- Rewrite our goal using summation by parts
  rw [show (fun n => S n / (n : ℝ) ^ σ) = 
      fun n => (∑ k in Finset.range n, b k * ((k : ℝ) + 1) ^ σ) / (n : ℝ) ^ σ 
      by funext n; rw [h_sum n]]

  -- Apply summation by parts (Abel's lemma)
  have h_aux : ∀ n, ∑ k in Finset.range n, b k * ((k : ℝ) + 1) ^ σ = 
      s * (n : ℝ) ^ σ - ∑ k in Finset.range n, (s - ∑ j in Finset.range (k + 1), b j) * 
      (((k + 1 : ℝ) ^ σ) - (k : ℝ) ^ σ) := by
    intro n
    have := @summation_by_parts ℝ _ _ _ _ (fun k => (k : ℝ) ^ σ) (fun k => ∑ j in Finset.range k, b j) 0 n
    simp at this
    rw [this]
    simp [s]
    rw [← sum_range_add_sum_Ico _ (Nat.le_refl n)]
    simp
    congr
    ext k
    rw [← sub_sub, sub_right_comm]
    congr
    rw [← sum_range_succ]
    simp

  -- Simplify using the auxiliary result
  simp_rw [h_aux]
  simp only [div_eq_mul_inv, mul_sub]
  rw [← tendsto_sub_iff]
  refine tendsto_sub ?_ ?_
  · -- First term tends to s
    simp [mul_comm]
    exact tendsto_const_nhds
  · -- Second term tends to s
    have h_tendsto' : Tendsto (fun n : ℕ => ∑ k in Finset.range n, 
        (s - ∑ j in Finset.range (k + 1), b j) * (((k + 1 : ℝ) ^ σ - (k : ℝ) ^ σ) / (n : ℝ) ^ σ)) 
        atTop (𝓝 0) := by
      refine tendsto_zero_of_sum_tendsto_zero_of_nonneg_le ?_ ?_ ?_
      · intro k
        apply mul_nonneg
        · rw [sub_nonneg]
          exact le_tsum hb (k + 1) (fun i _ => le_of_lt (hb.nonneg_of_nonneg (fun _ => le_of_lt (by linarith))))
        · apply div_nonneg
          · apply sub_nonneg_of_le
            apply Real.rpow_le_rpow_of_nonneg (Nat.cast_le.2 (Nat.le_succ k)) (Nat.cast_nonneg k) hσ.le
          · exact Nat.cast_nonneg n
      · intro n
        calc _ ≤ ∑ k in Finset.range n, (s - ∑ j in Finset.range (k + 1), b j) * (σ * (k + 1) ^ (σ - 1)) / (n : ℝ) ^ σ := ?_
               _ ≤ ∑ k in Finset.range n, (ε / 2) * (σ * (k + 1) ^ (σ - 1)) / (n : ℝ) ^ σ := ?_
               _ = (ε / 2) * σ / (n : ℝ) ^ σ * ∑ k in Finset.range n, (k + 1) ^ (σ - 1) := ?_
               _ ≤ (ε / 2) * σ / (n : ℝ) ^ σ * (n + 1) ^ σ / σ := ?_
               _ ≤ ε / 2 := ?_
        sorry  -- These calculations would need more detailed steps
      · exact h_tendsto
    exact h_tendsto'
  done