/-
Polya-Szego Problem 81.3
Part One, Chapter 2

Original problem:
The numbers

$$
\begin{gathered}
a_{1}, a_{2}, \ldots, a_{n} ; \quad b_{1}, b_{2}, \ldots, b_{n} ; \quad \ldots ; \quad l_{1}, l_{2}, \ldots, l_{n}, \\
\alpha, \beta, \ldots, \lambda
\end{gathered}
$$

are positive,

$$
\alpha+\beta+\cdots+\lambda=1 .
$$

Then

$$
\begin{gathered}
a_{1}^{\alpha} b_{1}^{\beta} \cdots l_{1}^{\lambda}+a_{2}^{\alpha} b_{2}^{\beta} \cdots l_{2}^{\lambda}+\cdots+a_{n}^{\alpha} b_{n}^{\beta} \cdots l_{n}^{\lambda} \\
\leqq\left(a_{1}+a_{2}+\cdots+a_{n}\right)^{\alpha}\

Formalization notes: -- 1. We formalize the inequality for n-tuples of positive reals
-- 2. We use Finset.sum for finite sums
-- 3. We assume we have k different sequences (a, b, ..., l) and k exponents (α, β, ..., λ)
-- 4. The exponents sum to 1 and are positive
-- 5. All numbers involved are positive reals
-- 6. We use Real.rpow for real exponentiation
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic

-- Formalization notes:
-- 1. We formalize the inequality for n-tuples of positive reals
-- 2. We use Finset.sum for finite sums
-- 3. We assume we have k different sequences (a, b, ..., l) and k exponents (α, β, ..., λ)
-- 4. The exponents sum to 1 and are positive
-- 5. All numbers involved are positive reals
-- 6. We use Real.rpow for real exponentiation

theorem problem_81_3 {k n : ℕ} (hpos : k > 0) (seqs : Fin k → Fin n → ℝ) (exps : Fin k → ℝ)
    (hseq_pos : ∀ i j, 0 < seqs i j) (hexp_pos : ∀ i, 0 < exps i) (hexp_sum : ∑ i : Fin k, exps i = 1) :
    ∑ j : Fin n, ∏ i : Fin k, (seqs i j) ^ (exps i) ≤ 
    ∏ i : Fin k, (∑ j : Fin n, seqs i j) ^ (exps i) := by
  sorry

-- Proof attempt:
theorem problem_81_3 {k n : ℕ} (hpos : k > 0) (seqs : Fin k → Fin n → ℝ) (exps : Fin k → ℝ)
    (hseq_pos : ∀ i j, 0 < seqs i j) (hexp_pos : ∀ i, 0 < exps i) (hexp_sum : ∑ i : Fin k, exps i = 1) :
    ∑ j : Fin n, ∏ i : Fin k, (seqs i j) ^ (exps i) ≤ 
    ∏ i : Fin k, (∑ j : Fin n, seqs i j) ^ (exps i) := by
  -- Define the sums for each sequence
  let sums := fun i => ∑ j, seqs i j
  have hsums_pos : ∀ i, 0 < sums i := by
    intro i
    apply Finset.sum_pos
    intro j _
    exact hseq_pos i j

  -- Rewrite the goal using these sums
  suffices ∑ j, ∏ i, (seqs i j / sums i) ^ (exps i) ≤ 1 by
    rw [← mul_le_mul_right (∏ i, (sums i) ^ (exps i))]
    · simp_rw [mul_sum, mul_prod]
      rw [prod_mul_distrib]
      conv => 
        lhs; intro j; arg 1; intro i; rw [← Real.rpow_mul (le_of_lt (hseq_pos i j))]
        rw [div_mul_cancel _ (ne_of_gt (hsums_pos i)), mul_comm, ← Real.rpow_mul (le_of_lt (hsums_pos i))]
        rw [hexp_sum, Real.rpow_one]
      simp [mul_comm]
    · apply prod_pos
      intro i _
      apply Real.rpow_pos_of_pos (hsums_pos i)

  -- Apply the generalized Hölder's inequality
  have : ∀ j, ∏ i, (seqs i j / sums i) ^ (exps i) ≤ ∑ i, exps i * (seqs i j / sums i) := by
    intro j
    apply Real.geom_mean_le_arith_mean_weighted _ _ hexp_sum (fun i => exps i) (fun i => seqs i j / sums i)
    · intro i
      exact le_of_lt (hexp_pos i)
    · intro i
      exact div_nonneg (le_of_lt (hseq_pos i j)) (le_of_lt (hsums_pos i))

  -- Sum over j and simplify
  calc
    ∑ j, ∏ i, (seqs i j / sums i) ^ (exps i) ≤ ∑ j, ∑ i, exps i * (seqs i j / sums i) := by
      apply Finset.sum_le_sum
      intro j _
      exact this j
    _ = ∑ i, ∑ j, exps i * (seqs i j / sums i) := by rw [Finset.sum_comm]
    _ = ∑ i, exps i * (∑ j, seqs i j / sums i) := by
      simp_rw [Finset.mul_sum]
    _ = ∑ i, exps i * 1 := by
      congr with i
      rw [← Finset.sum_div, div_self (ne_of_gt (hsums_pos i)), sum_const, card_fin, nsmul_eq_mul, mul_one]
    _ = 1 := by rw [← Finset.sum_mul, hexp_sum, one_mul]