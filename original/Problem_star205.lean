/-
Polya-Szego Problem *205
Part One, Chapter 4

Original problem:
Define $\tilde{T}_{0}=1$,

$$
\tilde{T}_{n}=\tilde{S}_{1}^{n}+\tilde{S}_{2}^{n}+\cdots+\tilde{S}_{n}^{n}
$$

for $n \geqq 1$. Compute $T_{n}$ and $\tilde{T}_{n}$ for $n \leqq 8$.\\

Formalization notes: -- We formalize T_n as the Bell numbers B_n (number of partitions of a set of size n)
-- We formalize \tilde{T}_n as the complementary Bell numbers \tilde{B}_n
-- The problem asks to compute these for n ≤ 8
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Finset.NatAntidiagonal

-- Formalization notes:
-- We formalize T_n as the Bell numbers B_n (number of partitions of a set of size n)
-- We formalize \tilde{T}_n as the complementary Bell numbers \tilde{B}_n
-- The problem asks to compute these for n ≤ 8

-- Bell numbers (T_n in the problem)
def bellNumber : ℕ → ℕ
  | 0 => 1
  | n + 1 => ∑ k : Finset.Icc 0 n, ((Nat.choose n k) * bellNumber k)

-- Complementary Bell numbers (\tilde{T}_n in the problem)
def compBellNumber : ℕ → ℤ
  | 0 => 1
  | n + 1 => ∑ k : Finset.Icc 0 n, ((-1 : ℤ) ^ (n - k)) * ((Nat.choose n k) * compBellNumber k)

-- Theorem stating the computed values for n ≤ 8
theorem problem_205_part_one : 
  -- Bell numbers T_n for n = 0 to 8
  (bellNumber 0 = 1) ∧ (bellNumber 1 = 1) ∧ (bellNumber 2 = 2) ∧ (bellNumber 3 = 5) ∧
  (bellNumber 4 = 15) ∧ (bellNumber 5 = 52) ∧ (bellNumber 6 = 203) ∧ 
  (bellNumber 7 = 877) ∧ (bellNumber 8 = 4140) ∧
  -- Complementary Bell numbers \tilde{T}_n for n = 0 to 8
  (compBellNumber 0 = (1 : ℤ)) ∧ (compBellNumber 1 = (0 : ℤ)) ∧ 
  (compBellNumber 2 = (1 : ℤ)) ∧ (compBellNumber 3 = (1 : ℤ)) ∧
  (compBellNumber 4 = (4 : ℤ)) ∧ (compBellNumber 5 = (11 : ℤ)) ∧ 
  (compBellNumber 6 = (41 : ℤ)) ∧ (compBellNumber 7 = (162 : ℤ)) ∧
  (compBellNumber 8 = (715 : ℤ)) := by
  sorry

-- Proof attempt:
theorem problem_205_part_one : 
  (bellNumber 0 = 1) ∧ (bellNumber 1 = 1) ∧ (bellNumber 2 = 2) ∧ (bellNumber 3 = 5) ∧
  (bellNumber 4 = 15) ∧ (bellNumber 5 = 52) ∧ (bellNumber 6 = 203) ∧ 
  (bellNumber 7 = 877) ∧ (bellNumber 8 = 4140) ∧
  (compBellNumber 0 = (1 : ℤ)) ∧ (compBellNumber 1 = (0 : ℤ)) ∧ 
  (compBellNumber 2 = (1 : ℤ)) ∧ (compBellNumber 3 = (1 : ℤ)) ∧
  (compBellNumber 4 = (4 : ℤ)) ∧ (compBellNumber 5 = (11 : ℤ)) ∧ 
  (compBellNumber 6 = (41 : ℤ)) ∧ (compBellNumber 7 = (162 : ℤ)) ∧
  (compBellNumber 8 = (715 : ℤ)) := by
  simp [bellNumber, compBellNumber]
  norm_num
  have : Finset.Icc 0 0 = {0} := by rfl
  simp [this]
  norm_num
  have : Finset.Icc 0 1 = {0, 1} := by rfl
  simp [this]
  norm_num
  have : Finset.Icc 0 2 = {0, 1, 2} := by rfl
  simp [this]
  norm_num
  have : Finset.Icc 0 3 = {0, 1, 2, 3} := by rfl
  simp [this]
  norm_num
  have : Finset.Icc 0 4 = {0, 1, 2, 3, 4} := by rfl
  simp [this]
  norm_num
  have : Finset.Icc 0 5 = {0, 1, 2, 3, 4, 5} := by rfl
  simp [this]
  norm_num
  have : Finset.Icc 0 6 = {0, 1, 2, 3, 4, 5, 6} := by rfl
  simp [this]
  norm_num
  have : Finset.Icc 0 7 = {0, 1, 2, 3, 4, 5, 6, 7} := by rfl
  simp [this]
  norm_num