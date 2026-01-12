/-
Polya-Szego Problem *194
Part One, Chapter 4

Original problem:
Show [by a combinatorial argument] that

$$
T_{n+1}=\binom{n}{0} T_{n}+\binom{n}{1} T_{n-1}+\binom{n}{2} T_{n-2}+\cdots+\binom{n}{n} T_{0} .
$$

Formalization notes: -- T_n represents the Bell number B_n (number of partitions of a set of size n)
-- The theorem states: B_{n+1} = Σ_{k=0}^n (choose n k) * B_{n-k}
-- This is equivalent to: B_{n+1} = Σ_{k=0}^n (choose n k) * B_k
-- since (choose n k) = (choose n (n-k)) and we can reindex the sum
-/

import Mathlib.Combinatorics.Bell
import Mathlib.Data.Nat.Choose.Basic

-- Formalization notes:
-- T_n represents the Bell number B_n (number of partitions of a set of size n)
-- The theorem states: B_{n+1} = Σ_{k=0}^n (choose n k) * B_{n-k}
-- This is equivalent to: B_{n+1} = Σ_{k=0}^n (choose n k) * B_k
-- since (choose n k) = (choose n (n-k)) and we can reindex the sum

theorem problem_194 (n : ℕ) : Bell (n + 1) = 
    ∑ k in Finset.range (n + 1), Nat.choose n k * Bell (n - k) := by
  sorry

-- Proof attempt:
theorem problem_194 (n : ℕ) : Bell (n + 1) = 
    ∑ k in Finset.range (n + 1), Nat.choose n k * Bell (n - k) := by
  rw [Bell.bell_succ]
  simp only [Nat.sum_antidiagonal_eq_sum_range_succ (fun k m ↦ Nat.choose n k * Bell m)]
  congr
  ext k
  rw [Nat.choose_symm (Nat.le_sub_of_add_le (Finset.mem_range.1 k.2))]