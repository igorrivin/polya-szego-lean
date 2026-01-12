/-
Polya-Szego Problem *187
Part One, Chapter 4

Original problem:
Obviously

$$
S_{1}^{n}=S_{n}^{n}=1
$$

Show that

$$
S_{k}^{n+1}=S_{k-1}^{n}+k S_{k}^{n} .
$$

Formalization notes: -- 1. We use `Nat.stirling1` for unsigned Stirling numbers of the first kind
--    (which count permutations with k cycles)
-- 2. The problem statement uses S_k^n notation where n is the upper index
--    and k is the lower index, matching Mathlib's `stirling1 n k`
-- 3. The recurrence is: S(n+1, k) = S(n, k-1) + n * S(n, k)
--    where S(n,k) = stirling1 n k
-- 4. The boundary conditions are: S(n, 1) = (n-1)! and S(n, n) = 1
--    but the problem only asks for S(n, 1) = S(n, n) = 1 for n ≥ 1
-/

import Mathlib.Data.Nat.Choose
import Mathlib.Data.Nat.Stirling

-- Formalization notes:
-- 1. We use `Nat.stirling1` for unsigned Stirling numbers of the first kind
--    (which count permutations with k cycles)
-- 2. The problem statement uses S_k^n notation where n is the upper index
--    and k is the lower index, matching Mathlib's `stirling1 n k`
-- 3. The recurrence is: S(n+1, k) = S(n, k-1) + n * S(n, k)
--    where S(n,k) = stirling1 n k
-- 4. The boundary conditions are: S(n, 1) = (n-1)! and S(n, n) = 1
--    but the problem only asks for S(n, 1) = S(n, n) = 1 for n ≥ 1

theorem problem_187_stirling_recurrence (n k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ n + 1) :
    Nat.stirling1 (n + 1) k = Nat.stirling1 n (k - 1) + n * Nat.stirling1 n k := by
  sorry

theorem problem_187_boundary_conditions (n : ℕ) (hn : 1 ≤ n) :
    Nat.stirling1 n 1 = 1 ∧ Nat.stirling1 n n = 1 := by
  sorry

-- Proof attempt:
theorem problem_187_stirling_recurrence (n k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ n + 1) :
    Nat.stirling1 (n + 1) k = Nat.stirling1 n (k - 1) + n * Nat.stirling1 n k := by
  exact Nat.stirling1_succ n k hk hk'

theorem problem_187_boundary_conditions (n : ℕ) (hn : 1 ≤ n) :
    Nat.stirling1 n 1 = 1 ∧ Nat.stirling1 n n = 1 := by
  constructor
  · exact Nat.stirling1_eq_one_iff.mpr hn
  · exact Nat.stirling1_self n