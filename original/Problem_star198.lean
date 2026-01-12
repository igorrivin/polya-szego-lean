/-
Polya-Szego Problem *198
Part One, Chapter 4

Original problem:
Obviously

$$
s_{1}^{n}=(n-1)!, \quad s_{n}^{n}=1 .
$$

Show that

$$
s_{k}^{n+1}=s_{k-1}^{n}+n s_{k}^{n} .
$$

Formalization notes: -- We formalize Stirling numbers of the first kind s(n, k) as Nat.stirling 1 n k
-- The recurrence s(n+1, k) = s(n, k-1) + n * s(n, k) for 1 ≤ k ≤ n+1
-- Base cases: s(n, 1) = (n-1)! and s(n, n) = 1 for n ≥ 1
-/

-- Imports
import Mathlib.Combinatorics.Stirling
import Mathlib.Data.Nat.Factorial.Basic

-- Formalization notes:
-- We formalize Stirling numbers of the first kind s(n, k) as Nat.stirling 1 n k
-- The recurrence s(n+1, k) = s(n, k-1) + n * s(n, k) for 1 ≤ k ≤ n+1
-- Base cases: s(n, 1) = (n-1)! and s(n, n) = 1 for n ≥ 1

theorem problem_198_part1 : 
    ∀ (n : ℕ) (h : n ≥ 1), 
      Nat.stirling 1 n 1 = (n - 1)! ∧ 
      Nat.stirling 1 n n = 1 := by
  sorry

theorem problem_198_recurrence : 
    ∀ (n k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ n + 1),
      Nat.stirling 1 (n + 1) k = 
        Nat.stirling 1 n (k - 1) + n * Nat.stirling 1 n k := by
  sorry

-- Proof attempt:
theorem problem_198_part1 : 
    ∀ (n : ℕ) (h : n ≥ 1), 
      Nat.stirling 1 n 1 = (n - 1)! ∧ 
      Nat.stirling 1 n n = 1 := by
  intro n hn
  constructor
  · exact Nat.stirling1_eq_fact_div n hn
  · exact Nat.stirling1_self n

theorem problem_198_recurrence : 
    ∀ (n k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ n + 1),
      Nat.stirling 1 (n + 1) k = 
        Nat.stirling 1 n (k - 1) + n * Nat.stirling 1 n k := by
  intro n k hk hk'
  exact Nat.stirling1_rec' n k hk hk'