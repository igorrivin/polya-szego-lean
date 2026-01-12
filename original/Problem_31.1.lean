/-
Polya-Szego Problem 31.1
Part One, Chapter 1

Original problem:
Prove that

$$
\binom{n}{r}=\binom{n-1}{r-1}+\binom{n-1}{r}
$$

in several ways, especially with and without a combinatorial interpretation, with and without the binomial theorem.\\

Formalization notes: -- We formalize the standard recurrence relation for binomial coefficients:
--   C(n, r) = C(n-1, r-1) + C(n-1, r)
-- This holds for all natural numbers n and r, with the understanding that:
--   C(n, r) = 0 when r > n or r < 0
--   C(n, 0) = 1 for all n ≥ 0
--   C(0, 0) = 1
-- Mathlib's `Nat.choose` function handles these boundary cases correctly.
-/

import Mathlib.Data.Nat.Choose.Basic

-- Formalization notes:
-- We formalize the standard recurrence relation for binomial coefficients:
--   C(n, r) = C(n-1, r-1) + C(n-1, r)
-- This holds for all natural numbers n and r, with the understanding that:
--   C(n, r) = 0 when r > n or r < 0
--   C(n, 0) = 1 for all n ≥ 0
--   C(0, 0) = 1
-- Mathlib's `Nat.choose` function handles these boundary cases correctly.

theorem problem_31_1 (n r : ℕ) : Nat.choose n r = Nat.choose (n - 1) (r - 1) + Nat.choose (n - 1) r := by
  sorry

-- Proof attempt:
theorem problem_31_1 (n r : ℕ) : Nat.choose n r = Nat.choose (n - 1) (r - 1) + Nat.choose (n - 1) r := by
  cases n
  · -- Case n = 0
    cases r
    · simp
    · simp
  · -- Case n = Nat.succ n'
    cases r
    · simp
    · exact Nat.choose_succ_succ n r