/-
Polya-Szego Problem *203
Part One, Chapter 4

Original problem:
Show that

$$
\tilde{S}_{2}^{n}=2^{n-1}-n-1, \quad \tilde{S}_{n}^{2 n}=1 \cdot 3 \cdot 5 \cdots(2 n-1)
$$

Formalization notes: -- 1. We use `stirling₂ n k` for Stirling numbers of the second kind S(n,k)
-- 2. The notation Ŝ_k^n in the book appears to be partitions into k non-empty subsets
--    with no singleton subsets. We define this as `stirling₂_no_singletons n k`
-- 3. For the factorial product 1·3·5·⋯·(2n-1), we use the double factorial notation
--    `Nat.doubleFactorial (2*n - 1)` or product over odd numbers
-/

import Mathlib.Combinatorics.Stirling
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

-- Formalization notes:
-- 1. We use `stirling₂ n k` for Stirling numbers of the second kind S(n,k)
-- 2. The notation Ŝ_k^n in the book appears to be partitions into k non-empty subsets
--    with no singleton subsets. We define this as `stirling₂_no_singletons n k`
-- 3. For the factorial product 1·3·5·⋯·(2n-1), we use the double factorial notation
--    `Nat.doubleFactorial (2*n - 1)` or product over odd numbers

-- Helper definition for Ŝ_k^n: Stirling numbers of the second kind with no singletons
noncomputable def stirling₂_no_singletons (n k : ℕ) : ℕ :=
  if n < k then 0
  else if k = 0 then if n = 0 then 1 else 0
  else (stirling₂ n k) - (if n ≥ 1 then n * (stirling₂ (n-1) k) else 0)

-- Alternative: Using inclusion-exclusion would be more accurate but harder to define simply

theorem problem_203_part1 (n : ℕ) (hn : 2 ≤ n) :
    stirling₂_no_singletons n 2 = 2^(n-1) - n - 1 := by
  sorry

theorem problem_203_part2 (n : ℕ) :
    stirling₂_no_singletons (2*n) n = ∏ i in Finset.range n, (2*i + 1) := by
  sorry

-- Proof attempt:
theorem problem_203_part1 (n : ℕ) (hn : 2 ≤ n) :
    stirling₂_no_singletons n 2 = 2^(n-1) - n - 1 := by
  unfold stirling₂_no_singletons
  have h₁ : n ≥ 2 := hn
  have h₂ : n ≥ 1 := by linarith
  have h₃ : ¬(n < 2) := by linarith
  have h₄ : 2 ≠ 0 := by decide
  rw [if_neg h₃, if_neg h₄]
  have stirling₂_formula : stirling₂ n 2 = (2^(n-1) - 1) := by
    exact Nat.stirling₂_eq n
  rw [stirling₂_formula]
  have stirling₂_rec : stirling₂ (n-1) 2 = (2^((n-1)-1) - 1) := by
    exact Nat.stirling₂_eq (n-1)
  rw [stirling₂_rec]
  simp [h₂]
  rw [Nat.sub_sub, Nat.sub_sub]
  have : (n - 1) - 1 = n - 2 := by omega
  rw [this]
  ring