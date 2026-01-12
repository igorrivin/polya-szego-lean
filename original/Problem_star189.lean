/-
Polya-Szego Problem *189
Part One, Chapter 4

Original problem:
Show that, for $n \geqq 1$,

$$
S_{k}^{n}=\frac{1}{k!}\left[k^{n}-\binom{k}{1}(k-1)^{n}+\binom{k}{2}(k-2)^{n}-\cdots+(-1)^{k} 0^{n}\right] .
$$

Formalization notes: -- We formalize the combinatorial interpretation of S_k^n as the number of surjections
-- from an n-element set to a k-element set, which equals k! * Stirling numbers of the second kind.
-- The formula given is the inclusion-exclusion formula for counting surjections.
-- We use ℕ for natural numbers and define the alternating sum formula.
-/

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.PartialFractions
import Mathlib.Analysis.Calculus.Residue

-- Formalization notes:
-- We formalize the combinatorial interpretation of S_k^n as the number of surjections
-- from an n-element set to a k-element set, which equals k! * Stirling numbers of the second kind.
-- The formula given is the inclusion-exclusion formula for counting surjections.
-- We use ℕ for natural numbers and define the alternating sum formula.

open Nat
open BigOperators

theorem problem_189 (n k : ℕ) (hk : 1 ≤ k) :
    ∑ i in Finset.range (k + 1), (-1 : ℤ) ^ i * (Nat.choose k i) * ((k - i : ℕ) ^ n : ℤ) = 
    (Nat.factorial k) * (Nat.stirlingS2 n k) := by
  sorry

-- Alternative formulation with explicit division by k!
theorem problem_189_alt (n k : ℕ) (hk : 1 ≤ k) :
    (∑ i in Finset.range (k + 1), (-1 : ℚ) ^ i * (Nat.choose k i : ℚ) * ((k - i : ℕ) ^ n : ℚ)) / (Nat.factorial k : ℚ) = 
    (Nat.stirlingS2 n k : ℚ) := by
  sorry

-- The original formula from the book (with 0^n interpreted as 0^0 = 1 when n=0)
theorem problem_189_original_formula (n k : ℕ) (hk : 1 ≤ k) :
    (1 / (Nat.factorial k : ℚ)) * 
    (∑ i in Finset.range (k + 1), (-1 : ℚ) ^ i * (Nat.choose k i : ℚ) * ((k - i : ℕ) ^ n : ℚ)) =
    if n = 0 ∧ k = 0 then 1 else if k > n then 0 else Nat.stirlingS2 n k := by
  sorry

-- Proof attempt:
theorem problem_189 (n k : ℕ) (hk : 1 ≤ k) :
    ∑ i in Finset.range (k + 1), (-1 : ℤ) ^ i * (Nat.choose k i) * ((k - i : ℕ) ^ n : ℤ) = 
    (Nat.factorial k) * (Nat.stirlingS2 n k) := by
  rw [← Int.ofNat_mul, ← Nat.cast_factorial, ← Nat.cast_stirlingS2]
  rw [← Nat.surjection_card]
  simp_rw [← Int.ofNat_pow, ← Int.ofNat_mul, ← Int.ofNat_choose]
  rw [Finset.sum_range_reflect (fun i => (-1 : ℤ) ^ i * (Nat.choose k i : ℤ) * (k - i : ℕ) ^ n : ℤ) k]
  simp_rw [Nat.sub_sub_self (le_of_lt (Finset.mem_range.1 (by simp))), Nat.choose_symm (le_of_lt (Finset.mem_range.1 (by simp)))]
  simp_rw [mul_assoc, ← mul_pow, ← mul_assoc]
  rw [Finset.sum_congr rfl (fun x hx => by 
      rw [Finset.mem_range] at hx
      rw [← mul_assoc, ← mul_assoc, mul_comm ((-1 : ℤ) ^ x) _, mul_assoc, mul_assoc])]
  simp_rw [← mul_add, ← mul_neg_one, ← pow_succ, neg_one_pow_mul_eq_zero_iff]
  rw [Finset.sum_mul]
  congr
  exact Finset.sum_range_reflect (fun i => (Nat.choose k i : ℤ) * (i : ℕ) ^ n) k