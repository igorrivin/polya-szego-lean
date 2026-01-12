/-
Polya-Szego Problem *204
Part One, Chapter 4

Original problem:
Returning to $S_{k}^{n}$, show that

$$
S_{n-1}^{n}=\binom{n}{2}, \quad S_{n-2}^{n}=\binom{n}{3} \frac{3 n-5}{4}, \quad S_{n-3}^{n}=\binom{n}{4} \frac{(n-2)(n-3)}{2}
$$

and, generally, that $S_{n-a}^{n}$ is a polynomial in $n$ of degree $2 a$ divisible by $n(n-1)(n-2) \cdots(n-a)$; of course, $a \geqq 1$.\\

Formalization notes: -- We formalize S_k^n as the number of partitions of an n-element set into k non-empty subsets
-- (Stirling numbers of the second kind). The notation S_{n-a}^n in the problem corresponds
-- to StirlingS2 n (n-a) in our formalization.
-- We prove the three specific formulas given and state the general polynomial property.
-/

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Algebra.BigOperators.Fin

-- Formalization notes:
-- We formalize S_k^n as the number of partitions of an n-element set into k non-empty subsets
-- (Stirling numbers of the second kind). The notation S_{n-a}^n in the problem corresponds
-- to StirlingS2 n (n-a) in our formalization.
-- We prove the three specific formulas given and state the general polynomial property.

open Nat

-- Stirling numbers of the second kind
noncomputable def StirlingS2 (n k : ℕ) : ℕ :=
  if k > n then 0
  else if n = 0 then if k = 0 then 1 else 0
  else if k = 0 then 0
  else k * StirlingS2 (n-1) k + StirlingS2 (n-1) (k-1)

-- Helper lemma for StirlingS2 properties (would need to be proven separately)
theorem StirlingS2_eq_stirling (n k : ℕ) : StirlingS2 n k = Nat.stirlingS2 n k := by
  sorry

-- The three specific formulas from the problem
theorem problem_204_specific_formulas (n : ℕ) :
  -- S_{n-1}^n = C(n, 2)
  (StirlingS2 n (n-1)) = Nat.choose n 2 ∧
  -- S_{n-2}^n = C(n, 3) * (3n-5)/4, when 4 divides C(n, 3) * (3n-5)
  (4 * StirlingS2 n (n-2)) = Nat.choose n 3 * (3*n - 5) ∧
  -- S_{n-3}^n = C(n, 4) * (n-2)(n-3)/2, when 2 divides C(n, 4) * (n-2)(n-3)
  (2 * StirlingS2 n (n-3)) = Nat.choose n 4 * ((n-2) * (n-3)) := by
  sorry

-- The general polynomial property
theorem problem_204_general_property (a n : ℕ) (ha : a ≥ 1) (hn : n ≥ a) :
  -- S_{n-a}^n is a polynomial in n of degree 2a
  ∃ (p : Polynomial ℚ), 
    p.degree = some (2*a) ∧
    -- The polynomial evaluates to S_{n-a}^n at n
    (p.eval (n : ℚ)) = (StirlingS2 n (n-a) : ℚ) ∧
    -- The polynomial is divisible by n(n-1)...(n-a)
    (∃ (q : Polynomial ℚ), p = (∏ i in Finset.range (a+1), (Polynomial.X - (i : ℚ))) * q) := by
  sorry

-- Alternative formulation using the explicit sum from the book's solution
theorem problem_204_sum_formula (a n : ℕ) (ha : a ≥ 1) (hn : n ≥ 2*a) :
  StirlingS2 n (n-a) = 
    ∑ k in Finset.Icc (a+1) (2*a), 
      Nat.choose n k * StirlingS2 k (k - (n - (n-a))) := by
  -- Note: We need to simplify k - (n - (n-a)) = k - a
  -- But more precisely, from the book: S_{n-a}^n = Σ_{k=a+1}^{2a} C(n,k) * Ŝ_{k-a}^k
  -- where Ŝ_{k-a}^k are related Stirling numbers
  sorry

-- Proof attempt:
theorem problem_204_specific_formulas (n : ℕ) :
  (StirlingS2 n (n-1)) = Nat.choose n 2 ∧
  (4 * StirlingS2 n (n-2)) = Nat.choose n 3 * (3*n - 5) ∧
  (2 * StirlingS2 n (n-3)) = Nat.choose n 4 * ((n-2) * (n-3)) := by
  -- First convert StirlingS2 to mathlib's stirlingS2
  simp only [StirlingS2_eq_stirling]
  -- Split into three subgoals
  apply And.intro
  · -- First formula: S(n, n-1) = C(n,2)
    cases n with
    | zero => simp [stirlingS2]
    | succ n =>
      cases n with
      | zero => simp [stirlingS2]
      | succ n =>
        induction' n with n ih
        · simp [stirlingS2, Nat.choose]
        · have : n.succ.succ - 1 = n.succ := by omega
          rw [this, stirlingS2, Nat.choose_succ_succ]
          simp [ih, Nat.mul_add, Nat.add_comm, Nat.mul_comm]
          ring
  · apply And.intro
    · -- Second formula: 4*S(n,n-2) = C(n,3)*(3n-5)
      cases n with
      | zero => simp [stirlingS2]
      | succ n =>
        cases n with
        | zero => simp [stirlingS2]
        | succ n =>
          cases n with
          | zero => simp [stirlingS2, Nat.choose]
          | succ n =>
            induction' n with n ih
            · simp [stirlingS2, Nat.choose]
              norm_num
            · have : n.succ.succ.succ - 2 = n.succ := by omega
              rw [this, stirlingS2, Nat.choose_succ_succ]
              simp [ih, Nat.mul_add, Nat.add_comm, Nat.mul_comm]
              ring_nf
              rw [Nat.succ_eq_add_one, Nat.succ_eq_add_one, Nat.succ_eq_add_one]
              ring
    · -- Third formula: 2*S(n,n-3) = C(n,4)*(n-2)(n-3)
      cases n with
      | zero => simp [stirlingS2]
      | succ n =>
        cases n with
        | zero => simp [stirlingS2]
        | succ n =>
          cases n with
          | zero => simp [stirlingS2, Nat.choose]
          | succ n =>
            cases n with
            | zero => simp [stirlingS2, Nat.choose]
            | succ n =>
              induction' n with n ih
              · simp [stirlingS2, Nat.choose]
                norm_num
              · have : n.succ.succ.succ.succ - 3 = n.succ := by omega
                rw [this, stirlingS2, Nat.choose_succ_succ]
                simp [ih, Nat.mul_add, Nat.add_comm, Nat.mul_comm]
                ring_nf
                rw [Nat.succ_eq_add_one, Nat.succ_eq_add_one, Nat.succ_eq_add_one, Nat.succ_eq_add_one]
                ring