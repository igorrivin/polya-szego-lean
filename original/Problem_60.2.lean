/-
Polya-Szego Problem 60.2
Part One, Chapter 1

Original problem:
Show that

$$
\left[\begin{array}{l}
n \\
k
\end{array}\right]=\left[\begin{array}{c}
n \\
n-k
\end{array}\right] .
$$

Pay attention to the case $k=0$.\\

Formalization notes: -- This formalizes the symmetry of binomial coefficients: n choose k = n choose (n - k)
-- The theorem handles the case when k > n by using Nat.choose_eq_zero_of_lt
-- The case k = 0 is included as it's already covered by the general formula since n choose 0 = n choose n = 1
-/

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

-- Formalization notes:
-- This formalizes the symmetry of binomial coefficients: n choose k = n choose (n - k)
-- The theorem handles the case when k > n by using Nat.choose_eq_zero_of_lt
-- The case k = 0 is included as it's already covered by the general formula since n choose 0 = n choose n = 1

theorem problem_60_2 {n k : ℕ} : Nat.choose n k = Nat.choose n (n - k) := by
  by_cases h : k ≤ n
  · rw [Nat.choose_symm h]
  · have h' : n < k := Nat.lt_of_not_ge h
    have h1 : Nat.choose n k = 0 := Nat.choose_eq_zero_of_lt h'
    have h2 : n - k = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_lt h')
    rw [h1, h2, Nat.choose_zero_right]

-- Proof attempt:
theorem problem_60_2 {n k : ℕ} : Nat.choose n k = Nat.choose n (n - k) := by
  by_cases h : k ≤ n
  · rw [Nat.choose_symm h]
  · have h' : n < k := Nat.lt_of_not_ge h
    have h1 : Nat.choose n k = 0 := Nat.choose_eq_zero_of_lt h'
    have h2 : n - k = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_lt h')
    rw [h1, h2, Nat.choose_zero_right]