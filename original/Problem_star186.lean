/-
Polya-Szego Problem *186
Part One, Chapter 4

Original problem:
Tabulate the numbers $S_{k}^{n}$ for $n \leqq 8,1 \leqq k \leqq n$.\\

Formalization notes: -- We formalize Stirling numbers of the second kind S(n,k) for n ≤ 8, 1 ≤ k ≤ n
-- Using Mathlib's `Nat.stirling2` function which gives Stirling numbers of the second kind
-- The theorem states that for each n from 1 to 8, the Stirling numbers match the table
-/

import Mathlib.Data.Nat.Choose
import Mathlib.Data.Nat.Stirling

-- Formalization notes:
-- We formalize Stirling numbers of the second kind S(n,k) for n ≤ 8, 1 ≤ k ≤ n
-- Using Mathlib's `Nat.stirling2` function which gives Stirling numbers of the second kind
-- The theorem states that for each n from 1 to 8, the Stirling numbers match the table

theorem problem_186 : 
  -- n = 1
  (Nat.stirling2 1 1 = 1) ∧
  -- n = 2
  (Nat.stirling2 2 1 = 1 ∧ Nat.stirling2 2 2 = 1) ∧
  -- n = 3
  (Nat.stirling2 3 1 = 1 ∧ Nat.stirling2 3 2 = 3 ∧ Nat.stirling2 3 3 = 1) ∧
  -- n = 4
  (Nat.stirling2 4 1 = 1 ∧ Nat.stirling2 4 2 = 7 ∧ Nat.stirling2 4 3 = 6 ∧ Nat.stirling2 4 4 = 1) ∧
  -- n = 5
  (Nat.stirling2 5 1 = 1 ∧ Nat.stirling2 5 2 = 15 ∧ Nat.stirling2 5 3 = 25 ∧ 
   Nat.stirling2 5 4 = 10 ∧ Nat.stirling2 5 5 = 1) ∧
  -- n = 6
  (Nat.stirling2 6 1 = 1 ∧ Nat.stirling2 6 2 = 31 ∧ Nat.stirling2 6 3 = 90 ∧ 
   Nat.stirling2 6 4 = 65 ∧ Nat.stirling2 6 5 = 15 ∧ Nat.stirling2 6 6 = 1) ∧
  -- n = 7
  (Nat.stirling2 7 1 = 1 ∧ Nat.stirling2 7 2 = 63 ∧ Nat.stirling2 7 3 = 301 ∧ 
   Nat.stirling2 7 4 = 350 ∧ Nat.stirling2 7 5 = 140 ∧ Nat.stirling2 7 6 = 21 ∧ 
   Nat.stirling2 7 7 = 1) ∧
  -- n = 8
  (Nat.stirling2 8 1 = 1 ∧ Nat.stirling2 8 2 = 127 ∧ Nat.stirling2 8 3 = 966 ∧ 
   Nat.stirling2 8 4 = 1701 ∧ Nat.stirling2 8 5 = 1050 ∧ Nat.stirling2 8 6 = 266 ∧ 
   Nat.stirling2 8 7 = 28 ∧ Nat.stirling2 8 8 = 1) := by
  native_decide

-- Proof attempt:
theorem problem_186 : 
  -- n = 1
  (Nat.stirling2 1 1 = 1) ∧
  -- n = 2
  (Nat.stirling2 2 1 = 1 ∧ Nat.stirling2 2 2 = 1) ∧
  -- n = 3
  (Nat.stirling2 3 1 = 1 ∧ Nat.stirling2 3 2 = 3 ∧ Nat.stirling2 3 3 = 1) ∧
  -- n = 4
  (Nat.stirling2 4 1 = 1 ∧ Nat.stirling2 4 2 = 7 ∧ Nat.stirling2 4 3 = 6 ∧ Nat.stirling2 4 4 = 1) ∧
  -- n = 5
  (Nat.stirling2 5 1 = 1 ∧ Nat.stirling2 5 2 = 15 ∧ Nat.stirling2 5 3 = 25 ∧ 
   Nat.stirling2 5 4 = 10 ∧ Nat.stirling2 5 5 = 1) ∧
  -- n = 6
  (Nat.stirling2 6 1 = 1 ∧ Nat.stirling2 6 2 = 31 ∧ Nat.stirling2 6 3 = 90 ∧ 
   Nat.stirling2 6 4 = 65 ∧ Nat.stirling2 6 5 = 15 ∧ Nat.stirling2 6 6 = 1) ∧
  -- n = 7
  (Nat.stirling2 7 1 = 1 ∧ Nat.stirling2 7 2 = 63 ∧ Nat.stirling2 7 3 = 301 ∧ 
   Nat.stirling2 7 4 = 350 ∧ Nat.stirling2 7 5 = 140 ∧ Nat.stirling2 7 6 = 21 ∧ 
   Nat.stirling2 7 7 = 1) ∧
  -- n = 8
  (Nat.stirling2 8 1 = 1 ∧ Nat.stirling2 8 2 = 127 ∧ Nat.stirling2 8 3 = 966 ∧ 
   Nat.stirling2 8 4 = 1701 ∧ Nat.stirling2 8 5 = 1050 ∧ Nat.stirling2 8 6 = 266 ∧ 
   Nat.stirling2 8 7 = 28 ∧ Nat.stirling2 8 8 = 1) := by
  native_decide