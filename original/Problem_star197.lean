/-
Polya-Szego Problem *197
Part One, Chapter 4

Original problem:
Tabulate the numbers $s_{k}^{n}$ for $n \leqq 8,1 \leqq k \leqq n$.\\

Formalization notes: -- We're formalizing the table of unsigned Stirling numbers of the first kind s(n,k)
-- for n ≤ 8 and 1 ≤ k ≤ n. These are given by Nat.stirling1 in Mathlib4.
-- The theorem states that for each n from 1 to 8, the Stirling numbers match the given table.
-/

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Stirling

-- Formalization notes: 
-- We're formalizing the table of unsigned Stirling numbers of the first kind s(n,k)
-- for n ≤ 8 and 1 ≤ k ≤ n. These are given by Nat.stirling1 in Mathlib4.
-- The theorem states that for each n from 1 to 8, the Stirling numbers match the given table.

theorem problem_197 : 
  -- n = 1
  (Nat.stirling1 1 1 = 1) ∧
  -- n = 2
  (Nat.stirling1 2 1 = 1) ∧ (Nat.stirling1 2 2 = 1) ∧
  -- n = 3
  (Nat.stirling1 3 1 = 2) ∧ (Nat.stirling1 3 2 = 3) ∧ (Nat.stirling1 3 3 = 1) ∧
  -- n = 4
  (Nat.stirling1 4 1 = 6) ∧ (Nat.stirling1 4 2 = 11) ∧ (Nat.stirling1 4 3 = 6) ∧ (Nat.stirling1 4 4 = 1) ∧
  -- n = 5
  (Nat.stirling1 5 1 = 24) ∧ (Nat.stirling1 5 2 = 50) ∧ (Nat.stirling1 5 3 = 35) ∧ 
  (Nat.stirling1 5 4 = 10) ∧ (Nat.stirling1 5 5 = 1) ∧
  -- n = 6
  (Nat.stirling1 6 1 = 120) ∧ (Nat.stirling1 6 2 = 274) ∧ (Nat.stirling1 6 3 = 225) ∧
  (Nat.stirling1 6 4 = 85) ∧ (Nat.stirling1 6 5 = 15) ∧ (Nat.stirling1 6 6 = 1) ∧
  -- n = 7
  (Nat.stirling1 7 1 = 720) ∧ (Nat.stirling1 7 2 = 1764) ∧ (Nat.stirling1 7 3 = 1624) ∧
  (Nat.stirling1 7 4 = 735) ∧ (Nat.stirling1 7 5 = 175) ∧ (Nat.stirling1 7 6 = 21) ∧
  (Nat.stirling1 7 7 = 1) ∧
  -- n = 8
  (Nat.stirling1 8 1 = 5040) ∧ (Nat.stirling1 8 2 = 13068) ∧ (Nat.stirling1 8 3 = 13132) ∧
  (Nat.stirling1 8 4 = 6769) ∧ (Nat.stirling1 8 5 = 1960) ∧ (Nat.stirling1 8 6 = 322) ∧
  (Nat.stirling1 8 7 = 28) ∧ (Nat.stirling1 8 8 = 1) := by
  native_decide

-- Proof attempt:
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Stirling

theorem problem_197 : 
  (Nat.stirling1 1 1 = 1) ∧
  (Nat.stirling1 2 1 = 1) ∧ (Nat.stirling1 2 2 = 1) ∧
  (Nat.stirling1 3 1 = 2) ∧ (Nat.stirling1 3 2 = 3) ∧ (Nat.stirling1 3 3 = 1) ∧
  (Nat.stirling1 4 1 = 6) ∧ (Nat.stirling1 4 2 = 11) ∧ (Nat.stirling1 4 3 = 6) ∧ (Nat.stirling1 4 4 = 1) ∧
  (Nat.stirling1 5 1 = 24) ∧ (Nat.stirling1 5 2 = 50) ∧ (Nat.stirling1 5 3 = 35) ∧ 
  (Nat.stirling1 5 4 = 10) ∧ (Nat.stirling1 5 5 = 1) ∧
  (Nat.stirling1 6 1 = 120) ∧ (Nat.stirling1 6 2 = 274) ∧ (Nat.stirling1 6 3 = 225) ∧
  (Nat.stirling1 6 4 = 85) ∧ (Nat.stirling1 6 5 = 15) ∧ (Nat.stirling1 6 6 = 1) ∧
  (Nat.stirling1 7 1 = 720) ∧ (Nat.stirling1 7 2 = 1764) ∧ (Nat.stirling1 7 3 = 1624) ∧
  (Nat.stirling1 7 4 = 735) ∧ (Nat.stirling1 7 5 = 175) ∧ (Nat.stirling1 7 6 = 21) ∧
  (Nat.stirling1 7 7 = 1) ∧
  (Nat.stirling1 8 1 = 5040) ∧ (Nat.stirling1 8 2 = 13068) ∧ (Nat.stirling1 8 3 = 13132) ∧
  (Nat.stirling1 8 4 = 6769) ∧ (Nat.stirling1 8 5 = 1960) ∧ (Nat.stirling1 8 6 = 322) ∧
  (Nat.stirling1 8 7 = 28) ∧ (Nat.stirling1 8 8 = 1) := by
  native_decide