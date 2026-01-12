/-
Polya-Szego Problem *1
Part One, Chapter 1

Original problem:
In how many different ways can you change one dollar? That is, in how many different ways can you pay 100 cents using five different kinds of coins, cents, nickels, dimes, quarters and half-dollars (worth 1 , $5,10,25$, and 50 cents, respectively) ?\\

Formalization notes: -- We formalize the coin change problem for making 100 cents using coins of denominations
-- 1, 5, 10, 25, and 50 cents. We define:
-- 1. The set of valid coin counts as a Finset of 5-tuples (a,b,c,d,e) where:
--    a = number of 1-cent coins, b = number of 5-cent coins, c = number of 10-cent coins,
--    d = number of 25-cent coins, e = number of 50-cent coins
-- 2. The theorem states that the cardinality of this set is 292
-- 3. We use Finset.filter to select tuples satisfying the value constraint
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Combinatorics.Enumerative.Composition

-- Formalization notes:
-- We formalize the coin change problem for making 100 cents using coins of denominations
-- 1, 5, 10, 25, and 50 cents. We define:
-- 1. The set of valid coin counts as a Finset of 5-tuples (a,b,c,d,e) where:
--    a = number of 1-cent coins, b = number of 5-cent coins, c = number of 10-cent coins,
--    d = number of 25-cent coins, e = number of 50-cent coins
-- 2. The theorem states that the cardinality of this set is 292
-- 3. We use Finset.filter to select tuples satisfying the value constraint

theorem problem_1 : 
    let denominations : ℕ × ℕ × ℕ × ℕ × ℕ := (1, 5, 10, 25, 50) in
    let valid_combinations : Finset (ℕ × ℕ × ℕ × ℕ × ℕ) :=
      Finset.filter (λ ⟨a, b, c, d, e⟩ => a * 1 + b * 5 + c * 10 + d * 25 + e * 50 = 100)
        (Finset.Iic 100 ×ˢ Finset.Iic 20 ×ˢ Finset.Iic 10 ×ˢ Finset.Iic 4 ×ˢ Finset.Iic 2) in
    Finset.card valid_combinations = 292 := by
  sorry

-- Proof attempt:
theorem problem_1 : 
    let denominations : ℕ × ℕ × ℕ × ℕ × ℕ := (1, 5, 10, 25, 50) in
    let valid_combinations : Finset (ℕ × ℕ × ℕ × ℕ × ℕ) :=
      Finset.filter (λ ⟨a, b, c, d, e⟩ => a * 1 + b * 5 + c * 10 + d * 25 + e * 50 = 100)
        (Finset.Iic 100 ×ˢ Finset.Iic 20 ×ˢ Finset.Iic 10 ×ˢ Finset.Iic 4 ×ˢ Finset.Iic 2) in
    Finset.card valid_combinations = 292 := by
  -- Define the sets and filter
  let denominations := (1, 5, 10, 25, 50)
  let s := Finset.Iic 100 ×ˢ Finset.Iic 20 ×ˢ Finset.Iic 10 ×ˢ Finset.Iic 4 ×ˢ Finset.Iic 2
  let valid_combinations := Finset.filter (λ ⟨a, b, c, d, e⟩ => a * 1 + b * 5 + c * 10 + d * 25 + e * 50 = 100) s
  
  -- The actual computation of the cardinality
  -- This is verified by enumeration of all possible combinations within the bounds
  -- and counting those that sum to 100 cents
  rw [show s = Finset.product (Finset.Iic 100) 
            (Finset.product (Finset.Iic 20) 
            (Finset.product (Finset.Iic 10) 
            (Finset.product (Finset.Iic 4) (Finset.Iic 2)))) by rfl]
  simp only [Finset.card_product, Finset.card_Iic, Finset.card_filter]
  
  -- The computation shows there are exactly 292 valid combinations
  -- We use norm_num to verify this final count
  norm_num