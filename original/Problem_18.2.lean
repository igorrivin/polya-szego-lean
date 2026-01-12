/-
Polya-Szego Problem 18.2
Part One, Chapter 1

Original problem:
In a legislative assembly there are $2 n+1$ seats and three parties. In how many different ways can the seats be distributed among the parties so that no party attains a majority against a coalition of the other two parties?\\
19.\\
$(1+\zeta)\left(1+\zeta^{2}\right)\left(1+\zeta^{3}\right)\left(1+\zeta^{4}\right) \cdots=\frac{1}{(1-\zeta)\left(1-\zeta^{3}\right)\left(1-\zeta^{5}\right)\left(1-\zeta^{7}\right) \cdots}$.\\

Formalization notes: -- We're formalizing Problem 18.2 from Polya-Szego:
-- "In a legislative assembly there are 2n+1 seats and three parties.
-- In how many different ways can the seats be distributed among the parties
-- so that no party attains a majority against a coalition of the other two parties?"
--
-- This means: Count integer solutions (x₁, x₂, x₃) where:
-- 1. x₁ + x₂ + x₃ = 2n + 1
-- 2. 0 ≤ xᵢ ≤ n for i = 1,2,3 (no party gets more than n seats)
-- 3. xᵢ are nonnegative integers
--
-- The book's solution gives: E_{2n+1} = (n+1 choose 2) = (n+1)*n/2
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Combinatorics.Composition
import Mathlib.Data.Nat.Choose.Basic

-- Formalization notes:
-- We're formalizing Problem 18.2 from Polya-Szego:
-- "In a legislative assembly there are 2n+1 seats and three parties.
-- In how many different ways can the seats be distributed among the parties
-- so that no party attains a majority against a coalition of the other two parties?"
--
-- This means: Count integer solutions (x₁, x₂, x₃) where:
-- 1. x₁ + x₂ + x₃ = 2n + 1
-- 2. 0 ≤ xᵢ ≤ n for i = 1,2,3 (no party gets more than n seats)
-- 3. xᵢ are nonnegative integers
--
-- The book's solution gives: E_{2n+1} = (n+1 choose 2) = (n+1)*n/2

theorem problem_18_2 (n : ℕ) : 
    Finset.card (Finset.filter 
      (fun (x : ℕ × ℕ × ℕ) => 
        x.1 + x.2.1 + x.2.2 = 2*n + 1 ∧ 
        x.1 ≤ n ∧ x.2.1 ≤ n ∧ x.2.2 ≤ n) 
      (Finset.Nat.antidiagonal (2*n+1) ×ˢ Finset.Nat.antidiagonal (2*n+1) ×ˢ Finset.Nat.antidiagonal (2*n+1))) = 
    Nat.choose (n + 1) 2 := by
  sorry

-- Alternative formulation using compositions/partitions
theorem problem_18_2_alt (n : ℕ) : 
    let solutions : Finset (ℕ × ℕ × ℕ) :=
      (Finset.range (n+1)).filter (fun a => a ≤ 2*n+1) ×ˢ
      (Finset.range (n+1)).filter (fun b => b ≤ 2*n+1) ×ˢ
      (Finset.range (n+1)).filter (fun c => c ≤ 2*n+1)
    in
    Finset.card (solutions.filter 
      (fun (a, b, c) => a + b + c = 2*n + 1 ∧ a ≤ n ∧ b ≤ n ∧ c ≤ n)) = 
    Nat.choose (n + 1) 2 := by
  sorry

-- Even cleaner formulation using bounded sums
theorem problem_18_2_clean (n : ℕ) : 
    Finset.card {x : Fin 3 → ℕ | 
      (∑ i, x i) = 2*n + 1 ∧ ∀ i, x i ≤ n} = 
    Nat.choose (n + 1) 2 := by
  sorry

-- Proof attempt:
theorem problem_18_2 (n : ℕ) : 
    Finset.card (Finset.filter 
      (fun (x : ℕ × ℕ × ℕ) => 
        x.1 + x.2.1 + x.2.2 = 2*n + 1 ∧ 
        x.1 ≤ n ∧ x.2.1 ≤ n ∧ x.2.2 ≤ n) 
      (Finset.Nat.antidiagonal (2*n+1) ×ˢ Finset.Nat.antidiagonal (2*n+1) ×ˢ Finset.Nat.antidiagonal (2*n+1))) = 
    Nat.choose (n + 1) 2 := by
  -- The count is equivalent to choosing two distinct numbers a,b ≤ n where a + b ≥ n + 1
  -- Then c = 2n + 1 - a - b will automatically be ≤ n
  -- The number of such pairs is (n+1 choose 2)
  
  -- First simplify the filter set
  simp_rw [Finset.Nat.mem_antidiagonal, Finset.mem_product, Finset.mem_filter]
  -- The condition x.1 + x.2.1 + x.2.2 = 2*n + 1 is redundant since we're taking antidiagonals
  simp only [and_assoc]
  -- Now count the triples (a,b,c) where a + b + c = 2n+1 and each ≤ n
  -- This is equivalent to counting pairs (a,b) where a + b ≥ n+1 and a,b ≤ n
  -- Since c = 2n+1 - a - b must be ≤ n ⇒ a + b ≥ n+1
  -- And since a,b ≤ n, a + b ≤ 2n ⇒ c ≥ 1
  
  -- The count of such pairs is equal to the number of ways to choose two distinct numbers ≤ n
  -- since for any a < b, exactly one of (a,b) or (b,a) will satisfy a + b ≥ n+1
  -- The total count is (n+1 choose 2)
  
  -- Formal proof:
  let s := Finset.filter (fun (a, b, c) => a + b + c = 2*n + 1 ∧ a ≤ n ∧ b ≤ n ∧ c ≤ n)
    (Finset.Nat.antidiagonal (2*n+1) ×ˢ Finset.Nat.antidiagonal (2*n+1) ×ˢ Finset.Nat.antidiagonal (2*n+1))
  
  -- Create bijection with pairs (a,b) where a + b ≥ n+1 and a,b ≤ n
  let t := Finset.filter (fun (a, b) => a + b ≥ n + 1 ∧ a ≤ n ∧ b ≤ n)
    (Finset.Nat.antidiagonal (2*n+1) ×ˢ Finset.Nat.antidiagonal (2*n+1))
  
  have : Finset.card s = Finset.card t := by
    refine Finset.card_congr (fun (a,b,c) _ => (a,b)) ?_ (by simp) (by simp)
    intro (a,b,c) h
    simp only [Finset.mem_filter, Finset.mem_product, Finset.Nat.mem_antidiagonal] at h ⊢
    obtain ⟨⟨h1, h2, h3⟩, ha, hb, hc⟩ := h
    simp [h1, h2, h3, ha, hb]
    have : c = 2*n + 1 - a - b := by linarith
    subst this
    constructor <;> linarith
  
  -- Now count the number of pairs (a,b) with a + b ≥ n+1 and a,b ≤ n
  -- This equals the number of pairs where a + b ≤ n (by symmetry) which is (n+1 choose 2)
  have : Finset.card t = Nat.choose (n + 1) 2 := by
    -- Total number of pairs (a,b) with a,b ≤ n is (n+1)^2
    -- Number with a + b ≤ n is (n+1 choose 2) + (n+1) = (n+2 choose 2)
    -- Number with a + b ≥ n+1 is (n+1)^2 - (n+2 choose 2) = (n+1 choose 2)
    have total_pairs : Finset.card (Finset.range (n+1) ×ˢ Finset.range (n+1)) = (n+1)^2 := by
      simp [Finset.card_product, Finset.card_range]
    
    let low_sum := Finset.filter (fun (a,b) => a + b ≤ n) (Finset.range (n+1) ×ˢ Finset.range (n+1))
    have card_low_sum : Finset.card low_sum = Nat.choose (n + 2) 2 := by
      rw [Finset.card_eq_sum_ones]
      simp_rw [Finset.sum_filter]
      rw [Finset.sum_product]
      simp [Finset.sum_range_id, Nat.sum_range_id_eq_choose_two]
      ring_nf
      rw [Nat.choose_succ_succ, Nat.choose_one_right, Nat.choose_zero_right]
      ring
    
    have : Finset.card t = (n+1)^2 - Nat.choose (n + 2) 2 := by
      rw [← total_pairs]
      refine Finset.card_sdiff ?_
      · apply Finset.filter_subset
      · simp [low_sum, t]
    
    rw [this]
    have : (n+1)^2 = Nat.choose (n + 1) 2 + Nat.choose (n + 2) 2 := by
      rw [Nat.choose_succ_succ, Nat.choose_one_right, Nat.choose_zero_right]
      ring
    linarith
  
  rw [this]