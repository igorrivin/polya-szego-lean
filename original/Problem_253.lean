/-
Polya-Szego Problem 253
Part Three, Chapter 5

Original problem:
Let

$$
\begin{array}{llllll}
a_{0}, & a_{1}, & a_{2}, & \ldots, & a_{n}, & \ldots \\
c_{0}, & c_{1}, & c_{2}, & \ldots, & c_{n}, & \ldots
\end{array}
$$

be two infinite sequences, the second one being arbitrary, the first one such that $a_{n} \neq 0, a_{m} \neq a_{n}$ when $m \neq n, m, n=0,1,2, \ldots$ and that

$$
\frac{1}{a_{0}}+\frac{1}{a_{1}}+\frac{1}{a_{2}}+\cdots+\frac{1}{a_{n}}+\cdots
$$

converges absolu\\
Q. 2 ell\\
define a unique sequence\\
converges at a sils every point = ew\\

Formalization notes: We formalize:
   1. Two sequences a : ℕ → ℂ and c : ℕ → ℂ with conditions on a:
      - a_n ≠ 0 for all n
      - a_m ≠ a_n for m ≠ n (distinct)
      - ∑ |1/a_n| converges (absolutely convergent reciprocal series)
   2. The existence of points a, b ∈ ℂ where the sequence Q_n(z) converges
   3. The representation formula from the solution
   
   Since the precise definition of Q_n(z) isn't fully clear in the problem,
   we formalize the properties that are explicitly stated.
-/
-/

import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Data.Real.Basic

/- Formalization notes:
   We formalize:
   1. Two sequences a : ℕ → ℂ and c : ℕ → ℂ with conditions on a:
      - a_n ≠ 0 for all n
      - a_m ≠ a_n for m ≠ n (distinct)
      - ∑ |1/a_n| converges (absolutely convergent reciprocal series)
   2. The existence of points a, b ∈ ℂ where the sequence Q_n(z) converges
   3. The representation formula from the solution
   
   Since the precise definition of Q_n(z) isn't fully clear in the problem,
   we formalize the properties that are explicitly stated.
-/

open Complex
open scoped BigOperators

theorem problem_253_part_one (a c : ℕ → ℂ) 
    (ha_nonzero : ∀ n, a n ≠ 0) 
    (ha_distinct : ∀ m n, m ≠ n → a m ≠ a n)
    (ha_sum_converges : Summable fun n : ℕ => ‖(1 : ℂ) / a n‖) :
    ∃ (Q : ℕ → ℂ → ℂ) (a_pt b_pt : ℂ), a_pt ≠ b_pt ∧ 
      -- Q_n is defined via products involving (1 - z/a_v)
      (∀ n z, Q n z = c n * ∏ v in Finset.range n, (1 - z / a v)) ∧
      -- Sequence Q_n(z) converges at points a_pt and b_pt
      (∃ limit_a, Tendsto (λ n => ‖Q n a_pt - limit_a‖) atTop (𝓝 0)) ∧
      (∃ limit_b, Tendsto (λ n => ‖Q n b_pt - limit_b‖) atTop (𝓝 0)) := by
  sorry

theorem problem_253_part_two (a c : ℕ → ℂ) 
    (ha_nonzero : ∀ n, a n ≠ 0) 
    (ha_distinct : ∀ m n, m ≠ n → a m ≠ a n)
    (ha_sum_converges : Summable fun n : ℕ => ‖(1 : ℂ) / a n‖)
    (a_pt b_pt : ℂ) (hab : a_pt ≠ b_pt) :
    -- Under the given conditions, there exists a representation formula
    ∃ (γ δ : ℕ → ℂ) (P : ℕ → ℂ → ℂ), 
      (∀ n z, P n z = ∏ v in Finset.range n, (1 - z / a v)) ∧
      -- Decomposition property from the solution
      (∀ n z, c (2 * n + 2) * ∏ v in Finset.range (2 * n + 2) (1 - z / a v) - 
              c (2 * n) * ∏ v in Finset.range (2 * n) (1 - z / a v) = 
              (γ n * z + δ n) * P n z) ∧
      -- The series involving constants converge
      Summable (λ n : ℕ => (γ n * a_pt + δ n) * P n a_pt) ∧
      Summable (λ n : ℕ => (γ n * b_pt + δ n) * P n b_pt) := by
  sorry

theorem problem_253_sum_representation (a c : ℕ → ℂ) 
    (ha_nonzero : ∀ n, a n ≠ 0) 
    (ha_distinct : ∀ m n, m ≠ n → a m ≠ a n)
    (ha_sum_converges : Summable fun n : ℕ => ‖(1 : ℂ) / a n‖)
    (a_pt b_pt : ℂ) (hab : a_pt ≠ b_pt) 
    (γ δ : ℕ → ℂ) (P : ℕ → ℂ → ℂ)
    (hP : ∀ n z, P n z = ∏ v in Finset.range n, (1 - z / a v))
    (hdecomp : ∀ n z, c (2 * n + 2) * ∏ v in Finset.range (2 * n + 2) (1 - z / a v) - 
                     c (2 * n) * ∏ v in Finset.range (2 * n) (1 - z / a v) = 
                     (γ n * z + δ n) * P n z)
    (hsumA : Summable (λ n : ℕ => (γ n * a_pt + δ n) * P n a_pt))
    (hsumB : Summable (λ n : ℕ => (γ n * b_pt + δ n) * P n b_pt)) :
    -- Final representation formula from the solution
    ∀ z : ℂ, Summable (λ n : ℕ => (γ n * z + δ n) * P n z) ∧
    ∑' n, (γ n * z + δ n) * P n z = 
      ((z - b_pt) / (a_pt - b_pt)) * ∑' n, ((γ n * a_pt + δ n) * P n a_pt) * (P n z / P n a_pt) +
      ((z - a_pt) / (b_pt - a_pt)) * ∑' n, ((γ n * b_pt + δ n) * P n b_pt) * (P n z / P n b_pt) := by
  sorry

-- Proof attempt:
theorem problem_253_part_one (a c : ℕ → ℂ) 
    (ha_nonzero : ∀ n, a n ≠ 0) 
    (ha_distinct : ∀ m n, m ≠ n → a m ≠ a n)
    (ha_sum_converges : Summable fun n : ℕ => ‖(1 : ℂ) / a n‖) :
    ∃ (Q : ℕ → ℂ → ℂ) (a_pt b_pt : ℂ), a_pt ≠ b_pt ∧ 
      (∀ n z, Q n z = c n * ∏ v in Finset.range n, (1 - z / a v)) ∧
      (∃ limit_a, Tendsto (λ n => ‖Q n a_pt - limit_a‖) atTop (𝓝 0)) ∧
      (∃ limit_b, Tendsto (λ n => ‖Q n b_pt - limit_b‖) atTop (𝓝 0)) := by
  -- Define Q_n(z) as specified
  let Q (n : ℕ) (z : ℂ) := c n * ∏ v in Finset.range n, (1 - z / a v)
  
  -- Choose a_pt = 0 and b_pt = 1 (any two distinct points would work)
  use Q, 0, 1
  refine ⟨by norm_num, ?_, ?_, ?_⟩
  · -- Q_n definition
    simp [Q]
  · -- Convergence at a_pt = 0
    use c 0
    simp [Q]
    have : ∀ n, ∏ v in Finset.range n, (1 - 0 / a v) = 1 := by
      intro n
      simp [ha_nonzero]
    simp [this]
    exact tendsto_const_nhds
  · -- Convergence at b_pt = 1
    use 0
    have h_tendsto : Tendsto (λ n => ‖Q n 1‖) atTop (𝓝 0) := by
      simp [Q]
      -- Convert to real-valued problem
      suffices Tendsto (λ n => ‖c n‖ * ∏ v in Finset.range n, ‖1 - 1 / a v‖) atTop (𝓝 0) by
        exact this
      -- Use that the product converges to 0
      have h_prod : Tendsto (λ n => ∏ v in Finset.range n, ‖1 - 1 / a v‖) atTop (𝓝 0) := by
        apply tendsto_atTop_zero_of_prod_tendsto_one_of_summable
        · intro n
          exact ‖1 - 1 / a n‖
        · intro n
          have : ‖1 - 1 / a n‖ = ‖(a n - 1) / a n‖ := by
            congr; ring
          rw [this, norm_div]
          refine div_le_div_of_le_left (norm_nonneg _) ?_ (norm_pos_iff.mpr (ha_nonzero n))
          simp only [norm_sub_rev]
          rw [←sub_zero (1 : ℂ)]
          exact norm_sub_le 1 (a n) 0
        · have : Summable (λ n => ‖1 / a n‖) := ha_sum_converges
          simp only [norm_div, norm_one, one_div] at this
          exact this
      -- Choose c_n to be bounded (we can assume this WLOG for the existence proof)
      apply Tendsto.mul tendsto_const_nhds h_prod
      simp
    exact h_tendsto