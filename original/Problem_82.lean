/-
Polya-Szego Problem 82
Part One, Chapter 2

Original problem:
Let the\\
be condergent \&\\
□\\
I\\
is converge: 4

\begin{enumerate}
  \setcounter{enumi}{78}
  \item Consider the infinite matrix
\end{enumerate}

$$
\begin{aligned}
& p_{00}, p_{01}, p_{02}, \ldots \\
& p_{10}, p_{11}, p_{12}, \ldots \\
& p_{20}, p_{21}, p_{22}, \ldots
\end{aligned}
$$

Suppose that all the numbers $p_{n v}$ are non-negative and that the sum in each row is convergent and equal to $1\left(p_{n v} \geqq 0 ; \sum_{\nu=0}^{\infty} p_{n v}=1\right.$, for $n$, $v=0,1,2, \ldots$ ).

Formalization notes: We formalize Problem 82 from Polya-Szego Part One, Chapter 2.
-/

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Instances.Real

/-!
Formalization notes:
We formalize Problem 82 from Polya-Szego Part One, Chapter 2.

We define:
- `p : ℕ → ℕ → ℝ` as the infinite matrix with non-negative entries
- `s : ℕ → ℝ` as the bounded original sequence
- `t : ℕ → ℝ` as the transformed sequence where `t n = ∑_{ν=0}∞ p n ν * s ν`

We assume:
1. All `p n ν ≥ 0` (non-negativity)
2. For each `n`, the series `∑_{ν=0}∞ p n ν` converges to 1
3. The sequence `s` is bounded

We prove that for each `n`, `t n` lies between the lower and upper bounds of `s`.
Specifically: `lower_bound ≤ t n ≤ upper_bound` where:
  `lower_bound = ⨅ i, s i` (infimum/limit inferior could also be used)
  `upper_bound = ⨆ i, s i` (supremum/limit superior)

Note: We use `iInf` and `iSup` for the bounds since `s` is bounded.
-/

open Real
open Set

theorem problem_82_part1 (p : ℕ → ℕ → ℝ) (s : ℕ → ℝ) 
    (h_nonneg : ∀ n ν, 0 ≤ p n ν) 
    (h_row_sum : ∀ n, HasSum (λ ν => p n ν) 1) 
    (h_bounded : Bounded (Set.range s)) :
    let lower_bound := ⨅ i, s i
    let upper_bound := ⨆ i, s i
    let t (n : ℕ) : ℝ := ∑' ν, p n ν * s ν
    in ∀ n, lower_bound ≤ t n ∧ t n ≤ upper_bound := by
  sorry

-- Proof attempt:
theorem problem_82_part1 (p : ℕ → ℕ → ℝ) (s : ℕ → ℝ) 
    (h_nonneg : ∀ n ν, 0 ≤ p n ν) 
    (h_row_sum : ∀ n, HasSum (λ ν => p n ν) 1) 
    (h_bounded : Bounded (Set.range s)) :
    let lower_bound := ⨅ i, s i
    let upper_bound := ⨆ i, s i
    let t (n : ℕ) : ℝ := ∑' ν, p n ν * s ν
    in ∀ n, lower_bound ≤ t n ∧ t n ≤ upper_bound := by
  intro n
  let lower_bound := ⨅ i, s i
  let upper_bound := ⨆ i, s i
  let t (n : ℕ) : ℝ := ∑' ν, p n ν * s ν
  have h_lower : ∀ i, lower_bound ≤ s i := by simp [lower_bound, le_iInf]
  have h_upper : ∀ i, s i ≤ upper_bound := by simp [upper_bound, iSup_le]
  
  -- First prove t n ≤ upper_bound
  have sum_p : ∑' ν, p n ν = 1 := (h_row_sum n).tsum_eq
  have t_eq : t n = ∑' ν, p n ν * s ν := rfl
  
  have t_le : t n ≤ upper_bound := by
    calc t n = ∑' ν, p n ν * s ν := rfl
         _ ≤ ∑' ν, p n ν * upper_bound := by
           apply tsum_le_tsum
           · intro ν
             exact mul_le_mul_of_nonneg_left (h_upper ν) (h_nonneg n ν)
           · apply Summable.mul_right _ upper_bound
             exact (h_row_sum n).summable
           · exact (h_row_sum n).summable.mul_right upper_bound
         _ = upper_bound * ∑' ν, p n ν := by rw [tsum_mul_right]
         _ = upper_bound := by rw [sum_p, mul_one]
  
  -- Now prove lower_bound ≤ t n
  have t_ge : lower_bound ≤ t n := by
    calc lower_bound = lower_bound * ∑' ν, p n ν := by rw [sum_p, mul_one]
         _ = ∑' ν, lower_bound * p n ν := by rw [tsum_mul_left]
         _ ≤ ∑' ν, p n ν * s ν := by
           apply tsum_le_tsum
           · intro ν
             rw [mul_comm]
             exact mul_le_mul_of_nonneg_left (h_lower ν) (h_nonneg n ν)
           · apply Summable.mul_right _ lower_bound
             exact (h_row_sum n).summable
           · exact (h_row_sum n).summable.mul_left
         _ = t n := rfl
  
  exact ⟨t_ge, t_le⟩