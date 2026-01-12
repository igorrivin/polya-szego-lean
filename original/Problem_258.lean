/-
Polya-Szego Problem 258
Part Three, Chapter 5

Original problem:
We suppose that the functions of the sequence $f_{0}(z), f_{1}(z), f_{2}(z), \ldots, f_{n}(z), \ldots$ are analytic in the open region $\Re$ and that the sequence of their real parts converges uniformly in every closed subdomain of $\Re$. Then the sequence of their imaginary parts either diverges at all points or it converges uniformly in any closed subdomain of $\Re$.

\begin{enumerate}
  \setcounter{enumi}{258}
  \item The series
\end{enumerate}

$$
\begin{aligned}
\frac{z}{1+z} & +\frac{z^{2}

Formalization notes: -- We formalize the second part of Problem 258 about the specific series.
-- The theorem states that the given series converges uniformly on domains either entirely 
-- inside or outside the unit circle, with specific sums: z when |z| < 1 and 1 when |z| > 1.
-- We'll formalize this as two separate theorems for clarity: one for inside and one for outside.
-/

-- Imports
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.UniformConvergence
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.SpecificLimits.Basic

-- Formalization notes: 
-- We formalize the second part of Problem 258 about the specific series.
-- The theorem states that the given series converges uniformly on domains either entirely 
-- inside or outside the unit circle, with specific sums: z when |z| < 1 and 1 when |z| > 1.
-- We'll formalize this as two separate theorems for clarity: one for inside and one for outside.

open Complex
open Metric
open Filter

/-- Define the partial products in the denominator -/
def denominator (z : ℂ) : ℕ → ℂ :=
  fun n ↦ ∏ k in Finset.range n, (1 + z ^ (2 ^ k))

/-- Define the n-th term of the series -/
def term (z : ℂ) (n : ℕ) : ℂ :=
  z ^ (2 ^ n) / denominator z (n + 1)

/-- The partial sums of the series -/
def partial_sum (z : ℂ) (n : ℕ) : ℂ :=
  ∑ k in Finset.range n, term z k

-- Theorem for inside the unit circle
theorem converges_inside_unit_circle (z : ℂ) (hz : ‖z‖ < 1) :
    ∃ (s : ℂ), Tendsto (partial_sum z) atTop (𝓝 s) ∧ s = z := by
  sorry

-- Theorem for uniform convergence inside the unit circle
theorem uniform_convergence_inside_unit_circle {K : Set ℂ} (hK : IsCompact K) 
    (hK_sub : K ⊆ ball (0 : ℂ) 1) :
    UniformConvergenceOn (fun n z ↦ partial_sum z n) (fun z ↦ z) atTop K := by
  sorry

-- Theorem for outside the unit circle  
theorem converges_outside_unit_circle (z : ℂ) (hz : 1 < ‖z‖) :
    ∃ (s : ℂ), Tendsto (partial_sum z) atTop (𝓝 s) ∧ s = 1 := by
  sorry

-- Theorem for uniform convergence outside the unit circle
theorem uniform_convergence_outside_unit_circle {K : Set ℂ} (hK : IsCompact K)
    (hK_sub : K ⊆ {z : ℂ | 1 < ‖z‖}) :
    UniformConvergenceOn (fun n z ↦ partial_sum z n) (fun z ↦ (1 : ℂ)) atTop K := by
  sorry

/-- Main theorem combining both cases: In any compact set either entirely inside or 
    entirely outside the unit circle, the series converges uniformly to the 
    appropriate limit function. -/
theorem problem_258_part_two {K : Set ℂ} (hK : IsCompact K) 
    (hK_in : K ⊆ ball (0 : ℂ) 1 ∨ K ⊆ {z : ℂ | 1 < ‖z‖}) :
    UniformConvergenceOn (fun n z ↦ partial_sum z n) 
      (fun z ↦ if h : z ∈ K then if hK_in.isLeft then (z : ℂ) else (1 : ℂ) 
              else 0) atTop K := by
  sorry

-- Formalization notes:
-- 1. We define the denominator product and terms of the series explicitly
-- 2. We split the statement into multiple theorems for clarity:
--    - Pointwise convergence inside/outside
--    - Uniform convergence on compact sets inside/outside
--    - Combined theorem for any compact set in either region
-- 3. The main result captures: uniform convergence in domains lying either entirely
--    inside or entirely outside the unit circle
-- 4. The sum is z when |z| < 1 and 1 when |z| > 1
-- 5. The original problem's first part about sequences of analytic functions with 
--    uniformly convergent real parts is a separate complex analysis result that
--    could be formalized separately

-- Proof attempt:
theorem converges_inside_unit_circle (z : ℂ) (hz : ‖z‖ < 1) :
    ∃ (s : ℂ), Tendsto (partial_sum z) atTop (𝓝 s) ∧ s = z := by
  have h_denom : Tendsto (denominator z) atTop (𝓝 (1 - z)) := by
    have : denominator z = fun n ↦ (1 - z ^ (2 ^ n)) / (1 - z) := by
      ext n
      rw [denominator]
      induction n with
      | zero => simp
      | succ n ih =>
        rw [Finset.prod_range_succ, ih]
        field_simp
        rw [← pow_mul, pow_succ 2 n, mul_comm]
    rw [this]
    have h_pow : Tendsto (fun n ↦ z ^ (2 ^ n)) atTop (𝓝 0) := by
      apply tendsto_pow_atTop_nhds_0_of_norm_lt_1
      exact hz
    apply Tendsto.congr' (eventually_of_forall fun n ↦ by ring_nf)
    simp [inv_eq_one_div]
    exact tendsto_const_nhds.div (tendsto_const_nhds.sub h_pow) (sub_ne_zero_of_ne (by linarith [norm_pos_iff.mp (norm_pos_iff.mpr hz.ne')]).ne.symm)
  
  have : partial_sum z = fun n ↦ z - z ^ (2 ^ n) / denominator z n := by
    ext n
    rw [partial_sum, term]
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih, denominator]
      field_simp
      ring
  
  refine ⟨z, ?_, rfl⟩
  rw [this]
  apply Tendsto.sub_const
  apply Tendsto.div
  · apply tendsto_pow_atTop_nhds_0_of_norm_lt_1 hz
  · exact h_denom
  · simp [norm_pos_iff.mp (norm_pos_iff.mpr hz.ne')]