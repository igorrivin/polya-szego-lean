/-
Polya-Szego Problem 37
Part Three, Chapter 1

Original problem:
Suppose that the numbers $z_{1}, z_{2}, \ldots, z_{n}, \ldots$ are all in the halfplane $\Re z \geqq 0$ and that the two series

$$
z_{1}+z_{2}+\cdots+z_{n}+\cdots \quad \text { and } \quad z_{1}^{2}+z_{2}^{2}+\cdots+z_{n}^{2}+\cdots
$$

converge. Then $\left|z_{1}\right|^{2}+\left|z_{2}\right|^{2}+\cdots+\left|z_{n}\right|^{2}+\cdots$ converges too.\\

Formalization notes: -- We formalize Problem 37 from Polya-Szego Part Three, Chapter 1:
-- Given a sequence of complex numbers z_n with Re(z_n) ≥ 0,
-- if both ∑ z_n and ∑ (z_n)^2 converge, then ∑ |z_n|^2 also converges.
-- We use Mathlib's convergence notions for series in ℂ.
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.NormedSpace.Basic

-- Formalization notes:
-- We formalize Problem 37 from Polya-Szego Part Three, Chapter 1:
-- Given a sequence of complex numbers z_n with Re(z_n) ≥ 0,
-- if both ∑ z_n and ∑ (z_n)^2 converge, then ∑ |z_n|^2 also converges.
-- We use Mathlib's convergence notions for series in ℂ.

theorem problem_37 {z : ℕ → ℂ} (h_nonneg_real : ∀ n, 0 ≤ (z n).re) 
    (h_sum_converges : Summable z) (h_sum_sq_converges : Summable (λ n => (z n) ^ 2)) : 
    Summable (λ n => Complex.normSq (z n)) := by
  sorry

-- Proof attempt:
theorem problem_37 {z : ℕ → ℂ} (h_nonneg_real : ∀ n, 0 ≤ (z n).re) 
    (h_sum_converges : Summable z) (h_sum_sq_converges : Summable (λ n => (z n) ^ 2)) : 
    Summable (λ n => Complex.normSq (z n)) := by
  -- Decompose z_n into real and imaginary parts
  let x := fun n => (z n).re
  let y := fun n => (z n).im
  
  -- Show summability of the real part series
  have hx_summable : Summable x := by
    simp [x]
    exact h_sum_converges.of_re
  
  -- Show summability of the real part of z_n^2 series
  have h_re_zsq_summable : Summable (fun n => (z n ^ 2).re) := by
    simp
    exact h_sum_sq_converges.of_re
  
  -- Express the real part of z_n^2 in terms of x and y
  have h_re_zsq_eq : (fun n => (z n ^ 2).re) = fun n => x n ^ 2 - y n ^ 2 := by
    ext n
    simp [x, y, Complex.mul_re]
    ring
  
  -- Rewrite the previous summability using this equality
  have h_xsq_ysq_summable : Summable (fun n => x n ^ 2 - y n ^ 2) := by
    rw [← h_re_zsq_eq]
    exact h_re_zsq_summable
  
  -- Show summability of x^2 series using nonnegativity and summability of x
  have h_xsq_summable : Summable (fun n => x n ^ 2) := by
    apply Summable.mul_of_nonneg hx_summable hx_summable
    intro n
    exact pow_two_nonneg (x n)
    intro n
    exact pow_two_nonneg (x n)
  
  -- Now show summability of y^2 series
  have h_ysq_summable : Summable (fun n => y n ^ 2) := by
    have : Summable (fun n => x n ^ 2 - (x n ^ 2 - y n ^ 2)) := by
      apply Summable.sub h_xsq_summable h_xsq_ysq_summable
    simp only [sub_sub_cancel] at this
    exact this
  
  -- Finally show summability of |z|^2 = x^2 + y^2
  have h_normsq_eq : (fun n => Complex.normSq (z n)) = fun n => x n ^ 2 + y n ^ 2 := by
    ext n
    simp [Complex.normSq, x, y]
  
  rw [h_normsq_eq]
  exact Summable.add h_xsq_summable h_ysq_summable