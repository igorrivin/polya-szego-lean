/-
Polya-Szego Problem 36
Part Three, Chapter 1

Original problem:
Assume the $-x \leqq \arg z \leqq{ }_{x}$. s

$$
z_{1}+z_{2}+\cdots
$$

are either both con\\
of $P(z)$ lie in the interior of the smallest convex polygon (the smallest line segment) that contains the zeros of $P(z)$.\\

Formalization notes: -- We formalize the statement: For complex numbers z_n with arguments bounded by α ∈ (0, π/2),
-- the series ∑ Re(z_n) converges absolutely if and only if ∑ |z_n| converges.
-- The "converse is obvious" part is handled by the equivalence.
-- We use absolute convergence since the problem mentions convergence of ∑|z_n|.
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

-- Formalization notes:
-- We formalize the statement: For complex numbers z_n with arguments bounded by α ∈ (0, π/2),
-- the series ∑ Re(z_n) converges absolutely if and only if ∑ |z_n| converges.
-- The "converse is obvious" part is handled by the equivalence.
-- We use absolute convergence since the problem mentions convergence of ∑|z_n|.

theorem problem_36 (α : ℝ) (hα : 0 < α ∧ α < π/2) (z : ℕ → ℂ) 
    (harg : ∀ n, -α ≤ (z n).arg ∧ (z n).arg ≤ α) :
    (Summable fun n : ℕ => Real.abs ((z n).re)) ↔ Summable fun n : ℕ => Complex.abs (z n)) := by
  sorry

-- Proof attempt:
theorem problem_36 (α : ℝ) (hα : 0 < α ∧ α < π/2) (z : ℕ → ℂ) 
    (harg : ∀ n, -α ≤ (z n).arg ∧ (z n).arg ≤ α) :
    (Summable fun n : ℕ => Real.abs ((z n).re)) ↔ Summable fun n : ℕ => Complex.abs (z n)) := by
  constructor
  · intro h
    have cos_pos : 0 < Real.cos α := by
      apply Real.cos_pos_of_mem_Ioo
      rw [← neg_lt_zero, neg_neg]
      exact ⟨by linarith [hα.1], hα.2⟩
    have bound : ∀ n, Complex.abs (z n) ≤ (Real.abs ((z n).re)) / Real.cos α := by
      intro n
      rw [Complex.abs, Real.abs_eq_self.mpr (le_of_lt (Real.cos_pos_of_mem_Ioo
            ⟨by linarith [hα.1, (harg n).1], by linarith [hα.2, (harg n).2]⟩))]
      have := Complex.abs_re_le_abs (z n)
      rw [Complex.abs, Real.sqrt_sq_eq_abs] at this
      have arg_eq : (z n).re = Complex.abs (z n) * Real.cos (z n).arg := by
        rw [← Complex.re_eq_abs_mul_cos_arg (z n)]
      rw [arg_eq]
      have cos_bound : Real.cos (z n).arg ≥ Real.cos α := by
        apply Real.cos_ge_of_mem_Icc
        · rw [abs_le]
          exact ⟨(harg n).1, (harg n).2⟩
        · exact ⟨by linarith [hα.1], hα.2⟩
      rw [Real.abs_mul]
      simp only [Real.abs_eq_self.mpr (Complex.abs.nonneg _)]
      apply div_le_of_le_mul cos_pos.le
      rw [mul_comm]
      exact mul_le_of_le_one_right (Complex.abs.nonneg _) cos_bound
    apply Summable.of_nonneg_of_le (fun n => Complex.abs.nonneg _) bound
    exact Summable.of_norm h
  · intro h
    have : ∀ n, Real.abs ((z n).re) ≤ Complex.abs (z n) := by
      intro n
      exact Complex.abs_re_le_abs (z n)
    exact Summable.of_nonneg_of_le (fun n => Real.abs_nonneg _) this h