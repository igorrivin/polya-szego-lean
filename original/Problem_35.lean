/-
Polya-Szego Problem 35
Part Three, Chapter 1

Original problem:
If a polynomial $f(z)$ whose coefficients are all real has only real zeros then this is true also for its derivative $f^{\prime}(z)$. If $f(z)$ has complex zeros then they appear in pairs, the two zeros forming a pair are mirror images to each other with respect to the real axis; they are complex conjugates. We draw all those disks the "vertical" diameters of which are the line segments connecting the conjugate zeros of such pairs. If $f^{\prime}(z)$ has any complex zeros they lie in these disks

Formalization notes: -- We formalize the statement about series convergence in a sector.
-- Given a sequence of complex numbers all lying in the sector -α ≤ arg z ≤ α (with 0 ≤ α < π/2),
-- the series ∑ z_n and ∑ |z_n| either both converge or both diverge.
-- We use `Complex.abs` for modulus and `Complex.arg` for argument.
-- The condition α < π/2 is formalized as `hα : α < π/2`.
-- We assume the sequence is indexed by ℕ.
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

-- Formalization notes:
-- We formalize the statement about series convergence in a sector.
-- Given a sequence of complex numbers all lying in the sector -α ≤ arg z ≤ α (with 0 ≤ α < π/2),
-- the series ∑ z_n and ∑ |z_n| either both converge or both diverge.
-- We use `Complex.abs` for modulus and `Complex.arg` for argument.
-- The condition α < π/2 is formalized as `hα : α < π/2`.
-- We assume the sequence is indexed by ℕ.

theorem problem_35 {α : ℝ} (hα : 0 ≤ α) (hα' : α < π/2) 
    (z : ℕ → ℂ) (hz : ∀ n, -α ≤ Complex.arg (z n) ∧ Complex.arg (z n) ≤ α) :
    (Summable z ↔ Summable (fun n => Complex.abs (z n))) := by
  sorry

-- Proof attempt:
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

theorem problem_35 {α : ℝ} (hα : 0 ≤ α) (hα' : α < π/2) 
    (z : ℕ → ℂ) (hz : ∀ n, -α ≤ Complex.arg (z n) ∧ Complex.arg (z n) ≤ α) :
    (Summable z ↔ Summable (fun n => Complex.abs (z n))) := by
  constructor
  · intro h
    apply Summable.of_norm
    exact h
  · intro h
    have hcos : 0 < Real.cos α := by
      apply Real.cos_pos_of_mem_Ioo
      linarith [hα, hα']
    have bound : ∀ n, Complex.abs (z n) ≤ Real.cos α * (Complex.re (z n)) := by
      intro n
      have hn := hz n
      rw [Complex.abs, Complex.normSq, Real.sqrt_sq (Complex.normSq_nonneg _)]
      simp only [Complex.normSq_apply]
      have := Complex.abs_mul_cos_arg (z n)
      rw [← Complex.norm_eq_abs] at this
      rw [this]
      have arg_le : |Complex.arg (z n)| ≤ α := by
        rw [abs_le]
        exact ⟨hn.1, hn.2⟩
      rw [← Real.cos_abs (Complex.arg (z n))]
      apply Real.cos_le_cos_of_abs_le (by linarith) arg_le
      simp
    have h' : Summable (fun n => Complex.re (z n)) := by
      apply Summable.of_nonneg_of_le _ (fun n => _) h
      · exact fun n => Complex.norm_nonneg (z n)
      · exact le_of_eq (Complex.norm_eq_abs (z n))
    have h'' : Summable z := by
      apply Summable.of_norm_bounded (fun n => (Real.cos α)⁻¹ * Complex.abs (z n)) ?_ ?_
      · apply Summable.mul_left (Real.cos α)⁻¹ h
      · intro n
        rw [← mul_inv_cancel (ne_of_gt hcos)]
        conv_lhs => rw [mul_comm]
        apply mul_le_mul_of_nonneg_left (bound n) (le_of_lt (inv_pos.mpr hcos))
    exact h''