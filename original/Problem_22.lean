/-
Polya-Szego Problem 22
Part Three, Chapter 1

Original problem:
Assum

The polynomi\\
cannot have a\\

Formalization notes: **
1. The theorem deals with complex polynomials having real coefficients
2. The key condition is that coefficients are non-negative and non-increasing: a₀ ≥ a₁ ≥ ... ≥ aₙ ≥ 0
3. The conclusion is that such polynomials have no roots inside the open unit disk
4. We use `Complex.abs z < 1` to represent the open unit disk
5. The polynomial is represented as a finite sum using `Finset.range (n + 1)`
6. The coefficients `a k` are cast from ℝ to ℂ implicitly through multiplication
-/

import Mathlib.Analysis.Complex.Polynomial
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Data.Complex.Basic

/-!
The Eneström-Kakeya theorem (also known as the Eneström-Kakeya theorem for polynomials).

Given a polynomial P(z) = ∑_{k=0}^n p_k z^k with real coefficients satisfying:
  0 ≤ p_n ≤ p_{n-1} ≤ ... ≤ p_1 ≤ p_0
then all roots z of P(z) satisfy |z| ≥ 1.

Equivalently, P(z) has no roots in the open unit disk {z : |z| < 1}.

Note: The original problem statement in Pólya-Szegő shows that for |z| ≤ 1, z ≠ 1,
|(1-z)P(z)| > 0, which implies P(z) ≠ 0 when |z| ≤ 1 and z ≠ 1.
-/

theorem enestrom_kakeya_theorem {n : ℕ} {p : ℕ → ℝ} (hp_nonneg : ∀ k, 0 ≤ p k) 
    (hp_mono : ∀ k < n, p (k + 1) ≤ p k) (hz : ℂ) (hroot : Polynomial.eval hz (Polynomial.ofFinsupp 
    (Finsupp.ofSupportFinite (fun k => if k ≤ n then p k else 0) ⟨Finset.Icc 0 n, 
    fun k hk => by simp [Finset.mem_Icc, not_le] at hk⟩)) = 0) : 
    1 ≤ Complex.abs hz := by
  sorry

-- Proof attempt:
theorem enestrom_kakeya_theorem {n : ℕ} {p : ℕ → ℝ} (hp_nonneg : ∀ k, 0 ≤ p k) 
    (hp_mono : ∀ k < n, p (k + 1) ≤ p k) (hz : ℂ) (hroot : Polynomial.eval hz (Polynomial.ofFinsupp 
    (Finsupp.ofSupportFinite (fun k => if k ≤ n then p k else 0) ⟨Finset.Icc 0 n, 
    fun k hk => by simp [Finset.mem_Icc, not_le] at hk⟩)) = 0) : 
    1 ≤ Complex.abs hz := by
  -- Assume for contradiction that |z| < 1
  by_contra h
  simp only [not_le] at h
  let P := Polynomial.ofFinsupp (Finsupp.ofSupportFinite (fun k => if k ≤ n then p k else 0) 
    ⟨Finset.Icc 0 n, fun k hk => by simp [Finset.mem_Icc, not_le] at hk⟩)
  
  -- Express (1 - z)P(z) in two forms
  have hP : (1 - hz) * Polynomial.eval hz P = p 0 + ∑ k in Finset.range n, (p (k + 1) - p k) * hz^(k + 1) - p n * hz^(n + 1) := by
    simp [Polynomial.eval_eq_sum]
    rw [mul_sum]
    simp_rw [mul_ite, mul_zero, ← mul_assoc, ← pow_succ]
    rw [Finset.sum_range_succ', Finset.sum_range_succ']
    simp only [Nat.lt_succ_iff, le_refl, ite_true, pow_zero, mul_one]
    ring_nf
    simp [Finset.sum_range_succ', add_sub_assoc]
  
  -- Since P(z) = 0, the left side is 0
  rw [hroot, zero_mul] at hP
  -- So we have p 0 + ... = 0
  have h_sum_eq : p 0 + ∑ k in Finset.range n, (p (k + 1) - p k) * hz^(k + 1) = p n * hz^(n + 1) := by
    rw [← eq_add_neg, ← hP]
    ring
  
  -- Take absolute values and use triangle inequality
  have h_abs_sum : |p 0 + ∑ k in Finset.range n, (p (k + 1) - p k) * hz^(k + 1)| ≤ 
      p 0 + ∑ k in Finset.range n, |(p (k + 1) - p k) * hz^(k + 1)| := by
    refine abs_add_le _ _
  
  -- Simplify the right hand side
  have h_rhs : p 0 + ∑ k in Finset.range n, |(p (k + 1) - p k) * hz^(k + 1)| = 
      p 0 + ∑ k in Finset.range n, (p k - p (k + 1)) * |hz|^(k + 1) := by
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    rw [abs_mul, Complex.abs_pow]
    have h_diff : p k - p (k + 1) ≥ 0 := by
      rw [sub_nonneg]
      exact hp_mono k (Finset.mem_range.1 hk)
    rw [abs_of_nonneg h_diff]
  
  -- The right hand side is ≤ p 0 + ... (using |z| < 1)
  have h_rhs_bound : p 0 + ∑ k in Finset.range n, (p k - p (k + 1)) * |hz|^(k + 1) < p 0 := by
    refine add_lt_of_nonpos_of_lt (le_refl _) ?_
    refine Finset.sum_neg_of_pos_of_nonpos ?_ ?_
    · intro k hk
      have := hp_mono k (Finset.mem_range.1 hk)
      rw [sub_pos]
      exact this
    · intro k hk
      rw [sub_nonneg]
      exact hp_mono k (Finset.mem_range.1 hk)
    · intro k hk
      rw [mul_nonpos_iff]
      left
      constructor
      · rw [sub_nonneg]
        exact hp_mono k (Finset.mem_range.1 hk)
      · exact pow_nonneg (Complex.abs.nonneg _) _
    · exact pow_lt_one (Complex.abs.nonneg _) h (by linarith [Finset.mem_range.1 hk])
  
  -- Now we have |p n * z^(n+1)| < p 0
  rw [h_sum_eq] at h_abs_sum
  have h_abs_pn : |p n * hz^(n + 1)| = p n * |hz|^(n + 1) := by
    rw [abs_mul, abs_of_nonneg (hp_nonneg n), Complex.abs_pow]
  
  have h_pn_bound : p n * |hz|^(n + 1) < p 0 := by
    linarith [h_abs_sum.trans_lt (h_rhs.trans_lt h_rhs_bound)]
  
  -- But p n ≥ p 0 and |z| < 1 leads to contradiction
  have h_pn_ge_p0 : p 0 ≤ p n := by
    induction' n with k hk
    · simp
    · trans p k
      · exact hk
      · exact hp_mono k (Nat.lt_succ_self _)
  
  have h_false : p 0 < p 0 := by
    refine lt_of_le_of_lt ?_ h_pn_bound
    refine mul_le_of_le_one_left (hp_nonneg n) ?_
    exact pow_le_one (n + 1) (Complex.abs.nonneg _) h.le
  
  exact lt_irrefl _ h_false