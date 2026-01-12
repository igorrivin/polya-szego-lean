/-
Polya-Szego Problem 31
Part Three, Chapter 1

Original problem:
The derivative $P^{\prime}(z)$ of $P(z)$ cannot have any zeros outside the smallest convex polygon that contains all the zeros of $P(z)$ (considered as points in the complex plane). Those zeros of $P^{\prime}(z)$ that are not zeros\\
of $P(z)$ lie in th line segment) th\\

Formalization notes: -- We formalize the Gauss-Lucas theorem: For a non-constant complex polynomial P,
-- all roots of its derivative P' lie in the convex hull of the roots of P.
-- Specifically:
-- 1. If P is a non-constant polynomial over ℂ
-- 2. Let roots(P) be the multiset of roots of P (with multiplicity)
-- 3. Let hull(P) be the convex hull of roots(P) as points in ℂ ≃ ℝ²
-- 4. Then for any z ∈ ℂ such that P.derivative.eval z = 0, we have z ∈ convexHull ℝ (roots P).toFinset
-- Note: We use .toFinset to remove duplicates since convex hull only cares about distinct points
-/

import Mathlib.Analysis.Complex.Polynomial
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Hull

-- Formalization notes:
-- We formalize the Gauss-Lucas theorem: For a non-constant complex polynomial P,
-- all roots of its derivative P' lie in the convex hull of the roots of P.
-- Specifically:
-- 1. If P is a non-constant polynomial over ℂ
-- 2. Let roots(P) be the multiset of roots of P (with multiplicity)
-- 3. Let hull(P) be the convex hull of roots(P) as points in ℂ ≃ ℝ²
-- 4. Then for any z ∈ ℂ such that P.derivative.eval z = 0, we have z ∈ convexHull ℝ (roots P).toFinset
-- Note: We use .toFinset to remove duplicates since convex hull only cares about distinct points

theorem gauss_lucas_theorem {P : ℂ[X]} (hP : P ≠ 0) (hz : Polynomial.eval z (Polynomial.derivative P) = 0) :
    z ∈ convexHull ℝ ((Polynomial.roots P).toFinset : Set ℂ) := by
  sorry

-- Alternative formulation using the convex hull of the set of roots directly
theorem gauss_lucas_theorem' {P : ℂ[X]} (hP : P ≠ 0) (hz : Polynomial.eval z (Polynomial.derivative P) = 0) :
    z ∈ convexHull ℝ {w : ℂ | Polynomial.IsRoot P w} := by
  sorry

-- Stronger version: The roots of P' lie in the convex hull of the roots of P,
-- and if z is a root of P' but not of P, then z lies in the relative interior
-- of the convex hull (or at least not at an extreme point that isn't also a root of P).
-- This captures the "line segment" comment from the problem statement.
theorem gauss_lucas_theorem_refined {P : ℂ[X]} (hP : P ≠ 0) 
    (hz : Polynomial.eval z (Polynomial.derivative P) = 0) 
    (hz_not_root : ¬Polynomial.IsRoot P z) :
    ∃ (x y : ℂ) (t : ℝ), 
      x ∈ (Polynomial.roots P).toFinset ∧ 
      y ∈ (Polynomial.roots P).toFinset ∧ 
      0 ≤ t ∧ t ≤ 1 ∧ z = (1 - t) • x + t • y := by
  sorry

-- Proof attempt:
theorem gauss_lucas_theorem {P : ℂ[X]} (hP : P ≠ 0) (hz : Polynomial.eval z (Polynomial.derivative P) = 0) :
    z ∈ convexHull ℝ ((Polynomial.roots P).toFinset : Set ℂ) := by
  -- First handle the case where P is constant (contradicts hP)
  by_cases h_deg : P.degree = 0
  · exfalso
    exact hP (Polynomial.eq_C_of_degree_eq_zero h_deg)
  
  -- Main case: P is non-constant
  have h_deg_pos : 0 < P.degree := Nat.pos_of_ne_zero h_deg
  have h_roots_nonempty : (Polynomial.roots P).toFinset.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty, ← Polynomial.roots_toFinset_eq_empty]
    exact Polynomial.roots_ne_zero hP
  
  -- Express P in terms of its roots
  let roots := (Polynomial.roots P).toFinset
  have hP_eq : P = Polynomial.C (Polynomial.leadingCoeff P) * ∏ a in roots, (Polynomial.X - Polynomial.C a) ^ (Polynomial.roots P).count a := by
    rw [Polynomial.eq_prod_roots_of_splits_id (Polynomial.splits_of_degree_eq_one (Polynomial.natDegree_pos_iff_degree_pos.mpr h_deg_pos))]
    simp [Polynomial.roots_toFinset]
  
  -- Compute the derivative
  have h_deriv : Polynomial.derivative P = Polynomial.C (Polynomial.leadingCoeff P) * 
      (∑ b in roots, (Polynomial.roots P).count b * (Polynomial.X - Polynomial.C b) ^ ((Polynomial.roots P).count b - 1) * 
      ∏ a in roots.erase b, (Polynomial.X - Polynomial.C a) ^ (Polynomial.roots P).count a)) := by
    rw [hP_eq, Polynomial.derivative_mul, Polynomial.derivative_C, zero_mul, zero_add, Polynomial.derivative_prod]
    simp only [Polynomial.derivative_pow, Polynomial.derivative_sub, Polynomial.derivative_C, Polynomial.derivative_X, sub_zero, one_mul]
    rw [Finset.mul_sum]
    congr; ext b
    rw [Finset.prod_erase_mul _ _ (Finset.mem_erase.mpr ⟨Ne.symm (by simp), Finset.mem_of_mem_erase ‹_›⟩)]
  
  -- Evaluate at z
  rw [h_deriv, Polynomial.eval_mul, Polynomial.eval_C, mul_eq_zero] at hz
  rcases hz with ⟨rfl, hz⟩
  · simp [Polynomial.leadingCoeff_eq_zero.mp rfl] at hP
  clear hP_eq h_deriv
  
  -- The sum evaluates to zero, so we can express z as a convex combination
  rw [Polynomial.eval_finset_sum, Finset.sum_eq_zero_iff] at hz
  have h_sum : ∑ b in roots, (Polynomial.roots P).count b / (z - b) = 0 := by
    refine Finset.sum_congr rfl fun b hb ↦ ?_
    specialize hz b hb
    rw [Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at hz
    replace hz := mul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr (Ne.symm (by simp at hb; exact hb)))) hz
    rw [mul_eq_zero, mul_eq_zero, pow_eq_zero_iff, sub_eq_zero] at hz
    push_neg at hz
    simp [hz.1, hz.2.1, ← div_eq_mul_inv]
  
  -- Rewrite the sum in terms of conjugates
  have h_sum_conj : ∑ b in roots, (Polynomial.roots P).count b • ((z - b)⁻¹) = 0 := by
    simp_rw [← smul_eq_mul]
    exact h_sum
  
  -- Extract the convex combination
  let weights := fun b ↦ (Polynomial.roots P).count b / (z - b)
  let total_weight := ∑ b in roots, (Polynomial.roots P).count b
  have h_total_weight_pos : 0 < total_weight := by
    simp [total_weight]
    exact Polynomial.count_roots_lt_degree hP h_deg_pos
  
  -- Show z is in the convex hull
  refine convexHull_eq_convexCombination.1 z roots ?_
  use fun b ↦ (Polynomial.roots P).count b / (total_weight * (z - b).conj)
  constructor
  · intro b hb
    have : (z - b) ≠ 0 := by simp at hb; exact sub_ne_zero.mpr (Ne.symm hb)
    rw [div_mul_eq_div_mul_one_div, ← conj_inv, ← div_eq_mul_inv]
    refine div_nonneg ?_ ?_
    · exact Nat.cast_nonneg _
    · exact (mul_pos h_total_weight_pos (Complex.normSq_pos.mpr this)).le
  · constructor
    · simp [← Finset.sum_div, h_sum, div_zero]
    · simp [smul_eq_mul, ← mul_assoc, ← Finset.sum_mul, h_sum_conj, zero_mul]

theorem gauss_lucas_theorem' {P : ℂ[X]} (hP : P ≠ 0) (hz : Polynomial.eval z (Polynomial.derivative P) = 0) :
    z ∈ convexHull ℝ {w : ℂ | Polynomial.IsRoot P w} := by
  rw [← Polynomial.mem_roots hP, ← Polynomial.roots_toFinset]
  exact gauss_lucas_theorem hP hz

theorem gauss_lucas_theorem_refined {P : ℂ[X]} (hP : P ≠ 0) 
    (hz : Polynomial.eval z (Polynomial.derivative P) = 0) 
    (hz_not_root : ¬Polynomial.IsRoot P z) :
    ∃ (x y : ℂ) (t : ℝ), 
      x ∈ (Polynomial.roots P).toFinset ∧ 
      y ∈ (Polynomial.roots P).toFinset ∧ 
      0 ≤ t ∧ t ≤ 1 ∧ z = (1 - t) • x + t • y := by
  have := gauss_lucas_theorem hP hz
  rw [convexHull_eq_convexCombination] at this
  obtain ⟨w, hw₁, hw₂, hw₃⟩ := this
  have h_sum : ∑ b in (Polynomial.roots P).toFinset, w b = 1 := hw₂.1
  have h_pos : ∀ b ∈ (Polynomial.roots P).toFinset, 0 ≤ w b := hw₁
  have h_eq : z = ∑ b in (Polynomial.roots P).toFinset, w b • b := hw₃
  
  -- Since z is not a root, the support has at least two points
  have h_card : 2 ≤ ((Polynomial.roots P).toFinset).card := by
    by_contra h
    push_neg at h
    rcases Finset.card_lt_two.1 h with (rfl | ⟨a, b, hab⟩)
    · simp [Finset.sum_empty] at h_eq
      exact hz_not_root (by simp [h_eq])
    · simp [hab] at h_eq
      have : w a = 1 := by
        have := h_sum; simp [hab] at this
        exact this
      rw [h_eq, this, one_smul]
      exact hz_not_root (by simp [hab])
  
  -- Use Carathéodory's theorem to reduce to affine combination of two points
  obtain ⟨S, hS, hS'⟩ := AffineIndependent.carathéodory ⟨z, h_eq⟩
  have hS_card : S.card = 2 := by
    refine le_antisymm (hS'.trans (Finset.card_le_of_subset (Finset.subset_univ _))) ?_
    refine (Nat.succ_le_of_lt h_card).trans ?_
    exact Finset.card_lt_card (Finset.ssubset_iff_of_subset hS).mpr ⟨a, Finset.mem_univ a, hS'⟩
  
  -- Extract the two points and their weights
  rcases Finset.card_eq_two.1 hS_card with ⟨x, y, hxy, rfl⟩
  use x, y, w y / (w x + w y)
  have hwx : w x ≠ 0 := by
    intro h; rw [h, zero_add] at h_sum
    exact hz_not_root (by simp [h_eq, hxy, h_sum])
  have hwy : w y ≠ 0 := by
    intro h; rw [h, add_zero] at h_sum
    exact hz_not_root (by simp [h_eq, hxy, h_sum])
  refine ⟨Finset.mem_of_subset hS (by simp), Finset.mem_of_subset hS (by simp), ?_, ?_, ?_⟩
  · exact div_nonneg (h_pos y (Finset.mem_of_subset hS (by simp))) (add_nonneg (h_pos x _) (h_pos y _))
  · rw [div_le_one (add_pos (lt_of_le_of_ne (h_pos x _) hwx.symm) (lt_of_le_of_ne (h_pos y _) hwy.symm))]
    simp [← h_sum, hxy]
  · simp [h_eq, hxy, smul_add, ← mul_smul, ← div_eq_inv_mul]
    rw [div_eq_iff (ne_of_gt (add_pos (lt_of_le_of_ne (h_pos x _) hwx.symm) (lt_of_le_of_ne (h_pos y _) hwy.symm)))]
    ring