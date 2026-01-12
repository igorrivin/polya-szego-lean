/-
Polya-Szego Problem 92
Part One, Chapter 2

Original problem:
Let $a, A, b, B$. be positive numbers, $a<A, b<B$. If the $n$ numbers $a_{1}, a_{2}, \ldots, a_{n}$ lie between $a$ and $A$, and the $n$ numbers $b_{1}, b_{2}, \ldots, b_{n}$ between $b$ and $B$ we can prove that

$$
1 \leqq \frac{\left(a_{1}^{2}+a_{2}^{2}+\cdots+a_{n}^{2}\right)\left(b_{1}^{2}+b_{2}^{2}+\cdots+b_{n}^{2}\right)}{\left(a_{1} b_{1}+a_{2} b_{2}+\cdots+a_{n} b_{n}\right)^{2}} \leqq\left(\frac{\sqrt{\frac{A B}{a b}}+\sqrt{\frac{a b}{A B}}}{2}\right)^{2} .
$$

The first inequality is 

Formalization notes: We formalize the inequality from Problem 92 in Polya-Szego. The theorem states bounds for the ratio
of products of sums of squares to the square of the sum of products.
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
Formalization notes:
We formalize the inequality from Problem 92 in Polya-Szego. The theorem states bounds for the ratio
of products of sums of squares to the square of the sum of products.

We capture:
1. The setup: positive bounds a < A and b < B, and sequences within these bounds
2. The inequality: 1 ≤ (∑aᵢ²)(∑bᵢ²)/(∑aᵢbᵢ)² ≤ ((√(AB/ab) + √(ab/AB))/2)²
3. We use Finset.sum for finite sums over indices 1 to n
4. The equality condition is not formalized here as it requires additional structure
   (integer conditions and specific arrangements of values)
-/

open Real
open Finset

theorem problem_92 (n : ℕ) (a A b B : ℝ) (ha_pos : 0 < a) (hA_pos : 0 < A) (hb_pos : 0 < b) 
    (hB_pos : 0 < B) (haA : a < A) (hbB : b < B) (a_seq b_seq : Fin n → ℝ)
    (ha_bounds : ∀ i, a ≤ a_seq i ∧ a_seq i ≤ A) (hb_bounds : ∀ i, b ≤ b_seq i ∧ b_seq i ≤ B) :
    let s_a2 := ∑ i : Fin n, (a_seq i) ^ 2
    let s_b2 := ∑ i : Fin n, (b_seq i) ^ 2
    let s_ab := ∑ i : Fin n, a_seq i * b_seq i
    in 1 ≤ (s_a2 * s_b2) / (s_ab ^ 2) ∧ 
       (s_a2 * s_b2) / (s_ab ^ 2) ≤ (((Real.sqrt (A * B / (a * b)) + Real.sqrt (a * b / (A * B))) / 2) ^ 2) := by
  sorry

-- Proof attempt:
theorem problem_92 (n : ℕ) (a A b B : ℝ) (ha_pos : 0 < a) (hA_pos : 0 < A) (hb_pos : 0 < b) 
    (hB_pos : 0 < B) (haA : a < A) (hbB : b < B) (a_seq b_seq : Fin n → ℝ)
    (ha_bounds : ∀ i, a ≤ a_seq i ∧ a_seq i ≤ A) (hb_bounds : ∀ i, b ≤ b_seq i ∧ b_seq i ≤ B) :
    let s_a2 := ∑ i : Fin n, (a_seq i) ^ 2
    let s_b2 := ∑ i : Fin n, (b_seq i) ^ 2
    let s_ab := ∑ i : Fin n, a_seq i * b_seq i
    in 1 ≤ (s_a2 * s_b2) / (s_ab ^ 2) ∧ 
       (s_a2 * s_b2) / (s_ab ^ 2) ≤ (((Real.sqrt (A * B / (a * b)) + Real.sqrt (a * b / (A * B))) / 2) ^ 2) := by
  let s_a2 := ∑ i : Fin n, (a_seq i) ^ 2
  let s_b2 := ∑ i : Fin n, (b_seq i) ^ 2
  let s_ab := ∑ i : Fin n, a_seq i * b_seq i
  have h_denom_pos : 0 < s_ab ^ 2 := by
    apply pow_pos
    refine sum_pos (fun i _ => ?_) (by simp)
    have ha : 0 < a_seq i := lt_of_lt_of_le ha_pos (ha_bounds i).1
    have hb : 0 < b_seq i := lt_of_lt_of_le hb_pos (hb_bounds i).1
    exact mul_pos ha hb
  constructor
  · -- First inequality: Cauchy-Schwarz
    have h_cs := sum_mul_sum_ge_square_of_sum_mul (fun i => a_seq i) (fun i => b_seq i)
    simp only [← sum_mul_sum] at h_cs
    rw [one_le_div_iff h_denom_pos]
    exact h_cs
  · -- Second inequality
    rw [div_le_iff h_denom_pos]
    let C := Real.sqrt (A * B / (a * b))
    have hC_pos : 0 < C := Real.sqrt_pos.mpr (div_pos (mul_pos hA_pos hB_pos) (mul_pos ha_pos hb_pos))
    have hC_inv : Real.sqrt (a * b / (A * B)) = C⁻¹ := by
      rw [Real.sqrt_div (mul_pos ha_pos hb_pos).le, Real.sqrt_div (mul_pos hA_pos hB_pos).le]
      simp [mul_comm, mul_div_assoc, div_div]
    have key_ineq : ∀ i, (a_seq i) * (b_seq i) * (C + C⁻¹) ≤ (a_seq i)^2 * C + (b_seq i)^2 * C⁻¹ := by
      intro i
      have h1 : 0 ≤ (a_seq i * Real.sqrt C - b_seq i / Real.sqrt C) ^ 2 := sq_nonneg _
      have h2 := (sub_nonneg.mp h1)
      rw [sub_sq, add_sub] at h2
      simp only [mul_pow, div_pow, Real.sq_sqrt hC_pos.le] at h2
      rw [← sub_nonneg] at h2
      have h3 : Real.sqrt C * (Real.sqrt C) = C := Real.mul_self_sqrt hC_pos.le
      have h4 : (1 / Real.sqrt C) * (Real.sqrt C) = 1 := by field_simp [ne_of_gt hC_pos]
      nth_rewrite 2 [← h4] at h2
      rw [← mul_assoc, mul_comm (b_seq i ^ 2), ← mul_assoc] at h2
      field_simp [ne_of_gt hC_pos] at h2 ⊢
      ring_nf at h2 ⊢
      exact h2
    have sum_ineq : s_ab * (C + C⁻¹) ≤ s_a2 * C + s_b2 * C⁻¹ := by
      simp_rw [← sum_add_distrib, ← sum_mul_left]
      exact sum_le_sum (fun i _ => key_ineq i)
    have h_main : s_a2 * s_b2 ≤ (s_a2 * C + s_b2 * C⁻¹)^2 / (4 * C * C⁻¹) := by
      have h := mul_le_of_le_div (mul_pos hC_pos (inv_pos.mpr hC_pos)) sum_ineq
      rw [mul_comm _ (C + C⁻¹), mul_assoc, ← mul_add] at h
      have h4 : 4 * C * C⁻¹ = 4 := by field_simp [ne_of_gt hC_pos]
      rw [h4] at h
      have h5 : (C + C⁻¹) ^ 2 = C^2 + C⁻¹^2 + 2 := by
        rw [add_sq, sq, sq, inv_mul_cancel (ne_of_gt hC_pos)]
        ring
      rw [h5] at h
      simp only [mul_add, mul_pow, mul_inv_cancel (ne_of_gt hC_pos), mul_one] at h
      ring_nf at h ⊢
      exact h
    rw [hC_inv]
    simp_rw [C]
    have h_denom : 4 * Real.sqrt (A * B / (a * b)) * Real.sqrt (a * b / (A * B)) = 4 := by
      rw [← Real.sqrt_mul (div_pos (mul_pos hA_pos hB_pos) (mul_pos ha_pos hb_pos)).le,
          ← Real.sqrt_mul (div_pos (mul_pos ha_pos hb_pos) (mul_pos hA_pos hB_pos)).le,
          mul_div_assoc, mul_div_cancel' _ (ne_of_gt (mul_pos hA_pos hB_pos)),
          Real.sqrt_mul_self (mul_pos ha_pos hb_pos).le,
          Real.sqrt_mul_self (mul_pos hA_pos hB_pos).le]
      field_simp
    rw [h_denom] at h_main
    simp_rw [div_one, ← div_div, ← pow_two, ← add_div, ← mul_div_assoc, ← div_pow]
    ring_nf at h_main ⊢
    exact h_main