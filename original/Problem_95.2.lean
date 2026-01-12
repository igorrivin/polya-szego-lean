/-
Polya-Szego Problem 95.2
Part One, Chapter 2

Original problem:
If all the roots of the equation of degree $n$

$$
x^{n}-a_{1} x^{n-1}+a_{2} x^{n-2}-\cdots=0
$$

are real, they are all contained in the interval with the endpoints

$$
\frac{a_{1}}{n} \pm \frac{n-1}{n}\left(a_{1}^{2}-\frac{2 n}{n-1} a_{2}\right)^{\frac{1}{2}} .
$$

Formalization notes: 1. We formalize the problem about real monic polynomials of degree n with alternating signs
2. The polynomial is: x^n - a₁*x^(n-1) + a₂*x^(n-2) - ... = 0
3. We assume all roots are real (this is the hypothesis)
4. We prove that each root lies within the interval with endpoints:
   a₁/n ± ((n-1)/n) * √(a₁² - (2n/(n-1)) * a₂)
5. We use `Polynomial.roots` to get the multiset of roots
6. We require n ≥ 2 since for n=1, the formula involves division by (n-1)
7. The coefficients a₁, a₂ are real numbers
-/
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Algebra.Basic

/-!
Formalization notes:
1. We formalize the problem about real monic polynomials of degree n with alternating signs
2. The polynomial is: x^n - a₁*x^(n-1) + a₂*x^(n-2) - ... = 0
3. We assume all roots are real (this is the hypothesis)
4. We prove that each root lies within the interval with endpoints:
   a₁/n ± ((n-1)/n) * √(a₁² - (2n/(n-1)) * a₂)
5. We use `Polynomial.roots` to get the multiset of roots
6. We require n ≥ 2 since for n=1, the formula involves division by (n-1)
7. The coefficients a₁, a₂ are real numbers
-/

open Polynomial
open Real

theorem problem_95_2 {𝕜 : Type} [Field 𝕜] [CharZero 𝕜] [Algebra ℝ 𝕜] 
    {n : ℕ} {a₁ a₂ : ℝ} (hn : n ≥ 2) :
    ∀ (p : Polynomial ℝ) (hp : p = ∑ i in Finset.range (n + 1), 
        ((-1 : ℝ) ^ i * (if i = 0 then (0 : ℝ) else if i = 1 then a₁ else if i = 2 then a₂ else 0)) 
        * (X : Polynomial ℝ) ^ (n - i))),
    (∀ x : ℝ, p.eval x = 0 → Polynomial.IsRoot p x) → 
    (∀ x : ℝ, Polynomial.IsRoot p x → 
      let x_val : ℝ := x
      let lower_bound : ℝ := a₁ / (n : ℝ) - ((n - 1 : ℝ) / (n : ℝ)) * 
          Real.sqrt (a₁ ^ 2 - (2 * (n : ℝ) / ((n : ℝ) - 1)) * a₂)
      let upper_bound : ℝ := a₁ / (n : ℝ) + ((n - 1 : ℝ) / (n : ℝ)) * 
          Real.sqrt (a₁ ^ 2 - (2 * (n : ℝ) / ((n : ℝ) - 1)) * a₂)
      lower_bound ≤ x_val ∧ x_val ≤ upper_bound) := by
  sorry

-- Proof attempt:
theorem problem_95_2 {𝕜 : Type} [Field 𝕜] [CharZero 𝕜] [Algebra ℝ 𝕜] 
    {n : ℕ} {a₁ a₂ : ℝ} (hn : n ≥ 2) :
    ∀ (p : Polynomial ℝ) (hp : p = ∑ i in Finset.range (n + 1), 
        ((-1 : ℝ) ^ i * (if i = 0 then (0 : ℝ) else if i = 1 then a₁ else if i = 2 then a₂ else 0)) 
        * (X : Polynomial ℝ) ^ (n - i))),
    (∀ x : ℝ, p.eval x = 0 → Polynomial.IsRoot p x) → 
    (∀ x : ℝ, Polynomial.IsRoot p x → 
      let x_val : ℝ := x
      let lower_bound : ℝ := a₁ / (n : ℝ) - ((n - 1 : ℝ) / (n : ℝ)) * 
          Real.sqrt (a₁ ^ 2 - (2 * (n : ℝ) / ((n : ℝ) - 1)) * a₂)
      let upper_bound : ℝ := a₁ / (n : ℝ) + ((n - 1 : ℝ) / (n : ℝ)) * 
          Real.sqrt (a₁ ^ 2 - (2 * (n : ℝ) / ((n : ℝ) - 1)) * a₂)
      lower_bound ≤ x_val ∧ x_val ≤ upper_bound) := by
  intro p hp hroot x hx
  have hmonic : p.Monic := by
    rw [hp]
    simp only [Finset.sum_range_succ, Finset.mem_range, ite_true, ite_false, mul_zero, zero_mul, 
               add_zero, Polynomial.monic_X_pow, Polynomial.monic_mul, Polynomial.monic_X, 
               Polynomial.monic_one, Polynomial.monic_pow]
    intro i hi
    split_ifs <;> simp [*]
  
  have hdeg : p.natDegree = n := hmonic.natDegree_eq
  
  -- Extract roots and their properties
  let roots := p.roots
  have hroots_card : Multiset.card roots = n := by
    rw [Polynomial.card_roots', hdeg]
    exact hmonic.ne_zero
  
  have hsum : ∑ x in roots.toFinset, x = a₁ := by
    rw [hp, Polynomial.sum_roots_eq_neg_coeff_of_monic_of_card_eq_natDegree hmonic hroots_card]
    simp [Finset.sum_range_succ, hdeg]
  
  have hsum_sq : ∑ x in roots.toFinset, x^2 = a₁^2 - 2 * a₂ := by
    rw [hp, ← Polynomial.sum_roots_pow_eq_coeff_of_monic_of_card_eq_natDegree hmonic hroots_card 2]
    simp [Finset.sum_range_succ, hdeg]
    ring
  
  -- Main inequality derivation
  have hx_in_roots : x ∈ roots.toFinset := by
    rw [Finset.mem_def, Multiset.mem_toFinset, Polynomial.mem_roots hmonic.ne_zero]
    exact hx
  
  let other_roots := roots.toFinset.erase x
  have hother_card : other_roots.card = n - 1 := by
    rw [Finset.card_erase_of_mem hx_in_roots, hroots_card, Multiset.card_toFinset]
  
  have hsum_other : ∑ y in other_roots, y = a₁ - x := by
    rw [← hsum, Finset.sum_erase_eq_sub hx_in_roots]
  
  have hsum_sq_other : ∑ y in other_roots, y^2 = (a₁^2 - 2 * a₂) - x^2 := by
    rw [← hsum_sq, Finset.sum_erase_eq_sub (by simpa using hx_in_roots)]
  
  -- Apply Cauchy-Schwarz inequality
  have h_cauchy_schwarz : (∑ y in other_roots, y)^2 ≤ other_roots.card * ∑ y in other_roots, y^2 := by
    exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  
  rw [hsum_other, hsum_sq_other, hother_card] at h_cauchy_schwarz
  simp only [Nat.cast_sub, Nat.cast_one] at h_cauchy_schwarz
  replace h_cauchy_schwarz := (mul_le_mul_left (by linarith [hn] : 0 < (n - 1 : ℝ))).mpr h_cauchy_schwarz
  rw [← mul_assoc, mul_comm ((n - 1 : ℝ) * _), mul_assoc] at h_cauchy_schwarz
  
  -- Rearrange to quadratic inequality
  have h_quadratic : (n : ℝ) * x^2 - 2 * a₁ * x + (a₁^2 - (2 * (n : ℝ) / (n - 1 : ℝ)) * a₂) ≤ 0 := by
    rw [← sub_nonpos]
    convert h_cauchy_schwarz using 1
    ring_nf
    field_simp [by linarith [hn] : (n - 1 : ℝ) ≠ 0]
    ring
  
  -- Solve quadratic inequality
  let discriminant := (2 * a₁)^2 - 4 * (n : ℝ) * (a₁^2 - (2 * (n : ℝ) / (n - 1 : ℝ)) * a₂)
  have h_discriminant : discriminant = 4 * (n : ℝ) / (n - 1 : ℝ) * (n * a₂ - (n - 1) * a₁^2) := by
    ring_nf
    field_simp [by linarith [hn] : (n - 1 : ℝ) ≠ 0]
    ring
  
  have h_roots : ∀ x, (n : ℝ) * x^2 - 2 * a₁ * x + (a₁^2 - (2 * (n : ℝ) / (n - 1 : ℝ)) * a₂) = 0 ↔
      x = a₁ / (n : ℝ) - ((n - 1 : ℝ) / (n : ℝ)) * Real.sqrt (a₁^2 - (2 * (n : ℝ) / (n - 1 : ℝ)) * a₂) ∨
      x = a₁ / (n : ℝ) + ((n - 1 : ℝ) / (n : ℝ)) * Real.sqrt (a₁^2 - (2 * (n : ℝ) / (n - 1 : ℝ)) * a₂) := by
    intro x
    rw [← Polynomial.rootSet_def, Polynomial.rootSet_quadratic]
    · simp only [discriminant, Nat.cast_ofNat]
      field_simp [by linarith [hn] : (n : ℝ) ≠ 0]
      ring_nf
    · exact (by linarith [hn] : (n : ℝ) ≠ 0)
  
  -- The solution lies between the roots
  have h_solution : lower_bound ≤ x ∧ x ≤ upper_bound := by
    rw [← h_roots]
    exact quadratic_nonpos_iff_le_roots (by linarith [hn] : (n : ℝ) > 0) h_quadratic
  
  exact h_solution