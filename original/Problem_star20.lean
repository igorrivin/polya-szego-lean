/-
Polya-Szego Problem *20
Part Three, Chapter 1

Original problem:
Let $c_{1}, c_{2}, \ldots, c_{n}$ be positive numbers and
\end{enumerate}

$$
c_{1}+c_{2}+\cdots+c_{n} \leqq 1
$$

The absolute values of the zeros of the polynomial

$$
z^{n}+a_{1} z^{n-1}+a_{2} z^{n-2}+\cdots+a_{n}
$$

are not larger than

$$
M=\max \left(\frac{\left|a_{1}\right|}{c_{1}}, \sqrt{\frac{\left|a_{2}\right|}{c_{2}}}, \ldots, \sqrt[n]{\frac{\left|a_{n}\right|}{c_{n}}}\right)
$$

Formalization notes: We formalize the statement about bounds on polynomial roots given coefficients and positive weights.
Given:
  - Positive weights c₁,...,cₙ with sum ≤ 1
  - Polynomial zⁿ + a₁zⁿ⁻¹ + ... + aₙ
Then all roots z satisfy |z| ≤ M where:
  M = max(|a₁|/c₁, √(|a₂|/c₂), ..., ⁿ√(|aₙ|/cₙ))
  
We use:
  - `Polynomial ℂ` for complex polynomials
  - `c : Fin n → ℝ` for the weights (positive)
  - `a : Fin n → ℂ` for coefficients
  - `M` defined as the maximum over the scaled coefficient magnitudes
  - The theorem states that for any root z of the polynomial, |z| ≤ M
-/
-/

import Mathlib.Analysis.Complex.Polynomial
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/- Formalization notes:
We formalize the statement about bounds on polynomial roots given coefficients and positive weights.
Given:
  - Positive weights c₁,...,cₙ with sum ≤ 1
  - Polynomial zⁿ + a₁zⁿ⁻¹ + ... + aₙ
Then all roots z satisfy |z| ≤ M where:
  M = max(|a₁|/c₁, √(|a₂|/c₂), ..., ⁿ√(|aₙ|/cₙ))
  
We use:
  - `Polynomial ℂ` for complex polynomials
  - `c : Fin n → ℝ` for the weights (positive)
  - `a : Fin n → ℂ` for coefficients
  - `M` defined as the maximum over the scaled coefficient magnitudes
  - The theorem states that for any root z of the polynomial, |z| ≤ M
-/

open Complex Polynomial

theorem problem_20 (n : ℕ) (c : Fin n → ℝ) (a : Fin n → ℂ) 
    (hpos : ∀ i, 0 < c i) (hsum : ∑ i : Fin n, c i ≤ 1) :
    let p : Polynomial ℂ := 
      Polynomial.monomial (n : ℕ) 1 + 
      ∑ i : Fin n, Polynomial.monomial (n - 1 - i.val) (a i)
    let M : ℝ := 
      Finset.sup (Finset.univ : Finset (Fin n)) fun i => 
        Real.rpow ((a i).abs / c i) (1 / ((i.val + 1) : ℝ))
    ∀ z : ℂ, p.IsRoot z → Complex.abs z ≤ M := by
  sorry

-- Proof attempt:
theorem problem_20 (n : ℕ) (c : Fin n → ℝ) (a : Fin n → ℂ) 
    (hpos : ∀ i, 0 < c i) (hsum : ∑ i : Fin n, c i ≤ 1) :
    let p : Polynomial ℂ := 
      Polynomial.monomial (n : ℕ) 1 + 
      ∑ i : Fin n, Polynomial.monomial (n - 1 - i.val) (a i)
    let M : ℝ := 
      Finset.sup (Finset.univ : Finset (Fin n)) fun i => 
        Real.rpow ((a i).abs / c i) (1 / ((i.val + 1) : ℝ))
    ∀ z : ℂ, p.IsRoot z → Complex.abs z ≤ M := by
  intro p M z hz
  have hp : p = Polynomial.monomial n 1 + ∑ i : Fin n, Polynomial.monomial (n - 1 - i.val) (a i) := rfl
  have hroot : p.eval z = 0 := hz
  simp [hp, Polynomial.eval_add, Polynomial.eval_monomial] at hroot
  have hMpos : 0 ≤ M := by
    apply Finset.sup_le_iff.2
    intro i _
    apply Real.rpow_nonneg_of_nonneg
    exact div_nonneg (Complex.abs.nonneg _) (le_of_lt (hpos i))
  have hM_def : ∀ i, (a i).abs ≤ c i * M^(i.val + 1) := by
    intro i
    have hi : M ≥ Real.rpow ((a i).abs / c i) (1 / ((i.val + 1) : ℝ)) := 
      Finset.le_sup (Finset.mem_univ i)
    rw [Real.rpow_le_rpow_iff (div_pos (Complex.abs.nonneg _) (hpos i)) (by positivity) (by simp)]
    rw [div_pow, Real.rpow_nat_cast, Real.rpow_one_div_cancel (by positivity) (by simp)]
    field_simp [ne_of_gt (hpos i)]
    exact hi
  have hsum_parts : ∑ i : Fin n, (a i).abs * M^(n - 1 - i.val) ≤ M^n := by
    calc
      ∑ i : Fin n, (a i).abs * M^(n - 1 - i.val) 
        ≤ ∑ i : Fin n, c i * M^(i.val + 1) * M^(n - 1 - i.val) := by
          apply Finset.sum_le_sum
          intro i _
          rw [mul_assoc]
          apply mul_le_mul_of_nonneg_right (hM_def i)
          apply pow_nonneg hMpos
      _ = ∑ i : Fin n, c i * M^n := by
          congr; ext i
          rw [← pow_add, Nat.cast_add, Nat.cast_add]
          have : (n : ℝ) = (i.val + 1) + (n - 1 - i.val) := by
            rw [add_comm, Nat.add_sub_assoc (Nat.le_pred_of_lt i.is_lt), Nat.sub_add_cancel (Nat.le_refl _)]
            simp
          rw [this, pow_add]
          ring
      _ = M^n * ∑ i : Fin n, c i := by simp_rw [mul_comm (M^n), Finset.sum_mul]
      _ ≤ M^n * 1 := mul_le_mul_of_nonneg_left hsum (pow_nonneg hMpos n)
      _ = M^n := mul_one _
  have h_poly_bound : M^n - ∑ i : Fin n, (a i).abs * M^(n - 1 - i.val) ≥ 0 := by linarith
  by_contra hzM
  push_neg at hzM
  have hz_pos : 0 < Complex.abs z := Complex.abs.pos (Polynomial.IsRoot.def.mp hz)
  have hz_pow_pos : 0 < (Complex.abs z)^n := pow_pos hz_pos n
  have h_poly_pos : (Complex.abs z)^n - ∑ i : Fin n, (a i).abs * (Complex.abs z)^(n - 1 - i.val) > 0 := by
    apply sub_pos_of_lt
    calc
      ∑ i : Fin n, (a i).abs * (Complex.abs z)^(n - 1 - i.val) 
        < ∑ i : Fin n, (a i).abs * M^(n - 1 - i.val) := by
          apply Finset.sum_lt_sum
          · intro i _
            apply mul_lt_mul_of_pos_left hzM
            apply pow_pos hz_pos
          · use 0
            simp [hpos]
        _ ≤ M^n := by linarith
        _ < (Complex.abs z)^n := by rwa [pow_lt_pow_iff_of_pos_left hMpos hz_pos]
  have h_poly_nonpos : (Complex.abs z)^n - ∑ i : Fin n, (a i).abs * (Complex.abs z)^(n - 1 - i.val) ≤ 0 := by
    rw [← Complex.abs.map_mul, ← Complex.abs.map_sum, ← Complex.abs.map_neg, neg_sub, Complex.abs.map_sub]
    simp at hroot
    rw [hroot]
    simp [Complex.abs.map_sum, Complex.abs.map_mul]
  linarith