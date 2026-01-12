/-
Polya-Szego Problem *21
Part Three, Chapter 1

Original problem:
The absolute values of the roots of the equation

$$
z^{n}+a_{1} z^{n-1}+a_{2} z^{n-2}+\cdots+a_{n}=0
$$

are not larger than the largest among the numbers

$$
n\left|a_{1}\right|, \quad \sqrt{n\left|a_{2}\right|}, \quad \sqrt[3]{n\left|a_{3}\right|}, \quad \ldots, \quad \sqrt[n]{n\left|a_{n}\right|}
$$

and they are 1\\

Formalization notes: -- We formalize the statement about bounds on the absolute values of roots of a complex polynomial.
-- The theorem states: For any complex polynomial z^n + a₁z^{n-1} + ... + a_n = 0,
-- all roots z satisfy |z| ≤ max_{1≤k≤n} (n|a_k|)^{1/k}
-- The "and they are 1" in the problem statement appears to be incomplete/truncated.
-- We formalize the main bound statement.
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.NNReal

-- Formalization notes:
-- We formalize the statement about bounds on the absolute values of roots of a complex polynomial.
-- The theorem states: For any complex polynomial z^n + a₁z^{n-1} + ... + a_n = 0,
-- all roots z satisfy |z| ≤ max_{1≤k≤n} (n|a_k|)^{1/k}
-- The "and they are 1" in the problem statement appears to be incomplete/truncated.
-- We formalize the main bound statement.

theorem problem_21 (n : ℕ) (hn : n > 0) (a : ℕ → ℂ) (z : ℂ) 
    (hz : (∑ k in Finset.range (n + 1), 
      if k = 0 then z ^ n else if k ≤ n then a k * z ^ (n - k) else 0) = 0) 
    (h_last : a n ≠ 0) :
    Complex.abs z ≤ 
      Finset.sup' (Finset.Icc 1 n) (Finset.Nonempty_Icc_subtype (by omega)) 
        (fun k : ℕ => 
          Real.sqrt ((k : ℝ) * Complex.abs (a k)) ^ ((k : ℝ)⁻¹ : ℝ)) := by
  sorry

-- Proof attempt:
theorem problem_21 (n : ℕ) (hn : n > 0) (a : ℕ → ℂ) (z : ℂ) 
    (hz : (∑ k in Finset.range (n + 1), 
      if k = 0 then z ^ n else if k ≤ n then a k * z ^ (n - k) else 0) = 0) 
    (h_last : a n ≠ 0) :
    Complex.abs z ≤ 
      Finset.sup' (Finset.Icc 1 n) (Finset.Nonempty_Icc_subtype (by omega)) 
        (fun k : ℕ => 
          Real.sqrt ((k : ℝ) * Complex.abs (a k)) ^ ((k : ℝ)⁻¹ : ℝ)) := by
  -- First, rewrite the polynomial equation in a more convenient form
  have poly_eq : z^n = -∑ k in Finset.Icc 1 n, a k * z^(n - k) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, ite_true, ite_false, add_zero] at hz
    rw [eq_neg_iff_add_eq_zero.mp hz]
    congr
    ext k
    simp only [Finset.mem_Icc, and_imp]
    intro hk1 hkn
    rw [if_pos (by omega)]
  
  -- Assume |z| > 0 (otherwise trivial)
  by_cases hz_zero : z = 0
  · simp [hz_zero]
  
  have hz_abs_pos : 0 < Complex.abs z := Complex.abs.pos.mpr hz_zero
  
  -- Divide both sides by z^n
  have sum_eq : 1 = ∑ k in Finset.Icc 1 n, a k * z^(-k) := by
    rw [← neg_eq_iff_eq_neg.mpr poly_eq]
    field_simp [pow_ne_zero _ hz_zero]
    ring
  
  -- Take absolute values and apply triangle inequality
  have abs_sum : 1 ≤ ∑ k in Finset.Icc 1 n, Complex.abs (a k) * Complex.abs z ^ (-k) := by
    rw [← Complex.abs.map_sum]
    refine le_trans (Complex.abs.le_abs_self _) ?_
    rw [sum_eq]
    norm_num
  
  -- For each term in the sum, we'll show it's ≤ (n|a_k|)^{1/k} / |z|
  have main_ineq : ∀ k ∈ Finset.Icc 1 n, 
      Complex.abs (a k) * Complex.abs z ^ (-k) ≤ (k * Complex.abs (a k)) ^ (1/k) / Complex.abs z := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    have hk_pos : 0 < (k : ℝ) := by omega
    rw [Real.rpow_nat_cast, Real.rpow_nat_cast, ← Real.rpow_mul (Complex.abs_nonneg _), 
        mul_comm, inv_mul_cancel hk_pos.ne', Real.rpow_one, ← div_eq_mul_inv]
    refine (mul_le_mul_left (by positivity)).mpr ?_
    rw [← Real.rpow_le_rpow_iff (by positivity) (by positivity) hk_pos, 
        Real.rpow_mul (by positivity), Real.rpow_one, Real.rpow_neg (by positivity), inv_mul_cancel hk_pos.ne']
    exact Real.le_rpow_inv_of_pos_of_le (by positivity) (by omega) (by norm_num)
  
  -- Combine the inequalities
  have bound : 1 ≤ ∑ k in Finset.Icc 1 n, (k * Complex.abs (a k)) ^ (1/k) / Complex.abs z := by
    refine le_trans abs_sum (Finset.sum_le_sum main_ineq)
  
  -- Now argue that at least one term must satisfy the inequality
  have : ∃ k ∈ Finset.Icc 1 n, (k * Complex.abs (a k)) ^ (1/k) / Complex.abs z ≥ 1/n := by
    contrapose! bound
    have : ∑ k in Finset.Icc 1 n, (k * Complex.abs (a k)) ^ (1/k) / Complex.abs z < n * (1/n) := by
      refine lt_of_le_of_lt (Finset.sum_le_card_nsmul _ _ _ ?_) (by rw [nsmul_eq_mul]; norm_num; linarith)
      intro k hk
      exact (this k hk).le
    simp at this
    linarith
  
  -- Extract the maximal term
  obtain ⟨k, hk, hk_bound⟩ := this
  rw [Finset.mem_Icc] at hk
  have hk_pos : 0 < (k : ℝ) := by omega
  
  -- Rearrange the inequality to get the bound on |z|
  have : Complex.abs z ≤ (k * Complex.abs (a k)) ^ (1/k) := by
    rwa [div_le_iff hz_abs_pos, one_mul] at hk_bound
  
  -- Show this is ≤ the supremum
  refine le_trans this ?_
  apply Finset.le_sup' _ hk
  simp only [Real.sqrt_eq_rpow, Real.rpow_nat_cast]
  congr
  rw [← Real.rpow_mul (by positivity)]
  simp [hk_pos.ne', mul_inv_cancel]