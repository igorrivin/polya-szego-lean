/-
Polya-Szego Problem 217
Part Three, Chapter 5

Original problem:
Arrange the successive powers of the trinomial $1+w+w^{2}$ in a regular triangular array

$$
\begin{aligned}
& 1 \\
& 1+\boldsymbol{w}+w^{2} \\
& 1+2 w+3 w^{2}+2 w^{3}+w^{4} \\
& 1+3 w+6 w^{2}+7 w^{3}+6 w^{4}+3 w^{5}+w^{6} \\
& \text {. } \text { w } \text {. . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . }
\end{aligned}
$$

The sum of the middle terms (in boldface) is

$$
1+w+3 w^{2}+7 w^{3}+\cdots=\frac{1}{\sqrt{1-2 w-3 w^{2}}} .
$$

\begin{enumerate}
  \setcounter{e

Formalization notes: We formalize the generating function identity for the sum of middle terms in the expansion of (1 + w + w²)^n.
The theorem states that the generating function for the middle coefficients (boldface terms in the triangular array)
equals 1/√(1 - 2w - 3w²).
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Polynomial
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.ENNReal
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
Formalization notes:
We formalize the generating function identity for the sum of middle terms in the expansion of (1 + w + w²)^n.
The theorem states that the generating function for the middle coefficients (boldface terms in the triangular array)
equals 1/√(1 - 2w - 3w²).

Specifically, if we let a_n be the middle coefficient in (1 + w + w²)^n (for n ≥ 0), then:
  ∑_{n=0}^∞ a_n w^n = 1/√(1 - 2w - 3w²)

We formalize this as an equality of formal power series in ℝ[[w]] within the radius of convergence.
The radius of convergence is |w| < 1/3 (since 1 - 2w - 3w² = (1-3w)(1+w)).

Note: We use ℝ rather than ℂ for simplicity, but the identity holds in ℂ within the disk |w| < 1/3.
-/

open Complex
open Real
open Finset
open Nat

/-- The middle coefficient in the expansion of (1 + w + w²)^n.
    For n=0: coefficient is 1
    For n=1: coefficient of w^1 is 1
    For n=2: coefficient of w^2 is 3
    etc. -/
def middle_coeff (n : ℕ) : ℝ :=
  if h : 2 * n ≥ n then
    let k := n  -- The middle term is at degree n in (1+w+w²)^n
    -- Coefficient of w^n in (1+w+w²)^n = ∑_{j=0}^n ∑_{i=0}^{n-j} (n choose j) * (j choose i)
    -- where j = # of w² terms, i = # of w terms among the remaining j terms
    ∑ j in range (n + 1), ∑ i in range (j + 1),
      if i + 2*j = n then (Nat.choose n j : ℝ) * (Nat.choose j i : ℝ) else 0
  else 0

theorem problem_217_middle_terms_sum :
    ∃ (R : ℝ) (hR : 0 < R), ∀ (w : ℂ), Complex.abs w < R →
      HasSum (λ n : ℕ => (middle_coeff n : ℂ) * w ^ n) 
        (1 / Real.sqrt ((1 : ℂ) - 2 * w - 3 * w ^ 2)) := by
  sorry

/-!
Additional notes:
1. The function `middle_coeff` computes the coefficient of w^n in (1+w+w²)^n, which are:
   n=0: 1
   n=1: 1
   n=2: 3
   n=3: 7
   n=4: 19
   etc.

2. The theorem states that within the radius of convergence R (which is at least 1/3),
   the power series ∑ middle_coeff(n) w^n converges to 1/√(1-2w-3w²).

3. The book's solution uses the identity:
   ∑_{n=0}^∞ [dⁿ/dxⁿ (1+x+x²)^n]_{x=0} wⁿ/n! = 1/√(1-2w-3w²)
   and notes that [dⁿ/dxⁿ (1+x+x²)^n]_{x=0} = n! * middle_coeff(n)

4. For the binomial case (1+w)^n (Pascal's triangle), the corresponding identity would be:
   ∑_{n=0}^∞ C(2n, n) w^n = 1/√(1-4w)  (Catalan numbers generating function)
-/

/-- Bonus: The binomial case mentioned in the problem -/
theorem problem_217_binomial_middle_terms_sum (k : ℕ) :
    ∃ (R : ℝ) (hR : 0 < R), ∀ (w : ℂ), Complex.abs w < R →
      HasSum (λ n : ℕ => (Nat.choose (k + 2 * n) n : ℂ) * w ^ n)
        ((1 / Real.sqrt ((1 : ℂ) - 4 * w)) * (((1 : ℂ) - Real.sqrt (1 - 4 * w)) / (2 * w)) ^ k) := by
  sorry

-- Proof attempt:
theorem problem_217_middle_terms_sum :
    ∃ (R : ℝ) (hR : 0 < R), ∀ (w : ℂ), Complex.abs w < R →
      HasSum (λ n : ℕ => (middle_coeff n : ℂ) * w ^ n) 
        (1 / Real.sqrt ((1 : ℂ) - 2 * w - 3 * w ^ 2)) := by
  use 1/3
  constructor
  · norm_num
  intro w hw
  have hw' : Complex.abs w < 1/3 := hw
  have hw_pos : 0 < (1/3 : ℝ) := by norm_num
  have h_conv : ∀ (w : ℂ), Complex.abs w < 1/3 → 
      Summable (λ n : ℕ => (middle_coeff n : ℂ) * w ^ n) := by
    intro w hw
    apply summable_of_norm_bounded _ (summable_geometric_of_lt_1 _ _)
    · exact (Complex.abs w).toNNReal
    · simp [Complex.abs.abs, Complex.abs.nonneg]
    · rwa [Complex.norm_eq_abs, ← Complex.abs_ofReal, abs_lt] at hw
    · intro n
      rw [norm_mul, norm_eq_abs, Complex.abs_ofReal, abs_middle_coeff_le]
      rw [← mul_pow, norm_eq_abs, Complex.abs_ofReal]
      exact mul_le_of_le_one_left (pow_nonneg (Complex.abs.nonneg _) n) (abs_middle_coeff_le n)
  have h_sqrt : Complex.abs (3 * w ^ 2 + 2 * w - 1) < 1 := by
    have : Complex.abs (3 * w ^ 2 + 2 * w) ≤ 3 * (Complex.abs w)^2 + 2 * Complex.abs w := by
      rw [Complex.abs.map_add, Complex.abs.map_mul, Complex.abs.map_mul]
      refine add_le_add ?_ ?_
      · exact mul_le_mul_of_nonneg_left (pow_le_pow_left (Complex.abs.nonneg _) le_rfl 2) (by norm_num)
      · exact mul_le_mul_of_nonneg_left (Complex.abs.nonneg _) (by norm_num)
    rw [← sub_neg, Complex.abs.map_sub]
    refine lt_of_le_of_lt (sub_le_sub_left this 1) ?_
    have : Complex.abs w < 1 := by linarith [show 1/3 < 1 by norm_num]
    rw [← sub_neg, ← neg_sub]
    refine lt_of_le_of_lt (le_trans (le_abs_self _) (abs_sub _ _)) ?_
    nlinarith [show 0 ≤ Complex.abs w from Complex.abs.nonneg w, hw]
  have h_sqrt_ne : (1 - 2 * w - 3 * w ^ 2 : ℂ) ≠ 0 := by
    intro h
    have : (1 - 3 * w) * (1 + w) = 1 - 2 * w - 3 * w ^ 2 := by ring
    rw [← this, h, mul_eq_zero] at h
    cases h with
    | inl h => 
      have : w = 1/3 := by linear_combination h
      have := Complex.abs.ne_of_lt hw
      contradiction
    | inr h =>
      have : w = -1 := by linear_combination h
      have : Complex.abs (-1 : ℂ) < 1/3 := by simpa using hw
      norm_num at this
  have h_deriv : ∀ n, middle_coeff n = (Polynomial.evalDerivAt (1 + Polynomial.X + Polynomial.X^2) n 0).toReal / n! := by
    intro n
    simp [middle_coeff, Polynomial.evalDerivAt, Polynomial.eval_nat_cast_deriv]
    rw [← Nat.cast_factorial]
    field_simp
    congr
    apply Polynomial.deriv_nat_cast_mul
  have h_sum : HasSum (λ n => (middle_coeff n : ℂ) * w ^ n) (1 / Real.sqrt (1 - 2 * w - 3 * w ^ 2)) := by
    rw [← mul_one_div, ← hasSum_mul_left_iff (ne_of_gt (Real.sqrt_pos.2 (sub_pos.2 h_sqrt)))]
    simp_rw [← Complex.ofReal_div, ← Complex.ofReal_mul, ← Complex.ofReal_pow, h_deriv]
    have := hasSum_deriv_pow_series (1 + Polynomial.X + Polynomial.X^2) w hw'
    simp at this
    convert this using 1
    ext n
    simp [mul_comm _ (w ^ n), mul_assoc]
  exact h_sum