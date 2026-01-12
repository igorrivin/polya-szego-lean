/-
Polya-Szego Problem 18
Part Three, Chapter 1

Original problem:
Assume $a_{n} \neq 0$. The absolute value of none of the zeros of the polynomial

$$
P(z)=z^{n}+a_{1} z^{n-1}+a_{2} z^{n-2}+\cdots+a_{n}
$$

is smaller than the only positive zero $\zeta$ of the polynomial

$$
z^{n}+\left|a_{1}\right| z^{n-1}+\left|a_{2}\right| z^{n-2}+\cdots+\left|a_{n-1}\right| z-\left|a_{n}\right| .
$$

\begin{enumerate}
  \setcounter{enumi}{18}
  \item All the zeros of the polynomial $z^{n}+c$ are on the circle centred at $z=0$ with radius $|c|^{1 / n}$.\\

Formalization notes: -- 1. We formalize the statement about zeros of z^n + c
-- 2. The theorem states that all roots of z^n + c = 0 lie on the circle |z| = |c|^(1/n)
-- 3. We use ℂ for complex numbers and ℝ for real numbers
-- 4. We assume n ≥ 1 since for n=0 the statement is trivial/meaningless
-- 5. The absolute value |c|^(1/n) is the positive real n-th root of |c|
-/

import Mathlib.Analysis.Complex.Polynomial
import Mathlib.Analysis.SpecialFunctions.Pow.Real

-- Formalization notes:
-- 1. We formalize the statement about zeros of z^n + c
-- 2. The theorem states that all roots of z^n + c = 0 lie on the circle |z| = |c|^(1/n)
-- 3. We use ℂ for complex numbers and ℝ for real numbers
-- 4. We assume n ≥ 1 since for n=0 the statement is trivial/meaningless
-- 5. The absolute value |c|^(1/n) is the positive real n-th root of |c|

theorem problem_18 (n : ℕ) (hn : n ≥ 1) (c : ℂ) :
    ∀ (z : ℂ), (Polynomial.eval z (Polynomial.monomial n 1 + Polynomial.C c) = 0) → 
    Complex.abs z = Real.sqrt ((Real.sqrt (Complex.abs c ^ 2)) ^ (1 / (n : ℝ))) := by
  sorry

-- Proof attempt:
theorem problem_18 (n : ℕ) (hn : n ≥ 1) (c : ℂ) :
    ∀ (z : ℂ), (Polynomial.eval z (Polynomial.monomial n 1 + Polynomial.C c) = 0) → 
    Complex.abs z = Real.sqrt ((Real.sqrt (Complex.abs c ^ 2)) ^ (1 / (n : ℝ))) := by
  intro z hz
  -- Simplify the polynomial equation to z^n = -c
  have h_eq : z ^ n = -c := by
    simp [Polynomial.eval_add, Polynomial.eval_monomial, Polynomial.eval_C] at hz
    exact sub_eq_zero.mp hz
  -- Take absolute values of both sides
  have h_abs : Complex.abs (z ^ n) = Complex.abs (-c) := by congr
  -- Simplify both sides
  simp only [Complex.abs.map_neg, Complex.abs.map_pow, Complex.abs.map_one, one_pow, mul_one] at h_abs
  -- Simplify the right-hand side
  rw [← Complex.abs.map_neg, neg_neg] at h_abs
  -- Rewrite using real number operations
  rw [← Real.rpow_nat_cast, ← Real.rpow_mul (Complex.abs.nonneg z)] at h_abs
  simp only [Nat.cast_ofNat, mul_one] at h_abs
  -- Solve for |z|
  have h_nz : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have h_abs_nonneg : 0 ≤ Complex.abs z := Complex.abs.nonneg z
  rw [← Real.rpow_eq_rpow_iff h_abs_nonneg (Complex.abs.nonneg c) h_nz] at h_abs
  rw [h_abs]
  -- Simplify the expression
  simp only [Real.sqrt_eq_rpow, Real.rpow_two, Real.sqrt_sq (Complex.abs.nonneg c)]
  norm_cast
  rw [Real.rpow_nat_cast]
  field_simp [h_nz]
  ring