/-
Polya-Szego Problem 151
Part Three, Chapter 4

Original problem:
We have for $0<\Re s<1$

$$
\int_{0}^{\infty} x^{s-1} e^{-i x} d x=\Gamma(s) e^{-\frac{i \pi s}{2}}
$$

\begin{enumerate}
  \setcounter{enumi}{151}
  \item The equation
\end{enumerate}

$$
\int_{0}^{\infty} \frac{\sin \left(x^{n}\right)}{x^{n}} d x=\frac{1}{n-1} \Gamma\left(\frac{1}{n}\right) \sin \left(\frac{n-1}{n} \frac{\pi}{2}\right)
$$

holds for $n>1$.\\

Formalization notes: -- We formalize the main integral identity for n > 1.
-- The theorem states that for real n > 1, the integral ∫₀^∞ sin(xⁿ)/xⁿ dx 
-- equals (1/(n-1)) * Γ(1/n) * sin((n-1)π/(2n)).
-- We use `Real` for the domain and `ENNReal` for the extended nonnegative reals.
-- The integral is formalized as `∫ x in (0)..∞, sin (x ^ n) / (x ^ n)`
-- Note: We need to handle the singularity at x=0 carefully.
-/

import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Fourier.PoissonSummation

-- Formalization notes:
-- We formalize the main integral identity for n > 1.
-- The theorem states that for real n > 1, the integral ∫₀^∞ sin(xⁿ)/xⁿ dx 
-- equals (1/(n-1)) * Γ(1/n) * sin((n-1)π/(2n)).
-- We use `Real` for the domain and `ENNReal` for the extended nonnegative reals.
-- The integral is formalized as `∫ x in (0)..∞, sin (x ^ n) / (x ^ n)`
-- Note: We need to handle the singularity at x=0 carefully.

theorem problem_151 (n : ℝ) (hn : n > 1) : 
    ∫ x in (0)..∞, Real.sin ((x : ℂ) ^ n) / ((x : ℂ) ^ n) = 
    (1 / (n - 1)) * Complex.Gamma (1 / n) * Real.sin (((n - 1) * π) / (2 * n)) := by
  sorry

-- Proof attempt:
theorem problem_151 (n : ℝ) (hn : n > 1) : 
    ∫ x in (0)..∞, Real.sin ((x : ℂ) ^ n) / ((x : ℂ) ^ n) = 
    (1 / (n - 1)) * Complex.Gamma (1 / n) * Real.sin (((n - 1) * π) / (2 * n)) := by
  -- First, perform the substitution y = x^n
  let s := 1 / n
  have hn' : 0 < s ∧ s < 1 := by
    have n_pos : 0 < n := by linarith
    simp only [s, one_div]
    constructor
    · exact inv_pos.mpr n_pos
    · exact (inv_lt_one n_pos).mpr hn
  have hs : 0 < 1 - s := by linarith [hn'.2]
  
  -- Change variables x = y^(1/n)
  have integral_eq : ∫ x in (0)..∞, Real.sin ((x : ℂ) ^ n) / ((x : ℂ) ^ n) = 
      ∫ y in (0)..∞, Real.sin (y : ℂ) / (y : ℂ) * (1/n) * y^(1/n - 1) := by
    refine' integral_comp_rpow_Ioc _ _ _
    · linarith
    · simp [hn.ne']
    · intro x hx
      simp only [Complex.ofReal_mul, Complex.ofReal_sin, Complex.ofReal_div, Complex.ofReal_cpow hx.1.le]
      rw [← Complex.cpow_nat_cast, ← Complex.cpow_mul_ofReal_nonneg hx.1.le]
      field_simp [hn.ne', (ne_of_gt hx.1).symm]
      ring_nf
      simp [mul_comm]
  
  rw [integral_eq]
  -- Now rewrite the integral in terms of Gamma function
  have key_integral : ∫ y in (0)..∞, Real.sin y / y * y^(1/n - 1) = 
      Complex.Gamma (1/n) * Real.sin (π/2 * (1 - 1/n)) := by
    have := integral_mul_cpow_sin_eq_gamma s hn'.1 hn'.2
    simp only [one_div, sub_eq_add_neg, neg_div] at this
    rw [← this]
    congr
    ext y
    by_cases hy : y = 0
    · simp [hy]
    · have y_pos : 0 < y := by
        rw [← ne_iff_lt_iff] at hy
        exact hy (mem_Ioc.mp y.2).1
      simp [y_pos, div_eq_mul_inv, mul_assoc]
  
  -- Combine results and simplify
  rw [integral_mul_left, key_integral]
  field_simp [hn.ne', (ne_of_gt (by linarith : 0 < n - 1)).symm]
  congr 1
  · ring
  · rw [mul_comm, ← mul_assoc, mul_div_assoc, div_eq_mul_inv, mul_comm π, mul_comm _ (π/2)]
    congr 1
    field_simp [hn.ne']
    ring