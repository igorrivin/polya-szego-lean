/-
Polya-Szego Problem 61
Part One, Chapter 1

Original problem:
If $A(z) \ll P(z)$ and $A^{*}(z) \ll P^{*}(z)$ then we have also

$$
A(z)+A^{*}(z) \ll P(z)+P^{*}(z)
$$

and

$$
A(z) A^{*}(z) \ll P(z) P^{*}(z)
$$

\begin{enumerate}
  \setcounter{enumi}{61}
  \item If $n$ is a positive integer we have
\end{enumerate}

$$
\left(1+\frac{z}{n}\right)^{n} \ll e^{z} .
$$

\begin{enumerate}
  \setcounter{enumi}{62}
  \item Put
\end{enumerate}

$$
f(z)=z+a_{2} z^{2}+a_{3} z^{3}+\cdots+a_{n} z^{n}+\cdots .
$$

From

$$
z \frac{f^{\prime}(z)}{f(z)} \ll \frac{1+z}{1-z}


Formalization notes: -- We formalize the coefficient-wise inequality (1 + z/n)^n ≪ e^z for complex power series.
-- For a series A(z) = Σ a_k z^k and P(z) = Σ p_k z^k, A(z) ≪ P(z) means |a_k| ≤ p_k for all k.
-- Here, e^z has coefficients 1/k!, and (1 + z/n)^n is a polynomial with binomial coefficients.
-- The theorem states that for all n ∈ ℕ⁺ and all k, the absolute value of the k-th coefficient
-- of (1 + z/n)^n is ≤ the k-th coefficient of e^z, which is 1/k!.
-/

import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Complex.Polynomial
import Mathlib.Data.Complex.Basic

-- Formalization notes:
-- We formalize the coefficient-wise inequality (1 + z/n)^n ≪ e^z for complex power series.
-- For a series A(z) = Σ a_k z^k and P(z) = Σ p_k z^k, A(z) ≪ P(z) means |a_k| ≤ p_k for all k.
-- Here, e^z has coefficients 1/k!, and (1 + z/n)^n is a polynomial with binomial coefficients.
-- The theorem states that for all n ∈ ℕ⁺ and all k, the absolute value of the k-th coefficient
-- of (1 + z/n)^n is ≤ the k-th coefficient of e^z, which is 1/k!.

theorem problem_61_part1 (n : ℕ) (hn : n > 0) (k : ℕ) :
    Complex.abs (((1 : ℂ) + (1 : ℂ) / (n : ℂ)) ^ n).coeff k ≤ (Real.exp 1).series.coeff k := by
  sorry

-- Alternative formulation using formal power series
theorem problem_61_part1_alt (n : ℕ) (hn : n > 0) :
    let P : ℂ⟦X⟧ := ((1 : ℂ⟦X⟧) + (1/n : ℂ) • X) ^ n
    let E : ℂ⟦X⟧ := FormalMultilinearSeries.mk (fun k => (k.factorial : ℂ)⁻¹)
    ∀ k, Complex.abs (P.coeff k) ≤ Complex.abs (E.coeff k) := by
  sorry

-- Proof attempt:
theorem problem_61_part1 (n : ℕ) (hn : n > 0) (k : ℕ) :
    Complex.abs (((1 : ℂ) + (1 : ℂ) / (n : ℂ)) ^ n).coeff k ≤ (Real.exp 1).series.coeff k := by
  simp only [Complex.exp_eq_exp_ℂ, Real.exp_eq_exp_ℂ, Complex.coeff_exp, Complex.abs_inv, Complex.abs_natCast]
  simp only [Complex.coeff_pow, Complex.coeff_one, Complex.coeff_X, Complex.abs_one, Complex.abs_div, Complex.abs_natCast]
  
  have : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne.symm
  rw [Complex.coeff_pow (1 + (1 : ℂ)/n) n k]
  
  -- Simplify the binomial coefficient part
  simp only [Complex.coeff_one, Complex.coeff_X, one_div, Complex.abs_one, Complex.abs_div, Complex.abs_natCast]
  
  -- Main inequality
  have h₁ : Complex.abs (Nat.choose n k * (1 / (n : ℂ)) ^ k) = Nat.choose n k / (n ^ k) := by
    rw [Complex.abs_mul, Complex.abs_ofNat, Complex.abs_pow, Complex.abs_inv, Complex.abs_natCast]
    simp [div_eq_mul_inv]
  
  have h₂ : Nat.choose n k / (n ^ k) ≤ 1 / (k.factorial : ℝ) := by
    rw [div_eq_mul_one_div, div_eq_mul_one_div]
    gcongr
    · exact Nat.choose_le_pow n k
    · simp [inv_nonneg, Nat.cast_nonneg]
  
  rw [h₁]
  norm_cast
  exact h₂