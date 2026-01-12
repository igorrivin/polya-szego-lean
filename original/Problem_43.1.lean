/-
Polya-Szego Problem 43.1
Part One, Chapter 1

Original problem:
Verify the identity

$$
\sum_{1}^{\infty} \frac{(-1)^{n-1} x^{n}}{n!n}=e^{-x} \sum_{1}^{\infty}\left(1+\frac{1}{2}+\frac{1}{3}+\cdots+\frac{1}{n}\right) \frac{x^{n}}{n!} .
$$

Let $y$ be an arbitrarily often differentiable function of $z$. We define the operation $\left(z \frac{d}{d z}\right)^{n} y$ by the recursion formula

$$
\left(z \frac{d}{d z}\right)^{n} y=z \frac{d}{d z}\left(z \frac{d}{d z}\right)^{n-1} y, \quad z \frac{d}{d z} y=z y^{\prime} .
$$

E.g.

$$
\left(z \frac{d}{d z}\right)^{

Formalization notes: -- 1. We formalize Problem 44: If f is a polynomial with integer coefficients,
--    then ∑_{k=0}^∞ f(k)/k! is an integer multiple of e.
-- 2. We use Polynomial ℤ for "polynomial with integral coefficients"
-- 3. The sum is formalized using expSeries as it converges absolutely
-- 4. The theorem states ∃ (n : ℤ), ∑_{k=0}^∞ f(k)/k! = n * Real.exp 1
-/

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Real.Exponential
import Mathlib.Data.Polynomial.Basic
import Mathlib.Data.Polynomial.Eval
import Mathlib.Analysis.Calculus.FormalMultilinearSeries
import Mathlib.Analysis.Analytic.Basic

-- Formalization notes:
-- 1. We formalize Problem 44: If f is a polynomial with integer coefficients,
--    then ∑_{k=0}^∞ f(k)/k! is an integer multiple of e.
-- 2. We use Polynomial ℤ for "polynomial with integral coefficients"
-- 3. The sum is formalized using expSeries as it converges absolutely
-- 4. The theorem states ∃ (n : ℤ), ∑_{k=0}^∞ f(k)/k! = n * Real.exp 1

theorem problem_44 (f : Polynomial ℤ) : 
    ∃ (n : ℤ), ∑' (k : ℕ), (f.eval (k : ℤ) : ℂ) / (Nat.factorial k : ℂ) = (n : ℂ) * Real.exp 1 := by
  sorry

-- Proof attempt:
theorem problem_44 (f : Polynomial ℤ) : 
    ∃ (n : ℤ), ∑' (k : ℕ), (f.eval (k : ℤ) : ℂ) / (Nat.factorial k : ℂ) = (n : ℂ) * Real.exp 1 := by
  -- First, express f as a linear combination of binomial coefficients
  have h := Polynomial.as_sum_range f
  -- f can be written as ∑_{i=0}^d a_i * (X choose i), where d = f.natDegree
  let d := f.natDegree
  let a := fun i => f.coeff i
  have f_eq : f = ∑ i in Finset.range (d + 1), C (a i) * (Polynomial.X.choose i) := by
    rw [Polynomial.as_sum_range, Polynomial.sum_range]; rfl
  
  -- The sum splits into a finite sum over the coefficients
  rw [f_eq, Polynomial.eval_sum, map_sum]
  simp_rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_nat_cast, Polynomial.eval_X, Polynomial.eval_choose]
  
  -- The infinite sum commutes with the finite sum
  rw [tsum_fintype]
  simp_rw [mul_comm _ (Nat.factorial _), ←mul_div_assoc, ←cast_mul]
  
  -- Each term a_i * (k choose i) / k! = a_i / (i! * (k - i)!)
  simp_rw [Nat.choose_mul_factorial_mul_factorial (le_of_lt (Nat.lt_succ_of_le (Finset.mem_range.1 ?_)))]
  rotate_left
  any_goals exact Finset.mem_range.1 (Finset.mem_range.1 (by assumption))
  
  -- Rewrite as a_i / i! * 1 / (k - i)!
  simp_rw [mul_assoc, mul_one_div, ←cast_mul, ←mul_assoc]
  
  -- The sum over k becomes a_i / i! * ∑_{k=i}^∞ 1/(k-i)!
  simp_rw [←tsum_mul_left]
  have tsum_eq : ∀ i, ∑' (k : ℕ), (1 : ℂ) / (Nat.factorial (k - i) : ℂ) = Real.exp 1 := by
    intro i
    rw [←tsum_eq_tsum_of_ne_zero_bij _ (fun k => k + i)]
    · simp_rw [Nat.add_sub_cancel, tsum_exp]
    · intro k _ _ h; exact (Nat.add_right_cancel h).symm
    · intro b; refine ⟨b - i, ?_⟩
      simp only [Nat.add_sub_of_le (Nat.le.intro rfl), imp_true_iff, eq_self_iff_true]
  
  simp_rw [tsum_eq, mul_comm _ (Real.exp 1), ←mul_assoc]
  
  -- Now we have ∑_{i=0}^d (a i / i!) * e = (∑_{i=0}^d a i / i!) * e
  rw [Finset.sum_mul]
  
  -- The coefficient is an integer because a i ∈ ℤ and i! divides the denominator
  use ∑ i in Finset.range (d + 1), a i / Nat.factorial i
  simp only [Rat.coe_int_div, Rat.cast_div, Rat.cast_coe_int, Rat.cast_natCast]
  norm_cast
  rw [mul_comm]
  rfl