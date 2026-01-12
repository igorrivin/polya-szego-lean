/-
Polya-Szego Problem 68
Part One, Chapter 2

Original problem:
Suppose that the $2 m$ functions

$$
\begin{aligned}
& f\left(x_{1}\right), f\left(x_{2}\right), \ldots, f_{m}(x) \\
& \varphi\left(x_{1}\right), \varphi\left(x_{2}\right), \ldots, \varphi_{m}(x)
\end{aligned}
$$

are properly integrable over the interval $[a, b]$. Then we have

$$
\begin{aligned}
& \int_{a}^{b} f_{1}(x) \varphi_{1}(x) d x \quad \int_{a}^{b} f_{1}(x) \varphi_{2}(x) d x \quad \ldots \quad \int_{a}^{b} f_{1}(x) \varphi_{m}(x) d x \\
& \int_{a}^{b} f_{2}(x) \varphi_{1}(x) d x \quad

Formalization notes: -- 1. We formalize the identity: det(∫[a,b] f_i(x) φ_j(x) dx) = 
--    (1/m!) * ∫_{[a,b]^m} det(f_i(x_j)) * det(φ_i(x_j)) ∏ dx_j
-- 2. We assume all functions are integrable on [a,b]
-- 3. We use ℝ as the base field for simplicity
-- 4. The m-dimensional integral is over the cube [a,b]^m
-- 5. We use `Finset` for the finite index sets
-/

import Mathlib.Analysis.Calculus.Integral.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.LinearAlgebra.Matrix.Determinant
import Mathlib.MeasureTheory.Integral.IntervalIntegral

-- Formalization notes:
-- 1. We formalize the identity: det(∫[a,b] f_i(x) φ_j(x) dx) = 
--    (1/m!) * ∫_{[a,b]^m} det(f_i(x_j)) * det(φ_i(x_j)) ∏ dx_j
-- 2. We assume all functions are integrable on [a,b]
-- 3. We use ℝ as the base field for simplicity
-- 4. The m-dimensional integral is over the cube [a,b]^m
-- 5. We use `Finset` for the finite index sets

open Real
open Matrix
open scoped BigOperators

theorem problem_68 {m : ℕ} {a b : ℝ} (hab : a ≤ b) 
    (f : Fin m → ℝ → ℝ) (φ : Fin m → ℝ → ℝ)
    (hf : ∀ i, IntervalIntegrable (f i) volume a b)
    (hφ : ∀ i, IntervalIntegrable (φ i) volume a b) :
    let A : Matrix (Fin m) (Fin m) ℝ := 
      fun i j => ∫ x in a..b, f i x * φ j x
    in det A = (1 / (Nat.factorial m : ℝ)) * 
      ∫ x : Fin m → ℝ in Set.pi Set.univ (fun _ => Set.Icc a b),
        (Matrix.det (fun i j : Fin m => f i (x j))) * 
        (Matrix.det (fun i j : Fin m => φ i (x j))) := by
  sorry

-- Proof attempt:
theorem problem_68 {m : ℕ} {a b : ℝ} (hab : a ≤ b) 
    (f : Fin m → ℝ → ℝ) (φ : Fin m → ℝ → ℝ)
    (hf : ∀ i, IntervalIntegrable (f i) volume a b)
    (hφ : ∀ i, IntervalIntegrable (φ i) volume a b) :
    let A : Matrix (Fin m) (Fin m) ℝ := 
      fun i j => ∫ x in a..b, f i x * φ j x
    in det A = (1 / (Nat.factorial m : ℝ)) * 
      ∫ x : Fin m → ℝ in Set.pi Set.univ (fun _ => Set.Icc a b),
        (Matrix.det (fun i j : Fin m => f i (x j))) * 
        (Matrix.det (fun i j : Fin m => φ i (x j))) := by
  -- First, express the determinant as a sum over permutations
  simp only [det_apply]
  
  -- Rewrite the integral of the product as a product of integrals
  have h1 : ∀ (σ : Equiv.Perm (Fin m)), 
    ∏ i, (∫ x in a..b, f i x * φ (σ i) x) = 
    ∫ x in Set.pi Set.univ (fun _ => Set.Icc a b), ∏ i, (f i (x i) * φ (σ i) (x i)) := by
    intro σ
    refine (intervalIntegral.prod_integral hab _).symm
    intro i
    exact (hf i).mul (hφ (σ i))
  
  -- Rewrite the product as a product of f's times product of φ's
  have h2 : ∀ (σ : Equiv.Perm (Fin m)) (x : Fin m → ℝ),
    ∏ i, (f i (x i) * φ (σ i) (x i)) = 
    (∏ i, f i (x i)) * (∏ i, φ (σ i) (x i)) := by
    intro σ x
    simp only [Finset.prod_mul_distrib]
  
  -- Combine the previous steps
  simp_rw [h1, h2]
  
  -- Bring the sum inside the integral
  rw [integral_finset_sum]
  · simp_rw [mul_sum]
    congr
    ext x
    rw [← sum_mul]
    congr
    ext σ
    rw [← Finset.prod_equiv σ.symm]
    · simp only [Equiv.symm_symm, Equiv.Perm.coe_mul, Function.comp_apply, Equiv.Perm.symm_apply_apply]
    · intro i
      simp only [Equiv.Perm.invFun_eq_symm]
  
  -- Show integrability of the integrand
  · intro σ hσ
    apply Continuous.integrableOn_compact
    · apply IsCompact.pi
      intro i
      exact isCompact_Icc
    · apply Continuous.mul
      · apply continuous_pi
        intro i
        exact (continuous_apply i).comp continuous_fst
      · apply continuous_pi
        intro i
        exact (continuous_apply (σ i)).comp continuous_fst
  
  -- The remaining part is to recognize the determinant terms
  have h3 : ∀ (x : Fin m → ℝ),
    ∑ σ : Equiv.Perm (Fin m), Equiv.Perm.sign σ * ∏ i, φ (σ i) (x i) = 
    det fun i j => φ i (x j) := by
    intro x
    simp [det_apply]
  
  have h4 : ∀ (x : Fin m → ℝ),
    ∑ σ : Equiv.Perm (Fin m), Equiv.Perm.sign σ * ∏ i, f i (x i) = 
    det fun i j => f i (x j) := by
    intro x
    simp [det_apply]
  
  simp_rw [h3, h4]
  
  -- Final normalization factor comes from integrating over [a,b]^m
  rw [integral_const_mul]
  norm_cast
  rw [← Nat.cast_factorial, one_div]
  
  -- Show integrability of the determinant product
  apply Continuous.integrableOn_compact
  · exact isCompact_pi_finite fun _ => isCompact_Icc
  · apply Continuous.mul
    · apply continuous_det
      intro i j
      exact (continuous_apply j).comp continuous_fst
    · apply continuous_det
      intro i j
      exact (continuous_apply j).comp continuous_fst