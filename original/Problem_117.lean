/-
Polya-Szego Problem 117
Part One, Chapter 3

Original problem:
If the Dirichlet series [VIII, Chap. 1, § 5 ]

$$
a_{1} 1^{-s}+a_{2} 2^{-s}+a_{3} 3^{-s}+\cdots+a_{n} n^{-s}+\cdots=D(s)
$$

converges for $s=\sigma, \sigma>0$ we obtain for $s>\sigma$

$$
D(s) \Gamma(s)=\int_{0}^{\infty} P(y) y^{s-1} d y
$$

where

$$
a_{1} e^{-y}+a_{2} e^{-2 y}+a_{3} e^{-3 y}+\cdots+a_{n} e^{-n y}+\cdots=P(y)
$$

\begin{enumerate}
  \setcounter{enumi}{117}
  \item Suppose that $f(x)$ is properly integrable over every finite interval and that $\int_{-\infty}^{\infty}|f(x)| d x$

Formalization notes: -- We formalize the two limit statements about integrals involving sin(nx) and |sin(nx)|
-- The assumptions are:
-- 1. f is integrable on every finite interval (locally integrable)
-- 2. f is absolutely integrable on ℝ
-- The conclusions are the two limit equalities
-/

import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.SetIntegral

-- Formalization notes:
-- We formalize the two limit statements about integrals involving sin(nx) and |sin(nx)|
-- The assumptions are:
-- 1. f is integrable on every finite interval (locally integrable)
-- 2. f is absolutely integrable on ℝ
-- The conclusions are the two limit equalities

theorem problem_117 {f : ℝ → ℝ} (hf_loc : ∀ (a b : ℝ), IntervalIntegrable f volume a b)
    (hf_abs_int : Integrable (fun x : ℝ => |f x|)) :
    Tendsto (fun (n : ℕ) => ∫ x : ℝ, f x * Real.sin ((n : ℝ) * x)) atTop (𝓝 0) ∧
    Tendsto (fun (n : ℕ) => ∫ x : ℝ, f x * |Real.sin ((n : ℝ) * x)|) atTop 
      (𝓝 ((2/π) * ∫ x : ℝ, f x)) := by
  sorry

-- Proof attempt:
theorem problem_117 {f : ℝ → ℝ} (hf_loc : ∀ (a b : ℝ), IntervalIntegrable f volume a b)
    (hf_abs_int : Integrable (fun x : ℝ => |f x|)) :
    Tendsto (fun (n : ℕ) => ∫ x : ℝ, f x * Real.sin ((n : ℝ) * x)) atTop (𝓝 0) ∧
    Tendsto (fun (n : ℕ) => ∫ x : ℝ, f x * |Real.sin ((n : ℝ) * x)|) atTop 
      (𝓝 ((2/π) * ∫ x : ℝ, f x)) := by
  constructor
  · -- First part: Riemann-Lebesgue lemma
    apply tendsto_integral_mul_sin_of_integrable_abs hf_loc hf_abs_int
  · -- Second part: integral with absolute sine
    have h_avg : ∀ x ≠ 0, Tendsto (fun n : ℕ => (π * n)⁻¹ * ∑ k in Finset.range n, |Real.sin (k * x)|) atTop (𝓝 (2 / π)) := by
      intro x hx
      have := tendsto_sum_abs_sin_mul_inv (by rwa [Ne.def, mul_eq_zero, or_iff_left (Nat.cast_ne_zero.mpr Nat.zero_lt_one.ne')])
      simp_rw [mul_comm] at this
      convert this using 1
      field_simp [pi_ne_zero]
      ring
    apply tendsto_integral_abs_sin_of_integrable_abs hf_loc hf_abs_int h_avg