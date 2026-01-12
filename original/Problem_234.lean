/-
Polya-Szego Problem 234
Part Three, Chapter 5

Original problem:
Let $f(z)=a_{0}+a_{1} z+a_{2} z^{2}+\cdots+a_{n} z^{n}+\cdots$ be regular in the disk $|z|<R, f\left(r e^{i \vartheta}\right)=U(r, \vartheta)+i V(r, \vartheta), U(r, \vartheta), V(r, \vartheta)$ are real. Then the equation

$$
\int_{0}^{2 \pi}[U(r, \vartheta)]^{2} d \vartheta=\int_{0}^{2 \pi}[V(r, \vartheta)]^{-2} d \vartheta
$$

holds for $0<r<R$ provided that it holds for $r=0$.\\

Formalization notes: -- We formalize Problem 234 from Polya-Szego:
-- Let f(z) = Σ a_n z^n be analytic in |z| < R.
-- Write f(re^{iθ}) = U(r,θ) + iV(r,θ) where U,V are real-valued.
-- If ∫_0^{2π} [U(0,θ)]^2 dθ = ∫_0^{2π} [V(0,θ)]^2 dθ,
-- then for all 0 < r < R, we have ∫_0^{2π} [U(r,θ)]^2 dθ = ∫_0^{2π} [V(r,θ)]^2 dθ.
--
-- We use:
-- `f : ℂ → ℂ` is the analytic function
-- `h_analytic` states f is analytic on the open disk of radius R
-- `h_integral_zero` states the equality holds at r=0
-- The conclusion states the equality holds for all r in (0,R)
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.MeasureTheory.Integral.IntervalIntegral

-- Formalization notes:
-- We formalize Problem 234 from Polya-Szego:
-- Let f(z) = Σ a_n z^n be analytic in |z| < R.
-- Write f(re^{iθ}) = U(r,θ) + iV(r,θ) where U,V are real-valued.
-- If ∫_0^{2π} [U(0,θ)]^2 dθ = ∫_0^{2π} [V(0,θ)]^2 dθ,
-- then for all 0 < r < R, we have ∫_0^{2π} [U(r,θ)]^2 dθ = ∫_0^{2π} [V(r,θ)]^2 dθ.
--
-- We use:
-- `f : ℂ → ℂ` is the analytic function
-- `h_analytic` states f is analytic on the open disk of radius R
-- `h_integral_zero` states the equality holds at r=0
-- The conclusion states the equality holds for all r in (0,R)

theorem problem_234 {R : ℝ} (hR : 0 < R) (f : ℂ → ℂ) 
    (h_analytic : AnalyticOn ℂ f (Metric.ball (0 : ℂ) R)) :
    (∀ (r : ℝ) (hr : r ∈ Set.Ioo (0 : ℝ) R), 
      let U : ℝ → ℝ := fun θ => (f (↑r * Complex.exp (θ * Complex.I))).re
      let V : ℝ → ℝ := fun θ => (f (↑r * Complex.exp (θ * Complex.I))).im in
      ∫ θ in (0 : ℝ)..(2 * π), (U θ)^2 = ∫ θ in (0 : ℝ)..(2 * π), (V θ)^2) ↔
    (let U0 : ℝ → ℝ := fun θ => (f 0).re
     let V0 : ℝ → ℝ := fun θ => (f 0).im in
     ∫ θ in (0 : ℝ)..(2 * π), (U0 θ)^2 = ∫ θ in (0 : ℝ)..(2 * π), (V0 θ)^2) := by
  sorry

-- Proof attempt:
theorem problem_234 {R : ℝ} (hR : 0 < R) (f : ℂ → ℂ) 
    (h_analytic : AnalyticOn ℂ f (Metric.ball (0 : ℂ) R)) :
    (∀ (r : ℝ) (hr : r ∈ Set.Ioo (0 : ℝ) R), 
      let U : ℝ → ℝ := fun θ => (f (↑r * Complex.exp (θ * Complex.I))).re
      let V : ℝ → ℝ := fun θ => (f (↑r * Complex.exp (θ * Complex.I))).im in
      ∫ θ in (0 : ℝ)..(2 * π), (U θ)^2 = ∫ θ in (0 : ℝ)..(2 * π), (V θ)^2) ↔
    (let U0 : ℝ → ℝ := fun θ => (f 0).re
     let V0 : ℝ → ℝ := fun θ => (f 0).im in
     ∫ θ in (0 : ℝ)..(2 * π), (U0 θ)^2 = ∫ θ in (0 : ℝ)..(2 * π), (V0 θ)^2) := by
  constructor
  · intro h
    specialize h 0 (by simp [hR])
    simp at h
    exact h
  · intro h r hr
    have hf := h_analytic.hasFPowerSeriesOnBall (Metric.ball_mem_nhds _ hR)
    let a : ℕ → ℂ := fun n => hf.powerSeries.coeff n
    let b : ℕ → ℝ := fun n => (a n).re
    let c : ℕ → ℝ := fun n => (a n).im
    
    have U_expansion (θ : ℝ) : 
      U r θ = (a 0).re + ∑' n : ℕ, r^n * (b n * Real.cos (n * θ) - c n * Real.sin (n * θ)) := by
      simp [U]
      rw [hf.hasSum_ball hr.2]
      simp [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.re_ofReal_mul, Complex.re_add]
      congr
      ext n
      rw [Complex.re_ofReal_mul, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
      simp [Complex.exp_mul_I, Complex.cos, Complex.sin, Complex.re, Complex.ofReal_cos, Complex.ofReal_sin]
      ring
    
    have V_expansion (θ : ℝ) : 
      V r θ = (a 0).im + ∑' n : ℕ, r^n * (b n * Real.sin (n * θ) + c n * Real.cos (n * θ)) := by
      simp [V]
      rw [hf.hasSum_ball hr.2]
      simp [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.im_ofReal_mul, Complex.im_add]
      congr
      ext n
      rw [Complex.im_ofReal_mul, Complex.im_ofReal_mul, Complex.im_ofReal_mul]
      simp [Complex.exp_mul_I, Complex.cos, Complex.sin, Complex.im, Complex.ofReal_cos, Complex.ofReal_sin]
      ring
    
    have U_sq_integral : 
      (1 / (2 * π)) * ∫ θ in (0)..(2 * π), (U r θ)^2 = 
      b 0^2 + (1/2) * ∑' n : ℕ, r^(2 * n) * (b n^2 + c n^2) := by
      rw [U_expansion]
      simp_rw [pow_add, pow_mul, ← mul_assoc]
      have := Real.tsum_sq_cos_sin_integral (b 0) (fun n => r^n * b n) (fun n => r^n * c n)
      simp at this
      rw [← this]
      congr
      ext θ
      simp_rw [pow_add, pow_mul, ← mul_assoc]
    
    have V_sq_integral : 
      (1 / (2 * π)) * ∫ θ in (0)..(2 * π), (V r θ)^2 = 
      c 0^2 + (1/2) * ∑' n : ℕ, r^(2 * n) * (b n^2 + c n^2) := by
      rw [V_expansion]
      simp_rw [pow_add, pow_mul, ← mul_assoc]
      have := Real.tsum_sq_sin_cos_integral (c 0) (fun n => r^n * b n) (fun n => r^n * c n)
      simp at this
      rw [← this]
      congr
      ext θ
      simp_rw [pow_add, pow_mul, ← mul_assoc]
    
    have h0 : b 0^2 = c 0^2 := by
      simp [U0, V0] at h
      exact h
    
    rw [← mul_right_inj' (by norm_num : (2 * π) ≠ 0), ← intervalIntegral.integral_mul_const,
        ← intervalIntegral.integral_mul_const]
    simp [U_sq_integral, V_sq_integral, h0]