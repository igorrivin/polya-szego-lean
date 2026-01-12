/-
Polya-Szego Problem 306
Part Three, Chapter 6

Original problem:
Suppose that the function $f(z)$ is regular for $|z|<R$ but not of the form $c z^{n}, c$ constant, $n$ integer; let

$$
I_{2}(r)=\frac{1}{2 \pi} \int_{0}^{2 \pi}\left|f\left(r e^{i \vartheta}\right)\right|^{2} d \vartheta
$$

denote the arithmetic mean of $|f(z)|^{2}$ on the circle $|z|=r, r<R$. The function $I_{2}(r)$ is monotone increasing with $r$ and $\log I_{2}(r)$ is a strictly convex function of $\log r$.\\

Formalization notes: -- 1. We formalize the statement about I₂(r) being strictly increasing and log I₂(r) being strictly convex in log r
-- 2. We assume f is holomorphic on the open disk of radius R
-- 3. We exclude the case where f(z) = c*z^n for some constant c and integer n
-- 4. I₂(r) is defined as the mean square modulus on the circle |z| = r
-/

import Mathlib.Analysis.Complex.PowerSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Convex.Function
import Mathlib.MeasureTheory.Integral.CircleIntegral

open Complex
open Real
open Set
open Filter
open scoped Real
open scoped ComplexConjugate

-- Formalization notes:
-- 1. We formalize the statement about I₂(r) being strictly increasing and log I₂(r) being strictly convex in log r
-- 2. We assume f is holomorphic on the open disk of radius R
-- 3. We exclude the case where f(z) = c*z^n for some constant c and integer n
-- 4. I₂(r) is defined as the mean square modulus on the circle |z| = r

theorem problem_306 {R : ℝ} (hR : 0 < R) (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (ball (0 : ℂ) R))
    (h_not_monomial : ∀ (c : ℂ) (n : ℕ), ¬ ∀ z, f z = c * z ^ n) :
    let I₂ : ℝ → ℝ := fun r =>
      if h : 0 ≤ r ∧ r < R then
        (1 / (2 * π)) * ∫ θ in (0 : ℝ)..(2 * π), ‖f (r * exp (θ * I))‖ ^ 2
      else 0
    in
    -- I₂ is strictly increasing on (0, R)
    (∀ ⦃r₁ r₂ : ℝ⦄, 0 < r₁ → r₁ < r₂ → r₂ < R → I₂ r₁ < I₂ r₂) ∧
    -- log ∘ I₂ ∘ Real.exp is strictly convex on (-∞, log R)
    StrictConvexOn ℝ (Set.Iio (Real.log R)) (Real.log ∘ I₂ ∘ Real.exp) := by
  sorry

-- Proof attempt:
theorem problem_306 {R : ℝ} (hR : 0 < R) (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (ball (0 : ℂ) R))
    (h_not_monomial : ∀ (c : ℂ) (n : ℕ), ¬ ∀ z, f z = c * z ^ n) :
    let I₂ : ℝ → ℝ := fun r =>
      if h : 0 ≤ r ∧ r < R then
        (1 / (2 * π)) * ∫ θ in (0 : ℝ)..(2 * π), ‖f (r * exp (θ * I))‖ ^ 2
      else 0
    in
    (∀ ⦃r₁ r₂ : ℝ⦄, 0 < r₁ → r₁ < r₂ → r₂ < R → I₂ r₁ < I₂ r₂) ∧
    StrictConvexOn ℝ (Set.Iio (Real.log R)) (Real.log ∘ I₂ ∘ Real.exp) := by
  let I₂ := fun r ↦ if h : 0 ≤ r ∧ r < R then
    (1 / (2 * π)) * ∫ θ in (0 : ℝ)..(2 * π), ‖f (r * exp (θ * I))‖ ^ 2 else 0
  
  -- Step 1: Express I₂ as a power series
  have h_power_series : ∀ r ∈ Ioo 0 R, I₂ r = ∑' n : ℕ, ‖f.powerSeries 0.coeff n‖^2 * r^(2 * n) := by
    intro r hr
    have hf_analytic : AnalyticOn ℂ f (ball 0 R) := hf.analyticOn
    have hf_power_series : ∀ z ∈ ball (0 : ℂ) R, f z = ∑' n : ℕ, (f.powerSeries 0).coeff n * z ^ n :=
      fun z hz ↦ (hf_analytic 0 (mem_ball_self hR) hz).hasPowerSeriesOnBall.choose_spec.2
    simp [I₂, hr.1, hr.2]
    rw [← Complex.norm_eq_abs, ← Complex.norm_sq_eq_norm_sq]
    have := circleIntegral_pow_pow (f := fun z ↦ ‖f z‖^2) r hr.1 hr.2
    simp_rw [hf_power_series _ (mem_ball.2 (by linarith [hr.2]))]
    simp_rw [norm_sq_mul, norm_sq_pow]
    rw [this]
    simp_rw [mul_pow, ← pow_mul, mul_comm _ (2 * π), integral_mul_right]
    norm_num
    rw [tsum_mul_right]
    congr with n
    ring
  
  -- Step 2: Show I₂ is strictly increasing
  have h_strict_mono : ∀ ⦃r₁ r₂⦄, 0 < r₁ → r₁ < r₂ → r₂ < R → I₂ r₁ < I₂ r₂ := by
    intro r₁ r₂ hr₁ hr₁₂ hr₂
    rw [h_power_series r₁ ⟨hr₁, hr₁₂.trans hr₂⟩, h_power_series r₂ ⟨hr₁.trans hr₁₂, hr₂⟩]
    have h_nonzero : ∃ n, ‖f.powerSeries 0.coeff n‖^2 ≠ 0 := by
      by_contra h
      push_neg at h
      have h_monomial : ∃ c n, ∀ z, f z = c * z ^ n := by
        have h_coeff : ∃! n, f.powerSeries 0.coeff n ≠ 0 := by
          have h_finite : {n | f.powerSeries 0.coeff n ≠ 0}.Finite := by
            by_contra h_infinite
            obtain ⟨n, hn⟩ := Infinite.exists_ne 0 h_infinite
            exact h n (pow_eq_zero hn)
          obtain ⟨n, hn⟩ := h_finite.nonempty
          refine ⟨n, hn, fun m hm ↦ ?_⟩
          by_contra hmn
          exact h_not_monomial (f.powerSeries 0.coeff n) n (fun z ↦ ?_) ⟨n, m, hmn⟩
          simp [h_power_series, h, hmn]
        exact ⟨f.powerSeries 0.coeff n, n, fun z ↦ ?_⟩
      exact h_not_monomial _ _ h_monomial
    apply tsum_lt_tsum_of_nonneg
    · intro n
      exact mul_nonneg (norm_sq_nonneg _) (pow_nonneg hr₁.le _)
    · obtain ⟨n, hn⟩ := h_nonzero
      refine ⟨n, ?_⟩
      simp [hn, pow_lt_pow_left hr₁₂ hr₁.le (by norm_num)]
    · intro n
      exact mul_nonneg (norm_sq_nonneg _) (pow_nonneg hr₁.le _)
    · apply summable_of_nonneg_of_le
      · intro n
        exact mul_nonneg (norm_sq_nonneg _) (pow_nonneg hr₁.le _)
      · intro n
        rw [mul_le_mul_left (norm_sq_pos.2 hn)]
        exact pow_le_pow_left hr₁.le hr₁₂.le (by norm_num)
      · exact (hasSum_tsum (summable_of_nonneg_of_le
          (fun n ↦ mul_nonneg (norm_sq_nonneg _) (pow_nonneg hr₁.le _))
          (fun n ↦ le_rfl) _)).summable
  
  -- Step 3: Show log ∘ I₂ ∘ exp is strictly convex
  have h_strict_convex : StrictConvexOn ℝ (Iio (log R)) (log ∘ I₂ ∘ exp) := by
    refine StrictConvexOn.mono (convex_Iio _) ?_ ?_
    · intro x hx
      have hr : 0 < exp x ∧ exp x < R := by
        rw [mem_Iio] at hx
        exact ⟨exp_pos x, exp_lt_exp.mpr hx⟩
      rw [Function.comp_apply, Function.comp_apply, I₂, if_pos hr]
      exact log_pos (h_strict_mono (exp_pos x) (exp_pos (x + 1)) (by linarith [hx]) (by linarith [hx]))
    · refine strictConvexOn_iff_forall_pos.2 fun x y hx hy hxy a b ha hb hab ↦ ?_
      have hx' : exp x < R := by rwa [mem_Iio] at hx
      have hy' : exp y < R := by rwa [mem_Iio] at hy
      have h_pos : 0 < exp x ∧ 0 < exp y := ⟨exp_pos x, exp_pos y⟩
      rw [Function.comp_apply, Function.comp_apply, Function.comp_apply, Function.comp_apply,
          log_mul (exp_pos _).le (exp_pos _).le, log_exp, log_exp]
      have := h_power_series (exp (a • x + b • y)) ⟨exp_pos _, exp_lt_exp.mpr (by linarith)⟩
      rw [this, exp_add, exp_mul, exp_mul]
      refine log_lt_log (by positivity) ?_
      refine (tsum_lt_tsum_of_nonneg (fun n ↦ mul_nonneg (norm_sq_nonneg _) ?_)
        (by obtain ⟨n, hn⟩ := h_nonzero; exact ⟨n, by simp [hn, pow_lt_pow_left hxy h_pos.1.le (by norm_num)]⟩)
        (fun n ↦ mul_nonneg (norm_sq_nonneg _) (pow_nonneg h_pos.1.le _))
        (summable_of_nonneg_of_le (fun n ↦ mul_nonneg (norm_sq_nonneg _) (pow_nonneg h_pos.1.le _))
          (fun n ↦ le_rfl) _)).2 ?_
      · exact pow_nonneg (exp_pos _).le _
      · refine tsum_congr fun n ↦ ?_
        rw [mul_pow, ← pow_mul, ← pow_add, add_mul, mul_comm a, mul_comm b]
        congr 2
        ring
  
  exact ⟨h_strict_mono, h_strict_convex⟩