/-
Polya-Szego Problem 310
Part Three, Chapter 6

Original problem:
We suppose that $f(z)$ is regular and not constant for $|z|<R$ and that $p$ is a positive number. We define

$$
I_{p}(r)=\frac{1}{2 \pi} \int_{0}^{2 \pi}\left|f\left(r e^{i \vartheta}\right)\right|^{p} d \vartheta, \quad r<R
$$

The function $I_{p}(r)$ is monotone increasing with $r$ and $\log I_{p}(r)$ is a convex function of $\log r$. (Cf. 306, 308, 307, 267 and 304, for an analogous case see IV 19.)

\begin{enumerate}
  \setcounter{enumi}{310}
  \item An analytic function that is regular in t

Formalization notes: -- We formalize the main theorem: For f holomorphic on the open disk D(0,R),
-- the function I_p(r) = (1/(2π))∫_0^{2π} |f(re^{iθ})|^p dθ is:
-- 1. Monotone increasing in r for 0 < r < R
-- 2. log I_p(r) is convex in log r
-- We assume p > 0 and f is holomorphic and non-constant on the open disk.
-/

import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Convex.Function

-- Formalization notes:
-- We formalize the main theorem: For f holomorphic on the open disk D(0,R),
-- the function I_p(r) = (1/(2π))∫_0^{2π} |f(re^{iθ})|^p dθ is:
-- 1. Monotone increasing in r for 0 < r < R
-- 2. log I_p(r) is convex in log r
-- We assume p > 0 and f is holomorphic and non-constant on the open disk.

open Complex Real MeasureTheory Interval
open scoped Real NNReal ENNReal

theorem problem_310 {R : ℝ} (hR : 0 < R) (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (Metric.ball 0 R))
    (hconst : ¬∀ z ∈ Metric.ball 0 R, f z = f 0) (p : ℝ) (hp : 0 < p) :
    let I : ℝ → ℝ := fun r =>
      if h : r ∈ Set.Ioo (0 : ℝ) R then
        (1 / (2 * π)) * ∫ θ in (0 : ℝ)..(2 * π), ‖f (r * exp (θ * I))‖ ^ p
      else 0
    -- Monotonicity
    ∧ MonotoneOn I (Set.Ioo (0 : ℝ) R)
    -- Convexity of log I_p(r) as a function of log r
    ∧ ConvexOn ℝ (Set.Ioo (0 : ℝ) R) (fun r => Real.log (I r)) := by
  sorry

-- Proof attempt:
theorem problem_310 {R : ℝ} (hR : 0 < R) (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (Metric.ball 0 R))
    (hconst : ¬∀ z ∈ Metric.ball 0 R, f z = f 0) (p : ℝ) (hp : 0 < p) :
    let I : ℝ → ℝ := fun r =>
      if h : r ∈ Set.Ioo (0 : ℝ) R then
        (1 / (2 * π)) * ∫ θ in (0 : ℝ)..(2 * π), ‖f (r * exp (θ * I))‖ ^ p
      else 0
    ∧ MonotoneOn I (Set.Ioo (0 : ℝ) R)
    ∧ ConvexOn ℝ (Set.Ioo (0 : ℝ) R) (fun r => Real.log (I r)) := by
  let I := fun r => if h : r ∈ Set.Ioo (0 : ℝ) R then
    (1 / (2 * π)) * ∫ θ in (0 : ℝ)..(2 * π), ‖f (r * exp (θ * I))‖ ^ p else 0
  have hI : ∀ r ∈ Set.Ioo (0 : ℝ) R, I r = (1 / (2 * π)) * ∫ θ in (0 : ℝ)..(2 * π), ‖f (r * exp (θ * I))‖ ^ p :=
    fun r hr => dif_pos hr
  have hI_nonneg : ∀ r ∈ Set.Ioo (0 : ℝ) R, 0 < I r := by
    intro r hr
    rw [hI r hr]
    refine mul_pos (by norm_num) (intervalIntegral_pos_of_pos_measure ?_ ?_)
    · exact Continuous.aestronglyMeasurable (by continuity)
    · intro θ hθ
      simp only [norm_pos]
      apply NeZero.of_not_differentiableOn_const hf hconst ⟨r * exp (θ * I), ?_⟩
      simp [Metric.mem_ball, hr.1, hr.2, norm_eq_abs, abs_of_pos hr.1]
  
  -- Monotonicity part
  have mono : MonotoneOn I (Set.Ioo (0 : ℝ) R) := by
    intro r₁ hr₁ r₂ hr₂ hle
    rw [hI r₁ hr₁, hI r₂ hr₂]
    have hsub : Metric.ball 0 r₁ ⊆ Metric.ball 0 r₂ := Metric.ball_subset_ball hle
    have hf₁ : DifferentiableOn ℂ f (Metric.ball 0 r₁) := hf.mono hsub
    have hf₂ : DifferentiableOn ℂ f (Metric.ball 0 r₂) := hf.mono (Metric.ball_subset_ball le_rfl)
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine intervalIntegral_mono_ae (by norm_num) (by norm_num) ?_
    filter_upwards [ae_of_all _ (fun θ => ?_)] with θ hθ
    · exact Continuous.aestronglyMeasurable (by continuity)
    · exact Continuous.aestronglyMeasurable (by continuity)
    · simp only [norm_pow, Real.norm_eq_abs, abs_pow, abs_norm]
      refine pow_le_pow_of_le_left (norm_nonneg _) ?_ hp.le
      apply Complex.abs_max_principle (hf₂) (isOpen_ball) (Metric.ball_subset_closedBall.trans Metric.closedBall_subset_ball hr₂.2)
      · exact Metric.mem_ball_self hr₁.1
      · simp [Metric.mem_sphere, norm_eq_abs, abs_of_pos hr₁.1]
  
  -- Convexity part
  have convex : ConvexOn ℝ (Set.Ioo (0 : ℝ) R) (fun r => Real.log (I r)) := by
    refine ConvexOn.mono (fun r hr => (hI_nonneg r hr).le) ?_ (Set.Subset.refl _)
    have h_log_I : ∀ r ∈ Set.Ioo (0 : ℝ) R, Real.log (I r) = Real.log (1/(2*π)) + Real.log (∫ θ in (0)..(2*π), ‖f (r * exp (θ * I))‖ ^ p) := by
      intro r hr
      rw [hI r hr, Real.log_mul (by norm_num) (intervalIntegral_pos_of_pos_measure (Continuous.aestronglyMeasurable (by continuity)) 
        (fun θ _ => pow_pos (norm_pos_iff.mpr (NeZero.of_not_differentiableOn_const hf hconst ⟨r * exp (θ * I), by simp [Metric.mem_ball, hr.1, hr.2]⟩)) _)).ne']
    refine ConvexOn.add_const _ (by norm_num)
    refine ConvexOn.log ?_ ?_ (fun r hr => ?_)
    · refine ConvexOn.integral (convex_Icc _ _) (fun θ _ => ?_)
      refine ConvexOn.comp (convexOn_pow hp) ?_ ?_
      · exact convexOn_norm.comp (hf.analyticOn.isOpen_ball.continuousOn.mono (Metric.ball_subset_ball (le_of_lt hr.2))).convexOn_log_norm
          (convex_Ioo 0 R) (fun r hr' => ⟨hr'.1, hr'.2.le⟩)
      · intro r hr'
        exact norm_nonneg _
    · intro r hr
      exact intervalIntegral_pos_of_pos_measure (Continuous.aestronglyMeasurable (by continuity)) 
        (fun θ _ => pow_pos (norm_pos_iff.mpr (NeZero.of_not_differentiableOn_const hf hconst ⟨r * exp (θ * I), by simp [Metric.mem_ball, hr.1, hr.2]⟩)) _)
    · exact intervalIntegral_pos_of_pos_measure (Continuous.aestronglyMeasurable (by continuity)) 
        (fun θ _ => pow_pos (norm_pos_iff.mpr (NeZero.of_not_differentiableOn_const hf hconst ⟨r * exp (θ * I), by simp [Metric.mem_ball, hr.1, hr.2]⟩)) _)
  
  exact ⟨mono, convex⟩