/-
Polya-Szego Problem 251
Part Three, Chapter 5

Original problem:
If the series

$$
g(z)+g^{\prime}(z)+g^{\prime \prime}(z)+\cdots+g^{(n j}(z)+\cdots
$$

converges at one single point at which $g(z)$ is regular then $g(z)$ is an entire function and the series converges at every point. The convergence is uniform in any finite domain of the $z$-plane.\\

Formalization notes: -- We formalize the statement about convergence of the series of derivatives.
-- Let g : ℂ → ℂ be a function that is holomorphic at some point a.
-- If the series ∑_{n=0}^∞ g^{(n)}(a) converges, then:
-- 1. g is entire (holomorphic on all ℂ)
-- 2. For any z : ℂ, the series ∑_{n=0}^∞ g^{(n)}(z) converges
-- 3. The convergence is uniform on bounded subsets of ℂ
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.NormedSpace.OperatorNorm
import Mathlib.Topology.UniformSpace.UniformConvergence

-- Formalization notes:
-- We formalize the statement about convergence of the series of derivatives.
-- Let g : ℂ → ℂ be a function that is holomorphic at some point a.
-- If the series ∑_{n=0}^∞ g^{(n)}(a) converges, then:
-- 1. g is entire (holomorphic on all ℂ)
-- 2. For any z : ℂ, the series ∑_{n=0}^∞ g^{(n)}(z) converges
-- 3. The convergence is uniform on bounded subsets of ℂ

-- We use `HasFPowerSeriesAt` to express that g is analytic at a point.
-- `DifferentiableOn ℂ g Set.univ` means g is entire.
-- `TendstoUniformlyOn` captures uniform convergence on bounded sets.

theorem problem_251 {g : ℂ → ℂ} {a : ℂ} (hg : ∃ p : FormalMultilinearSeries ℂ ℂ ℂ, HasFPowerSeriesAt g p a)
    (h_conv : ∃ L : ℂ, Tendsto (λ n => ∑ k in Finset.range n, iteratedDeriv k g a) atTop (𝓝 L)) :
    DifferentiableOn ℂ g Set.univ ∧
    (∀ z : ℂ, ∃ L_z : ℂ, Tendsto (λ n => ∑ k in Finset.range n, iteratedDeriv k g z) atTop (𝓝 L_z)) ∧
    (∀ (s : Set ℂ) (hs : Bornology.IsBounded s),
      TendstoUniformlyOn (λ n z => ∑ k in Finset.range n, iteratedDeriv k g z)
        (λ z => ∑' n, iteratedDeriv n g z) atTop s) := by
  sorry

-- Proof attempt:
theorem problem_251 {g : ℂ → ℂ} {a : ℂ} (hg : ∃ p : FormalMultilinearSeries ℂ ℂ ℂ, HasFPowerSeriesAt g p a)
    (h_conv : ∃ L : ℂ, Tendsto (λ n => ∑ k in Finset.range n, iteratedDeriv k g a) atTop (𝓝 L)) :
    DifferentiableOn ℂ g Set.univ ∧
    (∀ z : ℂ, ∃ L_z : ℂ, Tendsto (λ n => ∑ k in Finset.range n, iteratedDeriv k g z) atTop (𝓝 L_z)) ∧
    (∀ (s : Set ℂ) (hs : Bornology.IsBounded s),
      TendstoUniformlyOn (λ n z => ∑ k in Finset.range n, iteratedDeriv k g z)
        (λ z => ∑' n, iteratedDeriv n g z) atTop s) := by
  obtain ⟨p, hp⟩ := hg
  obtain ⟨L, hL⟩ := h_conv
  
  -- Step 1: g is entire
  have h_entire : DifferentiableOn ℂ g Set.univ := by
    refine AnalyticOn.differentiableOn fun z _ => ?_
    -- The series converges everywhere because it converges at a
    have h_radius : p.radius = ∞ := by
      have := hasFPowerSeriesAt_iff_tendsto_tsum_deriv hp
      simp only [FormalMultilinearSeries.radius_eq_top_of_summable_norm, 
        ENNReal.top_eq_∞, ← this]
      exact summable_of_summable_hasSum (Summable.hasSum hL)
    exact ⟨p, HasFPowerSeriesOnBall.hasFPowerSeriesAt (hp.hasFPowerSeriesOnBall.mono h_radius.ge)⟩

  -- Step 2: The series converges pointwise everywhere
  have h_pointwise : ∀ z : ℂ, ∃ L_z : ℂ, Tendsto (λ n => ∑ k in Finset.range n, iteratedDeriv k g z) atTop (𝓝 L_z) := by
    intro z
    have := h_entire z (Set.mem_univ z)
    have h_analytic : AnalyticAt ℂ g z := this.analyticAt
    obtain ⟨p_z, hp_z⟩ := h_analytic
    have h_conv_z : Summable fun n => iteratedDeriv n g z := by
      refine summable_of_summable_of_subset ?_ (Finset.subset_univ _)
      have := summable_of_summable_hasSum hL
      exact this.of_norm
    exact ⟨∑' n, iteratedDeriv n g z, h_conv_z.hasSum.tendsto_sum_nat⟩

  -- Step 3: Uniform convergence on bounded sets
  have h_uniform : ∀ (s : Set ℂ) (hs : Bornology.IsBounded s),
    TendstoUniformlyOn (λ n z => ∑ k in Finset.range n, iteratedDeriv k g z)
      (λ z => ∑' n, iteratedDeriv n g z) atTop s := by
    intro s hs
    have h_loc_unif : ∀ z ∈ s, ∃ t ∈ 𝓝 z, TendstoUniformlyOn (λ n w => ∑ k in Finset.range n, iteratedDeriv k g w)
      (λ w => ∑' n, iteratedDeriv n g w) atTop t := by
      intro z hz
      have h_analytic : AnalyticAt ℂ g z := h_entire z (Set.mem_univ z)
      obtain ⟨p_z, hp_z⟩ := h_analytic
      refine ⟨Metric.ball z 1, Metric.ball_mem_nhds z one_pos, ?_⟩
      apply tendstoUniformlyOn_tsum_of_summable_norm
      · intro n
        exact (iteratedDeriv n g).continuous.continuousOn
      · intro w hw
        have := summable_of_summable_hasSum hL
        exact this.of_norm
    exact tendstoUniformlyOn_of_loc_uniform hs h_loc_unif

  exact ⟨h_entire, h_pointwise, h_uniform⟩