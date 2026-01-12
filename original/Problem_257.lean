/-
Polya-Szego Problem 257
Part Three, Chapter 5

Original problem:
The harmonic functions

$$
u_{0}(x, y), \quad u_{1}(x, y), \quad u_{2}(x, y), \quad \ldots, \quad u_{n}(x, y), \quad \ldots
$$

are assumed to be regular and positive in a certain open region $\Re$ of the $x, y$-plane. If the infinite series

$$
u_{0}(x, y)+u_{1}(x, y)+u_{2}(x, y)+\cdots+u_{n}(x, y)+\cdots
$$

converges at a single point of $\Re$ it converges everywhere in $\Re$; in fact, it converges uniformly in any closed subdomain of $\Re$.\\

Formalization notes: -- We formalize Harnack's theorem about convergence of series of positive harmonic functions.
-- Key aspects captured:
-- 1. A sequence of harmonic functions u_n on an open connected domain Ω ⊆ ℂ
-- 2. Each u_n is positive on Ω
-- 3. If the series ∑ u_n converges at a single point z₀ ∈ Ω, then:
--    a) It converges everywhere in Ω
--    b) It converges uniformly on compact subsets of Ω
-- We use ℂ for the complex plane, identifying ℝ² with ℂ via z = x + iy.
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Harmonic
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.NormedSpace.Complete
import Mathlib.Topology.UniformSpace.UniformConvergence

-- Formalization notes:
-- We formalize Harnack's theorem about convergence of series of positive harmonic functions.
-- Key aspects captured:
-- 1. A sequence of harmonic functions u_n on an open connected domain Ω ⊆ ℂ
-- 2. Each u_n is positive on Ω
-- 3. If the series ∑ u_n converges at a single point z₀ ∈ Ω, then:
--    a) It converges everywhere in Ω
--    b) It converges uniformly on compact subsets of Ω
-- We use ℂ for the complex plane, identifying ℝ² with ℂ via z = x + iy.

open Complex
open Set
open Filter
open scoped Topology

theorem harnack_convergence_theorem
    (Ω : Set ℂ) (hΩ : IsOpen Ω) (hΩ_conn : IsConnected Ω)
    (u : ℕ → ℂ → ℝ) (hu_harmonic : ∀ n, HarmonicOn (u n) Ω)
    (hu_pos : ∀ n z, z ∈ Ω → 0 ≤ u n z)
    (z₀ : ℂ) (hz₀ : z₀ ∈ Ω) 
    (h_converges_at_z₀ : ∃ L : ℝ, Tendsto (λ N ↦ ∑ n in Finset.range N, u n z₀) atTop (𝓝 L)) :
    -- The series converges pointwise everywhere in Ω
    (∀ z, z ∈ Ω → ∃ L : ℝ, Tendsto (λ N ↦ ∑ n in Finset.range N, u n z) atTop (𝓝 L)) ∧
    -- The series converges uniformly on compact subsets
    (∀ K : Set ℂ, IsCompact K → K ⊆ Ω → 
      TendstoUniformlyOn (λ N z ↦ ∑ n in Finset.range N, u n z) 
        (λ z ↦ Classical.choose (by
          intro hz
          exact h_converges_at_z₀)) 
        atTop K) := by
  sorry

-- Proof attempt:
theorem harnack_convergence_theorem
    (Ω : Set ℂ) (hΩ : IsOpen Ω) (hΩ_conn : IsConnected Ω)
    (u : ℕ → ℂ → ℝ) (hu_harmonic : ∀ n, HarmonicOn (u n) Ω)
    (hu_pos : ∀ n z, z ∈ Ω → 0 ≤ u n z)
    (z₀ : ℂ) (hz₀ : z₀ ∈ Ω) 
    (h_converges_at_z₀ : ∃ L : ℝ, Tendsto (λ N ↦ ∑ n in Finset.range N, u n z₀) atTop (𝓝 L)) :
    (∀ z, z ∈ Ω → ∃ L : ℝ, Tendsto (λ N ↦ ∑ n in Finset.range N, u n z) atTop (𝓝 L)) ∧
    (∀ K : Set ℂ, IsCompact K → K ⊆ Ω → 
      TendstoUniformlyOn (λ N z ↦ ∑ n in Finset.range N, u n z) 
        (λ z ↦ Classical.choose (by
          intro hz
          exact h_converges_at_z₀)) 
        atTop K) := by
  constructor
  · -- Part 1: Pointwise convergence everywhere
    intro z hz
    obtain ⟨L, hL⟩ := h_converges_at_z₀
    -- Construct the holomorphic functions f_n as in the book's solution
    have : ∀ n, ∃ v : ℂ → ℝ, HarmonicOn v Ω ∧ ConformalAt (fun z ↦ (u n z, v z)) z₀ := by
      intro n
      exact (hu_harmonic n).exists_conjugate hΩ hz₀
    choose v hv_harmonic hv_conformal using this
    let g (n : ℕ) (z : ℂ) : ℂ := Complex.exp (-(u n z) - Complex.I * (v n z))
    let f (N : ℕ) (z : ℂ) : ℂ := ∏ n in Finset.range N, g n z
    -- Key properties of f_n
    have hf_holo : ∀ N, DifferentiableOn ℂ (f N) Ω := by
      intro N
      apply DifferentiableOn.prod
      intro n hn
      apply DifferentiableOn.exp
      apply DifferentiableOn.neg
      exact (hu_harmonic n).differentiableOn
      apply DifferentiableOn.const_smul
      exact (hv_harmonic n).differentiableOn
    have hf_bound : ∀ N z, z ∈ Ω → Complex.abs (f N z) ≤ Complex.exp (-∑ n in Finset.range N, u n z) := by
      intro N z hz
      simp [f, g]
      rw [Complex.abs_exp]
      simp only [neg_add_rev, neg_mul, Complex.add_re, Complex.neg_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        sub_zero, mul_one, neg_neg]
      rw [← Finset.sum_neg_distrib]
      congr
      ext n
      ring
    -- The series converges at z₀ implies f_N(z₀) converges to non-zero limit
    have hf_lim : ∃ c, Tendsto (λ N ↦ f N z₀) atTop (𝓝 c) ∧ c ≠ 0 := by
      refine ⟨Complex.exp (-L), ?_, ?_⟩
      · apply Tendsto.comp (Continuous.tendsto Complex.continuous_exp _)
        apply Tendsto.neg
        exact hL
      · exact Complex.exp_ne_zero _
    -- By Hurwitz's theorem (solution 256), f_N converges locally uniformly to a non-zero holomorphic function
    obtain ⟨φ, hφ_holo, hφ, hφ_ne⟩ := 
      exists_tendsto_locallyUniformly_of_tendsto_pointwise_of_isPreconnected hΩ hΩ_conn hf_holo hf_lim
    -- Therefore the series converges at z
    refine ⟨∑' n, u n z, ?_⟩
    have h_sum : Tendsto (λ N ↦ ∑ n in Finset.range N, u n z) atTop (𝓝 (∑' n, u n z)) := by
      apply tendsto_tsum
      -- The convergence follows from the fact that |f_N(z)| converges to non-zero value
      have : Tendsto (λ N ↦ Complex.abs (f N z)) atTop (𝓝 (Complex.abs (φ z))) :=
        (Complex.continuous_abs.tendsto _).comp (hφ z hz)
      have : Complex.abs (φ z) ≠ 0 := by
        apply hφ_ne z hz
      rw [← Complex.exp_neg_tsum]
      apply Tendsto.comp (Continuous.tendsto Complex.continuous_exp _)
      apply Tendsto.neg
      rw [← tendsto_iff_abs_tendsto_zero]
      exact this
    exact h_sum
  · -- Part 2: Uniform convergence on compact subsets
    intro K hK hK_sub
    -- Use Dini's theorem for uniform convergence of monotone sequences
    apply tendstoUniformlyOn_of_monotone_of_tendsto_pointwise hK
    · intro N z hz
      exact Finset.sum_nonneg (fun n _ ↦ hu_pos n z (hK_sub hz))
    · intro N M hNM z hz
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset.mpr hNM) 
        (fun n _ ↦ hu_pos n z (hK_sub hz))
    · intro z hz
      exact Classical.choose_spec (by
        intro h
        exact h_converges_at_z₀) (hK_sub hz)