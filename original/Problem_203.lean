/-
Polya-Szego Problem 203
Part Three, Chapter 4

Original problem:
Let $g_{1}(z), g_{2}(z), \ldots, g_{n}(z), \ldots$ be entire functions which have real zeros only. If

$$
\lim _{n \rightarrow \infty} g_{n}(z)=g(z)
$$

uniformly in any finite domain, the entire function $g(z)$ can have only real zeros.\\

Formalization notes: -- 1. We formalize "entire functions" as `ℂ → ℂ` functions that are analytic everywhere
-- 2. "Real zeros only" means all zeros lie in ℝ (as a subset of ℂ)
-- 3. Uniform convergence in any finite domain is formalized as locally uniform convergence
-- 4. The conclusion is that g(z) can have only real zeros (non-real zeros are impossible)
-- 5. We use Hurwitz's theorem from Mathlib4 for the proof approach
-/

import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.Hurwitz
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Topology.UniformSpace.UniformConvergence

-- Formalization notes:
-- 1. We formalize "entire functions" as `ℂ → ℂ` functions that are analytic everywhere
-- 2. "Real zeros only" means all zeros lie in ℝ (as a subset of ℂ)
-- 3. Uniform convergence in any finite domain is formalized as locally uniform convergence
-- 4. The conclusion is that g(z) can have only real zeros (non-real zeros are impossible)
-- 5. We use Hurwitz's theorem from Mathlib4 for the proof approach

theorem problem_203 {g : ℂ → ℂ} {g_seq : ℕ → ℂ → ℂ} 
    (h_entire_seq : ∀ n, AnalyticOn ℂ (g_seq n) ⊤)
    (h_real_zeros : ∀ n, ∀ z, g_seq n z = 0 → z.im = 0)
    (h_loc_unif_conv : TendstoLocallyUniformly g_seq (pure g) Filter.atTop) 
    (h_entire_g : AnalyticOn ℂ g ⊤) :
    ∀ z, g z = 0 → z.im = 0 := by
  sorry

-- Proof attempt:
theorem problem_203 {g : ℂ → ℂ} {g_seq : ℕ → ℂ → ℂ} 
    (h_entire_seq : ∀ n, AnalyticOn ℂ (g_seq n) ⊤)
    (h_real_zeros : ∀ n, ∀ z, g_seq n z = 0 → z.im = 0)
    (h_loc_unif_conv : TendstoLocallyUniformly g_seq (pure g) Filter.atTop) 
    (h_entire_g : AnalyticOn ℂ g ⊤) :
    ∀ z, g z = 0 → z.im = 0 := by
  intro z hz
  -- Suppose for contradiction that g has a non-real zero
  by_contra h_nonreal
  -- Since g is entire and not identically zero (as it has a zero), we can find a small disk around z
  have h_nz : ∃ᶠ z in 𝓝[≠] z, g z ≠ 0 := by
    apply AnalyticOn.eventually_ne_of_ne h_entire_g
    · simp [AnalyticOn.analyticAt h_entire_g]
    · intro h
      exact h_nonreal (h ▸ hz)
  -- Apply Hurwitz's theorem to get a sequence of zeros converging to z
  obtain ⟨w, hw, hw_lim⟩ := 
    Complex.hurwitz_locallyUniform h_entire_seq h_entire_g h_loc_unif_conv z hz h_nz
  -- From the sequence property, all w_n have real zeros
  have h_real : ∀ n, (w n).im = 0 := h_real_zeros (w n).1 (w n).2 (hw n).2
  -- But their limit z has non-zero imaginary part by assumption
  have h_lim_im : Tendsto (fun n => (w n).im) atTop (𝓝 z.im) :=
    Tendsto.comp (continuous_im.continuousAt.tendsto _) hw_lim
  -- The limit of real numbers must be real (im = 0)
  have h_zero_im : z.im = 0 := by
    rw [← tendsto_const_nhds (a := 0)] at h_lim_im
    exact tendsto_nhds_unique h_lim_im (h_real ▸ tendsto_const_nhds)
  -- This contradicts our assumption that z.im ≠ 0
  contradiction