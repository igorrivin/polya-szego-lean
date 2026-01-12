/-
Polya-Szego Problem 256
Part Three, Chapter 5

Original problem:
We assume that in the unit disk, $|z|<1$, the functions $f_{0}(z), f_{1}(z), f_{2}(z), \ldots, f_{n}(z), \ldots$ are regular and different from zero and that their absolute values are smaller than 1 . If $\lim _{n \rightarrow \infty} f_{n}(0)=0$, then $\lim _{n \rightarrow \infty} f_{n}(z)=0$ in the entire open disk $|z|<1$; the convergence is actually uniform in every smaller disk $|z| \leqq r<1$.\\

Formalization notes: -- We formalize the statement about sequences of holomorphic functions on the open unit disk.
-- Key assumptions:
-- 1. Each fₙ is holomorphic on the open unit disk 𝔻
-- 2. Each fₙ is nonzero on 𝔻 (fₙ(z) ≠ 0 for all z ∈ 𝔻)
-- 3. Each |fₙ(z)| < 1 for all z ∈ 𝔻
-- 4. fₙ(0) → 0 as n → ∞
-- Conclusion:
-- 1. fₙ(z) → 0 pointwise for all z ∈ 𝔻
-- 2. The convergence is uniform on compact subsets of 𝔻 (which includes all closed disks |z| ≤ r < 1)
-/

import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Topology.UniformSpace.UniformConvergence

-- Formalization notes:
-- We formalize the statement about sequences of holomorphic functions on the open unit disk.
-- Key assumptions:
-- 1. Each fₙ is holomorphic on the open unit disk 𝔻
-- 2. Each fₙ is nonzero on 𝔻 (fₙ(z) ≠ 0 for all z ∈ 𝔻)
-- 3. Each |fₙ(z)| < 1 for all z ∈ 𝔻
-- 4. fₙ(0) → 0 as n → ∞
-- Conclusion:
-- 1. fₙ(z) → 0 pointwise for all z ∈ 𝔻
-- 2. The convergence is uniform on compact subsets of 𝔻 (which includes all closed disks |z| ≤ r < 1)

open Complex
open Metric
open Set
open Filter
open scoped Topology

-- The open unit disk
def unitDisk : Set ℂ := ball (0 : ℂ) 1

theorem problem_256 {f : ℕ → ℂ → ℂ} (hf_holo : ∀ n, DifferentiableOn ℂ (f n) unitDisk)
    (hf_nonzero : ∀ n, ∀ z ∈ unitDisk, f n z ≠ 0)
    (hf_bound : ∀ n, ∀ z ∈ unitDisk, Complex.abs (f n z) < 1)
    (h_zero_limit : Tendsto (λ n => f n 0) atTop (𝓝 0)) :
    -- Pointwise convergence on the entire disk
    (∀ z ∈ unitDisk, Tendsto (λ n => f n z) atTop (𝓝 0)) ∧
    -- Uniform convergence on compact subsets
    (∀ K : Set ℂ, IsCompact K → K ⊆ unitDisk → 
      TendstoUniformlyOn (λ n z => f n z) (λ _ => 0) atTop K) := by
  sorry

-- Proof attempt:
theorem problem_256 {f : ℕ → ℂ → ℂ} (hf_holo : ∀ n, DifferentiableOn ℂ (f n) unitDisk)
    (hf_nonzero : ∀ n, ∀ z ∈ unitDisk, f n z ≠ 0)
    (hf_bound : ∀ n, ∀ z ∈ unitDisk, Complex.abs (f n z) < 1)
    (h_zero_limit : Tendsto (λ n => f n 0) atTop (𝓝 0)) :
    (∀ z ∈ unitDisk, Tendsto (λ n => f n z) atTop (𝓝 0)) ∧
    (∀ K : Set ℂ, IsCompact K → K ⊆ unitDisk → 
      TendstoUniformlyOn (λ n z => f n z) (λ _ => 0) atTop K) := by
  constructor
  · -- Pointwise convergence
    intro z hz
    have hz_abs : Complex.abs z < 1 := by simpa [unitDisk] using hz
    have hz_ne_zero : z ≠ 0 ∨ z = 0 := by exact em (z = 0)
    cases hz_ne_zero with
    | inl hz_ne_0 =>
      -- Apply Schwarz lemma to each fₙ
      have h_schwarz : ∀ n, Complex.abs (f n z) ≤ Complex.abs (f n 0) := by
        intro n
        have h_holo := hf_holo n
        have h_nonzero := hf_nonzero n
        have h_bound := hf_bound n
        -- Define gₙ(z) = fₙ(z)/fₙ(0) when fₙ(0) ≠ 0
        by_cases hn : f n 0 = 0
        · simp [hn]
        · have h_unit : Complex.abs (f n 0) < 1 := h_bound 0 (by simp [unitDisk])
          have h_unit_pos : Complex.abs (f n 0) > 0 := Complex.abs.pos (ne_of_lt (h_bound _ _)).symm
          let φ := fun w => (z⁻¹ • w)
          let ψ := fun w => (f n 0)⁻¹ • w
          have h_φ : Differentiable ℂ φ := by simp; exact differentiable_id'.inv hz_ne_0
          have h_ψ : Differentiable ℂ ψ := by simp; exact differentiable_id'.inv hn
          have h_comp := (hf_holo n).comp (differentiableOn_univ.2 h_φ) (mapsTo_univ _)
          have h_comp_nonzero : ∀ w ∈ unitDisk, (f n ∘ φ) w ≠ 0 := by
            intro w hw
            apply h_nonzero
            simp [φ, unitDisk]
            rw [← mul_inv_cancel hz_ne_0, mul_comm, ← norm_mul]
            exact lt_of_le_of_lt (norm_mul_le _ _) (by simpa [unitDisk] using hw)
          have h_comp_bound : ∀ w ∈ unitDisk, Complex.abs ((f n ∘ φ) w) < 1 := by
            intro w hw
            apply h_bound
            simp [φ, unitDisk]
            rw [← mul_inv_cancel hz_ne_0, mul_comm, ← norm_mul]
            exact lt_of_le_of_lt (norm_mul_le _ _) (by simpa [unitDisk] using hw)
          have h_schwarz_aux := Complex.abs_le_of_abs_deriv_le_unit_ball (hf_holo n) h_nonzero h_bound z hz
          simp at h_schwarz_aux
          exact h_schwarz_aux
      -- Now use squeeze theorem
      apply squeeze_zero_norm (fun n => h_schwarz n)
      exact h_zero_limit
    | inr hz_eq_0 =>
      simp [hz_eq_0]
      exact h_zero_limit
  · -- Uniform convergence on compact subsets
    intro K hK hK_sub
    rcases exists_lt_mem_ball_of_subset_ball hK_sub with ⟨r, hr, hKr⟩
    have hr' : 0 ≤ r ∧ r < 1 := by linarith [norm_nonneg (0 : ℂ), hr]
    -- Apply maximum modulus principle to get uniform bound
    have h_unif : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ z ∈ K, Complex.abs (f n z) < ε := by
      intro ε hε
      obtain ⟨N, hN⟩ := tendsto_nhds.1 h_zero_limit ε hε
      use N
      intro n hn z hz
      have hz_abs : Complex.abs z ≤ r := by
        apply le_of_lt (hKr hz)
      -- Apply Schwarz lemma type argument
      have h_schwarz : ∀ w ∈ closedBall 0 r, Complex.abs (f n w) ≤ Complex.abs (f n 0) := by
        intro w hw
        have hw_abs : Complex.abs w ≤ r := by simpa using hw
        have hw_mem : w ∈ unitDisk := mem_ball.2 (lt_of_le_of_lt hw_abs hr'.2)
        by_cases hw0 : w = 0
        · simp [hw0]
        · have := Complex.abs_le_of_abs_deriv_le_unit_ball (hf_holo n) (hf_nonzero n) (hf_bound n) w hw_mem
          simp at this
          exact this
      specialize h_schwarz z (by simpa [closedBall] using hz_abs)
      rw [Complex.dist_zero_eq_abs] at hN
      exact lt_of_le_of_lt h_schwarz (hN n hn)
    exact tendstoUniformlyOn_iff.2 h_unif