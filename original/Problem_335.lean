/-
Polya-Szego Problem 335
Part Three, Chapter 6

Original problem:
The assumptions of $\mathbf{2 7 8}$ are weakened insofar as (3) is satisfied in all but possibly finitely many boundary points $z_{1}, z_{2}, \ldots, z_{n}$ of $\Re$. An other assumption, however, is added, namely that there exists a positive number $M^{\prime}$ for which the inequality

$$
|f(z)|<M^{\prime}
$$

holds everywhere in $\Re$. (Only the case $M^{\prime}>M$ is interesting.) This modification of the hypothesis does not change the conclusion of $\mathbf{2 7 8}$ that under those conditio

Formalization notes: -- We formalize a version of the maximum modulus principle with finitely many
-- exceptional boundary points. The theorem states that if f is holomorphic on
-- a bounded region R, continuous on its closure except possibly at finitely many
-- boundary points z₁, ..., zₙ, and satisfies |f(z)| ≤ M on the boundary (except
-- at the exceptional points), and is bounded by M' everywhere in R, then |f(z)| ≤ M
-- throughout R. If the inequality is strict on the boundary (except at exceptional
-- points), then it's strict in the interior too.
-/

import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.MaximumModulus
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Topology.MetricSpace.Basic

-- Formalization notes:
-- We formalize a version of the maximum modulus principle with finitely many
-- exceptional boundary points. The theorem states that if f is holomorphic on
-- a bounded region R, continuous on its closure except possibly at finitely many
-- boundary points z₁, ..., zₙ, and satisfies |f(z)| ≤ M on the boundary (except
-- at the exceptional points), and is bounded by M' everywhere in R, then |f(z)| ≤ M
-- throughout R. If the inequality is strict on the boundary (except at exceptional
-- points), then it's strict in the interior too.

-- We model the region R as a connected open set in ℂ.
-- The boundary condition is formalized using limits approaching boundary points.

open Complex
open Metric
open Set
open Filter

theorem problem_335 {R : Set ℂ} (hR_open : IsOpen R) (hR_conn : IsConnected R) 
    {f : ℂ → ℂ} (hf_holo : DifferentiableOn ℂ f R) 
    {M M' : ℝ} (hM_pos : 0 < M) (hM'_pos : 0 < M') (hM'_gt_M : M < M')
    (h_bound : ∀ z ∈ R, ‖f z‖ ≤ M') 
    {z_points : Finset ℂ} (hz_points_boundary : ∀ z ∈ z_points, z ∈ frontier R)
    (h_boundary_ineq : ∀ z ∈ frontier R \ (z_points : Set ℂ), 
        ∃ (l : Filter ℂ) (hl : Tendsto (λ w : ℂ => w) l (𝓝 z)), 
          ∀ᶠ w in l, w ∈ R ∧ ‖f w‖ ≤ M) 
    (h_strict_boundary : ∀ z ∈ frontier R \ (z_points : Set ℂ), 
        ∃ (l : Filter ℂ) (hl : Tendsto (λ w : ℂ => w) l (𝓝 z)), 
          ∀ᶠ w in l, w ∈ R ∧ ‖f w‖ < M ∨ w ∉ R) :
    (∀ z ∈ R, ‖f z‖ ≤ M) ∧ 
    (∀ z ∈ R, (∀ z' ∈ frontier R \ (z_points : Set ℂ), 
        ∃ (l : Filter ℂ) (hl : Tendsto (λ w : ℂ => w) l (𝓝 z')), 
          ∀ᶠ w in l, w ∈ R ∧ ‖f w‖ < M) → ‖f z‖ < M) := by
  sorry

-- Proof attempt:
constructor
  · -- First part: ‖f z‖ ≤ M for all z ∈ R
    by_contra h_contra
    push_neg at h_contra
    obtain ⟨z₀, hz₀, hz₀_gt⟩ := h_contra
    have hM'_le : M' ≤ M := by linarith [h_bound z₀ hz₀]
    linarith [hM'_gt_M, hM'_le]
  
  · -- Second part: strict inequality under stronger boundary conditions
    intro z hz h_strict
    by_contra h_contra
    push_neg at h_contra
    have hM_le : M ≤ ‖f z‖ := by linarith [h_bound z hz]
    have hM_eq : ‖f z‖ = M := by linarith
    
    -- Apply maximum modulus principle
    have h_max : IsMaxOn (norm ∘ f) R z := by
      refine' isMaxOn_iff.mpr ⟨hz, fun w hw => _⟩
      by_cases hw_front : w ∈ frontier R
      · by_cases hw_except : w ∈ (z_points : Set ℂ)
        · exact h_bound w (frontier_subset_closure hR_open hw_front) |>.trans hM_le.le
        · obtain ⟨l, hl, h_event⟩ := h_strict w ⟨hw_front, hw_except⟩
          have h_nhds : R ∈ 𝓝 w := hR_open.mem_nhds (frontier_subset_closure hR_open hw_front)
          have h_filt : Tendsto id l (𝓝 w) := hl
          obtain ⟨x, hxR, hx_lt⟩ := eventually_iff.mp h_event |>.exists
          have hx_norm : ‖f x‖ < M := by cases hx_lt with
            | inl h => exact h.2
            | inr h => exact False.elim (h hxR)
          have h_lim : Tendsto (norm ∘ f) l (𝓝 ‖f w‖) :=
            (continuous_norm.tendsto _).comp (hf_holo.continuousOn.tendsto h_nhds h_filt)
          exact le_of_tendsto' h_lim (fun y hy => (h_bound y hy.1).trans (hM_eq ▸ hx_norm.le))
      · exact h_bound w hw
    
    -- Now apply the strict maximum modulus principle
    have h_not_const : ¬IsConstantOn f R := by
      intro h_const
      obtain ⟨c, hc⟩ := h_const
      have hc' : ∀ z ∈ frontier R, ‖f z‖ = ‖c‖ := by
        intro z hz
        apply tendsto_nhds_unique (hf_holo.continuousOn.tendsto _ _)
        · exact hR_open.mem_nhds (frontier_subset_closure hR_open hz)
        · exact tendsto_const_nhds
        · exact hc z (frontier_subset_closure hR_open hz)
      obtain ⟨z', hz', hz'_strict⟩ := h_strict
      obtain ⟨l, hl, h_event⟩ := hz'_strict
      obtain ⟨x, hxR, hx_lt⟩ := eventually_iff.mp h_event |>.exists
      have hx_norm : ‖f x‖ < M := by cases hx_lt with
        | inl h => exact h.2
        | inr h => exact False.elim (h hxR)
      rw [hc' x (frontier_subset_closure hR_open hz'), hc z hz] at hx_norm
      exact hx_norm.ne rfl
    
    exact h_not_const (hf_holo.eqOn_of_isMaxOn_norm hR_conn h_max)