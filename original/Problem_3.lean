/-
Polya-Szego Problem 3
Part Three, Chapter 1

Original problem:
What sets of points in the $z$-plane are characterized by the condi-

$$
|z-a|+|z-b|=k ;|z-a|+|z-b| \leqq k, k>0 ?
$$

\begin{enumerate}
  \setcounter{enumi}{3}
  \item What open set of the $z$-plane is characterized by the condition
\end{enumerate}

$$
\left|z^{2}+a z+b\right|<R^{2} ?
$$

For what values of $R$ is this set connected, for what values of $R$ is it not connected?\\

Formalization notes: -- We formalize the two conditions from the problem:
-- 1. The set of points satisfying |z² + a*z + b| < R²
-- 2. The connectedness properties of this set for different R values
-- We work in ℂ (the z-plane) with complex numbers a, b, and real R > 0
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.NormedSpace.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Algebra.Order.Connected

-- Formalization notes:
-- We formalize the two conditions from the problem:
-- 1. The set of points satisfying |z² + a*z + b| < R²
-- 2. The connectedness properties of this set for different R values
-- We work in ℂ (the z-plane) with complex numbers a, b, and real R > 0

open Complex
open Set
open Metric

theorem problem_3_part_3 : 
    -- For given complex numbers a, b and positive real R,
    -- define the open set S = {z : ℂ | |z² + a*z + b| < R²}
    ∀ (a b : ℂ) (R : ℝ) (hR : R > 0), 
    let S : Set ℂ := {z : ℂ | Complex.abs (z^2 + a * z + b) < R^2} in
    -- S is open (since it's a preimage of an open interval under a continuous function)
    IsOpen S ∧
    -- Connectedness conditions:
    -- There exists some R₀ > 0 such that:
    (∃ (R₀ : ℝ) (hR₀ : R₀ > 0), 
      -- For R < R₀, S is connected
      (∀ (R' : ℝ), 0 < R' ∧ R' < R₀ → 
        let S' : Set ℂ := {z : ℂ | Complex.abs (z^2 + a * z + b) < R'^2} in
        IsConnected S') ∧
      -- For R > R₀, S is not connected (disconnected)
      (∀ (R' : ℝ), R' > R₀ → 
        let S' : Set ℂ := {z : ℂ | Complex.abs (z^2 + a * z + b) < R'^2} in
        ¬ IsConnected S')) := by
  sorry

-- Proof attempt:
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.NormedSpace.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Algebra.Order.Connected
import Mathlib.Analysis.Complex.Polynomial

open Complex
open Set
open Metric
open Topology

theorem problem_3_part_3 : 
    ∀ (a b : ℂ) (R : ℝ) (hR : R > 0), 
    let S : Set ℂ := {z : ℂ | Complex.abs (z^2 + a * z + b) < R^2} in
    IsOpen S ∧
    (∃ (R₀ : ℝ) (hR₀ : R₀ > 0), 
      (∀ (R' : ℝ), 0 < R' ∧ R' < R₀ → 
        let S' : Set ℂ := {z : ℂ | Complex.abs (z^2 + a * z + b) < R'^2} in
        IsConnected S') ∧
      (∀ (R' : ℝ), R' > R₀ → 
        let S' : Set ℂ := {z : ℂ | Complex.abs (z^2 + a * z + b) < R'^2} in
        ¬ IsConnected S')) := by
  intro a b R hR
  let S := {z : ℂ | Complex.abs (z^2 + a * z + b) < R^2}
  -- Part 1: S is open
  have hS_open : IsOpen S := by
    apply isOpen_lt
    · exact continuous_abs.comp (continuous_add (continuous_add (continuous_pow 2) (continuous_mul_left a)) (continuous_const b))
    · exact continuous_const
  -- Part 2: Connectedness conditions
  let p : ℂ → ℂ := fun z => z^2 + a * z + b
  let p' : ℂ → ℂ := fun z => 2 * z + a  -- derivative of p
  -- Find critical point where p' = 0
  let z_crit : ℂ := -a / 2
  have h_crit : p' z_crit = 0 := by
    simp [p']
    ring
  -- Evaluate p at critical point
  let p_crit := p z_crit
  let R₀ := Real.sqrt (Complex.abs p_crit)
  have hR₀ : R₀ > 0 := by
    apply Real.sqrt_pos.mpr
    by_cases h : p_crit = 0
    · simp [h, R₀]
      exact hR
    · exact Complex.abs.pos h
  -- Now prove the connectedness properties
  refine ⟨hS_open, R₀, hR₀, ?_, ?_⟩
  · -- For R' < R₀, S' is connected
    intro R' ⟨hR'pos, hR'lt⟩
    let S' := {z | Complex.abs (p z) < R'^2}
    have hR'sq_lt : R'^2 < Complex.abs p_crit := by
      rw [← Real.sqrt_lt_sqrt_iff (by positivity), Real.sq_sqrt (Complex.abs.nonneg p_crit)]
      exact hR'lt
    -- The set S' is a single connected component around the roots of p
    have h_conn : IsConnected S' := by
      apply IsPreconnected.isConnected
      · -- Nonempty: contains the roots of p
        let z1 := (-a + (a^2 - 4 * b).sqrt) / 2
        let z2 := (-a - (a^2 - 4 * b).sqrt) / 2
        have hz1 : p z1 = 0 := by
          simp [p]
          field_simp
          ring_nf
          rw [← pow_two, Complex.sqrt_mul_self]
          simp
        have hz2 : p z2 = 0 := by
          simp [p]
          field_simp
          ring_nf
          rw [← pow_two, Complex.sqrt_mul_self]
          simp
        have : z1 ∈ S' := by simp [S', hz1, hR'pos]
        exact ⟨z1, this⟩
      · -- Preconnected: path-connected
        refine isPreconnected_univ.image_of_continuousOn (fun z _ => p z) ?_
        exact (continuous_pow 2).add (continuous_const.mul continuous_id).add continuous_const
    exact h_conn
  · -- For R' > R₀, S' is not connected
    intro R' hR'gt
    let S' := {z | Complex.abs (p z) < R'^2}
    have hR'sq_gt : R'^2 > Complex.abs p_crit := by
      rw [← Real.sqrt_lt_sqrt_iff (by positivity), Real.sq_sqrt (Complex.abs.nonneg p_crit)]
      exact hR'gt
    -- The set S' has at least two connected components (around each root)
    have h_not_conn : ¬ IsConnected S' := by
      intro h_conn
      -- Find points z1 and z2 near the roots but separated by the critical point
      let z1 := (-a + (a^2 - 4 * b).sqrt) / 2
      let z2 := (-a - (a^2 - 4 * b).sqrt) / 2
      have hz1 : p z1 = 0 := by
        simp [p]
        field_simp
        ring_nf
        rw [← pow_two, Complex.sqrt_mul_self]
        simp
      have hz2 : p z2 = 0 := by
        simp [p]
        field_simp
        ring_nf
        rw [← pow_two, Complex.sqrt_mul_self]
        simp
      have hz1_in : z1 ∈ S' := by simp [S', hz1, hR'gt.trans_lt (by positivity)]
      have hz2_in : z2 ∈ S' := by simp [S', hz2, hR'gt.trans_lt (by positivity)]
      -- The critical point is not in S' since |p(z_crit)| = R₀^2 < R'^2 is false
      have h_crit_not_in : z_crit ∉ S' := by
        simp [S', p_crit]
        exact hR'sq_gt.not_lt (le_refl _)
      -- But any path from z1 to z2 must pass through z_crit (by continuity and intermediate value theorem)
      -- This contradicts connectedness
      obtain ⟨γ, hγ⟩ := h_conn.isPreconnected.joinedIn z1 z2 hz1_in hz2_in
      have h_cont : Continuous γ := hγ.1.continuousOn.restrict (by continuity)
      have h0 : γ 0 = z1 := hγ.2.1
      have h1 : γ 1 = z2 := hγ.2.2
      -- By intermediate value theorem, there exists t ∈ [0,1] such that γ t = z_crit
      have hIVT : z_crit ∈ γ '' (Icc 0 1) := by
        apply IntermediateValueIVT' h_cont
        · rw [h0, h1]
          simp [z_crit]
          field_simp
          ring
        · rw [h0, h1]
          simp [z_crit]
          field_simp
          ring
      obtain ⟨t, ht_mem, ht_eq⟩ := hIVT
      have : γ t ∈ S' := hγ.1 (mem_image_of_mem γ ht_mem)
      rw [ht_eq] at this
      exact h_crit_not_in this
    exact h_not_conn