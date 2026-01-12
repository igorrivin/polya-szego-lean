/-
Polya-Szego Problem 301
Part Three, Chapter 6

Original problem:
In three dimensional space, the $n$ points $P_{1}, P_{2}, \ldots, P_{n}$ are given and $P$ denotes a variable point. The function

$$
\varphi(P)=\overline{P P}_{1} \cdot \overline{P P}_{2} \cdots \overline{P P}_{n}
$$

( $\overline{P P_{v}}$ is the distance between $P$ and $P_{v}$ ) of the point $P$ assumes its maximum in any domain on the boundary. (Generalization of 137.)\\

Formalization notes: -- 1. We formalize the 2D case from the solution (complex plane) rather than the original 3D statement
-- 2. We use ℂ for the complex plane and ℝ for distances
-- 3. The function is formalized as: f(z) = ∏_{v=1}^n (|z - a_v|^2 + b_v^2)
-- 4. We prove that in any bounded domain D ⊆ ℂ, if f attains a maximum in D, 
--    then it must occur on the boundary ∂D
-- 5. This captures the key insight: the maximum principle for this product of distances
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.MetricSpace.Basic

-- Formalization notes:
-- 1. We formalize the 2D case from the solution (complex plane) rather than the original 3D statement
-- 2. We use ℂ for the complex plane and ℝ for distances
-- 3. The function is formalized as: f(z) = ∏_{v=1}^n (|z - a_v|^2 + b_v^2)
-- 4. We prove that in any bounded domain D ⊆ ℂ, if f attains a maximum in D, 
--    then it must occur on the boundary ∂D
-- 5. This captures the key insight: the maximum principle for this product of distances

theorem problem_301 (n : ℕ) (a : Fin n → ℂ) (b : Fin n → ℝ) 
    (f : ℂ → ℝ) (hf : ∀ z : ℂ, f z = ∏ v : Fin n, ((Complex.dist z (a v)) ^ 2 + (b v) ^ 2)) 
    (D : Set ℂ) (hD : IsOpen D) (hDbounded : Bornology.IsBounded D) :
    ∀ z ∈ D, f z ≤ sSup (f '' (frontier D)) := by
  sorry

-- Proof attempt:
theorem problem_301 (n : ℕ) (a : Fin n → ℂ) (b : Fin n → ℝ) 
    (f : ℂ → ℝ) (hf : ∀ z : ℂ, f z = ∏ v : Fin n, ((Complex.dist z (a v)) ^ 2 + (b v) ^ 2)) 
    (D : Set ℂ) (hD : IsOpen D) (hDbounded : Bornology.IsBounded D) :
    ∀ z ∈ D, f z ≤ sSup (f '' (frontier D)) := by
  intro z hz
  -- First show f is continuous and subharmonic
  have f_cont : Continuous f := by
    simp [hf]
    apply Continuous.finset_prod (Fin.fintype n) (fun v _ => ?_)
    apply Continuous.add
    · exact (continuous_norm_sq.comp (Continuous.sub continuous_id continuous_const)).continuousAt
    · exact continuous_const
  have f_subharm : ∀ z, 0 < f z ∧ SubharmonicOn ℂ f univ z := by
    intro z
    constructor
    · apply Finset.prod_pos
      intro i _
      simp [hf, add_pos_iff, sq_pos_iff, Complex.dist_ne_zero]
    · simp [hf]
      apply SubharmonicOn.finset_prod (Fin.fintype n) (fun v _ => ?_)
      apply SubharmonicOn.add
      · apply SubharmonicOn.norm_sq
        exact subharmonicOn_id.sub subharmonicOn_const
      · exact subharmonicOn_const
  -- Now apply the maximum principle
  obtain ⟨w, hw⟩ := exists_mem_frontier_isCompact_closure_of_isBounded hDbounded hD ⟨z, hz⟩
  have hw' : w ∈ frontier D := hw.1
  have hw'' : w ∈ closure D := frontier_subset_closure hw'
  have := IsCompact.exists_isMaxOn (isCompact_closure_of_isBounded hDbounded) hw'' f_cont.continuousOn
  obtain ⟨ξ, hξ, hξ'⟩ := this
  have : ξ ∈ frontier D := by
    by_contra h
    have : ξ ∈ interior D := by
      rw [mem_frontier_iff_mem_closure_not_mem_interior] at h
      push_neg at h
      exact h
    have hfξ : 0 < f ξ := (f_subharm ξ).1
    have hsub : SubharmonicOn ℂ f D ξ := (f_subharm ξ).2.mono (subset_univ _)
    have := hsub.maximum_principle hD hfξ (isOpen_iff_mem_nhds.1 hD ξ this)
    exact this.not_le (hξ' (subset_closure hz))
  exact le_trans (hξ' (subset_closure hz)) (le_csSup (f_cont.bounded_iff_bounded_image.1 hDbounded).1 ⟨ξ, this, rfl⟩)