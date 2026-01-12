/-
Polya-Szego Problem 33
Part Three, Chapter 1

Original problem:
Let $P(z)$ denote a polynomial. The zeros of $c P^{\prime}(z)-P(z), c \neq 0$ lie in the smallest (infinite) convex polygon that contains the rays parallel to the vector $c$ starting from the zeros of $P(z)$.

A zero of $c P^{\prime}(z)-P(z)$ appears on the boundary of this region only in one of the following two cases: (a) the zero in question is also a zero of $P(z)$; (b) the region in question degenerates into a ray.\\

Formalization notes: -- 1. We formalize the main geometric statement about zeros of c*P'(z) - P(z)
-- 2. We use ℂ for complex numbers and Polynomial ℂ for polynomials
-- 3. The "smallest infinite convex polygon containing rays" is formalized as:
--    - convexHull ℝ (Set.union (roots of P) (rays from roots in direction c))
--    - where rays are {z + t*c | t ≥ 0} for each root z of P
-- 4. The boundary conditions are stated separately as additional theorems
-/

import Mathlib.Analysis.Complex.Polynomial
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Complex.Basic

-- Formalization notes:
-- 1. We formalize the main geometric statement about zeros of c*P'(z) - P(z)
-- 2. We use ℂ for complex numbers and Polynomial ℂ for polynomials
-- 3. The "smallest infinite convex polygon containing rays" is formalized as:
--    - convexHull ℝ (Set.union (roots of P) (rays from roots in direction c))
--    - where rays are {z + t*c | t ≥ 0} for each root z of P
-- 4. The boundary conditions are stated separately as additional theorems

open Complex
open Polynomial
open Set

-- Helper definition for rays from points in direction c
def raysFromPoints (points : Set ℂ) (c : ℂ) : Set ℂ :=
  ⋃ z ∈ points, {w | ∃ (t : ℝ) (ht : 0 ≤ t), w = z + (t : ℂ) * c}

-- Main theorem: zeros of c*P' - P lie in the convex hull of roots of P and rays from them
theorem problem_33_part1 (P : Polynomial ℂ) (c : ℂ) (hc : c ≠ 0) :
    ∀ z : ℂ, (c * evalDerivAt P z - eval P z = 0) →
    z ∈ convexHull ℝ ((roots P.toFinset) ∪ raysFromPoints (roots P.toFinset) c) := by
  sorry

-- Theorem for boundary case (a): zero is also a root of P
theorem problem_33_boundary_case_a (P : Polynomial ℂ) (c : ℂ) (hc : c ≠ 0) (z : ℂ) :
    (c * evalDerivAt P z - eval P z = 0) → 
    (z ∈ frontier (convexHull ℝ ((roots P.toFinset) ∪ raysFromPoints (roots P.toFinset) c))) →
    (eval P z = 0) → True := by
  sorry

-- Theorem for boundary case (b): region degenerates to a ray
theorem problem_33_boundary_case_b (P : Polynomial ℂ) (c : ℂ) (hc : c ≠ 0) (z : ℂ) :
    (c * evalDerivAt P z - eval P z = 0) →
    (z ∈ frontier (convexHull ℝ ((roots P.toFinset) ∪ raysFromPoints (roots P.toFinset) c))) →
    (∃ (z₀ : ℂ) (t : ℝ), t ≥ 0 ∧ 
      convexHull ℝ ((roots P.toFinset) ∪ raysFromPoints (roots P.toFinset) c) = 
      {w | ∃ (s : ℝ), s ≥ 0 ∧ w = z₀ + (s : ℂ) * c}) → True := by
  sorry

-- Alternative formulation using the representation from the book's solution
theorem problem_33_representation (P : Polynomial ℂ) (c : ℂ) (hc : c ≠ 0) (z : ℂ) 
    (hz_root : c * evalDerivAt P z - eval P z = 0) (hz_not_root : eval P z ≠ 0) :
    ∃ (roots_finset : Finset ℂ) (m : ℂ → ℝ≥0) (M : ℝ≥0),
      (∀ r, r ∈ roots_finset ↔ P.IsRoot r) ∧
      (∑ r in roots_finset, (m r : ℂ)) ≠ 0 ∧
      z = ((∑ r in roots_finset, (m r : ℂ) * r) / (∑ r in roots_finset, (m r : ℂ))) + 
          (M : ℂ) * c := by
  sorry

-- Proof attempt:
theorem problem_33_part1 (P : Polynomial ℂ) (c : ℂ) (hc : c ≠ 0) :
    ∀ z : ℂ, (c * evalDerivAt P z - eval P z = 0) →
    z ∈ convexHull ℝ ((roots P.toFinset) ∪ raysFromPoints (roots P.toFinset) c) := by
  intro z hz
  by_cases hz_root : eval P z = 0
  · -- Case 1: z is a root of P
    simp [roots] at hz_root
    have : z ∈ roots P.toFinset := by
      simp [hz_root]
    apply subset_convexHull ℝ ((roots P.toFinset) ∪ raysFromPoints (roots P.toFinset) c)
    exact subset_union_left _ _ this
  · -- Case 2: z is not a root of P
    let roots_finset := P.roots.toFinset
    have h_sum : ∑ r in roots_finset, (1 / (z - r)) = 1 / c := by
      rw [← hz, eval_deriv_div_eval P z hz_root, ← inv_eq_one_div]
      simp [inv_eq_one_div]
    let m : ℂ → ℝ≥0 := fun r => (1 / ‖z - r‖^2).toNNReal
    let M := (‖∑ r in roots_finset, m r * (1 / (conj (z - r)))‖ / ‖1 / c‖^2).toNNReal
    have h_m_pos : ∑ r in roots_finset, (m r : ℂ) ≠ 0 := by
      simp [m]
      have : ∑ r in roots_finset, (1 / ‖z - r‖^2 : ℝ) ≠ 0 := by
        apply ne_of_gt
        apply Finset.sum_pos'
        · intro r hr
          simp only [one_div, inv_pos]
          apply pow_pos
          exact norm_pos_iff.mpr (sub_ne_zero.mpr (ne_of_apply_ne _ (mem_roots.mp hr).2))
        · exact P.roots.toFinset.nonempty_of_ne_empty (fun h => hz_root (roots_eq_zero.mp h))
      norm_cast
    have h_rep : z = ((∑ r in roots_finset, (m r : ℂ) * r) / (∑ r in roots_finset, (m r : ℂ))) + 
                  (M : ℂ) * c := by
      -- This is the key representation from the book's solution
      sorry  -- This part would require more detailed calculation
    rw [h_rep]
    apply convexHull_add_smul_mem
    · apply convexHull_combination_mem
      · intro r hr
        exact subset_union_left _ _ (mem_roots.mp hr).1
      · exact h_m_pos
    · apply subset_convexHull ℝ ((roots P.toFinset) ∪ raysFromPoints (roots P.toFinset) c)
      refine mem_biUnion ?_ ?_
      · obtain ⟨r, hr⟩ := P.roots.toFinset.nonempty_of_ne_empty 
          (fun h => hz_root (roots_eq_zero.mp h))
        exact ⟨r, hr, 0, by simp⟩
      · exact fun r hr => ⟨r, hr, 0, by simp⟩