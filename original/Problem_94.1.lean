/-
Polya-Szego Problem 94.1
Part One, Chapter 2

Original problem:
A solid is so located in a rectangular coordinate system that its intersection with any straight line that is parallel to one of the three coordinate axes is either empty or consists of just one point or just one line segment. (Such a solid need not be convex.) Let $S$ be the surface area of the boundary of the solid and $P, Q$ and $R$ the areas of its orthogonal projections onto the three coordinate planes respectively. Show that

$$
2\left(P^{2}+Q^{2}+R^{2}\right)^{\frac{1}{2}} \leqq S \leqq 2

Formalization notes: We formalize the inequality for convex polyhedra satisfying the intersection condition.
The problem involves:
1. A solid (polyhedron) in ℝ³ with the property that its intersection with any line parallel to 
   a coordinate axis is either empty, a point, or a single line segment.
2. S = surface area of the boundary
3. P, Q, R = areas of orthogonal projections onto the yz, xz, and xy planes respectively.
4. The inequality: 2√(P² + Q² + R²) ≤ S ≤ 2(P + Q + R)
-/

import Mathlib.Analysis.InnerProductSpace.Projection
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.Geometry.Euclidean.Basic

/-!
Formalization notes:

We formalize the inequality for convex polyhedra satisfying the intersection condition.
The problem involves:
1. A solid (polyhedron) in ℝ³ with the property that its intersection with any line parallel to 
   a coordinate axis is either empty, a point, or a single line segment.
2. S = surface area of the boundary
3. P, Q, R = areas of orthogonal projections onto the yz, xz, and xy planes respectively.
4. The inequality: 2√(P² + Q² + R²) ≤ S ≤ 2(P + Q + R)

We make several simplifications for formalization:
- We assume the solid is a convex polyhedron (as suggested by the book's solution)
- We use the Lebesgue measure for area/surface area
- We formalize the inequality for polyhedra with the given intersection property
- The "simple polyhedra" achieving equality are mentioned in comments

Note: The full problem with smooth surfaces would require measure-theoretic surface area
and projections, which is significantly more complex to formalize completely.
-/

open Set
open scoped RealInnerProductSpace

structure AxisAlignedPolyhedron where
  /-- The set of points in the polyhedron -/
  points : Set (ℝ × ℝ × ℝ)
  /-- The polyhedron is closed and bounded -/
  isCompact : IsCompact points
  /-- Convexity assumption -/
  convex : Convex ℝ points
  /-- Intersection condition: lines parallel to axes intersect in at most a segment -/
  intersection_condition : ∀ (axis : Fin 3) (c₁ c₂ : ℝ × ℝ), 
    let line := {p : ℝ × ℝ × ℝ | 
      match axis with
      | 0 => p.2.1 = c₁.1 ∧ p.2.2 = c₁.2  -- x fixed, y,z vary
      | 1 => p.1 = c₁.1 ∧ p.2.2 = c₁.2    -- y fixed, x,z vary  
      | 2 => p.1 = c₁.1 ∧ p.2.1 = c₁.2}   -- z fixed, x,y vary
    IsConnected (points ∩ line) ∧
    (points ∩ line).Subsingleton ∨ (∃ a b : ℝ, a ≤ b ∧ 
      points ∩ line = {p | match axis with
        | 0 => p = (a, c₁.1, c₁.2) ∨ p = (b, c₁.1, c₁.2) ∨ 
                ∃ t ∈ Set.Icc (0 : ℝ) 1, p = ((1 - t) * a + t * b, c₁.1, c₁.2)
        | 1 => p = (c₁.1, a, c₁.2) ∨ p = (c₁.1, b, c₁.2) ∨
                ∃ t ∈ Set.Icc (0 : ℝ) 1, p = (c₁.1, (1 - t) * a + t * b, c₁.2)
        | 2 => p = (c₁.1, c₁.2, a) ∨ p = (c₁.1, c₁.2, b) ∨
                ∃ t ∈ Set.Icc (0 : ℝ) 1, p = (c₁.1, c₁.2, (1 - t) * a + t * b)})

noncomputable def surfaceArea (P : AxisAlignedPolyhedron) : ℝ :=
  volume (Metric.frontier P.points)

noncomputable def projectionArea (P : AxisAlignedPolyhedron) (axis : Fin 3) : ℝ :=
  let proj : ℝ × ℝ × ℝ → ℝ × ℝ :=
    match axis with
    | 0 => λ p => (p.2.1, p.2.2)  -- Project onto yz-plane (x = 0)
    | 1 => λ p => (p.1, p.2.2)    -- Project onto xz-plane (y = 0)
    | 2 => λ p => (p.1, p.2.1)    -- Project onto xy-plane (z = 0)
  volume (proj '' P.points)

theorem problem_94_1 (P : AxisAlignedPolyhedron) :
    let S := surfaceArea P
    let P_area := projectionArea P 0  -- Projection onto yz-plane
    let Q_area := projectionArea P 1  -- Projection onto xz-plane  
    let R_area := projectionArea P 2  -- Projection onto xy-plane
    2 * Real.sqrt (P_area ^ 2 + Q_area ^ 2 + R_area ^ 2) ≤ S ∧ 
    S ≤ 2 * (P_area + Q_area + R_area) := by
  sorry

/-!
Additional theorems for the equality cases mentioned in the problem:

theorem cube_attains_upper_bound : 
    ∃ (cube : AxisAlignedPolyhedron), 
    let S := surfaceArea cube
    let P_area := projectionArea cube 0
    let Q_area := projectionArea cube 1
    let R_area := projectionArea cube 2
    S = 2 * (P_area + Q_area + R_area) := by
  sorry

theorem regular_octahedron_attains_lower_bound :
    ∃ (octahedron : AxisAlignedPolyhedron),
    let S := surfaceArea octahedron
    let P_area := projectionArea octahedron 0
    let Q_area := projectionArea octahedron 1
    let R_area := projectionArea octahedron 2
    S = 2 * Real.sqrt (P_area ^ 2 + Q_area ^ 2 + R_area ^ 2) := by
  sorry
-/

-- Proof attempt:
theorem problem_94_1 (P : AxisAlignedPolyhedron) :
    let S := surfaceArea P
    let P_area := projectionArea P 0  -- Projection onto yz-plane
    let Q_area := projectionArea P 1  -- Projection onto xz-plane  
    let R_area := projectionArea P 2  -- Projection onto xy-plane
    2 * Real.sqrt (P_area ^ 2 + Q_area ^ 2 + R_area ^ 2) ≤ S ∧ 
    S ≤ 2 * (P_area + Q_area + R_area) := by
  -- First we need to formalize the face decomposition of the polyhedron
  -- Since we're assuming convex polyhedron with axis-aligned intersections,
  -- we can model the faces appropriately
  have h_faces : ∃ (faces : Finset (Set (ℝ × ℝ × ℝ))), 
    (∀ f ∈ faces, ∃ a b c d : ℝ, f = {p | p.1 = a ∧ p.2.1 = b ∧ p.2.2 = c} ∨ 
                                  f = {p | p.1 = a ∧ p.2.1 = b ∧ p.2.2 ∈ Icc c d} ∨
                                  f = {p | p.1 = a ∧ p.2.2 = b ∧ p.2.1 ∈ Icc c d} ∨
                                  f = {p | p.2.1 = a ∧ p.2.2 = b ∧ p.1 ∈ Icc c d}) ∧
    (Metric.frontier P.points) = ⋃ f ∈ faces, f ∧
    (∀ f ∈ faces, ∀ g ∈ faces, f ≠ g → Disjoint f g) := by
    -- This would require a more detailed construction of the faces
    sorry -- omitting the face construction details for brevity

  -- Let's assume we have the faces decomposed as above
  rcases h_faces with ⟨faces, face_def, frontier_eq, face_disjoint⟩
  
  -- Define projection areas for each face
  let p_v (f : Set (ℝ × ℝ × ℝ)) : ℝ := volume ((λ p => (p.2.1, p.2.2)) '' f)
  let q_v (f : Set (ℝ × ℝ × ℝ)) : ℝ := volume ((λ p => (p.1, p.2.2)) '' f)
  let r_v (f : Set (ℝ × ℝ × ℝ)) : ℝ := volume ((λ p => (p.1, p.2.1)) '' f)
  
  -- Surface area is sum of face areas
  have hS : S = ∑ f in faces, Real.sqrt (p_v f ^ 2 + q_v f ^ 2 + r_v f ^ 2) := by
    rw [surfaceArea, frontier_eq]
    apply volume_eq_of_pairwise_disjoint_union
    · intro f hf
      exact MeasurableSet.of_isClosed (by cases (face_def.1 f hf); simp [*])
    · exact face_disjoint
    · simp only [Finset.set_biUnion_preimage_singleton]
      congr
      ext x
      simp only [mem_setOf_eq, mem_iUnion, exists_prop]
      rw [frontier_eq]
      simp
  
  -- Projection areas are sums of face projections
  have hP : P_area = ∑ f in faces, p_v f := by
    simp [projectionArea]
    rw [← image_Union, ← Finset.set_biUnion_preimage_singleton]
    rw [volume_Union_of_pairwise_disjoint]
    · congr
      ext x
      simp only [mem_setOf_eq, mem_iUnion, exists_prop]
    · intro f hf g hg hfg
      apply Disjoint.image _ (face_disjoint f hf g hg hfg)
      exact measurable_prod_mk_left
  
  have hQ : Q_area = ∑ f in faces, q_v f := by
    simp [projectionArea]
    rw [← image_Union, ← Finset.set_biUnion_preimage_singleton]
    rw [volume_Union_of_pairwise_disjoint]
    · congr
      ext x
      simp only [mem_setOf_eq, mem_iUnion, exists_prop]
    · intro f hf g hg hfg
      apply Disjoint.image _ (face_disjoint f hf g hg hfg)
      exact measurable_prod_mk_left
  
  have hR : R_area = ∑ f in faces, r_v f := by
    simp [projectionArea]
    rw [← image_Union, ← Finset.set_biUnion_preimage_singleton]
    rw [volume_Union_of_pairwise_disjoint]
    · congr
      ext x
      simp only [mem_setOf_eq, mem_iUnion, exists_prop]
    · intro f hf g hg hfg
      apply Disjoint.image _ (face_disjoint f hf g hg hfg)
      exact measurable_prod_mk_left

  -- Now prove the inequalities
  constructor
  · -- Lower bound: 2√(P² + Q² + R²) ≤ S
    rw [hS, hP, hQ, hR]
    have : ∀ f ∈ faces, 0 ≤ p_v f ∧ 0 ≤ q_v f ∧ 0 ≤ r_v f := by
      intro f hf
      simp [p_v, q_v, r_v]
      repeat' apply volume_nonneg
    simp_rw [← Real.sqrt_mul_self (by positivity)]
    have h_norm : Real.sqrt (P_area ^ 2 + Q_area ^ 2 + R_area ^ 2) = 
        Real.sqrt ((∑ f in faces, p_v f) ^ 2 + (∑ f in faces, q_v f) ^ 2 + (∑ f in faces, r_v f) ^ 2) := by
      rw [hP, hQ, hR]
    rw [h_norm]
    have : 2 * Real.sqrt ((∑ f in faces, p_v f) ^ 2 + (∑ f in faces, q_v f) ^ 2 + (∑ f in faces, r_v f) ^ 2) ≤ 
           ∑ f in faces, Real.sqrt (p_v f ^ 2 + q_v f ^ 2 + r_v f ^ 2) := by
      -- This is the key inequality: 2-norm of sums ≤ sum of 2-norms
      -- Equivalent to the triangle inequality for the L2 norm
      simp_rw [← Real.sqrt_mul_self (by positivity)]
      have h := Finset.sum_le_sum (fun f _ => Real.sqrt_le_sqrt (add_le_add (add_le_add (mul_self_le_mul_self (by positivity) (le_abs_self _)) 
        (mul_self_le_mul_self (by positivity) (le_abs_self _))) (mul_self_le_mul_self (by positivity) (le_abs_self _))))
      sorry -- Need to fill in details of this norm inequality
    linarith
  · -- Upper bound: S ≤ 2(P + Q + R)
    rw [hS, hP, hQ, hR]
    apply Finset.sum_le_sum
    intro f hf
    have : Real.sqrt (p_v f ^ 2 + q_v f ^ 2 + r_v f ^ 2) ≤ p_v f + q_v f + r_v f := by
      refine Real.sqrt_le_sqrt ?_
      rw [add_assoc]
      refine le_trans ?_ (add_le_add (add_le_add (le_self_sq (p_v f) (by positivity)) 
        (le_self_sq (q_v f) (by positivity))) (le_self_sq (r_v f) (by positivity)))
      ring
    linarith