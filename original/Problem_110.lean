/-
Polya-Szego Problem 110
Part One, Chapter 3

Original problem:
Assume : © B. that $m \leqq$ I \# continuous on ↓ b .\\

Formalization notes: This formalizes a theorem about analytic functions on the open unit disk 𝔻.
  We consider functions f that are analytic on 𝔻 (holomorphic on the open unit disk)
  and satisfy f(0) = 0, f'(0) = 1 (normalization conditions common in univalent function theory).
  
  The theorem states that if zf'(z) is starlike with respect to 0 (meaning the image of 𝔻 under
  zf'(z) is starlike about 0), then f is convex (meaning the image of 𝔻 under f is convex).
  
  This captures the essence of Problem 110: The argument/angle consideration suggests that
  convexity of f corresponds to starlikeness of zf'(z).
  
  Note: In complex analysis literature, a domain D is starlike about 0 if for every z ∈ D,
  the line segment from 0 to z is contained in D. A function g is starlike if g(0) = 0,
  g is analytic and injective (univalent) on 𝔻, and g(𝔻) is starlike about 0.
-/
-/

import Mathlib.Analysis.Complex.Conformal

open Complex
open Set
open Metric

/-- Formalization notes: 
  This formalizes a theorem about analytic functions on the open unit disk 𝔻.
  We consider functions f that are analytic on 𝔻 (holomorphic on the open unit disk)
  and satisfy f(0) = 0, f'(0) = 1 (normalization conditions common in univalent function theory).
  
  The theorem states that if zf'(z) is starlike with respect to 0 (meaning the image of 𝔻 under
  zf'(z) is starlike about 0), then f is convex (meaning the image of 𝔻 under f is convex).
  
  This captures the essence of Problem 110: The argument/angle consideration suggests that
  convexity of f corresponds to starlikeness of zf'(z).
  
  Note: In complex analysis literature, a domain D is starlike about 0 if for every z ∈ D,
  the line segment from 0 to z is contained in D. A function g is starlike if g(0) = 0,
  g is analytic and injective (univalent) on 𝔻, and g(𝔻) is starlike about 0.
-/

theorem problem_110_part_one_chapter_3 : 
    ∀ (f : ℂ → ℂ) (h : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (h_norm : f 0 = 0) (h_deriv_norm : deriv f 0 = 1)
    (h_starlike : ∀ z ∈ ball (0 : ℂ) 1, 
        ∃ t : ℝ, t ∈ Set.Ioo (0 : ℝ) 1 ∧ deriv f z * z = t • (z * deriv f z)),
    Convex ℝ (f '' (ball (0 : ℂ) 1)) := by
  sorry

-- Proof attempt:
theorem problem_110_part_one_chapter_3 : 
    ∀ (f : ℂ → ℂ) (h : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (h_norm : f 0 = 0) (h_deriv_norm : deriv f 0 = 1)
    (h_starlike : ∀ z ∈ ball (0 : ℂ) 1, 
        ∃ t : ℝ, t ∈ Set.Ioo (0 : ℝ) 1 ∧ deriv f z * z = t • (z * deriv f z)),
    Convex ℝ (f '' (ball (0 : ℂ) 1)) := by
  intro f hf h0 h1 h_starlike
  rw [Convex]
  intro w1 w2 hw1 hw2 a b ha hb hab
  obtain ⟨z1, hz1, rfl⟩ := hw1
  obtain ⟨z2, hz2, rfl⟩ := hw2
  have hz1' : z1 ∈ ball (0 : ℂ) 1 := hz1
  have hz2' : z2 ∈ ball (0 : ℂ) 1 := hz2
  have hf' : ∀ z ∈ ball (0 : ℂ) 1, DifferentiableAt ℂ f z := 
    fun z hz => hf.differentiableAt (ball_mem_nhds _ (by norm_num) hz)
  
  -- Key step: Show f is convex by parameterizing the line segment
  refine ⟨fun θ : ℝ => f (θ • z1 + (1 - θ) • z2), ?_, ?_⟩
  · intro θ hθ
    have hθ' : θ ∈ Icc (0 : ℝ) 1 := ⟨hθ.1.le, hθ.2.le⟩
    have h_mem : θ • z1 + (1 - θ) • z2 ∈ ball (0 : ℂ) 1 := by
      apply convex_ball (0 : ℂ) 1 hz1' hz2' hθ'
    apply mem_image_of_mem f h_mem
  · have h0' : f 0 = 0 := h0
    have h1' : deriv f 0 = 1 := h1
    have h_eq : a • f z1 + b • f z2 = f (a • z1 + b • z2) := by
      -- Main equality using starlikeness condition
      have h_path : ∀ t ∈ Icc (0 : ℝ) 1, DifferentiableAt ℂ (fun w => f (w • (a • z1 + b • z2))) t := by
        intro t ht
        apply DifferentiableAt.comp _ (hf' _ _)
        · apply DifferentiableAt.smul_const
          exact differentiableAt_id'
        · apply mem_ball.2
          calc
            ‖t • (a • z1 + b • z2)‖ = t * ‖a • z1 + b • z2‖ := norm_smul _ _
            _ ≤ 1 * ‖a • z1 + b • z2‖ := by gcongr; exact ht.2
            _ ≤ a * ‖z1‖ + b * ‖z2‖ := by
              rw [norm_smul, norm_smul]
              apply le_trans (norm_add_le _ _)
              gcongr
              exact le_refl _
            _ < a * 1 + b * 1 := by
              gcongr
              · exact mem_ball_iff_norm.1 hz1
              · exact mem_ball_iff_norm.1 hz2
            _ = 1 := by rw [← add_mul, hab, one_mul]
      have h_deriv : ∀ t ∈ Ioo (0 : ℝ) 1, 
          deriv (fun w => f (w • (a • z1 + b • z2))) t = deriv f (t • (a • z1 + b • z2)) * (a • z1 + b • z2) := by
        intro t ht
        apply deriv.comp
        · exact hf' _ (by apply mem_ball.2; simpa using ht.1)
        · exact (differentiableAt_id'.smul_const _).differentiableWithinAt
      have h_int : ∀ t ∈ Ioo (0 : ℝ) 1, deriv f (t • (a • z1 + b • z2)) * (a • z1 + b • z2) = 
          deriv f (t • (a • z1 + b • z2)) * t • (a • z1 + b • z2) / t := by
        intro t ht
        field_simp [ht.1.ne']
        rw [smul_smul]
      have h_star : ∀ t ∈ Ioo (0 : ℝ) 1, ∃ s ∈ Ioo (0 : ℝ) 1, 
          deriv f (t • (a • z1 + b • z2)) * t • (a • z1 + b • z2) = s • (t • (a • z1 + b • z2) * deriv f (t • (a • z1 + b • z2))) := by
        intro t ht
        apply h_starlike
        apply mem_ball.2
        simpa using ht.1
      have h_main : ∀ t ∈ Ioo (0 : ℝ) 1, deriv (fun w => f (w • (a • z1 + b • z2))) t = 
          (t • (a • z1 + b • z2) * deriv f (t • (a • z1 + b • z2))) / t := by
        intro t ht
        rw [h_deriv t ht, h_int t ht]
        obtain ⟨s, hs, h_eq⟩ := h_star t ht
        rw [h_eq]
        field_simp [ht.1.ne']
      have h_integral : f (a • z1 + b • z2) = ∫ t in (0 : ℝ)..1, deriv (fun w => f (w • (a • z1 + b • z2))) t := by
        have h_cont : ContinuousOn (fun t => deriv (fun w => f (w • (a • z1 + b • z2))) t) (Icc 0 1) := by
          apply ContinuousOn.deriv
          · exact h_path
          · exact continuousOn_id.smul continuousOn_const
        rw [← integral_of_hasDerivAt h_path h_cont]
        simp [h0]
      rw [h_integral]
      simp_rw [h_main]
      sorry -- The remaining part requires more advanced complex analysis machinery
    rw [h_eq]
    simp [h0]