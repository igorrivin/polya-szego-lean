/-
Polya-Szego Problem 186
Part Three, Chapter 4

Original problem:
The function $f(z)$ is meromorphic in the interior of the curve $L$ and regular on the curve $L$. If $|a|$ is larger than the maximum of $|f(z)|$ on $L$ then $f(z)$ assumes the value $a$ inside $L$ just as often as it has poles there.\\

Formalization notes: -- 1. We formalize the statement for a simple closed curve L in ℂ
-- 2. "Meromorphic in the interior" means meromorphic on an open set containing the closure of the interior
-- 3. "Regular on L" means holomorphic on a neighborhood of L
-- 4. "Assumes the value a just as often as it has poles" means the number of zeros of f(z) - a
--    (counting multiplicities) equals the number of poles (counting multiplicities) inside L
-- 5. We assume L is a simple closed rectifiable curve with interior U
-- 6. We use the argument principle to relate zeros and poles
-/

import Mathlib.Analysis.Complex.ArgumentPrinciple
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Topology.Algebra.Order.Compact

-- Formalization notes:
-- 1. We formalize the statement for a simple closed curve L in ℂ
-- 2. "Meromorphic in the interior" means meromorphic on an open set containing the closure of the interior
-- 3. "Regular on L" means holomorphic on a neighborhood of L
-- 4. "Assumes the value a just as often as it has poles" means the number of zeros of f(z) - a
--    (counting multiplicities) equals the number of poles (counting multiplicities) inside L
-- 5. We assume L is a simple closed rectifiable curve with interior U
-- 6. We use the argument principle to relate zeros and poles

theorem problem_186 {L : Set ℂ} {U : Set ℂ} {f : ℂ → ℂ} {a : ℂ} 
    (hL_simple : SimpleClosedCurve L) (hU_interior : U = interior L)
    (h_mero : MeromorphicOn f U) (h_reg_on_L : HolomorphicOn f (𝓝ˢ L))
    (h_bound : ∃ M : ℝ, 0 < M ∧ ∀ z ∈ L, Complex.abs (f z) ≤ M)
    (h_a_large : M < Complex.abs a) : 
    let M := sSup (Complex.abs ∘ f '' L) in
    let zeros_count := Complex.countZerosWithin (fun z => f z - a) U in
    let poles_count := Complex.countPolesWithin f U in
    zeros_count = poles_count := by
  sorry

-- Proof attempt:
let M := sSup (Complex.abs ∘ f '' L)
let zeros_count := Complex.countZerosWithin (fun z => f z - a) U
let poles_count := Complex.countPolesWithin f U

have hM_pos : 0 ≤ M := by
  obtain ⟨M', hM'⟩ := h_bound
  apply le_csSup (Complex.abs ∘ f '' L).bddAbove
  exact ⟨f (Classical.choose hL_simple.nonempty), mem_image_of_mem _ (Classical.choose_spec hL_simple.nonempty)⟩

have h_image : (fun z ↦ f z - a) '' L ⊆ Metric.ball 0 M := by
  rintro _ ⟨z, hz, rfl⟩
  simp only [Metric.mem_ball, dist_zero_left, Complex.norm_eq_abs]
  have hfz := (Classical.choose_spec h_bound).2 z hz
  linarith [h_a_large, hfz]

have h_ne_zero : ∀ z ∈ L, f z - a ≠ 0 := by
  intro z hz
  have hfz := (Classical.choose_spec h_bound).2 z hz
  intro h
  rw [h, Complex.abs.map_zero] at hfz
  linarith [h_a_large, hfz]

have h_winding : windingNumber (fun z ↦ f z - a) hL_simple 0 = 0 := by
  refine windingNumber_eq_zero_of_mapsTo_of_missing hL_simple ?_ ?_
  · exact h_image
  · exact fun _ _ ↦ by simp [h_ne_zero]

have h_arg_principle := argument_principle hL_simple hU_interior (h_mero.sub_const a) h_reg_on_L.const_sub 0

simp only [windingNumber_eq_zero_iff, h_winding, sub_zero, Nat.cast_inj] at h_arg_principle
exact h_arg_principle