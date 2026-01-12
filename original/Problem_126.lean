/-
Polya-Szego Problem 126
Part One, Chapter 3

Original problem:
If a monotone sequence of continuous functions converges on a closed interval to a continuous function it converges uniformly. (Theorem of Dini.)\\

Formalization notes: -- We formalize Dini's theorem for monotone sequences of continuous functions 
-- converging pointwise to a continuous function on a compact interval [a, b].
-- The sequence is assumed to be monotone (either increasing or decreasing).
-- We state the theorem in its standard form rather than the reduced case 
-- mentioned in the book's solution.
-/

import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Topology.Algebra.Order.MonotoneConvergence
import Mathlib.Topology.MetricSpace.Basic

-- Formalization notes: 
-- We formalize Dini's theorem for monotone sequences of continuous functions 
-- converging pointwise to a continuous function on a compact interval [a, b].
-- The sequence is assumed to be monotone (either increasing or decreasing).
-- We state the theorem in its standard form rather than the reduced case 
-- mentioned in the book's solution.

theorem dini_theorem {a b : ℝ} (hab : a ≤ b) {ι : Type*} [Preorder ι] [hι : Nonempty ι] 
    [NoMaxOrder ι] (F : ι → C(Set.Icc a b, ℝ)) (f : C(Set.Icc a b, ℝ))
    (h_mono : Monotone F ∨ Antitone F) (h_pointwise : ∀ x, Tendsto (fun n => F n x) atTop (𝓝 (f x)))
    (h_cont : ∀ n, Continuous (F n)) (h_cont_f : Continuous f) :
    TendstoUniformlyOn F f atTop (Set.Icc a b) := by
  sorry

-- Proof attempt:
theorem dini_theorem {a b : ℝ} (hab : a ≤ b) {ι : Type*} [Preorder ι] [hι : Nonempty ι] 
    [NoMaxOrder ι] (F : ι → C(Set.Icc a b, ℝ)) (f : C(Set.Icc a b, ℝ))
    (h_mono : Monotone F ∨ Antitone F) (h_pointwise : ∀ x, Tendsto (fun n => F n x) atTop (𝓝 (f x)))
    (h_cont : ∀ n, Continuous (F n)) (h_cont_f : Continuous f) :
    TendstoUniformlyOn F f atTop (Set.Icc a b) := by
  -- First, handle both monotone and antitone cases by considering the appropriate difference
  cases' h_mono with h_mono h_anti
  · -- Monotone case
    let G := fun n => (F n - f).norm
    have hG_cont : ∀ n, Continuous (G n) := fun n => by continuity
    have hG_mono : Antitone G := by
      intro i j hij
      simp only [G, ContinuousMap.coe_sub, Pi.sub_apply, ContinuousMap.norm_coe_le_norm]
      exact ContinuousMap.monotone_norm_of_monotone h_mono hij f
    have hG_pointwise : ∀ x ∈ Set.Icc a b, Tendsto (fun n => G n x) atTop (𝓝 0) := by
      intro x hx
      simp only [G, ContinuousMap.coe_sub, Pi.sub_apply, norm_sub_rev]
      rw [← tendsto_iff_norm_tendsto_zero]
      exact h_pointwise x
    exact tendstoUniformlyOn_of_antitone hG_cont hG_mono hG_pointwise (isCompact_Icc.mono hab)
  · -- Antitone case
    let G := fun n => (f - F n).norm
    have hG_cont : ∀ n, Continuous (G n) := fun n => by continuity
    have hG_mono : Antitone G := by
      intro i j hij
      simp only [G, ContinuousMap.coe_sub, Pi.sub_apply, ContinuousMap.norm_coe_le_norm]
      exact ContinuousMap.monotone_norm_of_antitone h_anti hij f
    have hG_pointwise : ∀ x ∈ Set.Icc a b, Tendsto (fun n => G n x) atTop (𝓝 0) := by
      intro x hx
      simp only [G, ContinuousMap.coe_sub, Pi.sub_apply, norm_sub_rev]
      rw [← tendsto_iff_norm_tendsto_zero]
      exact h_pointwise x
    exact tendstoUniformlyOn_of_antitone hG_cont hG_mono hG_pointwise (isCompact_Icc.mono hab)