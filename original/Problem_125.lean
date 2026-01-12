/-
Polya-Szego Problem 125
Part One, Chapter 3

Original problem:
Suppose that the real function $f(x)$ is defined on a finite or infinite interval and that it has there a continuous derivative $f^{\prime}(x)$. Consider the points of intersection of all the horizontal tangents of the curve $y=f(x)$ with the $y$-axis, i.e. the set $M$ of all points

$$
y=f(x) \quad \text { for which } \quad f^{\prime}(x)=0 .
$$

Prove that the set $M$ cannot fill out an entire interval. (This proposition admits a farreaching generalization.)\\

Formalization notes: -- We formalize: If f has a continuous derivative on an interval I (either finite or infinite),
-- then the set M = {f(x) | x ∈ I, f'(x) = 0} cannot contain a non-trivial open interval.
-- This captures the statement that "the set M cannot fill out an entire interval."
-/

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Instances.Real

-- Formalization notes: 
-- We formalize: If f has a continuous derivative on an interval I (either finite or infinite),
-- then the set M = {f(x) | x ∈ I, f'(x) = 0} cannot contain a non-trivial open interval.
-- This captures the statement that "the set M cannot fill out an entire interval."

theorem problem_125 (I : Set ℝ) (f : ℝ → ℝ) (hI : Convex ℝ I) 
    (hfd : DifferentiableOn ℝ f I) (hcont : ContinuousOn (deriv f) I) :
    ¬∃ (a b : ℝ), a < b ∧ Set.Ioo a b ⊆ {y | ∃ x ∈ I, f x = y ∧ deriv f x = 0} := by
  sorry

-- Proof attempt:
theorem problem_125 (I : Set ℝ) (f : ℝ → ℝ) (hI : Convex ℝ I) 
    (hfd : DifferentiableOn ℝ f I) (hcont : ContinuousOn (deriv f) I) :
    ¬∃ (a b : ℝ), a < b ∧ Set.Ioo a b ⊆ {y | ∃ x ∈ I, f x = y ∧ deriv f x = 0} := by
  intro ⟨a, b, hab, h⟩
  obtain ⟨c, hc⟩ : ∃ c ∈ Ioo a b, deriv f (Function.invFunOn f I c) = 0 := by
    have hsurj : Set.SurjOn f I (Ioo a b) := by
      intro y hy
      exact (h hy).imp fun x hx ↦ hx.1
    obtain ⟨c, hc⟩ : ∃ c ∈ Ioo a b, ∀ y ∈ Ioo a b, f (Function.invFunOn f I y) = c := by
      apply ConstantOn.exists_of_surjOn_connected hI.isPreconnected
      · exact isOpen_Ioo.connectedComponentIn hab.ne_empty
      · exact hsurj
      · intro x hx y hy
        obtain ⟨x', hx'⟩ := hsurj hy
        simp only [Function.invFunOn_eq hx'.1]
        exact hx'.2.2
    exact ⟨c, hc.1, by 
      obtain ⟨x, hx⟩ := hsurj hc.1
      have := hx.2.2
      rwa [Function.invFunOn_eq hx.1] at this⟩
  have hcI : Function.invFunOn f I c ∈ I := by
    obtain ⟨x, hx⟩ := h ⟨c, hc.1⟩
    exact hx.1
  have hderiv_eq : deriv f (Function.invFunOn f I c) = 0 := hc.2
  have hconst : ∀ x ∈ I, f x = c := by
    intro x hx
    have : ∀ x ∈ I, deriv f x = 0 := by
      intro x hx
      have : f x ∈ Ioo a b := by
        have := h ⟨f x, ⟨x, hx, rfl, this⟩⟩
        exact this
      obtain ⟨x', hx'⟩ := h ⟨f x, this⟩
      have hx'' := hx'.2.2
      rw [hx'.2.1] at hx''
      exact hx''
    have := Convex.norm_image_sub_le_of_norm_deriv_le hI hfd (fun x hx ↦ by rw [this x hx]; norm_num) hx hcI
    simp only [sub_self, norm_zero, zero_mul, norm_le_zero_iff] at this
    exact this
  have : ∃ y ∈ Ioo a b, y ≠ c := by
    obtain ⟨y, hy⟩ : ∃ y ∈ Ioo a b, y < c := exists_lt_of_lt hab.2 hc.1.2
    exact ⟨y, hy.1, hy.2.ne⟩
  obtain ⟨y, hy, hyne⟩ := this
  obtain ⟨x, hx⟩ := h ⟨y, hy⟩
  have : f x = c := hconst x hx.1
  linarith [hx.2.1]