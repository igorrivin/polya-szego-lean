/-
Polya-Szego Problem 297
Part Three, Chapter 6

Original problem:
We assume that the function $f(z)$ is regular and bounded in the disk $|z|<1$ and vanishes at the points $z_{1}, z_{2}, z_{3}, \ldots$ Then

$$
\left(1-\left|z_{1}\right|\right)+\left(1-\left|z_{2}\right|\right)+\left(1-\left|z_{3}\right|\right)+\cdots
$$

(the sum of the distances of the zeros from the unit circle) is finite or else $f(z) \equiv 0$.\\

Formalization notes: -- We formalize the statement: If f is holomorphic and bounded on the open unit disk,
-- and has zeros at a sequence of points z_n with |z_n| < 1, then either
-- ∑ (1 - |z_n|) converges or f is identically zero.
-- We assume the zeros are listed with multiplicity and are distinct in the sequence.
-- The theorem is known as the Blaschke condition for bounded analytic functions.
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.SpecialFunctions.Complex.Log

-- Formalization notes:
-- We formalize the statement: If f is holomorphic and bounded on the open unit disk,
-- and has zeros at a sequence of points z_n with |z_n| < 1, then either
-- ∑ (1 - |z_n|) converges or f is identically zero.
-- We assume the zeros are listed with multiplicity and are distinct in the sequence.
-- The theorem is known as the Blaschke condition for bounded analytic functions.

open Complex
open Metric
open Set
open Filter

theorem problem_297 (f : ℂ → ℂ) (hhol : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (hbdd : ∃ M : ℝ, ∀ z ∈ ball (0 : ℂ) 1, ‖f z‖ ≤ M) 
    (zeros : ℕ → ℂ) (hzeros : ∀ n, zeros n ∈ ball (0 : ℂ) 1 ∧ f (zeros n) = 0) 
    (hinj : Function.Injective zeros) :
    (Summable fun n : ℕ => 1 - ‖zeros n‖) ∨ ∀ z ∈ ball (0 : ℂ) 1, f z = 0 := by
  sorry

-- Proof attempt:
theorem problem_297 (f : ℂ → ℂ) (hhol : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (hbdd : ∃ M : ℝ, ∀ z ∈ ball (0 : ℂ) 1, ‖f z‖ ≤ M) 
    (zeros : ℕ → ℂ) (hzeros : ∀ n, zeros n ∈ ball (0 : ℂ) 1 ∧ f (zeros n) = 0) 
    (hinj : Function.Injective zeros) :
    (Summable fun n : ℕ => 1 - ‖zeros n‖) ∨ ∀ z ∈ ball (0 : ℂ) 1, f z = 0 := by
  by_cases h : ∀ z ∈ ball (0 : ℂ) 1, f z = 0
  · exact Or.inr h
  · push_neg at h
    obtain ⟨z₀, hz₀, hf⟩ := h
    refine Or.inl ?_
    -- Apply Blaschke condition
    have hM : ∃ M, 0 < M ∧ ∀ z ∈ ball (0 : ℂ) 1, ‖f z‖ ≤ M := by
      obtain ⟨M, hM⟩ := hbdd
      refine ⟨max M 1, by linarith, fun z hz => ?_⟩
      exact (hM z hz).trans (le_max_left _ _)
    obtain ⟨M, hMpos, hM⟩ := hM
    have hf_ne : f z₀ ≠ 0 := hf
    have h_blaschke := Complex.exists_blaschke_product_of_bounded_holomorphic
      f hhol hM zeros hzeros hinj z₀ hz₀ hf_ne
    obtain ⟨B, hB⟩ := h_blaschke
    -- The Blaschke product condition gives summability
    have h_sum : Summable fun n => 1 - ‖zeros n‖ := by
      refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hB.summable
      · simp only [sub_nonneg]
        exact norm_le_one_of_mem_ball (hzeros n).1
      · simp only [norm_smul, norm_eq_abs, abs_ofReal, Real.abs_one, mul_one]
        rw [← sub_le_sub_iff_right 1]
        refine (abs_sub_abs_le_abs_sub _ _).trans ?_
        simp only [map_sub, map_one, abs_one, abs_norm]
        exact le_of_eq (by ring)
    exact h_sum