/-
Polya-Szego Problem 162
Part One, Chapter 4

Original problem:
A sequence $x_{1}, x_{2}, x_{3}, \ldots, x_{n}, \ldots, 0 \leqq x_{n} \leqq 1$, is equidistributed on $[0,1]$ if and only if the "probability" of a term $x_{n}$ to fall into a certain subinterval of $[0,1]$ is equal to the length of that subinterval. More precisely, if the sequence has the following property: Let $[\alpha, \beta]$ be an arbitrary subinterval of $[0,1]$ and $v_{n}(\alpha, \beta)$ denote the number of $x_{v}$ 's, $v=1,2, \ldots, n$, on $[\alpha, \beta]$, then


\begin{equation*}
\

Formalization notes: -- We formalize several equivalent characterizations of equidistributed sequences on [0,1]
-- 1. The basic definition using counting measure (v_n(α,β)/n → β-α)
-- 2. The characterization using sums of elements in subintervals (s_n(α,β)/n → (β²-α²)/2)
-- 3. The Weyl criterion using moments (average of x^k → 1/(k+1))
-- 4. The Weyl criterion using trigonometric functions (average of cos/sin 2πkx → 0)
-- 5. The specific example of fractional parts of multiples of an irrational
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Intervals.Basic
import Mathlib.Topology.Instances.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Fourier.AddCircle

-- Formalization notes:
-- We formalize several equivalent characterizations of equidistributed sequences on [0,1]
-- 1. The basic definition using counting measure (v_n(α,β)/n → β-α)
-- 2. The characterization using sums of elements in subintervals (s_n(α,β)/n → (β²-α²)/2)
-- 3. The Weyl criterion using moments (average of x^k → 1/(k+1))
-- 4. The Weyl criterion using trigonometric functions (average of cos/sin 2πkx → 0)
-- 5. The specific example of fractional parts of multiples of an irrational

-- We'll use `ℕ → ℝ` to represent sequences
-- For the counting function, we use Finset.card with a filter

open Set
open Filter
open Finset
open BigOperators

-- First, define the basic notion of equidistribution
def equidistributed (x : ℕ → ℝ) : Prop :=
  ∀ (α β : ℝ) (hα : 0 ≤ α) (hβ : β ≤ 1) (h : α ≤ β),
    Tendsto (λ n : ℕ ↦ ((Finset.range n).filter (λ v ↦ α ≤ x v ∧ x v ≤ β)).card / (n : ℝ))
      atTop (𝓝 (β - α))

-- Problem 162: Equidistribution via sums in subintervals
theorem problem_162_equivalence (x : ℕ → ℝ) (hx : ∀ n, 0 ≤ x n ∧ x n ≤ 1) :
    equidistributed x ↔
    ∀ (α β : ℝ) (hα : 0 ≤ α) (hβ : β ≤ 1) (h : α ≤ β),
      Tendsto (λ n : ℕ ↦ 
        ((Finset.range n).filter (λ v ↦ α ≤ x v ∧ x v ≤ β)).sum x / (n : ℝ))
        atTop (𝓝 ((β^2 - α^2) / 2)) := by
  sorry

-- Problem 163: Weyl's criterion using moments
theorem problem_163_weyl_moments (x : ℕ → ℝ) (hx : ∀ n, 0 ≤ x n ∧ x n ≤ 1) :
    equidistributed x ↔
    ∀ (k : ℕ) (hk : k > 0),
      Tendsto (λ n : ℕ ↦ ((Finset.range n).sum (λ i ↦ (x i) ^ (k : ℕ))) / (n : ℝ))
        atTop (𝓝 (1 / ((k : ℝ) + 1))) := by
  sorry

-- Problem 164: Weyl's criterion using trigonometric functions
theorem problem_164_weyl_trigonometric (x : ℕ → ℝ) (hx : ∀ n, 0 ≤ x n ∧ x n ≤ 1) :
    equidistributed x ↔
    ∀ (k : ℕ) (hk : k > 0),
      (Tendsto (λ n : ℕ ↦ ((Finset.range n).sum (λ i ↦ Real.cos (2 * π * k * x i))) / (n : ℝ))
          atTop (𝓝 0)) ∧
      (Tendsto (λ n : ℕ ↦ ((Finset.range n).sum (λ i ↦ Real.sin (2 * π * k * x i))) / (n : ℝ))
          atTop (𝓝 0)) := by
  sorry

-- Problem 165: Fractional parts of multiples of an irrational are equidistributed
theorem problem_165_irrational_rotation (θ : ℝ) (hθ : Irrational θ) :
    let x : ℕ → ℝ := λ n ↦ θ * n - ⌊θ * n⌋
    equidistributed x := by
  intro x
  sorry

-- Proof attempt:
theorem problem_162_equivalence (x : ℕ → ℝ) (hx : ∀ n, 0 ≤ x n ∧ x n ≤ 1) :
    equidistributed x ↔
    ∀ (α β : ℝ) (hα : 0 ≤ α) (hβ : β ≤ 1) (h : α ≤ β),
      Tendsto (λ n : ℕ ↦ 
        ((Finset.range n).filter (λ v ↦ α ≤ x v ∧ x v ≤ β)).sum x / (n : ℝ))
        atTop (𝓝 ((β^2 - α^2) / 2)) := by
  constructor
  · intro h_eq α β hα hβ h_le
    have h_int : ∀ y ∈ Icc α β, y = α + ∫ t in α..y, 1 := by
      intro y hy
      simp [integral_const, sub_eq_add_neg, neg_add_eq_sub]
    have h_sum : ∀ n, ((Finset.range n).filter (λ v ↦ α ≤ x v ∧ x v ≤ β)).sum x = 
        ((Finset.range n).filter (λ v ↦ α ≤ x v ∧ x v ≤ β)).card * α +
        ((Finset.range n).filter (λ v ↦ α ≤ x v ∧ x v ≤ β)).sum (λ v ↦ ∫ t in α..x v, 1) := by
      intro n
      simp_rw [h_int _ (⟨(hx _).1, (hx _).2⟩)]
      rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
    simp_rw [h_sum, add_div, mul_div_assoc]
    apply Tendsto.add
    · have := h_eq α β hα hβ h_le
      simp_rw [mul_comm _ (α : ℝ)]
      exact this.const_mul α
    · have h_int' : ∀ v, α ≤ x v ∧ x v ≤ β → ∫ t in α..x v, 1 = x v - α := by
        intro v hv
        simp [integral_const, hv.2, hv.1]
      simp_rw [h_int']
      rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
      simp_rw [mul_comm _ (α : ℝ), ← sub_eq_add_neg, ← mul_sub]
      have := h_eq α β hα hβ h_le
      simp_rw [mul_comm _ ((β^2 - α^2)/2 - α*(β - α))]
      refine Tendsto.congr' ?_ (this.const_mul ((β^2 - α^2)/2 - α*(β - α)))
      simp [sq, ← mul_sub, sub_mul, mul_comm β, ← add_sub_assoc, ← sub_add, 
            ← mul_add, field_simps]
      ring
  · intro h_sum α β hα hβ h_le
    have h_sum' := h_sum 0 β hα hβ (hα.trans h_le)
    have h_sum'' := h_sum α 1 hα hβ h_le
    have h_sum''' := h_sum α β hα hβ h_le
    sorry -- The reverse direction is more involved and would require additional lemmas