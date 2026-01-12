/-
Polya-Szego Problem 98
Part One, Chapter 2

Original problem:
We define

$$
g(x)=\sin ^{2},
$$

and

Is $G(x)$ integrable ?\\

Formalization notes: We formalize the statement that the Dirichlet function (0 on rationals, 1 on irrationals)
is not Riemann integrable on any non-degenerate interval [a, b] with a < b.
-/

import Mathlib.Analysis.Calculus.Integral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Data.Real.Irrational

/-!
Formalization notes:
We formalize the statement that the Dirichlet function (0 on rationals, 1 on irrationals)
is not Riemann integrable on any non-degenerate interval [a, b] with a < b.

The function is defined as:
  G(x) = 0 if x is rational, 1 if x is irrational

We use `RiemannIntegrable` from Mathlib which requires the function to be bounded and
the lower and upper Riemann integrals to be equal.

The theorem states: For any real numbers a < b, the function G is not Riemann integrable on [a, b].
-/

open Set
open scoped Real

noncomputable section

/-- The Dirichlet function: 0 on rationals, 1 on irrationals -/
def dirichlet (x : ℝ) : ℝ := if (h : Irrational x) then 1 else 0

theorem problem_98 : ∀ (a b : ℝ), a < b → ¬RiemannIntegrable (dirichlet : ℝ → ℝ) (Set.uIcc a b) := by
  sorry

-- Proof attempt:
theorem problem_98 : ∀ (a b : ℝ), a < b → ¬RiemannIntegrable (dirichlet : ℝ → ℝ) (Set.uIcc a b) := by
  intro a b hlt
  rw [RiemannIntegrable]
  push_neg
  constructor
  · -- The function is bounded
    use 1
    intro x _
    simp [dirichlet]
    split_ifs <;> linarith
  · -- Lower and upper integrals are not equal
    have h1 : LowerIntegral (dirichlet : ℝ → ℝ) (uIcc a b) = 0 := by
      apply le_antisymm
      · apply LowerIntegral_le_upper (fun x _ => _)
        simp [dirichlet]
        split_ifs <;> linarith
      · apply le_of_forall_le_of_dense
        intro ε hε
        use const (uIcc a b) 0
        constructor
        · intro x hx
          simp [dirichlet]
          split_ifs <;> linarith
        · simp [integral_const]
          linarith
    have h2 : UpperIntegral (dirichlet : ℝ → ℝ) (uIcc a b) = b - a := by
      apply le_antisymm
      · apply le_of_forall_le_of_dense
        intro ε hε
        obtain ⟨q, hq⟩ := exists_irrational_between hlt
        let π := @Irrational.instNonemptySubtype
        use indicator (uIcc a b) (fun _ => 1) (by simp)
        constructor
        · intro x hx
          simp [dirichlet]
          split_ifs
          · simp
          · simp
        · simp [integral_indicator, indicator, Pi.one_apply, volume_Icc]
          rw [Real.volume_Icc]
          simp [hlt.le]
          linarith
      · apply UpperIntegral_le_LowerIntegral_add_const (fun x _ => _) hε
        simp [dirichlet]
        split_ifs <;> linarith
    rw [h1, h2]
    intro heq
    have : b - a = 0 := by linarith
    linarith [sub_pos.mpr hlt]