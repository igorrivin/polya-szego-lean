/-
Polya-Szego Problem 39
Part Three, Chapter 1

Original problem:
Let $z_{1}, z_{2}, \ldots, z_{n}, \ldots$ be arbitrary complex numbers. If there exists a positive distance $\delta$ such that $\left|z_{l}-z_{k}\right| \geqq \delta$ for $l<k$, $l, k=1,2,3, \ldots$ the convergence exponent of the sequence $\left|z_{1}\right|,\left|z_{2}\right|,\left|z_{3}\right|, \ldots$ is at most 2. [I 114.$]$\\

Formalization notes: -- We formalize the statement about convergence exponents of sequences with uniformly separated terms.
-- The convergence exponent ρ of a sequence (|z_n|) is defined as:
--   ρ = inf {α > 0 : ∑_{n=1}^∞ 1/|z_n|^α < ∞}
-- The theorem states that if complex numbers z_n satisfy |z_l - z_k| ≥ δ > 0 for all l < k,
-- then the convergence exponent of (|z_n|) is at most 2.
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Pi
import Mathlib.Analysis.Calculus.Series

-- Formalization notes:
-- We formalize the statement about convergence exponents of sequences with uniformly separated terms.
-- The convergence exponent ρ of a sequence (|z_n|) is defined as:
--   ρ = inf {α > 0 : ∑_{n=1}^∞ 1/|z_n|^α < ∞}
-- The theorem states that if complex numbers z_n satisfy |z_l - z_k| ≥ δ > 0 for all l < k,
-- then the convergence exponent of (|z_n|) is at most 2.

-- We define the convergence exponent formally and state the theorem.
-- Note: We assume the sequence (z_n) is infinite and all z_n are nonzero for the convergence exponent to be defined.

open Complex Set Filter
open scoped Topology

noncomputable section

/-- The convergence exponent of a sequence of positive real numbers. -/
def convergenceExponent (a : ℕ → ℝ) (ha_pos : ∀ n, 0 < a n) : ℝ :=
  sInf {α : ℝ | 0 < α ∧ Summable fun n : ℕ => (a n) ^ (-α)}

theorem problem_39 {z : ℕ → ℂ} (h_sep : ∃ δ > 0, ∀ l k : ℕ, l < k → δ ≤ dist (z l) (z k))
    (h_nonzero : ∀ n, z n ≠ 0) : 
    let r : ℕ → ℝ := fun n => Complex.abs (z n)
    let ρ := convergenceExponent r (fun n => Complex.abs.pos (h_nonzero n))
    in ρ ≤ 2 := by
  sorry

-- Proof attempt:
theorem problem_39 {z : ℕ → ℂ} (h_sep : ∃ δ > 0, ∀ l k : ℕ, l < k → δ ≤ dist (z l) (z k))
    (h_nonzero : ∀ n, z n ≠ 0) : 
    let r : ℕ → ℝ := fun n => Complex.abs (z n)
    let ρ := convergenceExponent r (fun n => Complex.abs.pos (h_nonzero n))
    in ρ ≤ 2 := by
  intro r ρ
  obtain ⟨δ, hδ_pos, h_sep⟩ := h_sep
  simp [convergenceExponent]
  apply csInf_le
  · use 3
    constructor
    · norm_num
    · apply summable_of_isBigO_nat (summable_nat_add_iff 1).mpr
      have h_card : ∀ n, Nat.card {k | r k ≤ n} ≤ (4 * n / δ + 1) ^ 2 := by
        intro n
        let B := {w : ℂ | Complex.abs w ≤ n}
        have h_bounded : Metric.Bounded B := by
          apply Metric.bounded_le
          exact n
        have h_sep' : ∀ l k, l < k → δ ≤ dist (z l) (z k) := h_sep
        let S := {k | r k ≤ n}
        have : Set.Finite S := by
          apply Metric.finite_le_of_separated h_bounded hδ_pos h_sep'
          intro k hk
          exact hk
        refine le_trans (Nat.card_le_of_finite this) ?_
        have : Nat.card S ≤ (⌊4 * n / δ⌋ + 1) ^ 2 := by
          refine Complex.card_le_of_separated hδ_pos n ?_
          intro l k hlk
          exact h_sep l k hlk
        refine this.trans ?_
        ring_nf
        apply pow_le_pow_left
        · linarith
        · exact Nat.le_floor_add_one _
      apply Summable.of_norm_bounded_eventually _ (summable_one_div_nat_pow.mpr (by norm_num))
      apply eventually_atTop.mpr
      use 1
      intro n hn
      simp only [norm_eq_abs, abs_inv, Real.abs_pow, abs_ofReal, abs_natCast]
      rw [inv_pow, ← Real.rpow_natCast]
      have h_r_pos : ∀ k, 0 < r k := fun k => Complex.abs.pos (h_nonzero k)
      have h_r_ge_one : ∀ k ≥ 1, 1 ≤ r k := by
        intro k hk
        have := h_sep 0 k (by omega)
        rw [dist_eq_norm, norm_sub_rev] at this
        calc
          1 ≤ δ / Complex.abs (z 0) := by
            have hz0 := Complex.abs.pos (h_nonzero 0)
            refine le_div_of_mul_le hz0 ?_
            rw [one_mul]
            exact this.trans (norm_le_norm_add_norm _ _)
          _ ≤ Complex.abs (z k) / Complex.abs (z 0) := by
            apply div_le_div_of_le_left (Complex.abs.pos (h_nonzero k)) (Complex.abs.pos (h_nonzero 0))
            exact this
          _ ≤ Complex.abs (z k) := by
            apply div_le_self (Complex.abs.pos (h_nonzero k)) (Complex.abs.pos (h_nonzero 0)).le
      rw [Real.rpow_neg (h_r_pos n).le, inv_inv]
      refine le_trans ?_ (pow_le_pow_left (h_r_ge_one n hn) 2)
      exact one_le_pow_of_one_le (h_r_ge_one n hn) 2
  · apply Real.sInf_nonempty
    use 3
    constructor
    · norm_num
    · exact summable_one_div_nat_pow.mpr (by norm_num)