/-
Polya-Szego Problem 18.1
Part One, Chapter 1

Original problem:
The first and the third problem considered in the solution of $\mathbf{9}$ (concerned with $A_{n}$ and $C_{n}$ respectively) are the extreme cases of a common generalization which, properly extended, includes also 18. Formulate such a generalization.\\

Formalization notes: -- We formalize the generating function identity for the number of solutions to
-- a bounded linear Diophantine equation ∑_{i=1}^l a_i x_i = n with 0 ≤ x_i ≤ p_i
-- The theorem states that the generating function ∑_{n=0}^∞ E_n x^n equals
-- ∏_{i=1}^l (1 - x^{a_i(p_i+1)})/(1 - x^{a_i}) as formal power series
-- We use Finsupp to represent solutions and formal power series
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Finsupp.Interval
import Mathlib.Data.Polynomial.Basic
import Mathlib.Data.Polynomial.AlgebraMap
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial
import Mathlib.Analysis.SpecialFunctions.Pow.Real

-- Formalization notes:
-- We formalize the generating function identity for the number of solutions to
-- a bounded linear Diophantine equation ∑_{i=1}^l a_i x_i = n with 0 ≤ x_i ≤ p_i
-- The theorem states that the generating function ∑_{n=0}^∞ E_n x^n equals
-- ∏_{i=1}^l (1 - x^{a_i(p_i+1)})/(1 - x^{a_i}) as formal power series
-- We use Finsupp to represent solutions and formal power series

open Polynomial
open Finsupp
open BigOperators

theorem problem_18_1_generating_function (l : ℕ) (a : Fin l → ℕ) (p : Fin l → ℕ) :
    let E (n : ℕ) : ℕ := 
      ((Finset.Icc 0).pi fun i => Finset.Icc 0 (p i)).filter 
        (fun x : Fin l → ℕ => ∑ i, a i * x i = n) |>.card
    in 
    (PowerSeries.mk fun n => (E n : ℂ)) = 
      ∏ i : Fin l, (1 - (PowerSeries.X : ℂ⟦X⟧) ^ ((a i) * (p i + 1))) / 
                   (1 - (PowerSeries.X : ℂ⟦X⟧) ^ (a i)) := by
  sorry

-- Proof attempt:
theorem problem_18_1_generating_function (l : ℕ) (a : Fin l → ℕ) (p : Fin l → ℕ) :
    let E (n : ℕ) : ℕ := 
      ((Finset.Icc 0).pi fun i => Finset.Icc 0 (p i)).filter 
        (fun x : Fin l → ℕ => ∑ i, a i * x i = n) |>.card
    in 
    (PowerSeries.mk fun n => (E n : ℂ)) = 
      ∏ i : Fin l, (1 - (PowerSeries.X : ℂ⟦X⟧) ^ ((a i) * (p i + 1))) / 
                   (1 - (PowerSeries.X : ℂ⟦X⟧) ^ (a i)) := by
  simp only [PowerSeries.ext_iff, PowerSeries.coeff_mk, PowerSeries.coeff_prod, 
    PowerSeries.coeff_div, PowerSeries.coeff_one, PowerSeries.coeff_X_pow]
  intro n
  let S := (Finset.Icc 0).pi fun i => Finset.Icc 0 (p i)
  have : ∀ (x : Fin l → ℕ), x ∈ S ↔ ∀ i, x i ∈ Finset.Icc 0 (p i) := by simp [S]
  simp only [this]
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  simp only [Nat.cast_sum, Nat.cast_one, Finset.sum_pi']
  have : ∀ x : Fin l → ℕ, (∀ i, x i ∈ Finset.Icc 0 (p i)) → 
    (if ∑ i, a i * x i = n then 1 else 0 : ℂ) = 
    ∏ i, if x i ≤ p i then (PowerSeries.X ^ (a i * x i) : ℂ⟦X⟧).coeff n else 0 := by
    intro x hx
    simp only [Finset.mem_Icc, forall_and] at hx
    simp only [hx.1, hx.2, ite_true]
    rw [PowerSeries.coeff_prod]
    simp only [PowerSeries.coeff_X_pow]
    split_ifs with h
    · have : ∀ i, a i * x i = (if ∑ i, a i * x i = n then a i * x i else 0) := by
        simp [h]
      simp [this, Finsupp.single_eq_same]
    · simp [Finsupp.single_eq_of_ne]
      intro i hi
      have : ∑ j, a j * x j = a i * x i + ∑ j in Finset.univ.erase i, a j * x j := by
        rw [Finset.sum_erase_eq_add i hi]
      rw [this] at h
      intro h'
      apply h
      rw [h', add_zero]
  simp [this]
  rw [Finset.sum_pi']
  simp only [Finset.sum_comm]
  congr
  ext i
  simp only [Finset.sum_apply]
  rw [Finset.sum_ite]
  simp only [Finset.sum_const, Finset.card_Icc, Nat.card_eq_fintype_card, Fintype.card_fin,
    Finset.sum_const_nat]
  simp only [Nat.cast_add, Nat.cast_one]
  rw [← PowerSeries.coeff_prod]
  simp only [PowerSeries.coeff_prod, PowerSeries.coeff_div, PowerSeries.coeff_one, 
    PowerSeries.coeff_X_pow]
  simp only [Finset.prod_ite_eq]
  have : ∀ (x : ℕ), x ∈ Finset.Icc 0 (p i) → 
    (if x ≤ p i then (PowerSeries.X ^ (a i * x) : ℂ⟦X⟧).coeff n else 0) = 
    (if a i * x = n then 1 else 0 : ℂ) := by
    intro x hx
    simp only [Finset.mem_Icc] at hx
    simp only [hx.2, ite_true, PowerSeries.coeff_X_pow]
  simp [this]
  rw [Finset.sum_ite]
  simp only [Finset.sum_const, Finset.card_Icc, Nat.card_eq_fintype_card, Fintype.card_fin,
    Finset.sum_const_nat]
  simp only [Nat.cast_add, Nat.cast_one]
  rw [← geom_sum_X_pow_eq_div (a i) (a i * (p i + 1)) n]
  simp only [PowerSeries.coeff_prod, PowerSeries.coeff_div, PowerSeries.coeff_one, 
    PowerSeries.coeff_X_pow]
  simp only [Finset.prod_ite_eq]
  simp only [PowerSeries.coeff_geom_series]
  simp only [ite_mul, zero_mul, mul_ite, mul_zero]
  simp only [Finset.sum_ite_eq]
  simp only [Finset.mem_range, ite_eq_left_iff]
  intro h
  simp [h]