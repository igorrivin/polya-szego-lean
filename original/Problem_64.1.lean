/-
Polya-Szego Problem 64.1
Part One, Chapter 1

Original problem:
Let $z_{1}, z_{2}, \ldots, z_{n}$ denote the zeros of the polynomial $z^{n}+a_{1} z^{n-1}+a_{2} z^{n-2}+\cdots+a_{n}$ and define

$$
s_{k}=z_{1}^{k}+z_{2}^{k}+\cdots+z_{n}^{k}
$$

Formalization notes: -- We formalize: For a monic polynomial p(z) = z^n + a₁z^{n-1} + ... + a_n with complex roots z₁,...,zₙ,
-- if the power sums s_k = ∑_{i=1}^n z_i^k satisfy |s_k| ≤ 1 for all 1 ≤ k ≤ n,
-- then |a_k| ≤ 1 for all 1 ≤ k ≤ n.
-- This captures the main conclusion from the problem statement.
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Polynomial.RingDivision
import Mathlib.Data.Polynomial.Identities
import Mathlib.Data.Finset.Basic

-- Formalization notes:
-- We formalize: For a monic polynomial p(z) = z^n + a₁z^{n-1} + ... + a_n with complex roots z₁,...,zₙ,
-- if the power sums s_k = ∑_{i=1}^n z_i^k satisfy |s_k| ≤ 1 for all 1 ≤ k ≤ n,
-- then |a_k| ≤ 1 for all 1 ≤ k ≤ n.
-- This captures the main conclusion from the problem statement.

theorem problem_64_1 (n : ℕ) (hn : n > 0) (p : ℂ[X]) (hp : p.Monic) (hp_deg : p.natDegree = n) :
    (∀ (k : ℕ), 1 ≤ k → k ≤ n → Complex.abs (∑ i in (p.roots.toFinset : Finset ℂ), (i : ℂ) ^ k) ≤ 1) →
    ∀ (k : ℕ), 1 ≤ k → k ≤ n → Complex.abs (p.coeff (n - k)) ≤ 1 := by
  sorry

-- Proof attempt:
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Polynomial.RingDivision
import Mathlib.Data.Polynomial.Identities
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Polynomial.Expand
import Mathlib.RingTheory.PowerSum.Basic

open Polynomial Complex

theorem problem_64_1 (n : ℕ) (hn : n > 0) (p : ℂ[X]) (hp : p.Monic) (hp_deg : p.natDegree = n) :
    (∀ (k : ℕ), 1 ≤ k → k ≤ n → Complex.abs (∑ i in (p.roots.toFinset : Finset ℂ), (i : ℂ) ^ k) ≤ 1) →
    ∀ (k : ℕ), 1 ≤ k → k ≤ n → Complex.abs (p.coeff (n - k)) ≤ 1 := by
  intro h_s k hk1 hkn
  let roots := p.roots.toFinset
  have h_roots : roots.card = n := by
    rw [← hp_deg, ← hp.roots_count, ← Multiset.toFinset_val, card_toFinset, count_roots]
    exact hp.ne_zero
  
  -- Express coefficients in terms of elementary symmetric polynomials
  have h_coeff : p.coeff (n - k) = (-1)^k * (∑ t in powersetLen k roots, ∏ x in t, x) := by
    rw [hp.coeff_eq_esymm_roots_of_card _ h_roots]
    rw [hp_deg]
    omega
  
  -- Relate power sums to elementary symmetric polynomials via Newton's identities
  have h_newton : ∀ m ≤ n, m ≠ 0 → 
      m * (-1)^m * (∑ t in powersetLen m roots, ∏ x in t, x) = 
      ∑ i in Finset.range m, (-1)^i * (∑ t in powersetLen i roots, ∏ x in t, x) * 
      (∑ z in roots, z^(m - i)) := by
    intro m hm hmnz
    convert NewtonIdentities m roots hmnz using 1
    · simp [h_roots]
    · simp [h_roots]
  
  -- Prove the bound by induction on k
  induction' k using Nat.strong_induction_on with k ih
  rw [h_coeff]
  cases' k with k
  · cases hk1
  · have hk_le_n : k.succ ≤ n := hkn
    have h_newton_k := h_newton k.succ hk_le_n (by simp)
    rw [mul_comm] at h_newton_k
    have h_sum_bounded : ∀ i < k.succ, Complex.abs (∑ z in roots, z ^ (k.succ - i)) ≤ 1 := by
      intro i hi
      apply h_s (k.succ - i)
      · omega
      · omega
    have h_ih : ∀ i < k.succ, Complex.abs ((-1)^i * (∑ t in powersetLen i roots, ∏ x in t, x)) ≤ 1 := by
      intro i hi
      rw [Complex.abs_mul, Complex.abs_neg_one_pow, one_mul]
      apply ih i hi
      · omega
      · exact Nat.le_trans (Nat.le_of_lt hi) hk_le_n
    rw [← Complex.abs_mul, ← h_newton_k]
    have h_div : Complex.abs (k.succ * (-1)^k.succ * (∑ t in powersetLen k.succ roots, ∏ x in t, x)) / k.succ ≤ 1 := by
      rw [← Complex.abs_div]
      apply le_trans (div_le_of_nonneg_of_le_mul (by norm_cast; exact Nat.pos_of_ne_zero (by omega)) 
        (Complex.abs.nonneg _) _)
      · rw [mul_comm]
        refine le_trans (Complex.abs_sum _ _) ?_
        apply Finset.sum_le_sum
        intro i hi
        rw [Finset.mem_range] at hi
        rw [Complex.abs_mul, Complex.abs_neg_one_pow, one_mul]
        exact mul_le_of_le_one_left (Complex.abs.nonneg _) (h_sum_bounded i hi) (h_ih i hi)
      · norm_cast
    rwa [mul_div_cancel_left] at h_div
    norm_cast
    exact Nat.pos_of_ne_zero (by omega)