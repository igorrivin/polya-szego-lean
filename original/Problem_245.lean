/-
Polya-Szego Problem 245
Part Three, Chapter 5

Original problem:
We assume that the coefficients $a_{0}, a_{1}, \ldots, a_{n}, \ldots$ of the power series $a_{0}+a_{1} z+\cdots+a_{n} z^{n}+\cdots$ are real and that $\varrho e^{i, \Sigma}$ and $\varrho e^{-i, \Sigma}$ are poles and the only singularities on the circle of convergence, $0<\alpha<\pi$. We call $V_{n}$ the number of changes of sign in the sequence $a_{0}, a_{1}, \ldots, a_{n-1}, a_{n}$. Then

$$
\lim _{n \rightarrow \infty} \frac{V_{n}}{n}=\frac{\alpha}{\pi} .
$$

[VIII 14.]\\

Formalization notes: We formalize the asymptotic result about the proportion of sign changes in the coefficients
of a power series with specific singularities on its circle of convergence.
-/

import Mathlib.Analysis.Complex.PowerSeries
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Sign

/-!
## Formalization notes:

We formalize the asymptotic result about the proportion of sign changes in the coefficients
of a power series with specific singularities on its circle of convergence.

Given:
1. A power series f(z) = ∑_{n=0}^∞ a_n z^n with real coefficients a_n
2. The circle of convergence has radius ρ > 0
3. The only singularities on the circle are at z = ρe^{iα} and z = ρe^{-iα} (poles)
4. 0 < α < π
5. V_n = number of sign changes in the sequence a_0, a_1, ..., a_n

Then: lim_{n→∞} V_n / n = α/π

We formalize this as a theorem about sequences satisfying the asymptotic form
from the solution: a_n = A n^{k-1} ρ^{-n} (sin(nα + δ) + ε_n) where ε_n → 0.

Note: We don't formalize the full power series structure, but rather the asymptotic
behavior that implies the limit about sign changes.
-/

open Filter Real
open scoped Topology

/-- Count sign changes in a finite sequence of real numbers.
    A sign change occurs between a_i and a_{i+1} when they have opposite signs
    and neither is zero. -/
def signChanges (seq : ℕ → ℝ) (n : ℕ) : ℕ :=
  ((Finset.range n).filter fun i =>
    (seq i > 0 ∧ seq (i + 1) < 0) ∨ (seq i < 0 ∧ seq (i + 1) > 0)).card

theorem problem_245_asymptotic (ρ : ℝ) (hρ : ρ > 0) (α : ℝ) (hα : 0 < α) (hα' : α < π)
    (A : ℝ) (hA : A > 0) (k : ℕ) (δ : ℝ) (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (a : ℕ → ℝ) (has_form : ∀ n, a n = A * (n : ℝ) ^ (k : ℝ)⁻¹ * (ρ : ℝ) ^ (-(n : ℝ)) 
      * (Real.sin (n * α + δ) + ε n)) :
    Tendsto (λ n : ℕ => (signChanges a n : ℝ) / n) atTop (𝓝 (α / π)) := by
  sorry

-- Proof attempt:
theorem problem_245_asymptotic (ρ : ℝ) (hρ : ρ > 0) (α : ℝ) (hα : 0 < α) (hα' : α < π)
    (A : ℝ) (hA : A > 0) (k : ℕ) (δ : ℝ) (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (a : ℕ → ℝ) (has_form : ∀ n, a n = A * (n : ℝ) ^ (k : ℝ)⁻¹ * (ρ : ℝ) ^ (-(n : ℝ)) 
      * (Real.sin (n * α + δ) + ε n)) :
    Tendsto (λ n : ℕ => (signChanges a n : ℝ) / n) atTop (𝓝 (α / π)) := by
  -- First, simplify the asymptotic form
  have main_term : ∀ n, a n = A * (n : ℝ) ^ (k : ℝ)⁻¹ * ρ ^ (-n) * (sin (n * α + δ) + ε n) := by
    intro n; exact has_form n
  clear has_form

  -- The key observation is that for large n, the sign of a_n is determined by sin(nα + δ)
  -- since ε_n → 0 and the other factors are positive
  have eventually_sign_determined : ∀ᶠ n in atTop,
      (a n > 0 ↔ sin (n * α + δ) > 0) ∧ (a n < 0 ↔ sin (n * α + δ) < 0) := by
    refine eventually_of_mem (hε (Ioo (-sin (α/2)) (sin (α/2))) (isOpen_Ioo.mem_nhds ?_)) ?_
    · have : 0 ∈ Ioo (-sin (α/2)) (sin (α/2)) := by
        simp only [mem_Ioo, neg_lt_zero, lt_self_iff_false, and_false]
        exact sin_pos_of_pos_of_lt_pi (half_pos hα) (half_lt_self hα')
      exact this
    intro n hn
    have hsin : |ε n| < sin (α/2) := by
      rw [abs_lt]
      exact ⟨hn.1, hn.2⟩
    constructor
    · constructor
      · intro han
        have : sin (n * α + δ) + ε n > 0 := by
          rw [←main_term n] at han
          have := mul_pos hA (Real.rpow_pos_of_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (by omega))) _)
          have := mul_pos this (Real.rpow_pos_of_pos hρ _)
          exact (zero_lt_mul_right this).mp han
        linarith [abs_lt.mp hsin]
      · intro hsin_pos
        have := mul_pos hA (Real.rpow_pos_of_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (by omega))) _)
        have := mul_pos this (Real.rpow_pos_of_pos hρ _)
        apply (zero_lt_mul_right this).mpr
        rw [main_term]
        refine mul_pos (by linarith) ?_
        have : sin (n * α + δ) > -ε n := by linarith [abs_lt.mp hsin]
        linarith
    · constructor
      · intro han
        have : sin (n * α + δ) + ε n < 0 := by
          rw [←main_term n] at han
          have := mul_pos hA (Real.rpow_pos_of_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (by omega))) _)
          have := mul_pos this (Real.rpow_pos_of_pos hρ _)
          exact (mul_neg_iff_of_pos_right this).mp han
        linarith [abs_lt.mp hsin]
      · intro hsin_neg
        have := mul_pos hA (Real.rpow_pos_of_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (by omega))) _)
        have := mul_pos this (Real.rpow_pos_of_pos hρ _)
        apply (mul_neg_iff_of_pos_right this).mpr
        rw [main_term]
        refine mul_neg_of_pos_of_neg (by linarith) ?_
        have : sin (n * α + δ) < -ε n := by linarith [abs_lt.mp hsin]
        linarith

  -- Now count sign changes by counting zero crossings of sin(nα + δ)
  -- The number of sign changes is asymptotically equal to the number of times
  -- nα + δ crosses a multiple of π, which is α/π per unit n
  let f (n : ℕ) := n * α + δ
  let crosses := fun n => ∃ m : ℤ, f n < m * π ∧ m * π < f (n + 1)
  
  have sign_changes_eq_crosses : ∀ᶠ n in atTop,
      signChanges a n = ((Finset.range n).filter crosses).card := by
    refine eventually_of_mem (eventually_and.2 ⟨eventually_ge_atTop 1, eventually_sign_determined⟩) ?_
    intro n ⟨hn, hsign⟩
    simp only [signChanges]
    congr
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    rw [and_congr_right (fun hi => ?_)]
    constructor
    · intro h
      cases' h with h h
      · have : sin (f i) > 0 ∧ sin (f (i + 1)) < 0 := by
          rw [←hsign.1 i (by omega), ←hsign.2 (i + 1) (by omega)]
          exact h
        obtain ⟨m, hm⟩ := exists_int_gt (f i / π)
        refine ⟨m, ?_, ?_⟩
        · have := sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [hα'])
          linarith [this.1]
        · have := sin_neg_of_neg_of_lt_pi (by linarith) (by linarith [hα'])
          linarith [this.1]
      · have : sin (f i) < 0 ∧ sin (f (i + 1)) > 0 := by
          rw [←hsign.2 i (by omega), ←hsign.1 (i + 1) (by omega)]
          exact h
        obtain ⟨m, hm⟩ := exists_int_lt (f (i + 1) / π)
        refine ⟨m, ?_, ?_⟩
        · have := sin_neg_of_neg_of_lt_pi (by linarith) (by linarith [hα'])
          linarith [this.1]
        · have := sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [hα'])
          linarith [this.1]
    · intro ⟨m, hmn, hmn'⟩
      have : sin (f i) * sin (f (i + 1)) < 0 := by
        refine sin_mul_sin_lt_of_lt_of_lt_pi ?_ ?_
        · exact hmn
        · rw [add_assoc] at hmn'
          exact hmn'
      cases' lt_or_gt_of_ne (ne_of_lt this) with h h
      · left
        rw [hsign.1 i (by omega), hsign.2 (i + 1) (by omega)]
        exact ⟨h.1, h.2⟩
      · right
        rw [hsign.2 i (by omega), hsign.1 (i + 1) (by omega)]
        exact ⟨h.1, h.2⟩

  -- The number of crosses is asymptotically α/π * n
  have crosses_asymptotic : Tendsto (λ n => (((Finset.range n).filter crosses).card : ℝ) / n) atTop (𝓝 (α / π)) := by
    simp only [crosses]
    have : Tendsto (λ n => (α * n + δ) / π) atTop atTop := by
      refine tendsto_atTop_add_const_right _ (tendsto_const_mul_atTop (div_pos hα pi_pos) tendsto_cast_nat_atTop_atTop)
    have := tendsto_div_floor_mul_self_atTop this
    simp only [div_div, mul_comm (α / π)] at this
    exact this

  -- Combine to get the final result
  refine Tendsto.congr' ?_ crosses_asymptotic
  filter_upwards [sign_changes_eq_crosses] with n hn
  simp [hn]