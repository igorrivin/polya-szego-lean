/-
Polya-Szego Problem 145
Part One, Chapter 4

Original problem:
If the series $a_{0}+a_{1}+a_{2}+\cdots, a_{n}$ real, $n=0,1,2, \ldots$, envelops the real number $A$ and if in addition $\left|a_{1}\right|>\left|a_{2}\right|>\left|a_{3}\right|>\cdots$

\footnotetext{${ }^{1}$ Obviously only the non-vanishing terms of the Maclaurin series are to be considered. E.g. the $n$-th partial sum of the Maclaurin series for $\cos x$ is

$$
1-\frac{x^{2}}{2!}+\frac{x^{4}}{4!}-\cdots+(-1)^{n} \frac{x^{2 n}}{(2 n)!}, \quad n=0,1,2, \ldots
$$
}
$$
n=0,1,2, \ldots
$$
then t

Formalization notes: -- We formalize the concept of a series "enveloping" a real number A.
-- A series ∑ a_n "envelops" A if the sequence of partial sums s_n = ∑_{k=0}^n a_k
-- satisfies: s_{2n} ≤ A ≤ s_{2n+1} for all n (or vice versa).
-- "Enveloped in the strict sense" means the inequalities are strict when |a_{n+1}| > 0.
-- The condition |a_1| > |a_2| > |a_3| > ... implies terms are nonzero after some point.
-/

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Real.Basic

-- Formalization notes: 
-- We formalize the concept of a series "enveloping" a real number A.
-- A series ∑ a_n "envelops" A if the sequence of partial sums s_n = ∑_{k=0}^n a_k
-- satisfies: s_{2n} ≤ A ≤ s_{2n+1} for all n (or vice versa).
-- "Enveloped in the strict sense" means the inequalities are strict when |a_{n+1}| > 0.
-- The condition |a_1| > |a_2| > |a_3| > ... implies terms are nonzero after some point.

theorem problem_145 {a : ℕ → ℝ} (A : ℝ) 
    -- The series envelops A: partial sums alternate around A
    (h_envelop : ∀ n, let s_n := ∑ k in Finset.range (2*n), a k
                     let s_n1 := s_n + a (2*n) in
                     s_n ≤ A ∧ A ≤ s_n1) 
    -- Absolute values strictly decrease
    (h_decreasing : ∀ n : ℕ, |a (n+1)| < |a n|) 
    -- First term is nonzero (to ensure meaningful alternation)
    (h_a0_ne_zero : a 0 ≠ 0) :
    -- Then: (1) Terms alternate in sign
    (∀ n, a n * a (n+1) < 0) ∧
    -- (2) A is strictly enveloped (partial sums strictly alternate around A)
    (∀ n, let s_n := ∑ k in Finset.range (2*n), a k
          let s_n1 := s_n + a (2*n) in
          s_n < A ∧ A < s_n1) := by
  sorry

-- Proof attempt:
theorem problem_145 {a : ℕ → ℝ} (A : ℝ) 
    (h_envelop : ∀ n, let s_n := ∑ k in Finset.range (2*n), a k
                     let s_n1 := s_n + a (2*n) in
                     s_n ≤ A ∧ A ≤ s_n1) 
    (h_decreasing : ∀ n : ℕ, |a (n+1)| < |a n|) 
    (h_a0_ne_zero : a 0 ≠ 0) :
    (∀ n, a n * a (n+1) < 0) ∧
    (∀ n, let s_n := ∑ k in Finset.range (2*n), a k
          let s_n1 := s_n + a (2*n) in
          s_n < A ∧ A < s_n1) := by
  constructor
  · -- Part 1: Prove terms alternate in sign
    intro n
    have h_abs : |a (n+1)| < |a n| := h_decreasing n
    have h_a0_pos : |a 0| > 0 := by simp [abs_pos.mpr h_a0_ne_zero]
    -- First show all terms are nonzero
    have h_a_ne_zero : ∀ n, a n ≠ 0 := by
      intro k
      induction k with
      | zero => exact h_a0_ne_zero
      | succ k ih =>
        apply abs_pos.mp
        apply lt_of_lt_of_le (h_decreasing k)
        exact abs_nonneg (a k)
    -- Now prove alternation
    cases' lt_or_gt_of_ne (h_a_ne_zero n) with hn_pos hn_neg
    · have : a (n+1) < 0 := by
        have := h_decreasing n
        rw [abs_of_pos hn_pos] at this
        rw [abs_lt] at this
        exact this.2
      exact mul_neg_of_pos_of_neg hn_pos this
    · have : a (n+1) > 0 := by
        have := h_decreasing n
        rw [abs_of_neg hn_neg] at this
        rw [abs_lt] at this
        exact this.1
      exact mul_neg_of_neg_of_pos hn_neg this
  · -- Part 2: Prove strict enveloping
    intro n
    let s_n := ∑ k in Finset.range (2*n), a k
    let s_n1 := s_n + a (2*n)
    have ⟨h_le, h_ge⟩ := h_envelop n
    constructor
    · -- Prove s_n < A
      by_contra h_not_lt
      push_neg at h_not_lt
      have h_eq : s_n = A := by linarith
      -- Now consider next partial sum
      have ⟨h_le', h_ge'⟩ := h_envelop (n+1)
      let s_n' := ∑ k in Finset.range (2*(n+1)), a k
      have : s_n' = s_n + a (2*n) + a (2*n+1) := by
        simp [Finset.sum_range_succ, add_assoc]
      rw [this] at h_le' h_ge'
      -- From h_eq and h_envelop (n+1), we get contradictions
      have h_alt := this.part_1 n
      have h_2n_pos : a (2*n) ≠ 0 := h_a_ne_zero (2*n)
      have h_2n1_pos : a (2*n+1) ≠ 0 := h_a_ne_zero (2*n+1)
      cases' lt_or_gt_of_ne h_2n_pos with h2n_pos h2n_neg
      · -- a(2n) positive case
        have h2n1_neg : a (2*n+1) < 0 := by
          have := this.part_1 (2*n)
          rw [mul_neg_iff] at this
          cases this with
          | inl h => exact h.2
          | inr h => exact h.2
        rw [h_eq] at h_ge'
        have : A + a (2*n) + a (2*n+1) ≥ A := h_ge'
        linarith
      · -- a(2n) negative case
        have h2n1_pos : a (2*n+1) > 0 := by
          have := this.part_1 (2*n)
          rw [mul_neg_iff] at this
          cases this with
          | inl h => exact h.1
          | inr h => exact h.1
        rw [h_eq] at h_le'
        have : A + a (2*n) + a (2*n+1) ≤ A := h_le'
        linarith
    · -- Prove A < s_n1
      by_contra h_not_gt
      push_neg at h_not_gt
      have h_eq : s_n1 = A := by linarith
      -- Consider previous partial sum when n > 0
      cases n with
      | zero =>
        simp at h_eq
        have := h_decreasing 0
        rw [←h_eq] at this
        simp [abs_of_ne_zero h_a0_ne_zero] at this
        exact lt_irrefl _ this
      | succ n =>
        have ⟨h_le', h_ge'⟩ := h_envelop n
        let s_n' := ∑ k in Finset.range (2*n), a k
        have : s_n = s_n' + a (2*n) + a (2*n+1) := by
          simp [Finset.sum_range_succ, add_assoc]
        rw [this] at h_eq
        have h_alt := this.part_1 (2*n)
        have h_2n_pos : a (2*n) ≠ 0 := h_a_ne_zero (2*n)
        have h_2n1_pos : a (2*n+1) ≠ 0 := h_a_ne_zero (2*n+1)
        cases' lt_or_gt_of_ne h_2n_pos with h2n_pos h2n_neg
        · -- a(2n) positive case
          have h2n1_neg : a (2*n+1) < 0 := by
            have := this.part_1 (2*n)
            rw [mul_neg_iff] at this
            cases this with
            | inl h => exact h.2
            | inr h => exact h.2
          rw [h_eq] at h_le'
          have : s_n' + a (2*n) + a (2*n+1) ≤ A := h_le'
          linarith
        · -- a(2n) negative case
          have h2n1_pos : a (2*n+1) > 0 := by
            have := this.part_1 (2*n)
            rw [mul_neg_iff] at this
            cases this with
            | inl h => exact h.1
            | inr h => exact h.1
          rw [h_eq] at h_ge'
          have : s_n' + a (2*n) + a (2*n+1) ≥ A := h_ge'
          linarith