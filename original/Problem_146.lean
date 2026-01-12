/-
Polya-Szego Problem 146
Part One, Chapter 4

Original problem:
Let the function $f(x)$ assume real values for real $x, x>R>0$. If $f(x)$ is enveloped for $x>R$ by the real series $a_{0}+\frac{a_{1}}{x}+\frac{a_{2}}{x^{2}}+\frac{a_{3}}{x^{3}}+\cdots$ then the numbers $a_{1}, a_{2}, a_{3}, \ldots$ have alternating signs and the series is strictly enveloping.\\

Formalization notes: -- We formalize the concept of "enveloped by a series" as:
-- For all x > R, there exists N such that for all n ≥ N,
-- the partial sum S_n(x) = a₀ + a₁/x + a₂/x² + ... + aₙ/xⁿ
-- satisfies f(x) - S_n(x) has the same sign as (-1)^(n+1) * a_{n+1}/x^{n+1}
-- This captures the alternating envelopment property.
-/

import Mathlib.Analysis.Asymptotics.Asymptotics
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Real

-- Formalization notes:
-- We formalize the concept of "enveloped by a series" as:
-- For all x > R, there exists N such that for all n ≥ N,
-- the partial sum S_n(x) = a₀ + a₁/x + a₂/x² + ... + aₙ/xⁿ
-- satisfies f(x) - S_n(x) has the same sign as (-1)^(n+1) * a_{n+1}/x^{n+1}
-- This captures the alternating envelopment property.

-- We define "strictly enveloping" as the inequality being strict.

structure EnvelopingSeries (f : ℝ → ℝ) (R : ℝ) (a : ℕ → ℝ) : Prop where
  pos_R : R > 0
  series_envelopes : ∀ x > R, ∀ n : ℕ, 
    let S_n := a 0 + ∑ k in Finset.range (n + 1), a (k + 1) / (x : ℝ) ^ (k + 1) in
    let next_term := a (n + 2) / (x : ℝ) ^ (n + 2) in
    (f x - S_n) * next_term < 0
  -- This ensures alternating signs and strict envelopment

theorem problem_146_part_one : 
    ∀ (f : ℝ → ℝ) (R : ℝ) (a : ℕ → ℝ),
    EnvelopingSeries f R a → 
    (∀ n : ℕ, n ≥ 1 → ((a n > 0 ∧ a (n + 1) < 0) ∨ (a n < 0 ∧ a (n + 1) > 0))) ∧
    (∀ x > R, ∀ n : ℕ, 
      let S_n := a 0 + ∑ k in Finset.range (n + 1), a (k + 1) / (x : ℝ) ^ (k + 1) in
      let S_{n+1} := S_n + a (n + 2) / (x : ℝ) ^ (n + 2) in
      (f x - S_n) * (f x - S_{n+1}) < 0) := by
  sorry

-- Proof attempt:
theorem problem_146_part_one : 
    ∀ (f : ℝ → ℝ) (R : ℝ) (a : ℕ → ℝ),
    EnvelopingSeries f R a → 
    (∀ n : ℕ, n ≥ 1 → ((a n > 0 ∧ a (n + 1) < 0) ∨ (a n < 0 ∧ a (n + 1) > 0))) ∧
    (∀ x > R, ∀ n : ℕ, 
      let S_n := a 0 + ∑ k in Finset.range (n + 1), a (k + 1) / (x : ℝ) ^ (k + 1) in
      let S_{n+1} := S_n + a (n + 2) / (x : ℝ) ^ (n + 2) in
      (f x - S_n) * (f x - S_{n+1}) < 0) := by
  intro f R a h
  constructor
  · -- First part: alternating signs
    intro n hn
    have := h.series_envelopes (R + 1) (by linarith [h.pos_R]) n
    simp at this
    let next_term := a (n + 2) / (R + 1) ^ (n + 2)
    have sign_condition : (f (R + 1) - (a 0 + ∑ k in Finset.range (n + 1), a (k + 1) / (R + 1) ^ (k + 1))) * next_term < 0 := this
    cases' lt_or_gt_of_ne (by rcases sign_condition with h; exact ne_of_lt h) with hneg hpos
    { -- Case when next_term is positive
      have : f (R + 1) - (a 0 + ∑ k in Finset.range (n + 1), a (k + 1) / (R + 1) ^ (k + 1)) < 0 := by linarith
      cases' n with n
      { -- Base case n=0
        simp at this
        have := h.series_envelopes (R + 1) (by linarith [h.pos_R]) 1
        simp at this
        have : (f (R + 1) - (a 0 + a 1 / (R + 1) + a 2 / (R + 1)^2)) * (a 3 / (R + 1)^3) < 0 := this
        by_cases h1 : a 1 > 0
        { right
          constructor
          · linarith [this]
          · exact h1 }
        { left
          constructor
          · linarith [this]
          · linarith } }
      { -- Inductive step
        have prev := h.series_envelopes (R + 1) (by linarith [h.pos_R]) (n)
        simp at prev
        by_cases h_an : a (n + 1) > 0
        { right
          constructor
          · exact h_an
          · linarith [prev] }
        { left
          constructor
          · linarith
          · linarith [prev] } } }
    { -- Case when next_term is negative
      have : f (R + 1) - (a 0 + ∑ k in Finset.range (n + 1), a (k + 1) / (R + 1) ^ (k + 1)) > 0 := by linarith
      cases' n with n
      { -- Base case n=0
        simp at this
        have := h.series_envelopes (R + 1) (by linarith [h.pos_R]) 1
        simp at this
        have : (f (R + 1) - (a 0 + a 1 / (R + 1) + a 2 / (R + 1)^2)) * (a 3 / (R + 1)^3) < 0 := this
        by_cases h1 : a 1 > 0
        { right
          constructor
          · linarith [this]
          · exact h1 }
        { left
          constructor
          · linarith [this]
          · linarith } }
      { -- Inductive step
        have prev := h.series_envelopes (R + 1) (by linarith [h.pos_R]) (n)
        simp at prev
        by_cases h_an : a (n + 1) > 0
        { right
          constructor
          · exact h_an
          · linarith [prev] }
        { left
          constructor
          · linarith
          · linarith [prev] } } }
  · -- Second part: strict envelopment
    intro x hx n
    let S_n := a 0 + ∑ k in Finset.range (n + 1), a (k + 1) / x ^ (k + 1)
    let S_{n+1} := S_n + a (n + 2) / x ^ (n + 2)
    have h1 := h.series_envelopes x hx n
    have h2 := h.series_envelopes x hx (n + 1)
    simp at h1 h2
    let term := a (n + 2) / x ^ (n + 2)
    let next_term := a (n + 3) / x ^ (n + 3)
    have : (f x - S_n) * term < 0 := h1
    have : (f x - S_{n+1}) * next_term < 0 := h2
    rw [show S_{n+1} = S_n + term by rfl] at this
    have : (f x - S_n - term) * next_term < 0 := this
    -- Now we need to show (f x - S_n) * (f x - S_n - term) < 0
    -- From the first inequality, we know (f x - S_n) and term have opposite signs
    -- From the second inequality, we know (f x - S_n - term) and next_term have opposite signs
    -- And from the first part, we know term and next_term have opposite signs
    -- Therefore (f x - S_n) and (f x - S_n - term) must have opposite signs
    have alt_signs : ∀ n : ℕ, n ≥ 1 → ((a n > 0 ∧ a (n + 1) < 0) ∨ (a n < 0 ∧ a (n + 1) > 0)) := by
      apply (problem_146_part_one f R a h).1
    cases' lt_or_gt_of_ne (ne_of_lt this) with hneg hpos
    { -- Case when (f x - S_n - term) > 0 and next_term < 0
      have : f x - S_n - term > 0 := by linarith
      have : next_term < 0 := by linarith
      have := alt_signs (n + 1) (by omega)
      cases' this with hcase1 hcase2
      { have : a (n + 2) > 0 := hcase1.1
        have : term > 0 := by positivity
        have : f x - S_n < term := by linarith
        have : f x - S_n > 0 := by linarith [this]
        linarith }
      { have : a (n + 2) < 0 := hcase2.1
        have : term < 0 := by positivity
        have : f x - S_n > term := by linarith
        have : f x - S_n < 0 := by linarith [this]
        linarith } }
    { -- Case when (f x - S_n - term) < 0 and next_term > 0
      have : f x - S_n - term < 0 := by linarith
      have : next_term > 0 := by linarith
      have := alt_signs (n + 1) (by omega)
      cases' this with hcase1 hcase2
      { have : a (n + 2) > 0 := hcase1.1
        have : term > 0 := by positivity
        have : f x - S_n < term := by linarith
        have : f x - S_n > 0 := by linarith [this]
        linarith }
      { have : a (n + 2) < 0 := hcase2.1
        have : term < 0 := by positivity
        have : f x - S_n > term := by linarith
        have : f x - S_n < 0 := by linarith [this]
        linarith } }