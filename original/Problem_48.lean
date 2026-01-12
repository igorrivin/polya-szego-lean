/-
Polya-Szego Problem 48
Part Three, Chapter 1

Original problem:
The existence of

$$
\lim _{n \rightarrow \infty}\left(u_{1}+u_{2}+\cdots+u_{n-1}+c u_{n}\right)=\alpha
$$

implies the existence of

$$
\lim _{n \rightarrow \infty}\left(u_{1}+u_{2}+\cdots+u_{n-1}+u_{n}\right)=\alpha
$$

in two cases only: if $c=0$ or if $\Re c>\frac{1}{2}$, but not if $\Re c \leqq \frac{1}{2}, c \neq 0$.\\

Formalization notes: We formalize the statement about limits of sequences with complex coefficients.
The problem concerns two sequences of partial sums:
  s_n = u₁ + u₂ + ... + u_{n-1} + c·u_n
  t_n = u₁ + u₂ + ... + u_n
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Instances.Real

/-!
Formalization notes:
We formalize the statement about limits of sequences with complex coefficients.
The problem concerns two sequences of partial sums:
  s_n = u₁ + u₂ + ... + u_{n-1} + c·u_n
  t_n = u₁ + u₂ + ... + u_n

We formalize the implication: if lim s_n = α exists, then lim t_n = α exists,
but only when c = 0 or Re(c) > 1/2.

Important: The "not if" part (counterexamples when Re(c) ≤ 1/2, c ≠ 0) is stated
as a separate theorem since it requires constructing specific counterexamples.
-/

open Complex

theorem problem_48_implication {c : ℂ} (hc : c = 0 ∨ re c > 1/2) :
    ∀ {u : ℕ → ℂ} {α : ℂ},
    (∃ L : Filter.Tendsto (λ n : ℕ ↦ (∑ k in Finset.range n, u k) + c * u n) Filter.atTop (𝓝 α)) →
    (∃ L' : Filter.Tendsto (λ n : ℕ ↦ ∑ k in Finset.range (n + 1), u k) Filter.atTop (𝓝 α)) := by
  sorry

theorem problem_48_counterexample {c : ℂ} (hc1 : re c ≤ 1/2) (hc2 : c ≠ 0) :
    ∃ (u : ℕ → ℂ) (α : ℂ),
    Filter.Tendsto (λ n : ℕ ↦ (∑ k in Finset.range n, u k) + c * u n) Filter.atTop (𝓝 α) ∧
    ¬Filter.Tendsto (λ n : ℕ ↦ ∑ k in Finset.range (n + 1), u k) Filter.atTop (𝓝 α) := by
  sorry

-- Proof attempt:
theorem problem_48_implication {c : ℂ} (hc : c = 0 ∨ re c > 1/2) :
    ∀ {u : ℕ → ℂ} {α : ℂ},
    (∃ L : Filter.Tendsto (λ n : ℕ ↦ (∑ k in Finset.range n, u k) + c * u n) Filter.atTop (𝓝 α)) →
    (∃ L' : Filter.Tendsto (λ n : ℕ ↦ ∑ k in Finset.range (n + 1), u k) Filter.atTop (𝓝 α)) := by
  intro u α ⟨L⟩
  cases' hc with hc0 hc1
  · -- Case c = 0
    simp [hc0] at L
    use L
    simp [Finset.sum_range_succ]
  · -- Case re c > 1/2
    let s := fun n ↦ ∑ k in Finset.range n, u k
    have h : Tendsto (fun n ↦ s n + c * u n) atTop (𝓝 α) := L
    have h_succ : Tendsto (fun n ↦ s (n + 1) + c * u (n + 1)) atTop (𝓝 α) :=
      Tendsto.comp (tendsto_atTop_atTop_of_monotone Nat.monotone_cast) h
    have key : ∀ n, u n = (s n + c * u n - s n) / c := by
      intro n
      field_simp [(show c ≠ 0 from by contrapose! hc1; simp [hc1, zero_re]; linarith)]
      ring
    have : Tendsto (fun n ↦ u n) atTop (𝓝 ((α - α) / c)) := by
      refine Tendsto.congr' ?_ (Tendsto.sub h h |>.div_const c)
      refine eventually_atTop.mpr ⟨0, fun n hn ↦ ?_⟩
      simp [key n]
    have : Tendsto u atTop (𝓝 0) := by simp [this]
    have : Tendsto (fun n ↦ s n) atTop (𝓝 α) := by
      have := Tendsto.add h (Tendsto.mul_const this |>.neg)
      convert this using 1
      ext n
      simp [← sub_eq_add_neg]
      rw [key n]
      field_simp [(show c ≠ 0 from by contrapose! hc1; simp [hc1, zero_re]; linarith)]
      ring
    use this
    simp [Finset.sum_range_succ]