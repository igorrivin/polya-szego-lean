/-
Polya-Szego Problem 45
Part Three, Chapter 1

Original problem:
What conditions must the series $u_{0}+u_{1}+u_{2}+\cdots+u_{n}+\cdots$ satisfy in order that its Cauchy product [I 34, II 23, VIII, Chap. 1, § 5] with any convergent series $v_{0}+v_{1}+v_{2}+\cdots+v_{n}+\cdots$ results in a convergent series

$$
\begin{aligned}
u_{0} v_{0} & +\left(u_{0} v_{1}+u_{1} v_{0}\right)+\left(u_{0} v_{2}+u_{1} v_{1}+u_{2} v_{0}\right)+\cdots \\
& +\left(u_{0} v_{n}+u_{1} v_{n-1}+\cdots+u_{n-1} v_{1}+u_{n} v_{0}\right)+\cdots ?
\end{aligned}
$$

\begin{enumerate}
  \s

Formalization notes: We formalize problem 47 from Polya-Szego:
A sequence (γ_n) turns any convergent series ∑a_n into a convergent series ∑γ_n a_n 
if and only if the series ∑|γ_n - γ_{n+1}| converges.
-/

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
Formalization notes:
We formalize problem 47 from Polya-Szego:
A sequence (γ_n) turns any convergent series ∑a_n into a convergent series ∑γ_n a_n 
if and only if the series ∑|γ_n - γ_{n+1}| converges.

We formalize this as:
Let (γ : ℕ → ℝ) be a real sequence. Then the following are equivalent:
1. For every convergent series ∑a_n (with a_n : ℝ), the series ∑(γ_n * a_n) converges.
2. The series ∑_{n=0}^∞ |γ_n - γ_{n+1}| converges.

Note: We use `HasSum` for series convergence and restrict to real numbers for simplicity.
The original problem is more general, but this captures the essential mathematical content.
-/

theorem problem_47_equivalence (γ : ℕ → ℝ) :
    (∀ (a : ℕ → ℝ), HasSum a s → ∃ t, HasSum (λ n => γ n * a n) t) ↔
    ∃ L : ℝ, HasSum (λ n => |γ n - γ (n + 1)|) L := by
  sorry

-- Proof attempt:
theorem problem_47_equivalence (γ : ℕ → ℝ) :
    (∀ (a : ℕ → ℝ), HasSum a s → ∃ t, HasSum (λ n => γ n * a n) t) ↔
    ∃ L : ℝ, HasSum (λ n => |γ n - γ (n + 1)|) L := by
  constructor
  · intro h
    by_cases hγ : ∃ B, ∀ n, |γ n| ≤ B
    · obtain ⟨B, hB⟩ := hγ
      refine ⟨γ 0 + ∑' n, |γ n - γ (n + 1)|, ?_⟩
      have h_telescope : ∀ N, γ N = γ 0 + ∑ n in Finset.range N, (γ n - γ (n + 1)) := by
        intro N
        induction N with
        | zero => simp
        | succ N ih =>
          rw [Finset.sum_range_succ, ih]
          ring
      have h_sum : HasSum (λ n => |γ n - γ (n + 1)|) (∑' n, |γ n - γ (n + 1)|) := by
        apply summable_hasSum
        apply Summable.of_nonneg_of_le _ _ (summable_abs_iff.mpr (summable_telescope γ))
        · intro n; exact abs_nonneg _
        · intro n; rfl
      refine HasSum.add _ h_sum
      exact hasSum_single 0 (by simp)
    · push_neg at hγ
      let a n := if n = 0 then 1 else 0
      have ha : HasSum a 1 := hasSum_ite_eq 0 1
      obtain ⟨t, ht⟩ := h a ha
      have hγ0 : |γ 0| ≤ |t| := by
        have := ht.unique (hasSum_single 0 (γ 0 * 1))
        simp [a] at this
        rw [← this]
        exact le_abs_self _
      refine ⟨γ 0 + ∑' n, |γ n - γ (n + 1)|, ?_⟩
      have h_telescope : ∀ N, γ N = γ 0 + ∑ n in Finset.range N, (γ n - γ (n + 1)) := by
        intro N
        induction N with
        | zero => simp
        | succ N ih =>
          rw [Finset.sum_range_succ, ih]
          ring
      have h_sum : HasSum (λ n => |γ n - γ (n + 1)|) (∑' n, |γ n - γ (n + 1)|) := by
        apply summable_hasSum
        apply Summable.of_nonneg_of_le _ _ (summable_abs_iff.mpr (summable_telescope γ))
        · intro n; exact abs_nonneg _
        · intro n; rfl
      exact HasSum.add (hasSum_single 0 (γ 0)) h_sum
  · intro h a ha
    obtain ⟨L, hL⟩ := h
    have hγ_bounded : ∃ B, ∀ n, |γ n| ≤ B := by
      have : Summable (λ n => |γ n - γ (n + 1)|) := ⟨L, hL⟩
      have h_telescope : ∀ N, γ N = γ 0 + ∑ n in Finset.range N, (γ n - γ (n + 1)) := by
        intro N
        induction N with
        | zero => simp
        | succ N ih =>
          rw [Finset.sum_range_succ, ih]
          ring
      refine ⟨|γ 0| + L, ?_⟩
      intro n
      rw [h_telescope n]
      have : |∑ n in Finset.range n, (γ n - γ (n + 1))| ≤ ∑ n in Finset.range n, |γ n - γ (n + 1)| :=
        Finset.abs_sum_le_sum_abs _ _
      have : ∑ n in Finset.range n, |γ n - γ (n + 1)| ≤ L := by
        rw [← hL.tsum_eq]
        exact sum_le_tsum _ (fun _ _ => abs_nonneg _) (summable_of_summable_abs hL)
      linarith [abs_add (γ 0) _]
    obtain ⟨B, hB⟩ := hγ_bounded
    have h_summable : Summable (λ n => γ n * a n) := by
      apply Summable.of_abs
      apply Summable.of_norm_bounded_eventually _ (Summable.mul_right ha.summable B)
      filter_upwards with n hn
      rw [norm_mul, norm_eq_abs, norm_eq_abs]
      exact mul_le_mul (hB n) le_rfl (abs_nonneg _) (abs_nonneg _)
    exact ⟨∑' n, γ n * a n, h_summable.hasSum⟩