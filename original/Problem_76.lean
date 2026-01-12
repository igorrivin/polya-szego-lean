/-
Polya-Szego Problem 76
Part One, Chapter 2

Original problem:
Assume $p_{1}>0, p_{2}>0, p_{3}>0, \ldots$ and that the sequence $P_{1}, P_{2}, P_{3}, \ldots, P_{n}=p_{1}+p_{2}+p_{3}+\cdots+p_{n}, \ldots$ is divergent, and $\lim _{n \rightarrow \infty} p_{n} P_{n}^{-1}=0$. Then

$$
\lim _{n \rightarrow \infty} \frac{p_{1} P_{1}^{-1}+p_{2} P_{2}^{-1}+\cdots+p_{n} P_{n}^{-1}}{\log P_{n}}=1
$$

(Generalization of $1+\frac{1}{2}+\frac{1}{3}+\cdots+\frac{1}{n} \sim \log n$.)\\

Formalization notes: We formalize Problem 76 from Polya-Szego's "Problems and Theorems in Analysis":
Given a sequence of positive terms p_n, with partial sums P_n = ∑_{k=1}^n p_k,
assuming:
1. P_n → ∞ (diverges to infinity)
2. p_n/P_n → 0 as n → ∞
Then:
  lim_{n→∞} (∑_{k=1}^n (p_k/P_k)) / (Real.log P_n) = 1
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Asymptotics.Asymptotics
import Mathlib.Topology.Instances.Real

/- Formalization notes:
We formalize Problem 76 from Polya-Szego's "Problems and Theorems in Analysis":
Given a sequence of positive terms p_n, with partial sums P_n = ∑_{k=1}^n p_k,
assuming:
1. P_n → ∞ (diverges to infinity)
2. p_n/P_n → 0 as n → ∞
Then:
  lim_{n→∞} (∑_{k=1}^n (p_k/P_k)) / (Real.log P_n) = 1

We use:
- `p : ℕ → ℝ` for the sequence p_n
- `P n = ∑_{k=1}^n p k` for the partial sums
- `Tendsto P atTop atTop` for divergence
- `Tendsto (λ n => p n / P n) atTop (𝓝 0)` for the second condition
- The conclusion uses `Filter.Tendsto` with the ratio approaching 1
-/

theorem problem_76 (p : ℕ → ℝ) (hp_pos : ∀ n, 0 < p n) :
    let P : ℕ → ℝ := λ n => ∑ k in Finset.range (n + 1), p k
    Tendsto P atTop atTop ∧ 
    Tendsto (λ n => p n / P n) atTop (𝓝 0) →
    Tendsto (λ n => ((∑ k in Finset.range (n + 1), p k / P k) / Real.log (P n))) 
      atTop (𝓝 1) := by
  sorry

-- Proof attempt:
theorem problem_76 (p : ℕ → ℝ) (hp_pos : ∀ n, 0 < p n) :
    let P : ℕ → ℝ := λ n => ∑ k in Finset.range (n + 1), p k
    Tendsto P atTop atTop ∧ 
    Tendsto (λ n => p n / P n) atTop (𝓝 0) →
    Tendsto (λ n => ((∑ k in Finset.range (n + 1), p k / P k) / Real.log (P n))) 
      atTop (𝓝 1) := by
  intro P h
  rcases h with ⟨hP, hpP⟩
  have hP_pos : ∀ n, 0 < P n := by
    intro n
    induction' n with n ih
    · simp [P, hp_pos]
    · simp [P]
      rw [Finset.sum_range_succ]
      exact add_pos ih (hp_pos (n + 1))
  
  -- Key step: show p_n/P_n = log(P_n) - log(P_{n-1}) + o(log(P_n) - log(P_{n-1}))
  have aux : Tendsto (λ n => (p n / P n) / (Real.log (P n) - Real.log (P (n - 1)))) atTop (𝓝 1) := by
    refine' Tendsto.congr' _ (tendsto_one_iff_log_div_sub_log.2 hP hP_pos hpP)
    filter_upwards [Filter.eventually_gt_atTop 0] with n hn
    have : P n = P (n - 1) + p n := by
      cases n
      · simp [P]
      · simp [P, Nat.succ_eq_add_one, Finset.sum_range_succ]
    rw [this]
    field_simp [hP_pos n, hP_pos (n - 1), ne_of_gt (hp_pos n)]
    ring
  
  -- Now rewrite the sum as a telescoping sum plus error terms
  let S n := ∑ k in Finset.range (n + 1), p k / P k
  have hS : ∀ n, S n = Real.log (P n) + ∑ k in Finset.range (n + 1), (p k / P k - (Real.log (P k) - Real.log (P (k - 1)))) := by
    intro n
    rw [S]
    have : Real.log (P n) = ∑ k in Finset.range (n + 1), (Real.log (P k) - Real.log (P (k - 1))) := by
      induction' n with n ih
      · simp [P]
      · rw [Finset.sum_range_succ, ih]
        simp
    rw [this]
    simp_rw [sub_add_eq_add_sub]
    rw [Finset.sum_add_distrib]
  
  -- The error sum is o(log P_n)
  have : Tendsto (λ n => (∑ k in Finset.range (n + 1), (p k / P k - (Real.log (P k) - Real.log (P (k - 1))))) / Real.log (P n)) atTop (𝓝 0) := by
    refine' Asymptotics.isLittleO.tendsto_div _
    refine' Asymptotics.isLittleO_sum_range_of_tendsto_zero _ aux
    intro k
    cases k
    · simp [P]
    · simp [P, Nat.succ_eq_add_one, Finset.sum_range_succ]
  
  -- Final computation
  refine' Tendsto.congr' _ ((tendsto_add_atTop_iff_nat 1).1 _)
  · filter_upwards [Filter.eventually_gt_atTop 0] with n hn
    rw [hS n]
    have hlog : 0 < Real.log (P n) := Real.log_pos (hP_pos n)
    field_simp [hlog.ne']
    ring
  · simp_rw [div_add_div_same]
    exact tendsto_const_nhds.add this