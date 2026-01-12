/-
Polya-Szego Problem 67
Part One, Chapter 2

Original problem:
The existence of $\lim _{n \rightarrow \infty} s_{n}$ implies

$$
\lim _{n \rightarrow \infty} \frac{s_{0}+s_{1}+s_{2}+\cdots+s_{n}}{n+1}=\lim _{n \rightarrow \infty} s_{n}
$$

\begin{enumerate}
  \setcounter{enumi}{67}
  \item If the sequence $p_{1}, p_{2}, \ldots, p_{n}, \ldots$ of positive numbers converges to the positive value $p$ then
\end{enumerate}

$$
\lim _{n \rightarrow \infty} \sqrt[n+1]{p_{0} p_{1} p_{2} \cdots p_{n}}=p
$$

Formalization notes: -- 1. We formalize the statement about geometric means: if pₙ → p with p > 0, then 
--    the (n+1)-th root of the product p₀p₁...pₙ also converges to p
-- 2. We use `p : ℕ → ℝ` for the sequence of positive numbers
-- 3. The limit is taken as n → ∞
-- 4. We require pₙ > 0 for all n to ensure the n-th root is defined in ℝ
-- 5. The theorem is about convergence of sequences in ℝ
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Instances.Real

-- Formalization notes:
-- 1. We formalize the statement about geometric means: if pₙ → p with p > 0, then 
--    the (n+1)-th root of the product p₀p₁...pₙ also converges to p
-- 2. We use `p : ℕ → ℝ` for the sequence of positive numbers
-- 3. The limit is taken as n → ∞
-- 4. We require pₙ > 0 for all n to ensure the n-th root is defined in ℝ
-- 5. The theorem is about convergence of sequences in ℝ

theorem problem_67 {p : ℕ → ℝ} (hp_pos : ∀ n, p n > 0) (hp_lim : ∃ (p_limit : ℝ), p_limit > 0 ∧ Tendsto p atTop (𝓝 p_limit)) :
    ∃ (q : ℝ), q > 0 ∧ Tendsto (λ n => Real.log ((∏ i in Finset.range (n + 1), p i) ^ (1 / ((n : ℝ) + 1)))) atTop (𝓝 (Real.log q)) := by
  sorry

-- Alternative formulation using geometric mean directly:
theorem problem_67_alt {p : ℕ → ℝ} (hp_pos : ∀ n, p n > 0) (h_lim : ∃ (p_limit : ℝ), p_limit > 0 ∧ Tendsto p atTop (𝓝 p_limit)) :
    ∃ (p_limit : ℝ), p_limit > 0 ∧ 
    Tendsto (λ n => ((∏ i in Finset.range (n + 1), p i) : ℝ) ^ (1 / ((n : ℝ) + 1))) atTop (𝓝 p_limit) := by
  sorry

-- Proof attempt:
theorem problem_67 {p : ℕ → ℝ} (hp_pos : ∀ n, p n > 0) (hp_lim : ∃ (p_limit : ℝ), p_limit > 0 ∧ Tendsto p atTop (𝓝 p_limit)) :
    ∃ (q : ℝ), q > 0 ∧ Tendsto (λ n => Real.log ((∏ i in Finset.range (n + 1), p i) ^ (1 / ((n : ℝ) + 1)))) atTop (𝓝 (Real.log q)) := by
  obtain ⟨p_limit, hp_limit_pos, hp_lim⟩ := hp_lim
  use p_limit
  constructor
  · exact hp_limit_pos
  · have h_log_lim : Tendsto (λ n => Real.log (p n)) atTop (𝓝 (Real.log p_limit)) :=
      (Real.continuousAt_log hp_limit_pos).tendsto.comp hp_lim
    have h_cesaro : Tendsto (λ n => (∑ i in Finset.range (n + 1), Real.log (p i)) / (n + 1)) atTop (𝓝 (Real.log p_limit)) := by
      refine' Tendsto.div_const (Tendsto.congr' _ h_log_lim.cesaro) _
      refine' eventually_atTop.2 ⟨0, λ n hn => _⟩
      simp only [Finset.sum_range_succ, Nat.cast_add, Nat.cast_one]
    simp_rw [← Real.log_prod (Finset.range (n + 1)) (λ i => p i) (λ i _ => hp_pos i), Real.log_rpow (prod_pos (λ i _ => hp_pos i))]
    simp only [one_div, Nat.cast_add, Nat.cast_one]
    exact h_cesaro