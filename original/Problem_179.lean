/-
Polya-Szego Problem 179
Part One, Chapter 4

Original problem:
Let

$$
f_{n}(x)=a_{n 1} x+a_{n 2} x^{2}+a_{n 3} x^{3}+\cdots, \quad n=1,2,3, \ldots
$$

be arbitrary functions, $\left|a_{n k}\right|<A$ for all positive integral values of $n$ and $k$ and

$$
\lim _{n \rightarrow \infty} f_{n}(x)=0 \quad \text { if } \quad 0<x<1
$$

Then we have for fixed $k, k=1,2,3, \ldots$

$$
\lim _{n \rightarrow \infty} a_{n k}=0
$$

\begin{enumerate}
  \setcounter{enumi}{179}
  \item Suppose that the series
\end{enumerate}

$$
a_{n 0}+a_{n 1}+a_{n 2}+\cdots+a_{n k}+\cdot

Formalization notes: -- We formalize the first part of Problem 179:
-- Given sequences of power series f_n(x) = Σ_{k=1}^∞ a_{n,k} x^k with |a_{n,k}| < A for all n,k,
-- and lim_{n→∞} f_n(x) = 0 for all x ∈ (0,1), then for each fixed k, lim_{n→∞} a_{n,k} = 0.
-- We work in ℝ for simplicity, though the problem is stated for complex coefficients.
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.NormedSpace.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic

-- Formalization notes:
-- We formalize the first part of Problem 179:
-- Given sequences of power series f_n(x) = Σ_{k=1}^∞ a_{n,k} x^k with |a_{n,k}| < A for all n,k,
-- and lim_{n→∞} f_n(x) = 0 for all x ∈ (0,1), then for each fixed k, lim_{n→∞} a_{n,k} = 0.
-- We work in ℝ for simplicity, though the problem is stated for complex coefficients.

theorem problem_179_part1 {A : ℝ} (hA_pos : 0 < A) 
    (a : ℕ → ℕ → ℝ) (ha_bound : ∀ n k, |a n k| < A)
    (h_conv : ∀ (x : ℝ) (hx : x ∈ Set.Ioo (0 : ℝ) 1), 
        Tendsto (λ n : ℕ ↦ ∑' k : ℕ, a n k * x ^ (k + 1)) atTop (𝓝 0)) 
    (k : ℕ) : 
    Tendsto (λ n : ℕ ↦ a n k) atTop (𝓝 0) := by
  sorry

-- Formalization notes:
-- We formalize Problem 180 (the second part shown):
-- Given sequences s_n = Σ_{k=0}^∞ a_{n,k} with |a_{n,k}| ≤ A_k for all n,k,
-- where Σ_{k=0}^∞ A_k converges, and lim_{n→∞} a_{n,k} = a_k exists for each k,
-- then Σ_{k=0}^∞ a_k converges and lim_{n→∞} s_n = Σ_{k=0}^∞ a_k.

theorem problem_180 {A : ℕ → ℝ} (hA_summable : Summable A)
    (a : ℕ → ℕ → ℝ) (ha_bound : ∀ n k, |a n k| ≤ A k)
    (h_conv_coeff : ∀ k, ∃ a_k : ℝ, Tendsto (λ n : ℕ ↦ a n k) atTop (𝓝 a_k))
    (s : ℕ → ℝ) (hs_def : ∀ n, s n = ∑' k : ℕ, a n k) :
    ∃ (s_inf : ℝ), Summable (λ k ↦ Classical.choose (h_conv_coeff k)) ∧ 
    Tendsto s atTop (𝓝 s_inf) ∧ 
    s_inf = ∑' k : ℕ, Classical.choose (h_conv_coeff k) := by
  sorry

-- Proof attempt:
theorem problem_179_part1 {A : ℝ} (hA_pos : 0 < A) 
    (a : ℕ → ℕ → ℝ) (ha_bound : ∀ n k, |a n k| < A)
    (h_conv : ∀ (x : ℝ) (hx : x ∈ Set.Ioo (0 : ℝ) 1), 
        Tendsto (λ n : ℕ ↦ ∑' k : ℕ, a n k * x ^ (k + 1)) atTop (𝓝 0)) 
    (k : ℕ) : 
    Tendsto (λ n : ℕ ↦ a n k) atTop (𝓝 0) := by
  -- We'll use the fact that if the limit of the series is 0 for all x ∈ (0,1),
  -- then each coefficient must tend to 0.
  -- Choose x = 1/2^(1/(k+1)) ∈ (0,1)
  let x : ℝ := (1/2)^(1/(k+1))
  have hx_pos : 0 < x := by apply Real.rpow_pos_of_pos; norm_num
  have hx_lt1 : x < 1 := by
    apply Real.rpow_lt_one_of_pos_of_lt_one (by norm_num) (by norm_num)
    apply one_div_pos.mpr; exact Nat.cast_pos.mpr (Nat.succ_pos k)
  have hx_mem : x ∈ Set.Ioo (0 : ℝ) 1 := ⟨hx_pos, hx_lt1⟩
  
  -- The series tends to 0 at this x
  have h_conv_x := h_conv x hx_mem
  
  -- The key observation: the k-th term dominates the series as x → 0
  -- So we can extract the coefficient a n k
  rw [Metric.tendsto_atTop] at h_conv_x ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := h_conv_x (ε * x^(k+1) / 2) (by positivity)
  use N
  intro n hn
  specialize hN n hn
  rw [dist_eq_norm, sub_zero] at hN ⊢
  
  -- We'll show |a n k| ≤ ε by contradiction
  by_contra h
  push_neg at h
  have h_lower : ε * x^(k+1) ≤ |a n k * x^(k+1)| := by
    rw [abs_mul]
    simp only [abs_pow]
    gcongr
  have h_sum_lower : ε * x^(k+1) ≤ ∑' k', |a n k' * x^(k'+1)| := by
    apply le_trans h_lower (le_tsum _ (fun k' => abs_nonneg _) ?_)
    intro i
    exact (ha_bound n i).le
  have h_sum_upper : ∑' k', |a n k' * x^(k'+1)| < ε * x^(k+1) / 2 := by
    refine lt_of_le_of_lt ?_ hN
    apply tsum_le_tsum (fun k' => abs_nonneg _) ?_ (summable_abs_of_summable ?_)
    · intro k'
      rw [abs_mul, abs_pow]
    · refine summable_of_norm_bounded _ (summable_geometric_of_lt_1 hx_pos.le hx_lt1) ?_
      intro k'
      rw [norm_mul, norm_pow, norm_eq_abs, norm_eq_abs]
      calc |a n k'| * |x| ^ (k' + 1) ≤ A * |x| ^ (k' + 1) := by gcongr; exact (ha_bound n k').le
           _ ≤ A * x ^ (k' + 1) := by gcongr; exact abs_eq_self.mpr hx_pos.le
  linarith