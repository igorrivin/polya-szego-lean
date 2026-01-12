/-
Polya-Szego Problem 70
Part One, Chapter 2

Original problem:
Let the two given sequences

$$
\begin{aligned}
& a_{0}, a_{1}, a_{2}, \ldots, a_{n}, \ldots \\
& b_{0}, b_{1}, b_{2}, \ldots, b_{n}, \ldots
\end{aligned}
$$

satisfy the conditions:

$$
\begin{aligned}
b_{n}>0, & n=0,1,2, \ldots ; \\
b_{0}+b_{1}+b_{2}+\cdots+b_{n}+\cdots & \text { diverges } ; \\
\lim _{n \rightarrow \infty} \frac{a_{n}}{b_{n}} & =s .
\end{aligned}
$$

\begin{enumerate}
  \setcounter{enumi}{70}
  \item Ass\\
the dum
\end{enumerate}

The ralbe\\
72 Let

The exister\\

Formalization notes: 
-/

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Asymptotics.Asymptotics
import Mathlib.Topology.Instances.Real

/-!
Problem 70 from Polya-Szego's "Problems and Theorems in Analysis"

Let {aₙ} and {bₙ} be sequences of real numbers such that:
1. bₙ > 0 for all n
2. The series ∑ bₙ diverges (i.e., ∑_{k=0}^n bₙ → ∞ as n → ∞)
3. lim_{n→∞} (aₙ / bₙ) = s

Then the generalized Cesàro mean converges to the same limit:
lim_{n→∞} (∑_{k=0}^n aₖ) / (∑_{k=0}^n bₖ) = s

This is a generalization of the Stolz-Cesàro theorem.
-/

theorem problem_70 (a b : ℕ → ℝ) (s : ℝ) 
    (hb_pos : ∀ n, 0 < b n) 
    (hb_div : Tendsto (λ n => ∑ k in Finset.range n, b k) atTop atTop)
    (h_lim : Tendsto (λ n => a n / b n) atTop (𝓝 s)) :
    Tendsto (λ n => (∑ k in Finset.range n, a k) / (∑ k in Finset.range n, b k)) atTop (𝓝 s) := by
  sorry

-- Proof attempt:
theorem problem_70 (a b : ℕ → ℝ) (s : ℝ) 
    (hb_pos : ∀ n, 0 < b n) 
    (hb_div : Tendsto (λ n => ∑ k in Finset.range n, b k) atTop atTop)
    (h_lim : Tendsto (λ n => a n / b n) atTop (𝓝 s)) :
    Tendsto (λ n => (∑ k in Finset.range n, a k) / (∑ k in Finset.range n, b k)) atTop (𝓝 s) := by
  -- Convert the limit condition to asymptotic notation
  have h_asymp : a =o[atTop] (λ n => b n) + O[atTop] (λ n => b n) := by
    rw [Asymptotics.isLittleO_iff] at h_lim ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.1 (h_lim (Metric.ball s ε))
    use N
    intro n hn
    specialize hN n hn
    simp only [dist_eq_norm, mem_ball] at hN
    rw [show a n / b n - s = (a n - s * b n) / b n by field_simp [hb_pos n]]
    rw [norm_div, norm_eq_abs, norm_eq_abs, ← mul_div_assoc, abs_div, abs_of_pos (hb_pos n)]
    exact hN

  -- The main part: rewrite the quotient as a weighted average
  refine Asymptotics.isLittleO.tendsto_div_nhds_zero ?_ |>.add_const s
  simp only [Asymptotics.isLittleO_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.1 (h_lim (Metric.ball s (ε/2)))
  let B n := ∑ k in Finset.range n, b k
  have hB_pos : ∀ n, 0 < B n := by
    intro n
    induction' n with n hn
    · simp [Finset.range_zero, Finset.sum_empty]
    · rw [Finset.range_succ, Finset.sum_insert (Finset.not_mem_range_self)]
      exact add_pos hn (hb_pos n)
  
  -- Split the sum into two parts: before and after N
  have key : ∀ n ≥ N, ‖∑ k in Finset.range n, (a k - s * b k)‖ / B n ≤ ε := by
    intro n hnN
    let S₁ := Finset.range N
    let S₂ := Finset.range n \ Finset.range N
    have h_split : Finset.range n = S₁ ∪ S₂ := by
      simp [Finset.union_sdiff_of_subset (Finset.range_mono (by linarith))]
    
    rw [h_split, Finset.sum_union (Finset.disjoint_sdiff.mono_left (Finset.range_subset)), 
        ← add_div, norm_add_lt_of_lt (ε/2) (ε/2), add_halves]
    · apply div_le_div_of_le (le_of_lt (hB_pos n))
      rw [norm_sum]
      refine le_trans (Finset.sum_le_sum (fun k hk => ?_)) ?_
      · specialize hN k (by simp only [Finset.mem_range, Finset.mem_sdiff] at hk; exact hk.2)
        simp only [mem_ball, dist_eq_norm] at hN
        rw [show a k - s * b k = b k * (a k / b k - s) by field_simp [hb_pos k]]
        rw [norm_mul, norm_eq_abs, abs_of_pos (hb_pos k)]
        exact mul_le_mul_of_nonneg_left (le_of_lt hN) (le_of_lt (hb_pos k))
      · rw [← Finset.sum_mul]
        refine mul_le_mul_of_nonneg_right (Finset.sum_le_sum_of_subset (Finset.sdiff_subset _ _)) ?_
        exact le_of_lt (hb_pos _)
    · apply div_lt_div_of_lt (hB_pos n)
      rw [norm_sum]
      refine lt_of_le_of_lt (Finset.sum_le_sum (fun k hk => ?_)) ?_
      · specialize hN k (by simp only [Finset.mem_range] at hk ⊢; exact lt_of_lt_of_le hk hnN)
        simp only [mem_ball, dist_eq_norm] at hN
        rw [show a k - s * b k = b k * (a k / b k - s) by field_simp [hb_pos k]]
        rw [norm_mul, norm_eq_abs, abs_of_pos (hb_pos k)]
        exact mul_le_mul_of_nonneg_left (le_of_lt hN) (le_of_lt (hb_pos k))
      · rw [← Finset.sum_mul]
        refine (mul_lt_mul_of_pos_right ?_ (hb_pos _))
        exact Finset.sum_lt_sum_of_nonempty (Finset.range_nonempty _) (fun k hk => hb_pos k)
  
  -- Final conclusion using the key estimate
  filter_upwards [eventually_ge_atTop N] with n hn using key n hn