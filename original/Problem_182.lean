/-
Polya-Szego Problem 182
Part One, Chapter 4

Original problem:
The function $g(t)$ has the following properties for $t \geqq 1$ :\\
(1) $g(t)$ is continuously differentiable;\\
(2) $g(t)$ is monotone increasing to $\infty$ as $t \rightarrow \infty$;\\
(3) $g^{\prime}(t)$ is monotone decreasing to 0 as $t \rightarrow \infty$;\\
(4) $\operatorname{tg}^{\prime}(t) \rightarrow 0$ as $t \rightarrow \infty$.\\
(Cf. 174.) Then the numbers

$$
x_{n}=g(n)-[g(n)], \quad n=1,2,3, \ldots
$$

are everywhere dense on the interval [ 0,1 ] but they are not equidistributed.

Formalization notes: We formalize the main limit theorem from Problem 182:
-/

import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Topology.Instances.Real
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Real.Irrational

/- Formalization notes:
We formalize the main limit theorem from Problem 182:

Given:
1. g : ℝ → ℝ with properties (1)-(4) as described
2. x_n = g(n) - ⌊g(n)⌋ (fractional part)
3. f : ℝ → ℝ that is integrable on [0,1]
4. A sequence n_k → ∞ such that x_{n_k} → ξ ∈ (0,1)
5. f is continuous at ξ

Then:
lim_{k→∞} (1/n_k) ∑_{i=1}^{n_k} f(x_i) = f(ξ)

We make several simplifications:
- We assume the sequence n_k is given as an increasing function ℕ → ℕ
- We use `Int.floor` for the integer part
- We require f to be Riemann integrable (using `IntervalIntegrable`)
- We formalize the convergence of Cesàro means
-/

open Set Filter
open scoped Topology

theorem problem_182_partial (g : ℝ → ℝ) (hg_cont_diff : ContDiff ℝ 1 g) 
    (hg_mono : ∀ t₁ t₂, 1 ≤ t₁ → t₁ ≤ t₂ → g t₁ ≤ g t₂) 
    (hg_tendsto : Tendsto g atTop atTop)
    (hg_deriv_mono : ∀ t₁ t₂, 1 ≤ t₁ → t₁ ≤ t₂ → deriv g t₂ ≤ deriv g t₁)
    (hg_deriv_tendsto : Tendsto (deriv g) atTop (𝓝 0))
    (hg_deriv_prod_tendsto : Tendsto (λ t => t * deriv g t) atTop (𝓝 0))
    (f : ℝ → ℝ) (hf_int : IntervalIntegrable f volume 0 1)
    (ξ : ℝ) (hξ : ξ ∈ Set.Ioo (0 : ℝ) 1)
    (seq : ℕ → ℕ) (hseq_strict_mono : StrictMono seq) 
    (hseq_limit : Tendsto (λ k => g (seq k) - (Int.floor (g (seq k)) : ℝ)) atTop (𝓝 ξ))
    (hf_cont_at_ξ : ContinuousAt f ξ) :
    Tendsto (λ k => (∑ i in Finset.range (seq k), f (g (i + 1) - (Int.floor (g (i + 1)) : ℝ))) / (seq k : ℝ))
      atTop (𝓝 (f ξ)) := by
  sorry

/- Formalization notes for the second part (discontinuity case):
If f has a jump discontinuity at ξ, then the set of limit points of the Cesàro means
is the interval [f(ξ-), f(ξ+)]. This requires defining one-sided limits and
working with cluster points of sequences.
-/

theorem problem_182_discontinuity (g : ℝ → ℝ) (hg_cont_diff : ContDiff ℝ 1 g) 
    (hg_mono : ∀ t₁ t₂, 1 ≤ t₁ → t₁ ≤ t₂ → g t₁ ≤ g t₂) 
    (hg_tendsto : Tendsto g atTop atTop)
    (hg_deriv_mono : ∀ t₁ t₂, 1 ≤ t₁ → t₁ ≤ t₂ → deriv g t₂ ≤ deriv g t₁)
    (hg_deriv_tendsto : Tendsto (deriv g) atTop (𝓝 0))
    (hg_deriv_prod_tendsto : Tendsto (λ t => t * deriv g t) atTop (𝓝 0))
    (f : ℝ → ℝ) (hf_int : IntervalIntegrable f volume 0 1)
    (ξ : ℝ) (hξ : ξ ∈ Set.Ioo (0 : ℝ) 1)
    (h_left_limit : ∃ L, Tendsto f (𝓝[<] ξ) (𝓝 L))
    (h_right_limit : ∃ R, Tendsto f (𝓝[>] ξ) (𝓝 R))
    (h_jump : h_left_limit.choose ≠ h_right_limit.choose) :
    Set.range (Filter.Tendsto (λ k => (∑ i in Finset.range k, f (g (i + 1) - (Int.floor (g (i + 1)) : ℝ))) / (k : ℝ))
      atTop) = Set.Icc h_left_limit.choose h_right_limit.choose := by
  sorry

-- Proof attempt:
theorem problem_182_partial (g : ℝ → ℝ) (hg_cont_diff : ContDiff ℝ 1 g) 
    (hg_mono : ∀ t₁ t₂, 1 ≤ t₁ → t₁ ≤ t₂ → g t₁ ≤ g t₂) 
    (hg_tendsto : Tendsto g atTop atTop)
    (hg_deriv_mono : ∀ t₁ t₂, 1 ≤ t₁ → t₁ ≤ t₂ → deriv g t₂ ≤ deriv g t₁)
    (hg_deriv_tendsto : Tendsto (deriv g) atTop (𝓝 0))
    (hg_deriv_prod_tendsto : Tendsto (λ t => t * deriv g t) atTop (𝓝 0))
    (f : ℝ → ℝ) (hf_int : IntervalIntegrable f volume 0 1)
    (ξ : ℝ) (hξ : ξ ∈ Set.Ioo (0 : ℝ) 1)
    (seq : ℕ → ℕ) (hseq_strict_mono : StrictMono seq) 
    (hseq_limit : Tendsto (λ k => g (seq k) - (Int.floor (g (seq k)) : ℝ)) atTop (𝓝 ξ))
    (hf_cont_at_ξ : ContinuousAt f ξ) :
    Tendsto (λ k => (∑ i in Finset.range (seq k), f (g (i + 1) - (Int.floor (g (i + 1)) : ℝ))) / (seq k : ℝ))
      atTop (𝓝 (f ξ)) := by
  -- First, we'll show that the fractional parts x_n are asymptotically equidistributed
  have h_equidist : ∀ ε > 0, ∃ N, ∀ n ≥ N, 
      ∀ a b ∈ Ioo (0:ℝ) 1, |(Finset.card (Finset.filter (λ i => g (i + 1) - ⌊g (i + 1)⌋ ∈ Ioo a b) (Finset.range n))) / n - (b - a)| < ε := by
    sorry -- This requires a separate equidistribution lemma based on the properties of g

  -- Define the fractional part function
  let x (n : ℕ) : ℝ := g n - ⌊g n⌋

  -- The main idea is to approximate the sum by an integral
  rw [Metric.tendsto_nhds]
  intro ε hε
  -- Since f is continuous at ξ, there exists δ such that |f y - f ξ| < ε/2 when |y - ξ| < δ
  obtain ⟨δ, hδ_pos, hδ⟩ := Metric.continuousAt_iff.1 hf_cont_at_ξ ε (by linarith)
  -- Choose δ small enough so that [ξ-δ, ξ+δ] ⊆ (0,1)
  have hδ' : δ ≤ min ξ (1 - ξ) := by
    have := hξ.1; have := hξ.2; linarith
  let δ' := min δ (min ξ (1 - ξ))
  have hδ'_pos : 0 < δ' := lt_min hδ_pos hδ'
  
  -- Using the equidistribution property
  obtain ⟨N1, hN1⟩ := h_equidist (ε / (2 * (‖f‖ + 1))) (by positivity)
  
  -- Using the convergence of x_{n_k} to ξ
  obtain ⟨N2, hN2⟩ := Metric.tendsto_atTop.1 hseq_limit δ' hδ'_pos
  
  -- Choose k large enough so that seq k ≥ N1 and k ≥ N2
  let N := max N1 (seq N2)
  obtain ⟨N3, hN3⟩ : ∃ N3, ∀ k ≥ N3, seq k ≥ N := by
    refine ⟨N2, λ k hk => ?_⟩
    have := hseq_strict_mono.id_le hk
    exact le_max_of_le_right this
    
  use N3
  intro k hk
  let n := seq k
  have hn : n ≥ N1 := by
    have := hN3 k hk
    exact le_max_of_le_left this
    
  -- Split the sum into parts where x_i is close to ξ and parts where it's not
  let close := Finset.filter (λ i => x (i + 1) ∈ Ioo (ξ - δ') (ξ + δ')) (Finset.range n)
  let far := Finset.filter (λ i => x (i + 1) ∉ Ioo (ξ - δ') (ξ + δ')) (Finset.range n)
  
  have h_union : Finset.range n = close ∪ far := by
    simp [close, far, Finset.filter_union_filter_neg_eq]
    
  have h_disjoint : Disjoint close far := by
    simp [close, far, Finset.disjoint_filter]
    
  -- Rewrite the original expression
  simp only [div_eq_mul_inv]
  rw [← Finset.sum_union h_disjoint, add_div]
  
  -- Estimate each part separately
  have h_close : |∑ i in close, f (x (i + 1)) / n - (Finset.card close / n) * f ξ| ≤ ε/2 := by
    rw [Finset.sum_div, ← mul_sum]
    have h_card : (Finset.card close : ℝ) = ∑ i in close, 1 := by simp
    rw [h_card, ← Finset.sum_sub_distrib]
    apply le_trans (Finset.abs_sum_le_sum_abs _ _) _
    simp only [abs_mul, abs_inv, abs_of_pos (Nat.cast_pos.mpr (hseq_strict_mono.id_le hk)), inv_mul_eq_div]
    apply Finset.sum_le_sum
    intro i hi
    have hx_close : x (i + 1) ∈ Ioo (ξ - δ') (ξ + δ') := by
      simpa [close] using hi
    have : |f (x (i + 1)) - f ξ| ≤ ε/2 := by
      apply hδ
      simp only [mem_Ioo] at hx_close
      rw [dist_eq_norm]
      exact lt_of_lt_of_le (abs_lt.2 ⟨by linarith, by linarith⟩) (min_le_left _ _)
    linarith
    
  have h_far_bound : |∑ i in far, f (x (i + 1)) / n| ≤ (‖f‖) * (1 - (2δ' - ε/(2*(‖f‖+1)))) := by
    sorry -- Similar estimation using the equidistribution property
    
  -- Combine the estimates
  have h_main : |(∑ i in Finset.range n, f (x (i + 1))) / n - f ξ| ≤ ε := by
    calc
      _ = |(∑ i in close, f (x (i + 1))) / n + (∑ i in far, f (x (i + 1))) / n - f ξ| := by
        congr; rw [← Finset.sum_union h_disjoint]
      _ ≤ |(∑ i in close, f (x (i + 1))) / n - (Finset.card close / n) * f ξ| 
          + |(∑ i in far, f (x (i + 1))) / n - (Finset.card far / n) * f ξ| := by
        apply abs_sub_le
      _ ≤ ε/2 + ε/2 := by
        apply add_le_add h_close
        sorry -- Complete this part using h_far_bound and equidistribution
      _ = ε := by ring
      
  exact h_main