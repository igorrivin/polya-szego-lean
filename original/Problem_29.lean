/-
Polya-Szego Problem 29
Part One, Chapter 4

Original problem:
If $f(x)$ is monotone for $x>0, \lim _{n-\infty} \varepsilon_{n}=0, c>0, \varepsilon_{n}>\frac{c}{n}$ we find

$$
\lim _{n \rightarrow \infty} \frac{f\left(\varepsilon_{n}\right)+f\left(\varepsilon_{n}+\frac{1}{n}\right)+f\left(\varepsilon_{n}+\frac{2}{n}\right)+\cdots+f\left(\varepsilon_{n}+\frac{n-1}{n}\right)}{n}=\int_{0}^{1} f(x) d x,
$$

provided that the integral at right exists and $f(x)$ is finite at $x=1$.

\begin{enumerate}
  \setcounter{enumi}{29}
  \item Assume that the monotone func

Formalization notes: **
-/

import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Topology.Instances.Real
import Mathlib.Analysis.Calculus.FDeriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral

/-!
Problem 29 from Polya-Szego's "Problems and Theorems in Analysis"

If f(x) is monotone for x > 0, lim_{n→∞} ε_n = 0, c > 0, ε_n > c/n, then
  lim_{n→∞} [f(ε_n) + f(ε_n + 1/n) + ... + f(ε_n + (n-1)/n)] / n = ∫₀¹ f(x) dx

provided that the integral exists and f(x) is finite at x = 1.

We formalize this for monotone decreasing functions (the increasing case is similar).
We assume f is integrable on [0,1] and finite at 1.
-/

theorem problem_29 {f : ℝ → ℝ} (hf_mono : MonotoneOn f (Set.Ioi 0)) 
    {ε : ℕ → ℝ} (hε_tends_to_zero : Filter.Tendsto ε Filter.atTop (𝓝 0)) 
    (c : ℝ) (hc : c > 0) (hε_bound : ∀ n, ε n > c / (n : ℝ)) 
    (hf_integrable : IntervalIntegrable f volume 0 1) 
    (hf_finite_at_one : ∃ L, Tendsto f (𝓝[>] 1) (𝓝 L)) :
    Filter.Tendsto (λ n : ℕ => 
      (∑ k in Finset.range n, f (ε n + (k : ℝ)/n)) / (n : ℝ))
      Filter.atTop (𝓝 (∫ x in (0:ℝ)..1, f x)) := by
  sorry

-- Proof attempt:
theorem problem_29 {f : ℝ → ℝ} (hf_mono : MonotoneOn f (Set.Ioi 0)) 
    {ε : ℕ → ℝ} (hε_tends_to_zero : Filter.Tendsto ε Filter.atTop (𝓝 0)) 
    (c : ℝ) (hc : c > 0) (hε_bound : ∀ n, ε n > c / (n : ℝ)) 
    (hf_integrable : IntervalIntegrable f volume 0 1) 
    (hf_finite_at_one : ∃ L, Tendsto f (𝓝[>] 1) (𝓝 L)) :
    Filter.Tendsto (λ n : ℕ => 
      (∑ k in Finset.range n, f (ε n + (k : ℝ)/n)) / (n : ℝ))
      Filter.atTop (𝓝 (∫ x in (0:ℝ)..1, f x)) := by
  -- First show that for large enough n, ε n + (n-1)/n ≤ 1
  have h_eventually_bounded : ∀ᶠ n in Filter.atTop, ε n + (n-1)/n ≤ 1 := by
    have hc' : 0 < c := hc
    filter_upwards [Filter.eventually_gt_atTop 0, 
                    hε_tends_to_zero.eventually (gt_mem_nhds (by linarith : 0 < c/2))] 
      with n hn hεn
    have : ε n < c/2 := hεn
    have : ε n + (n-1)/n < c/2 + (n-1)/n := by linarith
    have : c/2 + (n-1)/n ≤ 1 := by
      rw [div_eq_mul_inv]
      have : (n:ℝ)⁻¹ ≤ (c/2)/(n-1) := by
        rw [div_eq_mul_inv, mul_comm]
        apply inv_le_inv_of_le (by linarith [hn])
        have : c * (n-1) ≤ (c/2) * n := by
          rw [mul_comm, mul_comm (c/2)]
          apply mul_le_mul_of_nonneg_left _ hc.le
          linarith
        linarith
      linarith
    linarith
  
  -- Restrict to these n where the sum is bounded
  apply Filter.tendsto_congr' (h_eventually_bounded.mono fun n hn => ?_)
  intro n hn
  -- Rewrite the sum as a Riemann sum
  have : (∑ k in Finset.range n, f (ε n + k/n)) / n = 
         (∑ k in Finset.range n, f (ε n + k/n)) * (1/n) := by ring
  rw [this]
  clear this
  
  -- Show this is equal to the lower Riemann sum
  have : (∑ k in Finset.range n, f (ε n + k/n)) * (1/n) = 
         lowerRiemannSum f (Finset.range n) (ε n) (1/n) := by
    simp [lowerRiemannSum, mul_comm]
  
  rw [this]
  clear this
  
  -- Show the partition is tagged and has mesh tending to 0
  have h_partition : ∀ᶠ n in Filter.atTop, 
    IsPartition (Finset.range n) (ε n) (1/n) ∧ 
    Mesh (Finset.range n) (ε n) (1/n) < c⁻¹ := by
    filter_upwards [Filter.eventually_gt_atTop 0] with n hn
    constructor
    · refine ⟨?_, ?_⟩
      · intro k hk
        rw [Finset.mem_range] at hk
        have : (k : ℝ) < n := by exact_mod_cast hk
        have : ε n + k/n < ε n + n/n := by linarith [div_lt_div_of_lt (by norm_num) this]
        rw [div_self (by exact_mod_cast hn.ne')]
        exact hn
      · intro k hk
        rw [Finset.mem_range] at hk
        have : 0 < k/n := by positivity
        linarith [hε_bound n]
    · simp [Mesh]
      rw [div_lt_iff (by exact_mod_cast hn), mul_comm]
      exact hε_bound n
  
  -- Apply the Riemann sum convergence theorem
  refine tendsto_integral_lowerRiemannSum_of_hasIntegral ?_ ?_ ?_ ?_
  · exact hf_integrable
  · filter_upwards [h_partition] with n hn
    exact hn.1
  · apply tendsto_const_div_atTop_nhds_0_nat
  · filter_upwards [h_partition] with n hn
    exact hn.2