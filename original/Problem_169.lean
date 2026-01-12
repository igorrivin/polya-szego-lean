/-
Polya-Szego Problem 169
Part One, Chapter 4

Original problem:
Determine for real $x$ the function

$$
f(x)=\lim _{n \rightarrow \infty} \frac{\cos ^{2} \pi x+\cos ^{4} 2 \pi x+\cos ^{6} 3 \pi x+\cdots+\cos ^{2 n} n \pi x}{n} .
$$

\begin{enumerate}
  \setcounter{enumi}{169}
  \item The decimal fraction
\end{enumerate}

$$
\theta=0.12345678910111213 \ldots
$$

(the natural numbers listed consecutively) represents an irrational number. According to $\mathbf{1 6 6}$ the numbers

$$
n \theta-[n \theta], \quad n=1,2,3, \ldots
$$

are everywhere dense on the int

Formalization notes: -- We formalize Problem 169 from Polya-Szego:
-- f(x) = lim_{n→∞} (1/n) * Σ_{k=1}^n cos^{2k}(kπ x)
-- The problem asks to determine this function for real x.
-- We state the theorem that f(x) = 0 for all real x, which follows from:
-- 1. Each term cos^{2k}(kπ x) is bounded between 0 and 1
-- 2. For almost all x, cos(kπ x) has modulus < 1 for large k, making cos^{2k}(kπ x) → 0
-- 3. By Cesàro mean theorem, the average of terms tending to 0 also tends to 0
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Calculus.Limits.Basic

-- Formalization notes:
-- We formalize Problem 169 from Polya-Szego:
-- f(x) = lim_{n→∞} (1/n) * Σ_{k=1}^n cos^{2k}(kπ x)
-- The problem asks to determine this function for real x.
-- We state the theorem that f(x) = 0 for all real x, which follows from:
-- 1. Each term cos^{2k}(kπ x) is bounded between 0 and 1
-- 2. For almost all x, cos(kπ x) has modulus < 1 for large k, making cos^{2k}(kπ x) → 0
-- 3. By Cesàro mean theorem, the average of terms tending to 0 also tends to 0

theorem problem_169 (x : ℝ) : 
    Tendsto (λ (n : ℕ) => (∑ k in Finset.range n, Real.cos (π * (k + 1) * x) ^ (2 * (k + 1))) / n) 
    atTop (𝓝 0) := by
  sorry

-- Proof attempt:
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Calculus.Limits.Basic
import Mathlib.Analysis.NormedSpace.Basic
import Mathlib.Topology.Instances.Real

theorem problem_169 (x : ℝ) : 
    Tendsto (λ (n : ℕ) => (∑ k in Finset.range n, Real.cos (π * (k + 1) * x) ^ (2 * (k + 1))) / n) 
    atTop (𝓝 0) := by
  -- First, we show that each term is bounded between 0 and 1
  have h_bound : ∀ (k : ℕ), 0 ≤ Real.cos (π * (k + 1) * x) ^ (2 * (k + 1)) ∧ 
                          Real.cos (π * (k + 1) * x) ^ (2 * (k + 1)) ≤ 1 := by
    intro k
    constructor
    · apply pow_nonneg
      exact Real.cos_nonneg_of_mem_Icc (by linarith [Real.cos_le_one (π * (k + 1) * x)])
    · apply pow_le_one
      exact Real.abs_cos_le_one (π * (k + 1) * x)
  
  -- The key observation is that for almost all x, the terms tend to 0
  -- We'll use that if |cos(kπx)| < 1, then cos(kπx)^(2k) → 0
  have h_tendsto_zero : ∀ᶠ (k : ℕ) in atTop, 
      Real.cos (π * (k + 1) * x) ^ (2 * (k + 1)) ≤ 1 ∧ 
      Tendsto (λ k => Real.cos (π * (k + 1) * x) ^ (2 * (k + 1))) atTop (𝓝 0) := by
    -- For irrational x/(2π), |cos(kπx)| < 1 for all k
    -- For rational x/(2π), |cos(kπx)| = 1 for infinitely many k, but still tends to 0 for others
    -- The proof uses that for irrational x, kπx mod π is dense in [0,π]
    -- Here we'll just show the general case using that the limsup is ≤ 1 and the terms tend to 0
    apply eventually_of_forall
    intro k
    constructor
    · exact (h_bound k).2
    · by_cases h : ∃ k₀, Real.cos (π * (k₀ + 1) * x) = 1 ∨ Real.cos (π * (k₀ + 1) * x) = -1
      · -- If x is rational, there are infinitely many k where cos(kπx) = ±1
        -- But for other k, |cos(kπx)| < 1 and the term tends to 0
        -- The Cesàro mean will still tend to 0 because the terms where |cos(kπx)|=1 are rare
        -- This is the harder case, but we can still show the limit is 0
        sorry -- This part requires more advanced ergodic theory arguments
      · -- For irrational x, |cos(kπx)| < 1 for all k
        have h_lt : ∀ k, |Real.cos (π * (k + 1) * x)| < 1 := by
          intro k
          apply lt_of_le_of_ne (Real.abs_cos_le_one _)
          intro h_eq
          apply h
          use k
          rw [abs_eq_one] at h_eq
          exact h_eq
        apply Tendsto.pow_const
        apply Tendsto.comp (Real.tendsto_pow_atTop_nhds_0_of_lt_one (by norm_num))
        apply Tendsto.norm
        simp [h_lt]
        exact tendsto_const_nhds
  
  -- Now apply the Cesàro mean theorem
  apply tendsto_div_of_tendsto_norm_atTop_of_neg_lt_top
  · apply Tendsto.congr' (eventually_atTop.mpr ⟨0, λ n hn => by simp⟩)
    exact tendsto_norm_atTop_zero.comp h_tendsto_zero.2
  · simp [h_bound]
  · norm_num