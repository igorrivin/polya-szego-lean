/-
Polya-Szego Problem 152
Part One, Chapter 4

Original problem:
If $L(r)$ is slowly increasing then

$$
\lim _{r \rightarrow \infty} \frac{\log L(r)}{\log r}=0
$$

\begin{enumerate}
  \setcounter{enumi}{152}
  \item If $N(r)$ denotes the counting function of the sequence $r_{1}, r_{2}, r_{3}, \ldots, r_{n}, \ldots$ and if
\end{enumerate}

$$
N(r) \sim r^{\lambda} L(r),
$$

where $L(r)$ is slowly increasing, $0<\lambda<\infty$, then $\lambda$ is the convergence exponent of the sequence $r_{1}, r_{2}, r_{3}, \ldots, r_{n}, \ldots$

A sequence $r_{1}, r_{2}, r_

Formalization notes: -- 1. We formalize the statement about slowly increasing functions L(r)
-- 2. We define "slowly increasing" as: ∀c > 0, L(cr) ∼ L(r) as r → ∞
-- 3. The theorem states that if L is slowly increasing, then log(L(r))/log(r) → 0
-- 4. For the second part about regular sequences, we formalize the relationship
--    between the counting function N(r) and the convergence exponent λ
-/

import Mathlib.Analysis.Asymptotics.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

-- Formalization notes:
-- 1. We formalize the statement about slowly increasing functions L(r)
-- 2. We define "slowly increasing" as: ∀c > 0, L(cr) ∼ L(r) as r → ∞
-- 3. The theorem states that if L is slowly increasing, then log(L(r))/log(r) → 0
-- 4. For the second part about regular sequences, we formalize the relationship
--    between the counting function N(r) and the convergence exponent λ

-- Definition: L is slowly increasing if for all c > 0, L(cr) ∼ L(r) as r → ∞
def SlowlyIncreasing (L : ℝ → ℝ) : Prop :=
  ∀ (c : ℝ) (hc : c > 0), Asymptotics.IsEquivalent (Filter.atTop : Filter ℝ) (fun r => L (c * r)) (fun r => L r)

-- Theorem 152: If L is slowly increasing, then log(L(r))/log(r) → 0 as r → ∞
theorem problem_152 (L : ℝ → ℝ) (hL_pos : ∀ r > 0, L r > 0) (hL_slow : SlowlyIncreasing L) :
    Filter.Tendsto (fun r : ℝ => Real.log (L r) / Real.log r) Filter.atTop (𝓝 0) := by
  sorry

-- Definition of counting function for a sequence (r_n)
-- We assume r_n is nonnegative and increasing to infinity
def counting_function (seq : ℕ → ℝ) (h_nonneg : ∀ n, 0 ≤ seq n) (h_increasing : ∀ m n, m ≤ n → seq m ≤ seq n) 
    (h_tends_to_infinity : Filter.Tendsto seq Filter.atTop Filter.atTop) : ℝ → ℕ :=
  fun r => Nat.card {n : ℕ | seq n ≤ r}

-- Theorem 153: If N(r) ∼ r^λ * L(r) where L is slowly increasing and 0 < λ < ∞,
-- then λ is the convergence exponent of the sequence
theorem problem_153 (seq : ℕ → ℝ) (h_nonneg : ∀ n, 0 ≤ seq n) (h_increasing : ∀ m n, m ≤ n → seq m ≤ seq n)
    (h_tends_to_infinity : Filter.Tendsto seq Filter.atTop Filter.atTop) 
    (N : ℝ → ℕ) (hN_counting : N = counting_function seq h_nonneg h_increasing h_tends_to_infinity)
    (L : ℝ → ℝ) (hL_pos : ∀ r > 0, L r > 0) (hL_slow : SlowlyIncreasing L)
    (λ : ℝ) (hλ_pos : 0 < λ) (hλ_finite : λ < ∞) 
    (h_asymptotic : Asymptotics.IsEquivalent (Filter.atTop : Filter ℝ) 
      (fun r => (N r : ℝ)) (fun r => r ^ λ * L r)) :
    -- λ is the convergence exponent, meaning:
    -- ∑_{n=1}^∞ 1/(seq n)^s converges for s > λ and diverges for s < λ
    (∀ (s : ℝ), s > λ → Summable fun n : ℕ => 1 / ((seq n) ^ s)) ∧
    (∀ (s : ℝ), 0 < s → s < λ → ¬ Summable fun n : ℕ => 1 / ((seq n) ^ s)) := by
  sorry

-- Additional theorem for the broader definition of regular sequences mentioned in the text
theorem problem_153_broad (seq : ℕ → ℝ) (h_nonneg : ∀ n, 0 ≤ seq n) (h_increasing : ∀ m n, m ≤ n → seq m ≤ seq n)
    (h_tends_to_infinity : Filter.Tendsto seq Filter.atTop Filter.atTop) 
    (N : ℝ → ℕ) (hN_counting : N = counting_function seq h_nonneg h_increasing h_tends_to_infinity)
    (L : ℝ → ℝ) (hL_pos : ∀ r > 0, L r > 0) (hL_slow : SlowlyIncreasing L)
    (λ : ℝ) (hλ_pos : 0 < λ) (hλ_finite : λ < ∞) 
    (h_asymptotic : Asymptotics.IsEquivalent (Filter.atTop : Filter ℝ) 
      (fun r => (N r : ℝ)) (fun r => r ^ λ / L r)) :
    (∀ (s : ℝ), s > λ → Summable fun n : ℕ => 1 / ((seq n) ^ s)) ∧
    (∀ (s : ℝ), 0 < s → s < λ → ¬ Summable fun n : ℕ => 1 / ((seq n) ^ s)) := by
  sorry

-- Proof attempt:
theorem problem_152 (L : ℝ → ℝ) (hL_pos : ∀ r > 0, L r > 0) (hL_slow : SlowlyIncreasing L) :
    Filter.Tendsto (fun r : ℝ => Real.log (L r) / Real.log r) Filter.atTop (𝓝 0) := by
  -- We need to show that for any ε > 0, there exists R such that for all r ≥ R,
  -- |log(L r)/log r| < ε
  simp only [Filter.tendsto_nhds_iff, Real.norm_eq_abs, abs_div]
  intro ε hε
  -- Choose c = 2 and c = 1/2 in the slowly increasing condition
  have h2 := hL_slow 2 (by norm_num)
  have h_half := hL_slow (1/2) (by linarith)
  simp only [Asymptotics.isEquivalent_iff_exists_eq_mul] at h2 h_half
  obtain ⟨φ2, hφ2, hL2⟩ := h2
  obtain ⟨φ_half, hφ_half, hL_half⟩ := h_half
  -- For large enough r, L(2r)/L(r) is between 1/2 and 2
  have h_bound : ∀ᶠ r in Filter.atTop, 1/2 ≤ L (2 * r) / L r ∧ L (2 * r) / L r ≤ 2 := by
    apply Filter.Eventually.and
    · apply Filter.eventually_of_forall
      intro r
      have := hφ2 r
      simp at this
      have := hL2 r
      simp at this
      sorry -- Need to fill in details about φ2 tending to 1
    · apply Filter.eventually_of_forall
      intro r
      have := hφ_half r
      simp at this
      have := hL_half r
      simp at this
      sorry -- Need to fill in details about φ_half tending to 1
  -- Now take logs and divide by log r
  have h_log_bound : ∀ᶠ r in Filter.atTop, -ε ≤ Real.log (L r) / Real.log r ∧ 
      Real.log (L r) / Real.log r ≤ ε := by
    sorry -- Main calculation using the bounds and properties of logarithms
  -- Get the final result
  filter_upwards [h_log_bound] with r hr
  rw [abs_lt]
  exact ⟨hr.1, hr.2⟩