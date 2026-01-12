/-
Polya-Szego Problem 181
Part One, Chapter 4

Original problem:
Suppose that the common logarithms (to the base 10) of the natural numbers $1,2,3,4, \ldots$ are listed below each other in an infinite table of logarithms. Consider the digits at the $j$-th decimal place (to the right of the decimal point), $j \geqq 1$. There exists no definite probability for the distribution of the digits $0,1,2, \ldots, 9$ in this sequence. More exactly: let $v_{g}(n)$ denote the number of those integers $\leqq n$ whose logarithms show the digit $g$ at their $j$-th decimal p

Formalization notes: -- We formalize the statement that the asymptotic frequency of digit g at the j-th decimal place
-- of base-10 logarithms of natural numbers does not converge to a limit.
-- Specifically:
-- 1. log10_of k = Real.logb 10 k is the base-10 logarithm of k
-- 2. digit_at_place x j gives the j-th decimal digit of x (1-indexed from decimal point)
-- 3. v_g j g n = number of k ≤ n where digit_at_place (log10_of k) j = g
-- 4. The theorem states that for j ≥ 1, the sequence (v_g j g n)/n has no limit as n → ∞
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic

-- Formalization notes:
-- We formalize the statement that the asymptotic frequency of digit g at the j-th decimal place
-- of base-10 logarithms of natural numbers does not converge to a limit.
-- Specifically:
-- 1. log10_of k = Real.logb 10 k is the base-10 logarithm of k
-- 2. digit_at_place x j gives the j-th decimal digit of x (1-indexed from decimal point)
-- 3. v_g j g n = number of k ≤ n where digit_at_place (log10_of k) j = g
-- 4. The theorem states that for j ≥ 1, the sequence (v_g j g n)/n has no limit as n → ∞

-- Helper definition: Extract the j-th decimal digit (j ≥ 1) of a positive real number
noncomputable def digit_at_place (x : ℝ) (j : ℕ) : ℕ :=
  if h : j = 0 then 0 else
    let x' := x - ⌊x⌋  -- fractional part
    ⌊x' * (10 : ℝ) ^ j⌋.natAbs % 10

-- Count function for digit occurrences
def v_g (j : ℕ) (g : ℕ) (n : ℕ) : ℕ :=
  ((Finset.range (n + 1)).filter fun k => 
    digit_at_place (Real.logb (10 : ℝ) (k + 1)) (j + 1) = g).card

theorem problem_181 (j : ℕ) (g : ℕ) (hg : g < 10) :
    ¬∃ L : ℝ, Filter.Tendsto (fun n : ℕ => (v_g j g n : ℝ) / (n : ℝ)) 
      Filter.atTop (𝓝 L) := by
  sorry

-- Extended version with stronger statement about limit points forming an interval
theorem problem_181_strong (j : ℕ) (hpos : j > 0) (g : ℕ) (hg : g < 10) :
    let S : Set ℝ := {x | ∃ (f : ℕ → ℝ), Filter.Tendsto f Filter.atTop (𝓝 x) ∧ 
      ∀ n, f n = (v_g (j - 1) g n : ℝ) / (n : ℝ)}
    in Set.Nonempty S ∧ (∃ a b : ℝ, a < b ∧ Set.Icc a b ⊆ closure S) := by
  sorry

-- Proof attempt:
theorem problem_181 (j : ℕ) (g : ℕ) (hg : g < 10) :
    ¬∃ L : ℝ, Filter.Tendsto (fun n : ℕ => (v_g j g n : ℝ) / (n : ℝ)) 
      Filter.atTop (𝓝 L) := by
  intro h
  obtain ⟨L, hL⟩ := h
  have : ∀ ε > 0, ∃ N, ∀ n ≥ N, |(v_g j g n : ℝ)/n - L| < ε := by
    intro ε hε
    exact Filter.Tendsto.eventually (Metric.tendsto_nhds.mp hL ε hε) |>.exists
  -- The key idea is that logarithms are uniformly distributed mod 1
  -- We'll use this to show the digit frequency oscillates
  have uniform_dist : UniformContinuousOn (fun x => x - ⌊x⌋) (Set.Ici 0) := by
    apply uniformContinuousOn_subtype_iff.mpr
    refine ⟨Metric.uniformContinuous_iff.mpr fun ε hε => ⟨ε, hε, fun x y hxy => ?_⟩⟩
    simp only [dist_sub_eq_dist, Real.dist_eq] at hxy ⊢
    exact hxy
  have log_unif : TendstoUniformlyOn (fun n x => Real.logb 10 (x * (10 : ℝ)^n)) 
      (fun x => x - ⌊x⌋) atTop (Set.Ici 0) := by
    sorry -- This would require a substantial proof about uniform distribution
  -- The digit frequency would need to approach 1/10 if it converged
  have digit_freq : L = 1/10 := by
    sorry -- This would follow from uniform distribution results
  -- But we can find subsequences where the frequency is different
  obtain ⟨n₁, hn₁⟩ : ∃ n₁, (v_g j g n₁ : ℝ)/n₁ > 1/10 + 1/20 := by
    sorry -- Construct using powers of 10
  obtain ⟨n₂, hn₂⟩ : ∃ n₂, (v_g j g n₂ : ℝ)/n₂ < 1/10 - 1/20 := by
    sorry -- Construct using powers of 10^(j+1)
  -- This contradicts convergence to L = 1/10
  have h₁ := abs_lt.1 ((this (1/40) (by norm_num)) n₁ (le_max_left n₁ n₂))
  have h₂ := abs_lt.1 ((this (1/40) (by norm_num)) n₂ (le_max_right n₁ n₂))
  linarith [digit_freq, hn₁, hn₂, h₁.2, h₂.2]