/-
Polya-Szego Problem 183
Part One, Chapter 4

Original problem:
The sequence

$$
x_{n}=a(\log n)^{\sigma}-\left[a(\log n)^{\sigma}\right], \quad n=1,2,3, \ldots
$$

is for $0<\sigma<1$ everywhere dense on the interval [ 0,1 ] but not equidistributed. [176, 179.]\\

Formalization notes: -- 1. We formalize the sequence xₙ = a(log n)^σ - ⌊a(log n)^σ⌋
-- 2. We capture the properties: 
--    a) For 0 < σ < 1, the sequence is dense in [0,1]
--    b) The sequence is not equidistributed
-- 3. We use `Int.floor` for the integer part notation [·]
-- 4. We assume a > 0 since otherwise the problem is trivial
-- 5. We use `Set.dense` for density in the interval [0,1]
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Instances.Real

-- Formalization notes:
-- 1. We formalize the sequence xₙ = a(log n)^σ - ⌊a(log n)^σ⌋
-- 2. We capture the properties: 
--    a) For 0 < σ < 1, the sequence is dense in [0,1]
--    b) The sequence is not equidistributed
-- 3. We use `Int.floor` for the integer part notation [·]
-- 4. We assume a > 0 since otherwise the problem is trivial
-- 5. We use `Set.dense` for density in the interval [0,1]

theorem problem_183 (a : ℝ) (ha : a > 0) (σ : ℝ) (hσ : 0 < σ ∧ σ < 1) :
    -- The sequence is dense in [0,1]
    (Set.range (λ (n : ℕ) => 
        let x := a * (Real.log (n + 1)) ^ σ  -- n+1 to avoid log 0
        x - (Int.floor x : ℝ))) 
    ∩ Set.Icc (0 : ℝ) 1 |>.Dense ∧
    -- The sequence is not equidistributed
    ¬ (∀ (I : Set ℝ), I = Set.Icc (0 : ℝ) 1 → 
        Filter.Tendsto 
          (λ (N : ℕ) => ((Finset.range N).filter 
            (λ n => let x := a * (Real.log (n + 1)) ^ σ - (Int.floor (a * (Real.log (n + 1)) ^ σ) : ℝ)
                    in x ∈ I)).card : ℝ) / N)
          Filter.atTop (𝓝 (Set.volume I))) := by
  sorry

-- Proof attempt:
import Mathlib.Analysis.DistributionTheory.Dirac
import Mathlib.NumberTheory.DiophantineApproximation

theorem problem_183 (a : ℝ) (ha : a > 0) (σ : ℝ) (hσ : 0 < σ ∧ σ < 1) :
    (Set.range (λ (n : ℕ) => 
        let x := a * (Real.log (n + 1)) ^ σ
        x - (Int.floor x : ℝ))) 
    ∩ Set.Icc (0 : ℝ) 1 |>.Dense ∧
    ¬ (∀ (I : Set ℝ), I = Set.Icc (0 : ℝ) 1 → 
        Filter.Tendsto 
          (λ (N : ℕ) => ((Finset.range N).filter 
            (λ n => let x := a * (Real.log (n + 1)) ^ σ - (Int.floor (a * (Real.log (n + 1)) ^ σ) : ℝ)
                    in x ∈ I)).card : ℝ) / N)
          Filter.atTop (𝓝 (Set.volume I))) := by
  constructor
  · -- Proof of density
    apply Set.dense_iff_inter_open.2
    intro U hU hU_nonempty
    obtain ⟨y, hy⟩ := hU_nonempty
    obtain ⟨ε, hε, hy_mem⟩ := Metric.isOpen_iff.1 hU y hy
    have hε' : ε > 0 := by linarith
    -- Use Weyl's criterion for density of fractional parts
    have : ∃ (n : ℕ), a * (Real.log (n + 1)) ^ σ - ⌊a * (Real.log (n + 1)) ^ σ⌋ ∈ Set.Ioo (y - ε) (y + ε) ∩ Set.Icc 0 1 := by
      -- This follows from the growth condition 0 < σ < 1 and the fact that log grows slowly
      -- We need to find n such that the fractional part is ε-close to y
      sorry -- This part requires more advanced number theory machinery
    obtain ⟨n, hn⟩ := this
    exact ⟨a * (Real.log (n + 1)) ^ σ - ⌊a * (Real.log (n + 1)) ^ σ⌋, ⟨n, rfl⟩, hn⟩
  
  · -- Proof of non-equidistribution
    intro h_eq
    -- Construct a test interval where the limit proportion differs from its length
    let I := Set.Icc (0 : ℝ) (1/2)
    have hI : I = Set.Icc 0 (1/2) := rfl
    have h_vol : Set.volume I = 1/2 := by simp [hI]
    specialize h_eq I hI
    -- The key is that the sequence clusters more towards 0 due to the sublinear growth
    have : ¬Filter.Tendsto (λ N => ((Finset.range N).filter 
            (λ n => let x := a * (Real.log (n + 1)) ^ σ - (Int.floor (a * (Real.log (n + 1)) ^ σ) : ℝ)
                    in x ∈ I)).card : ℝ) / N)
          Filter.atTop (𝓝 (1/2)) := by
      -- This would require showing the limit is > 1/2
      sorry -- Needs calculation of discrepancy
    contradiction