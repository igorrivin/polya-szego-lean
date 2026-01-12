/-
Polya-Szego Problem 40
Part Three, Chapter 1

Original problem:
The limit points of the complex numbers

$$
\frac{1^{i \alpha}+2^{i \alpha}+3^{i \alpha}+\cdots+n^{i \alpha}}{n}, \alpha \text { real, } \alpha \gtrless 0, \quad n=1,2,3, \ldots
$$

fill out the entire circle with radius $\left(1+\alpha^{2}\right)^{-1 / 2}$ and center at the origin. [The expression in question is closely related to a sum of rectangles.]\\

Formalization notes: -- 1. We formalize: For any real α, the set of limit points of the sequence
--    s_n(α) := (1/n) * ∑_{k=1}^n k^(i*α) as n → ∞
--    is exactly the closed disk of radius (1+α²)^{-1/2} centered at 0.
-- 2. We interpret k^(i*α) as the complex exponential: exp(i*α*log(k)).
-- 3. The theorem states that the cluster points are exactly that disk.
-- 4. We use `Set.ClusterPt` for limit points in the complex plane.
-- 5. We consider α ≠ 0 for nontrivial case; α = 0 gives trivial disk radius 1.
-/

import Mathlib.Analysis.SpecialFunctions.Complex.Lemmas
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic

-- Formalization notes:
-- 1. We formalize: For any real α, the set of limit points of the sequence
--    s_n(α) := (1/n) * ∑_{k=1}^n k^(i*α) as n → ∞
--    is exactly the closed disk of radius (1+α²)^{-1/2} centered at 0.
-- 2. We interpret k^(i*α) as the complex exponential: exp(i*α*log(k)).
-- 3. The theorem states that the cluster points are exactly that disk.
-- 4. We use `Set.ClusterPt` for limit points in the complex plane.
-- 5. We consider α ≠ 0 for nontrivial case; α = 0 gives trivial disk radius 1.

theorem problem_40 (α : ℝ) (hα : α ≠ 0) :
    let s : ℕ → ℂ := fun n => 
      if n = 0 then 0 else ((Finset.range n).sum fun k => 
      ((k + 1 : ℂ) ^ (Complex.I * (α : ℂ))) / n)
    let radius := Real.sqrt ((1 + α ^ 2)⁻¹) in
    {z : ℂ | ‖z‖ ≤ radius} = 
      {z : ℂ | ClusterPt z (Filter.map s Filter.atTop)} := by
  sorry

-- Proof attempt:
theorem problem_40 (α : ℝ) (hα : α ≠ 0) :
    let s : ℕ → ℂ := fun n => 
      if n = 0 then 0 else ((Finset.range n).sum fun k => 
      ((k + 1 : ℂ) ^ (Complex.I * (α : ℂ))) / n)
    let radius := Real.sqrt ((1 + α ^ 2)⁻¹) in
    {z : ℂ | ‖z‖ ≤ radius} = 
      {z : ℂ | ClusterPt z (Filter.map s Filter.atTop)} := by
  let s' : ℕ → ℂ := fun n => (Finset.range n).sum fun k => ((k + 1 : ℂ) ^ (Complex.I * (α : ℂ)))
  have s_eq : s = fun n => if n = 0 then 0 else s' n / n := rfl
  let radius := Real.sqrt ((1 + α ^ 2)⁻¹)
  
  -- Step 1: Show the sequence is bounded by the radius
  have norm_bound : ∀ n, n ≠ 0 → ‖s n‖ ≤ radius := by
    intro n hn
    simp [s_eq, hn, norm_div, norm_eq_abs, norm_natCast]
    have : ‖s' n‖ ≤ Real.sqrt n * Real.sqrt (1 + α^2) := by
      -- This follows from the L^2 norm estimate for exponential sums
      sorry  -- Non-trivial number theory estimate needed here
    field_simp [hn]
    rw [← div_le_iff (by positivity), ← Real.sqrt_div (by positivity)]
    exact this
  
  -- Step 2: Any point in the disk is a cluster point
  have mem_disk_of_cluster : {z | ‖z‖ ≤ radius} ⊆ {z | ClusterPt z (Filter.map s Filter.atTop)} := by
    intro z hz
    -- Use Weyl's equidistribution criterion and Kronecker's theorem
    -- to show we can approximate any point in the disk
    sorry  -- Requires constructing appropriate subsequences
    
  -- Step 3: Any cluster point must be in the disk
  have cluster_of_mem_disk : {z | ClusterPt z (Filter.map s Filter.atTop)} ⊆ {z | ‖z‖ ≤ radius} := by
    intro z hz
    obtain ⟨u, hu, lim⟩ := hz.exists_seq
    have : Tendsto (fun n => ‖s (u n)‖) atTop (𝓝 ‖z‖) :=
      (Continuous.norm.tendsto _).comp lim
    refine le_of_tendsto' this fun n => ?_
    by_cases hn : u n = 0
    · simp [s_eq, hn]
      rw [norm_zero]
      positivity
    · exact norm_bound (u n) hn
  
  -- Combine both directions
  exact Set.Subset.antisymm cluster_of_mem_disk mem_disk_of_cluster