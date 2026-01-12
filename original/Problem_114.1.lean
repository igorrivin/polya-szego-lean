/-
Polya-Szego Problem 114.1
Part One, Chapter 3

Original problem:
Construct a function $f(x)$ that takes positive values and is bounded and integrable in any finite subinterval of $[0, \infty)$ and such that

$$
\int_{0}^{\infty}[f(x)]^{\alpha} d x
$$

converges for $\alpha=1$ but diverges for any real value of $\alpha$ different from 1 .\\

Formalization notes: -- 1. We formalize the existence of such a function f: ℝ → ℝ
-- 2. We use `IntervalIntegrable` to capture integrability on finite intervals
-- 3. We use `Tendsto (λ b ↦ ∫ x in 0..b, (f x)^α) atTop (𝓝 L)` for convergence of improper integrals
-- 4. We require f to be positive-valued: ∀ x ≥ 0, f x > 0
-- 5. We require boundedness on each finite interval: ∀ a b, 0 ≤ a ≤ b → ∃ M, ∀ x ∈ Set.Icc a b, |f x| ≤ M
-- 6. The condition "α = 1" means specifically α = 1, not α ≈ 1
-- 7. We formalize: integral converges at α=1, diverges for all other real α
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Integral.IntervalIntegral
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Integral.IntervalIntegral

-- Formalization notes:
-- 1. We formalize the existence of such a function f: ℝ → ℝ
-- 2. We use `IntervalIntegrable` to capture integrability on finite intervals
-- 3. We use `Tendsto (λ b ↦ ∫ x in 0..b, (f x)^α) atTop (𝓝 L)` for convergence of improper integrals
-- 4. We require f to be positive-valued: ∀ x ≥ 0, f x > 0
-- 5. We require boundedness on each finite interval: ∀ a b, 0 ≤ a ≤ b → ∃ M, ∀ x ∈ Set.Icc a b, |f x| ≤ M
-- 6. The condition "α = 1" means specifically α = 1, not α ≈ 1
-- 7. We formalize: integral converges at α=1, diverges for all other real α

theorem problem_114_1 : ∃ (f : ℝ → ℝ), 
    (∀ x ≥ 0, f x > 0) ∧ 
    (∀ (a b : ℝ), 0 ≤ a → a ≤ b → ∃ M : ℝ, ∀ x ∈ Set.Icc a b, |f x| ≤ M) ∧
    (∀ (a b : ℝ), 0 ≤ a → a ≤ b → IntervalIntegrable f volume a b) ∧
    (∃ (L : ℝ), Tendsto (λ b ↦ ∫ x in 0..b, f x) atTop (𝓝 L)) ∧
    (∀ (α : ℝ), α ≠ 1 → ¬∃ (L : ℝ), Tendsto (λ b ↦ ∫ x in 0..b, (f x) ^ α) atTop (𝓝 L)) := by
  sorry

-- Proof attempt:
theorem problem_114_1 : ∃ (f : ℝ → ℝ), 
    (∀ x ≥ 0, f x > 0) ∧ 
    (∀ (a b : ℝ), 0 ≤ a → a ≤ b → ∃ M : ℝ, ∀ x ∈ Set.Icc a b, |f x| ≤ M) ∧
    (∀ (a b : ℝ), 0 ≤ a → a ≤ b → IntervalIntegrable f volume a b) ∧
    (∃ (L : ℝ), Tendsto (λ b ↦ ∫ x in 0..b, f x) atTop (𝓝 L)) ∧
    (∀ (α : ℝ), α ≠ 1 → ¬∃ (L : ℝ), Tendsto (λ b ↦ ∫ x in 0..b, (f x) ^ α) atTop (𝓝 L)) := by
  let a : ℕ → ℝ := fun n => if n < 3 then 1/2 else 1/(n * (Real.log n)^2)
  
  let f : ℝ → ℝ := fun x =>
    let n := Nat.floor x + 1
    if x < n - (a n)^2 then a n else 1 / a n
  
  have h_pos : ∀ x ≥ 0, f x > 0 := by
    intro x hx
    let n := Nat.floor x + 1
    simp [f]
    split
    · exact (a n).prop
    · exact one_div_pos.mpr (a n).prop
  
  have h_bounded : ∀ (a b : ℝ), 0 ≤ a → a ≤ b → ∃ M : ℝ, ∀ x ∈ Set.Icc a b, |f x| ≤ M := by
    intro a b ha hab
    let n_start := Nat.floor a + 1
    let n_end := Nat.floor b + 1
    let M := (Finset.range (n_end + 1)).sup' (by simp) fun n => max (a n) (1 / a n)
    use M
    intro x hx
    simp [f]
    let n := Nat.floor x + 1
    have hn : n ∈ Finset.range (n_end + 1) := by
      apply Finset.mem_range_succ_iff.mpr
      exact Nat.floor_le_iff.mpr (hx.2.trans_lt (Nat.lt_floor_add_one b))
    split
    · exact (le_max_left _ _).trans (Finset.le_sup' _ _ hn)
    · exact (le_max_right _ _).trans (Finset.le_sup' _ _ hn)
  
  have h_integrable : ∀ (a b : ℝ), 0 ≤ a → a ≤ b → IntervalIntegrable f volume a b := by
    intro a b ha hab
    apply intervalIntegrable_of_bounded (f := f)
    · obtain ⟨M, hM⟩ := h_bounded a b ha hab
      exact ⟨M, hM⟩
    · apply ContinuousOn.aestronglyMeasurable
      apply ContinuousOn.piecewise
      · apply continuousOn_const
      · apply continuousOn_const
      · intro x hx
        simp only [mem_setOf_eq, not_lt]
        exact le_of_lt hx
  
  have h_converges_at_1 : ∃ (L : ℝ), Tendsto (λ b ↦ ∫ x in 0..b, f x) atTop (𝓝 L) := by
    use ∑' n : ℕ, a n
    have h_sum : Summable a := by
      apply summable_iff_hasSum.mpr
      sorry -- Need to show sum of a_n converges (using integral test)
    apply Tendsto.congr'
    · filter_upwards [Filter.atTop_basis] with b hb
      have h_int : ∫ x in 0..b, f x = ∑ n in Finset.range (Nat.floor b + 1), a n := sorry
      rw [h_int]
      simp [sum_eq_tsum_subtype]
    · exact tendsto_nhds_tsum h_sum
  
  have h_diverges_else : ∀ (α : ℝ), α ≠ 1 → ¬∃ (L : ℝ), Tendsto (λ b ↦ ∫ x in 0..b, (f x) ^ α) atTop (𝓝 L) := by
    intro α hα
    by_contra h
    obtain ⟨L, hL⟩ := h
    sorry -- Need to show integral diverges for α ≠ 1
    
  exact ⟨f, h_pos, h_bounded, h_integrable, h_converges_at_1, h_diverges_else⟩