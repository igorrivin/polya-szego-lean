/-
Polya-Szego Problem 103
Part One, Chapter 3

Original problem:
Let $v_{1}, v_{2}, \ldots, v_{n}, \ldots$ be positive integers, $v_{1} \leqq v_{2} \leqq v_{3} \leqq \cdots$. The set of limit points of the sequence

$$
\frac{v_{1}}{1+v_{1}}, \frac{v_{2}}{2+v_{2}}, \ldots, \frac{v_{n}}{n+v_{n}}, \ldots
$$

consists of a closed interval (of length 0 if the limit exists).\\

Formalization notes: -- 1. We formalize v as a sequence of positive integers: ℕ → ℕ with v n ≥ 1
-- 2. The sequence is non-decreasing: ∀ n, v n ≤ v (n+1)
-- 3. We consider the sequence a_n = (v n : ℝ) / (n + v n)
-- 4. The set of limit points (cluster points) of this sequence in ℝ
-- 5. The theorem states this set is a closed interval (possibly degenerate)
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Instances.Real
import Mathlib.Data.Real.Basic

-- Formalization notes:
-- 1. We formalize v as a sequence of positive integers: ℕ → ℕ with v n ≥ 1
-- 2. The sequence is non-decreasing: ∀ n, v n ≤ v (n+1)
-- 3. We consider the sequence a_n = (v n : ℝ) / (n + v n)
-- 4. The set of limit points (cluster points) of this sequence in ℝ
-- 5. The theorem states this set is a closed interval (possibly degenerate)

theorem problem_103 (v : ℕ → ℕ) (hv_pos : ∀ n, 0 < v n) (hv_mono : ∀ n, v n ≤ v (n + 1)) :
    ∃ (a b : ℝ), a ≤ b ∧ Set.range (ClusterPt (· : ℝ)) (fun n : ℕ => (v n : ℝ) / ((n : ℝ) + v n)) = 
    Set.Icc a b := by
  sorry

-- Proof attempt:
import Mathlib.Topology.Instances.Real
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Order.Basic

theorem problem_103 (v : ℕ → ℕ) (hv_pos : ∀ n, 0 < v n) (hv_mono : ∀ n, v n ≤ v (n + 1)) :
    ∃ (a b : ℝ), a ≤ b ∧ Set.range (ClusterPt (· : ℝ)) (fun n : ℕ => (v n : ℝ) / ((n : ℝ) + v n)) = 
    Set.Icc a b := by
  let a := liminf (fun n => (v n : ℝ) / (n + v n)) atTop
  let b := limsup (fun n => (v n : ℝ) / (n + v n)) atTop
  use a, b
  refine ⟨liminf_le_limsup (by apply isBounded_iff_bddBelow_bddAbove.2 ⟨⟨0, ?_⟩, ⟨⟨1, ?_⟩⟩⟩), ?_⟩
  · intro n
    simp only [le_refl, div_nonneg_iff, Nat.cast_nonneg, add_nonneg, Nat.cast_nonneg, le_refl, or_self]
  · intro n
    have : (v n : ℝ) ≤ (n : ℝ) + (v n : ℝ) := by simp [le_add_iff_nonneg_left, Nat.cast_nonneg]
    exact div_le_one_of_le this (by positivity)
  · ext x
    constructor
    · intro hx
      rcases hx with ⟨l, hl⟩
      simp only [Filter.ClusterPt, Filter.map_neBot_iff, Filter.inf_neBot_iff, Filter.mem_inf_principal] at hl
      have h₁ : liminf (fun n => (v n : ℝ) / (n + v n)) atTop ≤ x := by
        apply liminf_le_of_frequently_le
        apply hl.frequently.mono
        intro n hn
        exact le_of_lt hn
      have h₂ : x ≤ limsup (fun n => (v n : ℝ) / (n + v n)) atTop := by
        apply le_limsup_of_frequently_le
        apply hl.frequently.mono
        intro n hn
        exact le_of_lt hn
      exact ⟨h₁, h₂⟩
    · intro hx
      simp only [Set.mem_Icc] at hx
      have h_lim : liminf (fun n => (v n : ℝ) / (n + v n)) atTop ≤ 
                   limsup (fun n => (v n : ℝ) / (n + v n)) atTop :=
        liminf_le_limsup (by apply isBounded_iff_bddBelow_bddAbove.2 ⟨⟨0, ?_⟩, ⟨⟨1, ?_⟩⟩⟩)
      · intro n
        simp only [le_refl, div_nonneg_iff, Nat.cast_nonneg, add_nonneg, Nat.cast_nonneg, le_refl, or_self]
      · intro n
        have : (v n : ℝ) ≤ (n : ℝ) + (v n : ℝ) := by simp [le_add_iff_nonneg_left, Nat.cast_nonneg]
        exact div_le_one_of_le this (by positivity)
      rcases eq_or_lt_of_le h_lim with (h_eq | h_lt)
      · have h_lim_eq : Tendsto (fun n => (v n : ℝ) / (n + v n)) atTop (𝓝 a) := by
          rw [h_eq, liminf_eq_limsup_eq_lim]
          exact tendsto_of_liminf_eq_limsup ⟨h_lim, h_eq⟩
        rw [← h_eq] at hx
        simp at hx
        have : x = a := le_antisymm hx.2 hx.1
        rw [this]
        exact ⟨a, h_lim_eq.clusterPt⟩
      · have h_liminf : ∃ᶠ n in atTop, (v n : ℝ) / (n + v n) ∈ Ioo (a - (x - a)) x := by
          apply frequently_lt_of_lt_liminf
          · apply isBounded_iff_bddBelow_bddAbove.2 ⟨⟨0, ?_⟩, ⟨⟨1, ?_⟩⟩⟩
            intro n
            simp only [le_refl, div_nonneg_iff, Nat.cast_nonneg, add_nonneg, Nat.cast_nonneg, le_refl, or_self]
          · intro n
            have : (v n : ℝ) ≤ (n : ℝ) + (v n : ℝ) := by simp [le_add_iff_nonneg_left, Nat.cast_nonneg]
            exact div_le_one_of_le this (by positivity)
          · linarith
        have h_limsup : ∃ᶠ n in atTop, (v n : ℝ) / (n + v n) ∈ Ioo x (b + (b - x)) := by
          apply frequently_gt_of_limsup_gt
          · apply isBounded_iff_bddBelow_bddAbove.2 ⟨⟨0, ?_⟩, ⟨⟨1, ?_⟩⟩⟩
            intro n
            simp only [le_refl, div_nonneg_iff, Nat.cast_nonneg, add_nonneg, Nat.cast_nonneg, le_refl, or_self]
          · intro n
            have : (v n : ℝ) ≤ (n : ℝ) + (v n : ℝ) := by simp [le_add_iff_nonneg_left, Nat.cast_nonneg]
            exact div_le_one_of_le this (by positivity)
          · linarith
        have h_cluster : ClusterPt x (𝓝 x) := by rw [clusterPt_principal_iff]
          apply Filter.inf_neBot_iff.2 ⟨?_, ?_⟩
          · apply h_liminf.mono
            intro n hn
            exact Ioo_subset_Ioc_self hn
          · apply h_limsup.mono
            intro n hn
            exact Ioo_subset_Ico_self hn
        exact ⟨x, h_cluster⟩