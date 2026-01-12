/-
Polya-Szego Problem 132
Part One, Chapter 3

Original problem:
We assume that

$$
p_{1}(x, t), \quad p_{2}(x, t), \ldots, \quad p_{n}(x, t), \ldots
$$

are continuous functions of $x$ and $t, a \leqq_{t}^{x} \leqq b$, and that for each $n$

$$
p_{n}(x, t) \geqq 0, \quad \int_{a}^{b} p_{n}(x, t) d t=1
$$

Let $f(t)$ denote a continuous function. The functions

$$
f_{n}(x)=\int_{a}^{b} p_{n}(x, t) f(t) d t, \quad n=1,2,3, \ldots
$$

lie between the minimum and the maximum of $f(t)$ on $[a, b]$ for any $x$, $a \leqq x \leqq b$; i.e. $\min _{a \leqq x \leqq b} 

Formalization notes: -- 1. We formalize the two main conclusions of Problem 132:
--    a) f_n(x) lies between min f and max f on [a,b]
--    b) Under the given condition, f_n(x) → f(x) pointwise on (a,b)
-- 2. We use MeasureTheory to handle integrals, with continuity assumptions
-- 3. The uniform convergence condition is formalized using UniformConvergentOnFilter
-- 4. We assume f_n is defined as in the problem: f_n(x) = ∫_a^b p_n(x,t) f(t) dt
-/

import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Function.LpSpace
import Mathlib.MeasureTheory.Integral.IntegralEqOffNull
import Mathlib.Topology.UniformSpace.UniformConvergence

-- Formalization notes: 
-- 1. We formalize the two main conclusions of Problem 132:
--    a) f_n(x) lies between min f and max f on [a,b]
--    b) Under the given condition, f_n(x) → f(x) pointwise on (a,b)
-- 2. We use MeasureTheory to handle integrals, with continuity assumptions
-- 3. The uniform convergence condition is formalized using UniformConvergentOnFilter
-- 4. We assume f_n is defined as in the problem: f_n(x) = ∫_a^b p_n(x,t) f(t) dt

open Real
open Set
open Filter

theorem problem_132 {a b : ℝ} (hab : a < b) (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc a b)) 
    (p : ℕ → ℝ → ℝ → ℝ) (hp_cont : ∀ n, ContinuousOn (λ (x,t) ↦ p n x t) ((Set.Icc a b) ×ˢ (Set.Icc a b)))
    (hp_nonneg : ∀ n x t, a ≤ x → x ≤ b → a ≤ t → t ≤ b → 0 ≤ p n x t)
    (hp_integral_one : ∀ n x, a ≤ x → x ≤ b → 
        (MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Icc a b)) (λ t ↦ p n x t) = 1))
    (ε_pos : ℝ) (hε_pos : 0 < ε_pos) :
    -- Part 1: f_n(x) is bounded by min and max of f
    (∀ (n : ℕ) (x : ℝ) (hx : x ∈ Set.Icc a b), 
        let f_n : ℝ := ∫ t in a..b, p n x t * f t
        in iInf (λ x' : ℝ ↦ f x') x' ∈ Set.Icc a b ≤ f_n ∧ f_n ≤ iSup (λ x' : ℝ ↦ f x') x' ∈ Set.Icc a b) ∧
    -- Part 2: Under the additional condition, f_n converges pointwise to f on (a,b)
    (∀ (ε' : ℝ) (hε' : 0 < ε'), 
        let condition := ∀ᶠ (n : ℕ) in atTop, ∀ (x : ℝ) (hx : a + ε' ≤ x ∧ x ≤ b - ε'),
            |(∫ t in a..(x - ε'), p n x t) + (∫ t in (x + ε')..b, p n x t)| ≤ ε'
        in condition → 
        ∀ (x : ℝ) (hx : a < x ∧ x < b),
          Tendsto (λ n ↦ ∫ t in a..b, p n x t * f t) atTop (𝓝 (f x))) := by
  sorry

-- Proof attempt:
theorem problem_132 {a b : ℝ} (hab : a < b) (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc a b)) 
    (p : ℕ → ℝ → ℝ → ℝ) (hp_cont : ∀ n, ContinuousOn (λ (x,t) ↦ p n x t) ((Set.Icc a b) ×ˢ (Set.Icc a b)))
    (hp_nonneg : ∀ n x t, a ≤ x → x ≤ b → a ≤ t → t ≤ b → 0 ≤ p n x t)
    (hp_integral_one : ∀ n x, a ≤ x → x ≤ b → 
        (MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Icc a b)) (λ t ↦ p n x t) = 1))
    (ε_pos : ℝ) (hε_pos : 0 < ε_pos) :
    (∀ (n : ℕ) (x : ℝ) (hx : x ∈ Set.Icc a b), 
        let f_n : ℝ := ∫ t in a..b, p n x t * f t
        in iInf (λ x' : ℝ ↦ f x') x' ∈ Set.Icc a b ≤ f_n ∧ f_n ≤ iSup (λ x' : ℝ ↦ f x') x' ∈ Set.Icc a b) ∧
    (∀ (ε' : ℝ) (hε' : 0 < ε'), 
        let condition := ∀ᶠ (n : ℕ) in atTop, ∀ (x : ℝ) (hx : a + ε' ≤ x ∧ x ≤ b - ε'),
            |(∫ t in a..(x - ε'), p n x t) + (∫ t in (x + ε')..b, p n x t)| ≤ ε'
        in condition → 
        ∀ (x : ℝ) (hx : a < x ∧ x < b),
          Tendsto (λ n ↦ ∫ t in a..b, p n x t * f t) atTop (𝓝 (f x))) := by
  constructor
  · -- Part 1: f_n(x) is bounded by min and max of f
    intro n x hx
    let f_min := iInf (λ x' : ℝ ↦ f x') x' ∈ Set.Icc a b
    let f_max := iSup (λ x' : ℝ ↦ f x') x' ∈ Set.Icc a b
    have hf_bdd : BddBelow (f '' Icc a b) ∧ BddAbove (f '' Icc a b) :=
      ContinuousOn.image_compact_bddBelowAbove hf isCompact_Icc
    have hf_min : f_min ∈ f '' Icc a b :=
      ContinuousOn.image_Icc hf hx.1 hx.2 ▸ isCompact_Icc.iInf_mem
    have hf_max : f_max ∈ f '' Icc a b :=
      ContinuousOn.image_Icc hf hx.1 hx.2 ▸ isCompact_Icc.iSup_mem
    constructor
    · calc
        f_min = ∫ t in a..b, p n x t * f_min := by
          rw [integral_mul_const, hp_integral_one n x hx.1 hx.2, one_mul]
        _ ≤ ∫ t in a..b, p n x t * f t := by
          apply integral_mono_on
          · exact (hp_cont n).comp continuousOn_prod_left hx
          · exact continuousOn_const.mul hf
          · intro t ht
            exact mul_le_mul_of_nonneg_left (ciInf_le hf_bdd.1 ⟨t, ht⟩) (hp_nonneg n x t hx.1 hx.2 ht.1 ht.2)
          · exact le_refl _
    · calc
        ∫ t in a..b, p n x t * f t ≤ ∫ t in a..b, p n x t * f_max := by
          apply integral_mono_on
          · exact (hp_cont n).comp continuousOn_prod_left hx
          · exact continuousOn_const.mul hf
          · intro t ht
            exact mul_le_mul_of_nonneg_left (le_ciSup hf_bdd.2 ⟨t, ht⟩) (hp_nonneg n x t hx.1 hx.2 ht.1 ht.2)
          · exact le_refl _
        _ = f_max := by
          rw [integral_mul_const, hp_integral_one n x hx.1 hx.2, one_mul]
  · -- Part 2: Pointwise convergence
    intro ε' hε' hcond x hx
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨δ, hδ_pos, hδ⟩ := Metric.continuousAt_iff'.1 (hf.continuousAt (Icc_mem_nhds hx.1 hx.2)) ε hε
    let δ' := min δ (min (x - a) (b - x))
    have hδ'_pos : 0 < δ' := lt_min hδ_pos (lt_min (sub_pos.mpr hx.1) (sub_pos.mpr hx.2))
    
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hcond (min ε' δ') (lt_min hε' hδ'_pos))
    refine ⟨N, λ n hn, ?_⟩
    specialize hN n hn x ⟨hx.1.trans (le_add_of_sub_right_le (min_le_right _ _)), 
      hx.2.trans (sub_le_comm.1 (min_le_right _ _))⟩
    
    have h_int : ∫ t in a..b, p n x t * f t - f x = ∫ t in a..b, p n x t * (f t - f x) := by
      rw [integral_sub, integral_mul_const, hp_integral_one n x hx.1.le hx.2.le, one_mul, sub_self, sub_zero]
      · exact (hp_cont n).comp continuousOn_prod_left ⟨hx.1.le, hx.2.le⟩
      · exact continuousOn_const.mul hf
    
    rw [h_int, ← integral_union (Ioc_disjoint_Ioc le_rfl le_rfl) measurableSet_Ioc measurableSet_Ioc]
    have h_split : Ioc a b = Ioc a (x - min ε' δ') ∪ Ioc (x + min ε' δ') b ∪ Ioc (x - min ε' δ') (x + min ε' δ') := by
      rw [← Ioc_union_Ioc_eq_Ioc (by linarith) (by linarith), union_assoc]
    
    rw [h_split, integral_union (disjoint_union_left.1 (Ioc_disjoint_Ioc le_rfl le_rfl)).2.1 
      measurableSet_Ioc measurableSet_Ioc, integral_union (Ioc_disjoint_Ioc le_rfl le_rfl) 
      measurableSet_Ioc measurableSet_Ioc, add_assoc]
    
    refine le_trans (abs_add_three _ _ _) ?_
    refine add_le_add (add_le_add ?_ ?_) ?_
    · refine le_trans (abs_integral_le_integral_abs _) ?_
      refine integral_mono_on ?_ ?_ ?_ le_rfl
      · exact (hp_cont n).comp continuousOn_prod_left ⟨hx.1.le, hx.2.le⟩
      · exact continuousOn_const.mul (hf.sub continuousOn_const)
      · intro t ht
        exact abs_nonneg _
    · refine le_trans (abs_integral_le_integral_abs _) ?_
      refine integral_mono_on ?_ ?_ ?_ le_rfl
      · exact (hp_cont n).comp continuousOn_prod_left ⟨hx.1.le, hx.2.le⟩
      · exact continuousOn_const.mul (hf.sub continuousOn_const)
      · intro t ht
        exact abs_nonneg _
    · have h_mid : ∀ t ∈ Ioc (x - min ε' δ') (x + min ε' δ'), |f t - f x| < ε := by
        intro t ht
        apply hδ
        simp only [dist_eq_norm, norm_lt_iff]
        exact ⟨(sub_lt_sub_iff_right x).1 ht.1, (sub_lt_iff_lt_add x).1 ht.2⟩
      refine le_trans (abs_integral_le_integral_abs _) ?_
      refine le_trans (integral_mono_on ?_ ?_ ?_ le_rfl) ?_
      · exact (hp_cont n).comp continuousOn_prod_left ⟨hx.1.le, hx.2.le⟩
      · exact continuousOn_const.mul (hf.sub continuousOn_const)
      · intro t ht
        exact abs_nonneg _
      · rw [integral_mul_const]
        refine mul_le_mul_of_nonneg_right (le_of_lt h_mid) ?_
        exact integral_nonneg (λ t, hp_nonneg n x t hx.1.le hx.2.le (le_of_lt ht.1) (le_of_lt ht.2))
    
    · refine add_le_add (add_le_add ?_ ?_) (by linarith)
      · refine le_trans ?_ (le_trans hN (min_le_left _ _))
        simp only [abs_integral_le_integral_abs, integral_mul_const]
        refine integral_mono_on ?_ ?_ ?_ le_rfl
        · exact (hp_cont n).comp continuousOn_prod_left ⟨hx.1.le, hx.2.le⟩
        · exact continuousOn_const.mul (hf.sub continuousOn_const)
        · intro t ht
          exact abs_nonneg _
      · refine le_trans ?_ (le_trans hN (min_le_left _ _))
        simp only [abs_integral_le_integral_abs, integral_mul_const]
        refine integral_mono_on ?_ ?_ ?_ le_rfl
        · exact (hp_cont n).comp continuousOn_prod_left ⟨hx.1.le, hx.2.le⟩
        · exact continuousOn_const.mul (hf.sub continuousOn_const)
        · intro t ht
          exact abs_nonneg _