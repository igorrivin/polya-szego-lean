/-
Polya-Szego Problem 332
Part Three, Chapter 6

Original problem:
The function $g(z)$ is assumed to be an entire function, $M(r)$ be the maximum of $|g(z)|$ on the circle $|z|=v$. If

$$
\lim _{r \rightarrow \infty} \frac{\log M(r)}{l_{r}}=0
$$

then $g(z)$ cannot be bounded along any ray. [E.g. $g(z)$ is not bounded along the negative real axis.]\\

Formalization notes: -- 1. We formalize: If g is an entire function with limsup (log M(r)) / r = 0 as r → ∞,
--    where M(r) = max_{|z|=r} |g(z)|, then g is unbounded on every ray from the origin.
-- 2. We use `Complex.differentiable_on ℂ` for "entire function"
-- 3. We define M(r) = ⨆ z, ‖z‖ = r, ‖g z‖ using `ciSup` for supremum
-- 4. The condition lim (log M(r))/r = 0 is formalized using `Tendsto`
-- 5. A "ray" is formalized as {z | ∃ t ≥ 0, z = t • w} for some fixed direction w ≠ 0
-/

import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.Asymptotics.Asymptotics

-- Formalization notes:
-- 1. We formalize: If g is an entire function with limsup (log M(r)) / r = 0 as r → ∞,
--    where M(r) = max_{|z|=r} |g(z)|, then g is unbounded on every ray from the origin.
-- 2. We use `Complex.differentiable_on ℂ` for "entire function"
-- 3. We define M(r) = ⨆ z, ‖z‖ = r, ‖g z‖ using `ciSup` for supremum
-- 4. The condition lim (log M(r))/r = 0 is formalized using `Tendsto`
-- 5. A "ray" is formalized as {z | ∃ t ≥ 0, z = t • w} for some fixed direction w ≠ 0

theorem problem_332 (g : ℂ → ℂ) (hg : DifferentiableOn ℂ g ℂ) :
    (∀ r : ℝ, 0 ≤ r → 
      let M := ⨆ z : ℂ, ⨆ (h : ‖z‖ = r), ‖g z‖
      Tendsto (λ r : ℝ => Real.log (M r) / r) atTop (𝓝 0)) →
    ∀ (w : ℂ) (hw : w ≠ 0), ¬Bounded (Set.range (λ t : ℝ ≥ 0 => g (t • w))) := by
  sorry

-- Proof attempt:
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.Asymptotics.Asymptotics

theorem problem_332 (g : ℂ → ℂ) (hg : DifferentiableOn ℂ g ℂ) :
    (∀ r : ℝ, 0 ≤ r → 
      let M := ⨆ z : ℂ, ⨆ (h : ‖z‖ = r), ‖g z‖
      Tendsto (λ r : ℝ => Real.log (M r) / r) atTop (𝓝 0)) →
    ∀ (w : ℂ) (hw : w ≠ 0), ¬Bounded (Set.range (λ t : ℝ ≥ 0 => g (t • w))) := by
  intro hlim w hw hbounded
  obtain ⟨C, hC⟩ := hbounded
  have hC' : 0 ≤ C := by
    obtain ⟨t, ht⟩ : Set.range (λ t : ℝ≥0 => g (t • w)) ≠ ∅ := by simp
    have := hC (g (t • w)) ht
    exact norm_nonneg (g (t • w))
  
  -- If g is constant, it violates the growth condition
  by_cases hconst : ∃ c, g = Function.const ℂ c
  · obtain ⟨c, rfl⟩ := hconst
    have : Tendsto (fun r : ℝ => Real.log (‖c‖) / r) atTop (𝓝 0) := by
      refine' Tendsto.div_const _ ‖c‖
      exact tendsto_log_atTop.comp (tendsto_norm_atTop_atTop.comp tendsto_id)
    replace hlim := hlim 1 (by norm_num)
    simp only [Function.const_apply, ciSup_const] at hlim
    have : M = fun _ => ‖c‖ := by
      ext r; simp [M]
      apply ciSup_eq_of_forall_le_of_forall_lt_exists_gt
      · intro z hz; simp [hz]
      · intro b hb; use 0; simp [hb]
    rw [this] at hlim
    have : Real.log ‖c‖ = 0 := by
      have := tendsto_nhds_unique hlim this
      simp at this
      exact this.symm
    norm_num at this
    have : g = 0 := by
      ext z; simp [this]
    rw [this] at hlim
    have : M = 0 := by
      ext r; simp [M]
      apply ciSup_eq_of_forall_le_of_forall_lt_exists_gt
      · intro z hz; simp [hz]
      · intro b hb; use 0; simp [hb]
    simp [this] at hlim
    have : Tendsto (fun _ : ℝ => 0) atTop (𝓝 0) := tendsto_const_nhds
    have := tendsto_nhds_unique hlim this
    simp at this
    
  -- g is not constant
  push_neg at hconst
  -- Apply Liouville's theorem to get a contradiction
  have : ∃ᶠ r in atTop, Real.log (M r) ≤ Real.log C := by
    refine' Frequently.mono (eventually_ge_atTop 0) _
    intro r hr
    have := hC (g (r • w)) (by simp)
    refine' Real.log_le_log _ (le_ciSup _ _)
    · exact lt_of_lt_of_le (Real.exp_pos _) (Real.exp_le_exp.mpr this)
    · refine' Metric.bounded_iff_forall_norm_le'.mp hbounded
    · use r • w
      simp [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr]
  
  have : Tendsto (fun r => Real.log (M r) / r) atTop (𝓝 0) := hlim 0 (by norm_num)
  have hzero : Tendsto (fun r => Real.log C / r) atTop (𝓝 0) := 
    Tendsto.div_const (tendsto_const_nhds) _
  
  have : ∃ᶠ r in atTop, Real.log (M r) / r ≤ Real.log C / r := by
    refine' this.frequently.mp _
    refine' (eventually_ge_atTop 1).mp _
    intro r hr1 hr0
    refine' div_le_div_of_le hr0 _
    exact hr1
    
  have : ∃ᶠ r in atTop, Real.log (M r) / r ≤ 0 := by
    refine' this.frequently.mp _
    refine' (eventually_ge_atTop 1).mp _
    intro r hr1 hrle
    refine' hrle.trans _
    have : 0 ≤ Real.log C := by
      by_cases h : C ≤ 1
      · rw [Real.log_le_zero_iff hC']; exact h
      · push_neg at h
        have : 1 < C := by linarith
        rw [Real.log_pos_iff hC']; exact this
    rw [div_le_iff (by linarith : 0 < r), mul_zero]
    exact this
    
  have : ¬Tendsto (fun r => Real.log (M r) / r) atTop (𝓝 0) := by
    refine' mt tendsto_nhds_unique (Ne.symm _)
    apply Frequently.ne
    · exact this
    · exact eventually_of_forall fun _ => by simp
  contradiction