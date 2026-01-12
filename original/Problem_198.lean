/-
Polya-Szego Problem 198
Part One, Chapter 5

Original problem:
The two functions $\varphi(x)$ and $f(x)$ are continuous and positive on the interval $[a, b]$. Then

$$
\lim _{n \rightarrow \infty} \sqrt[n]{\int_{a}^{b} \varphi(x)[f(x)]^{n} d x}
$$

exists and is equal to the maximum of $f(x)$ on $[a, b]$.\\

Formalization notes: We formalize the statement about the limit of the nth root of the integral.
The theorem states that for continuous positive functions φ and f on [a, b],
the limit as n → ∞ of the nth root of ∫_a^b φ(x) * (f(x))^n dx exists
and equals the maximum value of f on [a, b].
-/

import Mathlib.Analysis.Calculus.ContDiff
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/- Formalization notes:
We formalize the statement about the limit of the nth root of the integral.
The theorem states that for continuous positive functions φ and f on [a, b],
the limit as n → ∞ of the nth root of ∫_a^b φ(x) * (f(x))^n dx exists
and equals the maximum value of f on [a, b].

We use:
- `ContinuousOn` for continuity on the closed interval
- `∀ x ∈ Set.Icc a b, 0 < φ x ∧ 0 < f x` for positivity
- `∫ x in a..b, φ x * (f x) ^ n` for the Riemann integral
- `Real.log` and `Real.exp` for the nth root via logarithm
- `sSup` for the supremum (maximum) of f on [a, b]
-/

theorem problem_198 {a b : ℝ} (hab : a ≤ b) 
    {φ f : ℝ → ℝ} (hφ_cont : ContinuousOn φ (Set.Icc a b)) 
    (hf_cont : ContinuousOn f (Set.Icc a b))
    (hpos : ∀ x, x ∈ Set.Icc a b → 0 < φ x ∧ 0 < f x) :
    ∃ M : ℝ, 
      Tendsto (λ n : ℕ => Real.log (∫ x in a..b, φ x * (f x) ^ n)) atTop (𝓝 (Real.log M)) ∧
      M = sSup (f '' (Set.Icc a b)) := by
  sorry

-- Proof attempt:
theorem problem_198 {a b : ℝ} (hab : a ≤ b) 
    {φ f : ℝ → ℝ} (hφ_cont : ContinuousOn φ (Set.Icc a b)) 
    (hf_cont : ContinuousOn f (Set.Icc a b))
    (hpos : ∀ x, x ∈ Set.Icc a b → 0 < φ x ∧ 0 < f x) :
    ∃ M : ℝ, 
      Tendsto (λ n : ℕ => Real.log (∫ x in a..b, φ x * (f x) ^ n)) atTop (𝓝 (Real.log M)) ∧
      M = sSup (f '' (Set.Icc a b)) := by
  set M := sSup (f '' (Set.Icc a b))
  have hM : M ∈ f '' (Set.Icc a b) := by
    apply IsCompact.sSup_mem
    · exact (isCompact_Icc.mapsTo_continuousOn hf_cont).image isCompact_Icc
    · rcases Set.eq_empty_or_nonempty (Set.Icc a b) with h|h
      { simp [h] at hpos; contradiction }
      { simp [Set.image_nonempty, h] }
  use M
  constructor
  · -- First prove the limit statement
    have hM_pos : 0 < M := by
      rcases hM with ⟨x, hx, rfl⟩
      exact (hpos x hx).2
    have hf_le_M : ∀ x ∈ Set.Icc a b, f x ≤ M := by
      intro x hx
      apply le_csSup ((isCompact_Icc.mapsTo_continuousOn hf_cont).image isCompact_Icc).bddAbove
      exact ⟨x, hx, rfl⟩
    have hφ_lower : ∃ c, 0 < c ∧ ∀ x ∈ Set.Icc a b, c ≤ φ x := by
      have := (isCompact_Icc.mapsTo_continuousOn hφ_cont).exists_forall_le isCompact_Icc (Set.nonempty_of_mem (left_mem_Icc.mpr hab))
      rcases this with ⟨x, hx, hx'⟩
      use φ x / 2
      constructor
      · exact half_pos (hpos x hx).1
      · intro y hy
        have := hx' y hy
        exact le_of_lt (lt_of_lt_of_le (half_lt_self (hpos x hx).1) this)
    rcases hφ_lower with ⟨c, hc_pos, hc⟩
    
    -- Upper bound
    have h_upper : ∀ n, Real.log (∫ x in a..b, φ x * (f x) ^ n) ≤ Real.log ((b - a) * ‖φ‖₊ * M ^ n) := by
      intro n
      apply Real.log_le_log
      · exact integral_pos_of_pos (fun x hx => mul_pos (hpos x hx).1 (Real.rpow_pos_of_pos (hpos x hx).2 _)) hab
      · rw [intervalIntegral.integral_of_le hab]
        apply set_integral_le_of_forall_le (MeasureTheory.volume.restrict (Set.Icc a b))
        · exact (hφ_cont.mul (hf_cont.pow n)).integrableOn_Icc
        · intro x hx
          exact mul_le_mul (le_of_lt (hpos x hx).1) (Real.rpow_le_rpow (le_of_lt (hpos x hx).2) (hf_le_M x hx) (Nat.cast_nonneg n)) 
            (Real.rpow_nonneg_of_nonneg (le_of_lt (hpos x hx).2) _) (le_of_lt (hpos x hx).1)
        · simp only [MeasureTheory.volume_apply, measurableSet_Icc, Real.volume_Icc, hab, sub_nonneg]
          exact mul_le_mul_of_nonneg_right (norm_le _ (norm_nonneg _)) (Real.rpow_nonneg_of_nonneg (le_of_lt hM_pos) _)
    
    -- Lower bound
    have h_lower : ∀ ε > 0, ∃ N, ∀ n ≥ N, Real.log (c * (M - ε) ^ n * (ε/2)) ≤ Real.log (∫ x in a..b, φ x * (f x) ^ n) := by
      intro ε hε
      rcases hM with ⟨x₀, hx₀, hx₀'⟩
      have hx₀_in : x₀ ∈ Set.Icc a b := hx₀
      have hε' : ε/2 > 0 := half_pos hε
      obtain ⟨δ, hδ_pos, hδ⟩ := ContinuousOn.continuousAt hf_cont hx₀_in
      have hδ' : δ > 0 ∧ ∀ x, |x - x₀| < δ → x ∈ Set.Icc a b → |f x - M| < ε := by
        simpa [abs_sub_comm, dist_eq] using hδ (ε) hε
      let δ' := min δ (ε/2)
      have hδ'_pos : δ' > 0 := lt_min hδ'.1 hε'
      have hI : ∫ x in Set.Ioc (x₀ - δ') (x₀ + δ'), φ x * (f x) ^ n ≤ ∫ x in a..b, φ x * (f x) ^ n := by
        rw [intervalIntegral.integral_of_le hab]
        apply set_integral_mono_set
        · exact (hφ_cont.mul (hf_cont.pow n)).integrableOn_Icc
        · exact (hφ_cont.mul (hf_cont.pow n)).integrableOn_Ioc
        · exact Ioc_subset_Icc_self.trans Icc_subset_Ici_self
        · exact eventually_of_forall fun x => mul_nonneg (le_of_lt (hpos x (Set.mem_Icc.mpr ⟨le_of_lt hab, le_rfl⟩)).1) 
            (Real.rpow_nonneg_of_nonneg (le_of_lt (hpos x (Set.mem_Icc.mpr ⟨le_of_lt hab, le_rfl⟩)).2) _)
      have hM_ε : M - ε > 0 := by
        apply sub_pos_of_lt
        exact lt_of_le_of_lt (le_csSup ((isCompact_Icc.mapsTo_continuousOn hf_cont).image isCompact_Icc).bddAbove ⟨x₀, hx₀, rfl⟩) 
          (add_lt_of_abs_sub_lt_left (hδ'.2 x₀ (by simp [hδ'_pos.le]) hx₀_in))
      have h_le : ∀ n, c * (M - ε) ^ n * (2 * δ') ≤ ∫ x in Set.Ioc (x₀ - δ') (x₀ + δ'), φ x * (f x) ^ n := by
        intro n
        have h_int : ∫ x in Set.Ioc (x₀ - δ') (x₀ + δ'), φ x * (f x) ^ n ≥ ∫ x in Set.Ioc (x₀ - δ') (x₀ + δ'), c * (M - ε) ^ n := by
          apply set_integral_mono
          · exact (ContinuousOn.mul hφ_cont (hf_cont.pow n)).integrableOn_Ioc
          · exact (ContinuousOn.const_mul (continuousOn_const) (by positivity)).integrableOn_Ioc
          · intro x hx
            apply mul_le_mul_of_nonneg_right (hc x (Ioc_subset_Icc_self hx)) (by positivity)
            apply Real.rpow_le_rpow (hpos x (Ioc_subset_Icc_self hx)).2.le
            have hx_dist : |x - x₀| < δ := by
              apply lt_of_le_of_lt (le_trans (min_le_left _ _) hδ'.1)
              exact abs_sub_lt_iff.1 (Ioc_subset_Ioo_self hx).1
            exact (le_of_lt (sub_lt_iff_lt_add.1 (abs_sub_lt_iff.1 (hδ'.2 x hx_dist (Ioc_subset_Icc_self hx))).2)).le
            exact Nat.cast_nonneg n
        rw [integral_mul_const, measure_volume_Ioc, min_eq_left (sub_le_self _ (by linarith)), 
            min_eq_left (sub_le_self _ (by linarith)), Real.volume_Ioc, sub_add_sub_cancel', 
            mul_assoc, mul_comm _ (2 * δ'), ← mul_assoc]
        exact h_int
      have h_lt : ∀ n, Real.log (c * (M - ε) ^ n * (2 * δ')) ≤ Real.log (∫ x in Set.Ioc (x₀ - δ') (x₀ + δ'), φ x * (f x) ^ n) := by
        intro n
        apply Real.log_le_log
        · positivity
        · exact h_le n
      refine ⟨0, fun n hn => ?_⟩
      refine le_trans ?_ (h_lt n)
      rw [Real.log_mul, Real.log_mul, Real.log_rpow, add_assoc, add_left_comm, ← add_assoc]
      · apply le_of_eq
        ring
      · positivity
      · positivity
      · positivity
    
    -- Combine bounds to show limit
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' _ _ (h_lower) (h_upper)
    · simp_rw [Real.log_mul, Real.log_rpow hM_pos, Real.log_mul _ _ (ne_of_gt (sub_pos.2 hab)), 
        add_assoc, add_left_comm (Real.log M * n) _ _, ← add_assoc]
      apply Tendsto.add
      · apply Tendsto.add
        · exact tendsto_const_nhds
        · exact tendsto_const_nhds
      · simp_rw [mul_comm _ n]
        exact tendsto_nhds_mul_const_atTop (by simp [hM_pos]) tendsto_nat_cast_atTop_atTop
    · simp_rw [Real.log_mul, Real.log_rpow hM_pos, Real.log_mul _ _ (ne_of_gt (sub_pos.2 hab)), 
        add_assoc, add_left_comm (Real.log M * n) _ _, ← add_assoc]
      apply Tendsto.add
      · apply Tendsto.add
        · exact tendsto_const_nhds
        · exact tendsto_const_nhds
      · simp_rw [mul_comm _ n]
        exact tendsto_nhds_mul_const_atTop (by simp [hM_pos]) tendsto_nat_cast_atTop_atTop
  · rfl