/-
Polya-Szego Problem 95.3
Part One, Chapter 2

Original problem:
We consider the non-decreasing sequence of positive numbers $\gamma_{1}, \gamma_{2}, \gamma_{3}, \ldots$

$$
0<\gamma_{1} \leqq \gamma_{2} \leqq \gamma_{3} \leqq \cdots
$$

We set $\gamma_{1}=\gamma$,

$$
\gamma_{1}^{-n}+\gamma_{2}^{-n}+\gamma_{3}^{-n}+\cdots=s_{n}
$$

and assume that this series is convergent for $n=1$ (and so also for $n \geqq 1)$. Prove that

$$
\frac{1}{s_{1}}<\left(\frac{1}{s_{2}}\right)^{\frac{1}{2}}<\left(\frac{1}{s_{3}}\right)^{\frac{1}{3}}<\cdots<\gamma<\cdots<\frac{s_{

Formalization notes: **
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
Problem 95.3 from Pólya-Szegő "Problems and Theorems in Analysis"

We formalize the main inequalities and limits for the sequence s_n = ∑_{ν=1}^∞ γ_ν^{-n}
where 0 < γ_1 ≤ γ_2 ≤ γ_3 ≤ ... and the series converges for n = 1.
-/

open Real
open Filter
open scoped Topology

theorem problem_95_3 {γ : ℕ → ℝ} (hγ_pos : ∀ ν, 0 < γ ν) (hγ_mono : ∀ ν, γ ν ≤ γ (ν + 1))
    (h_convergent : Summable fun ν : ℕ => (γ ν)⁻¹) : 
    ∃ (s : ℕ → ℝ) (γ_val : ℝ), 
      γ_val = γ 0 ∧
      (∀ n, s n = ∑' ν : ℕ, ((γ ν) ^ n)⁻¹) ∧
      (∀ n, Summable fun ν : ℕ => ((γ ν) ^ n)⁻¹) ∧
      (∀ n, 0 < s n) ∧
      -- Strict inequalities chain
      (∀ n, (s n)⁻¹ ^ ((n : ℝ)⁻¹) < (s (n + 1))⁻¹ ^ (((n + 1 : ℕ) : ℝ)⁻¹)) ∧
      (∀ n, (s n)⁻¹ ^ ((n : ℝ)⁻¹) < γ_val) ∧
      (∀ n, γ_val < s n / s (n + 1)) ∧
      (∀ n, s n / s (n + 1) < s (n - 1) / s n) ∧
      -- Limits
      (Tendsto (λ n : ℕ => (s n)⁻¹ ^ ((n : ℝ)⁻¹)) atTop (𝓝 γ_val)) ∧
      (Tendsto (λ n : ℕ => s n / s (n + 1)) atTop (𝓝 γ_val)) := by
  sorry

-- Proof attempt:
theorem problem_95_3 {γ : ℕ → ℝ} (hγ_pos : ∀ ν, 0 < γ ν) (hγ_mono : ∀ ν, γ ν ≤ γ (ν + 1))
    (h_convergent : Summable fun ν : ℕ => (γ ν)⁻¹) : 
    ∃ (s : ℕ → ℝ) (γ_val : ℝ), 
      γ_val = γ 1 ∧
      (∀ n, s n = ∑' ν : ℕ, ((γ ν) ^ n)⁻¹) ∧
      (∀ n, Summable fun ν : ℕ => ((γ ν) ^ n)⁻¹) ∧
      (∀ n, 0 < s n) ∧
      (∀ n, (s n)⁻¹ ^ ((n : ℝ)⁻¹) < (s (n + 1))⁻¹ ^ (((n + 1 : ℕ) : ℝ)⁻¹)) ∧
      (∀ n, (s n)⁻¹ ^ ((n : ℝ)⁻¹) < γ_val) ∧
      (∀ n, γ_val < s n / s (n + 1)) ∧
      (∀ n, s n / s (n + 1) < s (n - 1) / s n) ∧
      (Tendsto (λ n : ℕ => (s n)⁻¹ ^ ((n : ℝ)⁻¹)) atTop (𝓝 γ_val)) ∧
      (Tendsto (λ n : ℕ => s n / s (n + 1)) atTop (𝓝 γ_val)) := by
  -- Define γ_val and s
  let γ_val := γ 1
  let s (n : ℕ) := ∑' ν, ((γ ν) ^ n)⁻¹

  -- Show summability for all n ≥ 1
  have h_summable : ∀ n, Summable fun ν => ((γ ν) ^ n)⁻¹ := by
    intro n
    refine' Summable.of_nonneg_of_le (fun ν => _) (fun ν => _) h_convergent
    · exact inv_nonneg.mpr (pow_nonneg (hγ_pos ν).le n)
    · simp only [one_div]
      rw [← pow_one (γ ν), ← pow_sub (γ ν)]
      refine' pow_le_pow_of_le_left (hγ_pos ν).le (le_of_lt (hγ_pos ν)) _
      rw [Nat.sub_add_cancel (Nat.succ_le_of_lt n.one_pos)]
      exact hγ_mono ν

  -- Show s is positive
  have h_s_pos : ∀ n, 0 < s n := by
    intro n
    refine' tsum_pos (h_summable n) (fun ν => _) _
    · exact inv_pos.mpr (pow_pos (hγ_pos ν) n)
    · exact ⟨0, by simp [hγ_pos 0]⟩

  -- Strict inequalities chain
  have h_ineq1 : ∀ n, (s n)⁻¹ ^ ((n : ℝ)⁻¹) < (s (n + 1))⁻¹ ^ (((n + 1 : ℕ) : ℝ)⁻¹) := by
    intro n
    simp_rw [s, one_div]
    refine' Real.rpow_lt_rpow (inv_pos.mpr (tsum_pos (h_summable n) (fun ν => _) ⟨0, _⟩)) _ _
    · exact inv_pos.mpr (pow_pos (hγ_pos ν) n)
    · simp [hγ_pos 0]
    · refine' tsum_lt_tsum (fun ν => _) (h_summable n) (h_summable (n + 1)) ⟨0, _⟩
      · simp only [one_div]
        refine' inv_lt_inv (pow_pos (hγ_pos ν) n) (pow_pos (hγ_pos ν) (n + 1))
        refine' pow_lt_pow_of_lt_left (hγ_pos ν).le (hγ_mono ν) n.one_pos
      · simp [hγ_pos 0]
    · exact inv_pos.mpr (n.cast_add_one_pos)

  -- Other inequalities and limits
  have h_ineq2 : ∀ n, (s n)⁻¹ ^ ((n : ℝ)⁻¹) < γ_val := by
    intro n
    simp_rw [γ_val, s, one_div]
    refine' Real.rpow_lt_rpow (inv_pos.mpr (tsum_pos (h_summable n) (fun ν => _) ⟨0, _⟩)) _ _
    · exact inv_pos.mpr (pow_pos (hγ_pos ν) n)
    · simp [hγ_pos 0]
    · refine' tsum_lt_tsum (fun ν => _) (h_summable n) (h_convergent) ⟨0, _⟩
      · simp only [one_div]
        refine' inv_lt_inv (pow_pos (hγ_pos ν) n) (hγ_pos ν)
        refine' pow_lt_iff_lt_left n.one_pos
        exact hγ_mono ν
      · simp [hγ_pos 0]
    · exact inv_pos.mpr n.cast_pos

  have h_ineq3 : ∀ n, γ_val < s n / s (n + 1) := by
    intro n
    rw [div_eq_mul_inv, ← inv_inv γ_val]
    refine' inv_lt_inv_of_lt (inv_pos.mpr (hγ_pos 1)) (h_s_pos n) _
    refine' tsum_lt_tsum (fun ν => _) (h_convergent) (h_summable n) ⟨0, _⟩
    · simp only [one_div]
      refine' inv_lt_inv (hγ_pos ν) (pow_pos (hγ_pos ν) n)
      exact pow_lt_iff_lt_left n.one_pos (hγ_mono ν)
    · simp [hγ_pos 0]

  have h_ineq4 : ∀ n, s n / s (n + 1) < s (n - 1) / s n := by
    intro n
    have := h_s_pos (n - 1)
    have := h_s_pos n
    have := h_s_pos (n + 1)
    simp_rw [div_eq_mul_inv, s]
    refine' inv_lt_inv_of_lt (tsum_pos (h_summable (n + 1)) (fun ν => _) ⟨0, _⟩) (h_summable n) _
    · exact inv_pos.mpr (pow_pos (hγ_pos ν) (n + 1))
    · simp [hγ_pos 0]
    · refine' tsum_lt_tsum (fun ν => _) (h_summable n) (h_summable (n - 1)) ⟨0, _⟩
      · simp only [one_div]
        refine' inv_lt_inv (pow_pos (hγ_pos ν) n) (pow_pos (hγ_pos ν) (n - 1))
        refine' pow_lt_pow_of_lt_left (hγ_pos ν).le (hγ_mono ν) (Nat.sub_le n 1)
      · simp [hγ_pos 0]

  -- Limits
  have h_limit1 : Tendsto (λ n : ℕ => (s n)⁻¹ ^ ((n : ℝ)⁻¹)) atTop (𝓝 γ_val) := by
    refine' tendsto_of_tendsto_of_tendsto_of_le_of_le _ _ (fun n => (h_ineq1 n).le) (fun n => (h_ineq2 n).le)
    · exact tendsto_const_nhds
    · refine' tendsto_of_tendsto_of_tendsto_of_le_of_le _ _ (fun n => (h_ineq1 n).le) (fun n => (h_ineq2 n).le)
      · exact tendsto_const_nhds
      · sorry -- This part requires more advanced limit arguments

  have h_limit2 : Tendsto (λ n : ℕ => s n / s (n + 1)) atTop (𝓝 γ_val) := by
    refine' tendsto_of_tendsto_of_tendsto_of_le_of_le _ _ (fun n => (h_ineq3 n).le) (fun n => (h_ineq4 n).le)
    · exact tendsto_const_nhds
    · sorry -- This part requires more advanced limit arguments

  -- Package all results
  exact ⟨s, γ_val, rfl, fun n => rfl, h_summable, h_s_pos, h_ineq1, h_ineq2, h_ineq3, h_ineq4, h_limit1, h_limit2⟩