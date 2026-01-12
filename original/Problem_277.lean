/-
Polya-Szego Problem 277
Part Three, Chapter 6

Original problem:
We assume that the function $f(z)$ is regular and bounded in the sector $0<\arg z<\alpha$, continuous on the real axis and that $\lim _{x \rightarrow \infty} f(x)=0$, $x$ real, $x>0$. Then the limit relation

$$
\lim _{|z| \rightarrow \infty} f(z)=0
$$

holds uniformly in any sector $0 \leqq \arg z \leqq \alpha-\varepsilon<\alpha$.\\

Formalization notes: -- We formalize the statement about uniform convergence to 0 in a sector.
-- The assumptions are:
-- 1. f is holomorphic (regular) in the open sector {z | 0 < arg z < α}
-- 2. f is bounded in that sector
-- 3. f is continuous on the positive real axis (including boundary)
-- 4. f(x) → 0 as x → ∞ along the positive real axis
-- Conclusion: f(z) → 0 uniformly as |z| → ∞ in any closed subsector {z | 0 ≤ arg z ≤ α - ε}
-/

import Mathlib.Analysis.Complex.PhragmenLindelof
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log

-- Formalization notes:
-- We formalize the statement about uniform convergence to 0 in a sector.
-- The assumptions are:
-- 1. f is holomorphic (regular) in the open sector {z | 0 < arg z < α}
-- 2. f is bounded in that sector
-- 3. f is continuous on the positive real axis (including boundary)
-- 4. f(x) → 0 as x → ∞ along the positive real axis
-- Conclusion: f(z) → 0 uniformly as |z| → ∞ in any closed subsector {z | 0 ≤ arg z ≤ α - ε}

theorem problem_277 {α : ℝ} (hα : 0 < α) (hα_lt_pi : α < π) {f : ℂ → ℂ}
    (h_holo : DifferentiableOn ℂ f {z | 0 < Complex.arg z ∧ Complex.arg z < α})
    (h_bounded : ∃ M, ∀ z, 0 < Complex.arg z → Complex.arg z < α → ‖f z‖ ≤ M)
    (h_cont_on_real : ContinuousOn f {z | Complex.arg z = 0})
    (h_limit_on_real : Tendsto (λ (x : ℝ) => f x) Filter.atTop (𝓝 0)) :
    ∀ ε > 0, ∃ R > 0, ∀ z : ℂ, R ≤ Complex.abs z → 0 ≤ Complex.arg z → 
      Complex.arg z ≤ α - ε → ‖f z‖ ≤ ε := by
  sorry

-- Proof attempt:
theorem problem_277 {α : ℝ} (hα : 0 < α) (hα_lt_pi : α < π) {f : ℂ → ℂ}
    (h_holo : DifferentiableOn ℂ f {z | 0 < Complex.arg z ∧ Complex.arg z < α})
    (h_bounded : ∃ M, ∀ z, 0 < Complex.arg z → Complex.arg z < α → ‖f z‖ ≤ M)
    (h_cont_on_real : ContinuousOn f {z | Complex.arg z = 0})
    (h_limit_on_real : Tendsto (λ (x : ℝ) => f x) Filter.atTop (𝓝 0)) :
    ∀ ε > 0, ∃ R > 0, ∀ z : ℂ, R ≤ Complex.abs z → 0 ≤ Complex.arg z → 
      Complex.arg z ≤ α - ε → ‖f z‖ ≤ ε := by
  intro ε hε
  -- First handle the case when ε ≥ α
  by_cases hεα : α ≤ ε
  · obtain ⟨M, hM⟩ := h_bounded
    use 1, zero_lt_one
    intro z _ harg _
    exact hM z (by linarith [harg, hεα]) (by linarith [harg, hα])
  
  -- Main case: ε < α
  push_neg at hεα
  let β := π / α
  have hβ : 1 < β := by
    rw [← div_lt_iff hα, div_one]
    exact hα_lt_pi
  
  -- Apply Phragmen-Lindelöf principle
  obtain ⟨R, hR⟩ := Complex.PhragmenLindelof.horizontal_strip hβ h_holo h_bounded
    (fun z hz => h_cont_on_real z hz) h_limit_on_real ε hε
  
  -- Adjust R to work for our sector
  refine ⟨R, hR.1, ?_⟩
  intro z hRz harg0 hargαε
  -- Rotate the sector to match Phragmen-Lindelöf's horizontal strip
  let w := z ^ (π / (2 * α))
  have hw : ‖f z‖ = ‖f (w ^ (2 * α / π))‖ := by
    simp [w]
    congr 1
    rw [← Complex.cpow_mul]
    · simp [← div_div, div_self (ne_of_gt hα)]
    · exact Complex.ofReal_ne_zero.mpr (ne_of_gt (div_pos Real.pi_pos (mul_pos two_pos hα)))
  
  rw [hw]
  apply hR.2 w
  · simp [w]
    rw [Complex.norm_eq_abs, Complex.abs_cpow_eq_rpow_re_of_pos (Complex.abs.pos hRz.ne')]
    simp [Real.rpow_nonneg_of_nonneg (Complex.abs.nonneg _)]
    exact le_of_lt (Real.rpow_lt_rpow (by norm_num) hRz hβ)
  
  · simp [w, Complex.arg_cpow]
    have : 0 ≤ Complex.arg z := harg0
    have : Complex.arg z ≤ α - ε := hargαε
    rw [mul_comm, mul_div_assoc, mul_div_cancel_left _ (ne_of_gt Real.pi_pos)]
    constructor <;> linarith