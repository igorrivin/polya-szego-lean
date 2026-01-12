/-
Polya-Szego Problem 81.2
Part One, Chapter 2

Original problem:
The functions $f(x)$ and $g(x)$ and the numbers $\alpha$ and $\beta$ are positive,

$$
\alpha+\beta=1,
$$

and the functions are integrable in the interval $\left[x_{1}, x_{2}\right]$. Then

$$
\int_{x_{1}}^{x_{2}}[f(x)]^{x}[g(x)]^{\beta} d x \leqq\left[\int_{x_{1}}^{x_{2}} f(x) d x\right]^{\alpha}\left[\int_{x_{1}}^{x_{2}} g(x) d x\right]^{\beta}
$$

(For the particular case where $\alpha=\beta$ see 81.)\\

Formalization notes: -- 1. We formalize the inequality for real-valued functions on a closed interval [x₁, x₂]
-- 2. We assume f and g are positive and integrable on [x₁, x₂]
-- 3. α and β are positive reals with α + β = 1
-- 4. The inequality uses the weighted geometric mean form of Hölder's inequality
-- 5. We use `∫ x in x₁..x₂, ...` for the definite integral notation
-- 6. The inequality becomes an equality when f and g are proportional
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Integrable
import Mathlib.MeasureTheory.Integral.IntervalIntegral

-- Formalization notes:
-- 1. We formalize the inequality for real-valued functions on a closed interval [x₁, x₂]
-- 2. We assume f and g are positive and integrable on [x₁, x₂]
-- 3. α and β are positive reals with α + β = 1
-- 4. The inequality uses the weighted geometric mean form of Hölder's inequality
-- 5. We use `∫ x in x₁..x₂, ...` for the definite integral notation
-- 6. The inequality becomes an equality when f and g are proportional

theorem problem_81_2 {x₁ x₂ : ℝ} (hx : x₁ ≤ x₂) {f g : ℝ → ℝ} (hf : ∀ x, x₁ ≤ x → x ≤ x₂ → 0 < f x)
    (hg : ∀ x, x₁ ≤ x → x ≤ x₂ → 0 < g x) (hf_int : IntervalIntegrable f volume x₁ x₂)
    (hg_int : IntervalIntegrable g volume x₁ x₂) {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) 
    (hsum : α + β = 1) :
    ∫ x in x₁..x₂, (f x) ^ α * (g x) ^ β ≤ 
    (∫ x in x₁..x₂, f x) ^ α * (∫ x in x₁..x₂, g x) ^ β := by
  sorry

-- Proof attempt:
theorem problem_81_2 {x₁ x₂ : ℝ} (hx : x₁ ≤ x₂) {f g : ℝ → ℝ} (hf : ∀ x, x₁ ≤ x → x ≤ x₂ → 0 < f x)
    (hg : ∀ x, x₁ ≤ x → x ≤ x₂ → 0 < g x) (hf_int : IntervalIntegrable f volume x₁ x₂)
    (hg_int : IntervalIntegrable g volume x₁ x₂) {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) 
    (hsum : α + β = 1) :
    ∫ x in x₁..x₂, (f x) ^ α * (g x) ^ β ≤ 
    (∫ x in x₁..x₂, f x) ^ α * (∫ x in x₁..x₂, g x) ^ β := by
  -- Define p and q as Hölder conjugates (1/α and 1/β)
  let p := 1 / α
  let q := 1 / β
  have hp : 1 < p := by
    rw [← one_div_lt_one_div hα]
    simp [hsum, hβ]
  have hq : 1 < q := by
    rw [← one_div_lt_one_div hβ]
    simp [hsum, hα]
  have hp_pos : 0 < p := by linarith
  have hq_pos : 0 < q := by linarith
  have hpq : 1/p + 1/q = 1 := by
    rw [← hsum]
    simp [p, q]
    field_simp [hα.ne', hβ.ne']
    ring

  -- Apply Hölder's inequality
  have := intervalIntegral.holder hx hf_int hg_int hp_pos hq_pos hpq
  simp_rw [Real.rpow_mul (by positivity), Real.rpow_one] at this
  refine le_trans ?_ this
  apply intervalIntegral.integral_mono_on hx
  · exact (hf_int.pow α).mul (hg_int.pow β)
  · exact (hf_int.pow_const α).mul (hg_int.pow_const β)
  · intro x hx'
    rw [← Real.mul_rpow]
    · apply Real.rpow_le_rpow
      · exact mul_pos (hf x hx'.1 hx'.2) (hg x hx'.1 hx'.2)
      · rfl
      · positivity
    · exact (hf x hx'.1 hx'.2).le
    · exact (hg x hx'.1 hx'.2).le