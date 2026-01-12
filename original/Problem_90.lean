/-
Polya-Szego Problem 90
Part One, Chapter 2

Original problem:
The arbitrary numbers $a_{1}, a_{2}, \ldots, a_{n}$ and $b_{1}, b_{2}, \ldots, b_{n}$ are positive. We define

$$
\mathfrak{M}_{\varkappa}(a)=\left(a_{1}^{\varkappa}+a_{2}^{\varkappa}+\cdots+a_{n}^{\varkappa}\right)^{\frac{1}{x}} .
$$

Then

$$
\mathfrak{M}_{\varkappa}(a+b) \leqq \text { or } \geqq \mathfrak{M}_{\varkappa}(a)+\mathfrak{M}_{\varkappa}(b)
$$

according as $\varkappa \geqq 1$ or $\varkappa \leqq 1$. Equality is attained only for $a_{\nu}=\lambda b_{\nu}$, $v=1,2, \ldots, n$, or if 

Formalization notes: -- 1. We formalize Minkowski's inequality for real vectors with positive components
-- 2. 𝔐_κ(a) is the κ-norm: (∑ a_i^κ)^{1/κ}
-- 3. We handle the cases κ ≥ 1 and 0 < κ ≤ 1 separately (κ > 0 required for positivity)
-- 4. The equality condition: a_i = λ * b_i for some λ > 0, or κ = 1
-- 5. We use Finset.sum for finite sums over indices 1 to n
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.MeanInequalities
import Mathlib.Data.Real.Basic

-- Formalization notes:
-- 1. We formalize Minkowski's inequality for real vectors with positive components
-- 2. 𝔐_κ(a) is the κ-norm: (∑ a_i^κ)^{1/κ}
-- 3. We handle the cases κ ≥ 1 and 0 < κ ≤ 1 separately (κ > 0 required for positivity)
-- 4. The equality condition: a_i = λ * b_i for some λ > 0, or κ = 1
-- 5. We use Finset.sum for finite sums over indices 1 to n

theorem minkowski_inequality {n : ℕ} {κ : ℝ} (hκ_pos : 0 < κ) (a b : Fin n → ℝ) (ha_pos : ∀ i, 0 < a i) (hb_pos : ∀ i, 0 < b i) :
    let M := fun (x : Fin n → ℝ) => Real.rpow (∑ i, x i ^ κ) (1/κ)
    (if κ ≥ 1 then M (a + b) ≤ M a + M b else M (a + b) ≥ M a + M b) ∧
    (M (a + b) = M a + M b ↔ 
      κ = 1 ∨ ∃ (λ : ℝ) (hλ : 0 < λ), ∀ i, a i = λ * b i) := by
  sorry

-- Proof attempt:
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.MeanInequalities
import Mathlib.Data.Real.Basic

theorem minkowski_inequality {n : ℕ} {κ : ℝ} (hκ_pos : 0 < κ) (a b : Fin n → ℝ) (ha_pos : ∀ i, 0 < a i) (hb_pos : ∀ i, 0 < b i) :
    let M := fun (x : Fin n → ℝ) => Real.rpow (∑ i, x i ^ κ) (1/κ)
    (if κ ≥ 1 then M (a + b) ≤ M a + M b else M (a + b) ≥ M a + M b) ∧
    (M (a + b) = M a + M b ↔ 
      κ = 1 ∨ ∃ (λ : ℝ) (hλ : 0 < λ), ∀ i, a i = λ * b i) := by
  let M := fun (x : Fin n → ℝ) => Real.rpow (∑ i, x i ^ κ) (1/κ)
  have hκ_ne_zero : κ ≠ 0 := hκ_pos.ne'
  constructor
  · by_cases hκ_ge_one : κ ≥ 1
    · -- Case κ ≥ 1
      simp [hκ_ge_one]
      have h_sum_pos : 0 < ∑ i, (a i + b i) ^ κ := by
        apply Finset.sum_pos
        intro i _
        exact Real.rpow_pos_of_pos (by linarith [ha_pos i, hb_pos i]) κ
      have h_a_pos : 0 < ∑ i, a i ^ κ := Finset.sum_pos (fun i _ => Real.rpow_pos_of_pos (ha_pos i) κ)
      have h_b_pos : 0 < ∑ i, b i ^ κ := Finset.sum_pos (fun i _ => Real.rpow_pos_of_pos (hb_pos i) κ)
      rw [← Real.rpow_le_rpow_iff (by positivity) (by positivity) (inv_pos.mpr hκ_pos)]
      simp_rw [M, Real.rpow_inv_rpow_self hκ_ne_zero]
      refine le_trans ?_ (add_le_add
        (Real.LpNorm_le_LpNorm_add hκ_ge_one (fun i => a i) (fun i => b i) (fun i => (ha_pos i).le) (fun i => (hb_pos i).le))
        (fun i => (ha_pos i).le))
      simp_rw [Real.rpow_le_rpow_iff (by positivity) (by positivity) hκ_pos]
      exact Finset.sum_le_sum (fun i _ => by simp [add_rpow_le_of_pos (ha_pos i) (hb_pos i) hκ_ge_one])
    · -- Case 0 < κ ≤ 1
      simp [hκ_ge_one]
      have h_sum_pos : 0 < ∑ i, (a i + b i) ^ κ := by
        apply Finset.sum_pos
        intro i _
        exact Real.rpow_pos_of_pos (by linarith [ha_pos i, hb_pos i]) κ
      have h_a_pos : 0 < ∑ i, a i ^ κ := Finset.sum_pos (fun i _ => Real.rpow_pos_of_pos (ha_pos i) κ)
      have h_b_pos : 0 < ∑ i, b i ^ κ := Finset.sum_pos (fun i _ => Real.rpow_pos_of_pos (hb_pos i) κ)
      rw [← Real.rpow_le_rpow_iff (by positivity) (by positivity) (inv_pos.mpr hκ_pos)]
      simp_rw [M, Real.rpow_inv_rpow_self hκ_ne_zero]
      refine le_trans ?_ (Real.LpNorm_le_LpNorm_add_of_le_one (le_of_lt hκ_pos) (le_of_not_ge hκ_ge_one)
        (fun i => a i) (fun i => b i) (fun i => (ha_pos i).le) (fun i => (hb_pos i).le))
      simp_rw [Real.rpow_le_rpow_iff (by positivity) (by positivity) hκ_pos]
      exact Finset.sum_le_sum (fun i _ => by simp [add_rpow_le_of_pos (ha_pos i) (hb_pos i) (le_of_not_ge hκ_ge_one)])
  · constructor
    · intro h_eq
      by_cases hκ_eq_one : κ = 1
      · exact Or.inl hκ_eq_one
      · right
        have hκ_ge_one := Ne.lt_of_le hκ_eq_one
        have h_sum_pos : 0 < ∑ i, (a i + b i) ^ κ := by
          apply Finset.sum_pos
          intro i _
          exact Real.rpow_pos_of_pos (by linarith [ha_pos i, hb_pos i]) κ
        have h_a_pos : 0 < ∑ i, a i ^ κ := Finset.sum_pos (fun i _ => Real.rpow_pos_of_pos (ha_pos i) κ)
        have h_b_pos : 0 < ∑ i, b i ^ κ := Finset.sum_pos (fun i _ => Real.rpow_pos_of_pos (hb_pos i) κ)
        rw [← Real.rpow_inv_rpow_self hκ_ne_zero, ← Real.rpow_inv_rpow_self hκ_ne_zero, ← Real.rpow_inv_rpow_self hκ_ne_zero] at h_eq
        simp_rw [M] at h_eq
        rw [← Real.rpow_eq_rpow_iff (by positivity) (by positivity) (inv_pos.mpr hκ_pos)] at h_eq
        simp_rw [Real.rpow_inv_rpow_self hκ_ne_zero] at h_eq
        obtain ⟨λ, hλ, h⟩ := Real.LpNorm_add_eq_iff hκ_ge_one (fun i => a i) (fun i => b i) (fun i => (ha_pos i).le) (fun i => (hb_pos i).le) h_eq
        exact ⟨λ, hλ, h⟩
    · intro h
      cases' h with hκ_eq_one h_exists
      · simp [M, hκ_eq_one]
        rw [← Finset.sum_add_distrib]
        congr
        ext i
        simp [hκ_eq_one]
      · obtain ⟨λ, hλ, h⟩ := h_exists
        simp [M]
        rw [← Real.rpow_inv_rpow_self hκ_ne_zero, ← Real.rpow_inv_rpow_self hκ_ne_zero, ← Real.rpow_inv_rpow_self hκ_ne_zero]
        congr
        simp_rw [h]
        simp [mul_rpow (hλ.le) (hb_pos _), ← mul_add]
        rw [← Finset.sum_mul, mul_rpow (Finset.sum_pos (fun i _ => by positivity)).le (by positivity)]
        field_simp [hκ_ne_zero]