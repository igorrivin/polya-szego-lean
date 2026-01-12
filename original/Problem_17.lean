/-
Polya-Szego Problem 17
Part Three, Chapter 1

Original problem:
If $z_{0}$ is a zero of the polynomial

$$
z^{n}+a_{1} z^{n-1}+a_{2} z^{n-2}+\cdots+a_{n}
$$

then $\left|z_{0}\right|$ is not larger than the only positive zero $\zeta$ of the polynomial $z^{n}-\left|a_{1}\right| z^{n-1}-\left|a_{2}\right| z^{n-2}-\cdots-\left|a_{n}\right|$.\\

Formalization notes: -- 1. We formalize the statement that if z₀ is a root of a polynomial P(z) = z^n + ∑ a_k z^{n-k},
--    then |z₀| ≤ ζ, where ζ is the unique positive real root of Q(z) = z^n - ∑ |a_k| z^{n-k}.
-- 2. We assume n ≥ 1 (polynomial of positive degree)
-- 3. We require that Q has exactly one positive real root
-- 4. We work over ℂ for the polynomial roots but compare with real ζ
-/

import Mathlib.Analysis.Complex.Polynomial
import Mathlib.Analysis.SpecialFunctions.Pow.Real

-- Formalization notes: 
-- 1. We formalize the statement that if z₀ is a root of a polynomial P(z) = z^n + ∑ a_k z^{n-k},
--    then |z₀| ≤ ζ, where ζ is the unique positive real root of Q(z) = z^n - ∑ |a_k| z^{n-k}.
-- 2. We assume n ≥ 1 (polynomial of positive degree)
-- 3. We require that Q has exactly one positive real root
-- 4. We work over ℂ for the polynomial roots but compare with real ζ

theorem polyaszego_17 (n : ℕ) (hn : n ≥ 1) (a : ℕ → ℂ) (z₀ : ℂ) (hroot : (Polynomial.monomial n 1 + ∑ k in Finset.Icc 1 n, C (a k) * Polynomial.monomial (n - k))).eval z₀ = 0) :
    ∃ (ζ : ℝ) (hζ : ζ > 0), 
    (∀ (z : ℝ), z > 0 → (Polynomial.monomial n (1 : ℂ) + ∑ k in Finset.Icc 1 n, C (|a k|) * Polynomial.monomial (n - k : ℕ)).eval (z : ℂ) = 0 → z = ζ) ∧
    Complex.abs z₀ ≤ ζ := by
  sorry

-- Proof attempt:
theorem polyaszego_17 (n : ℕ) (hn : n ≥ 1) (a : ℕ → ℂ) (z₀ : ℂ) (hroot : (Polynomial.monomial n 1 + ∑ k in Finset.Icc 1 n, C (a k) * Polynomial.monomial (n - k))).eval z₀ = 0) :
    ∃ (ζ : ℝ) (hζ : ζ > 0), 
    (∀ (z : ℝ), z > 0 → (Polynomial.monomial n (1 : ℂ) + ∑ k in Finset.Icc 1 n, C (|a k|) * Polynomial.monomial (n - k : ℕ)).eval (z : ℂ) = 0 → z = ζ) ∧
    Complex.abs z₀ ≤ ζ := by
  -- Define the polynomial Q(z) = z^n - ∑ |a_k| z^{n-k}
  let Q : ℝ → ℝ := fun z => z^n - ∑ k in Finset.Icc 1 n, |a k| * z^(n - k)
  
  -- Show Q has exactly one positive root (by intermediate value theorem and strict monotonicity)
  have hQ : ∃! ζ : ℝ, ζ > 0 ∧ Q ζ = 0 := by
    have h0 : Q 0 = 0 := by simp [Q]
    have hlim : Tendsto Q atTop atTop := by
      simp [Q]
      apply Tendsto.sub
      · exact tendsto_pow_atTop hn
      · apply Tendsto.sum
        intro k hk
        simp at hk
        exact tendsto_const_mul_pow_atTop (n - k) (abs_nonneg (a k))
    obtain ⟨ζ, hζ⟩ := intermediate_value_Ioo' (by linarith) hlim
    use ζ
    refine ⟨hζ, ?_⟩
    intro y hy
    have mono : StrictMonoOn Q (Set.Ici 0) := by
      apply StrictMonoOn.sub
      · exact strictMonoOn_pow hn
      · apply StrictMonoOn.sum
        intro k hk
        exact strictMonoOn_const_mul_pow (n - k) (abs_nonneg (a k))
    exact StrictMonoOn.injOn mono (by linarith) (by linarith) hy hζ.2
  
  -- Extract the unique positive root ζ
  obtain ⟨ζ, ⟨hζpos, hζroot⟩, hζuniq⟩ := hQ
  
  -- Show the main result
  refine ⟨ζ, hζpos, ?_, ?_⟩
  · -- Uniqueness of positive root
    intro z hzpos hzroot
    exact hζuniq z ⟨hzpos, hzroot⟩
  · -- Bound on |z₀|
    have hz₀ : z₀^n = -∑ k in Finset.Icc 1 n, a k * z₀^(n - k) := by
      rw [← hroot]
      simp [Polynomial.eval_add, Polynomial.eval_monomial, Polynomial.eval_sum, Polynomial.eval_mul, Polynomial.eval_C]
    have hineq : |z₀|^n ≤ ∑ k in Finset.Icc 1 n, |a k| * |z₀|^(n - k) := by
      rw [← Complex.abs.map_neg, ← hz₀]
      apply Complex.abs.sum_le
    have hQeval : Q |z₀| ≤ 0 := by
      simp [Q]
      linarith
    -- Apply intermediate value theorem argument
    by_contra h
    push_neg at h
    have hQpos : Q |z₀| > 0 := by
      apply StrictMonoOn.strictMono_of_lt (fun z => ?_) hζpos h
      · exact mono_of_strictMonoOn_Q Q hn a
      · rw [hζroot]
        exact hQeval
    linarith [hQeval, hQpos]
where
  mono_of_strictMonoOn_Q (Q : ℝ → ℝ) (hn : n ≥ 1) (a : ℕ → ℂ) : StrictMonoOn Q (Set.Ici 0) := by
    apply StrictMonoOn.sub
    · exact strictMonoOn_pow hn
    · apply StrictMonoOn.sum
      intro k hk
      exact strictMonoOn_const_mul_pow (n - k) (abs_nonneg (a k))