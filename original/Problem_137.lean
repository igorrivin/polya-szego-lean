/-
Polya-Szego Problem 137
Part One, Chapter 3

Original problem:
Let $f(x)$ denote a function that is properly integrable over $[a, b]$ ( $[0,2 \pi]$ ). Two polynomials (trigonometric polynomials), $p(x)$ and $P(x)$, can then be found for any positive $\varepsilon$ so that for $a \leqq x \leqq b(0 \leqq x \leqq 2 \pi)$

$$
p(x) \leqq f(x) \leqq P(x)
$$

and

$$
\int_{a}^{b} P(x) d x-\int_{a}^{b} p(x) d x<\varepsilon \quad\left(\int_{0}^{2 \pi} P(x) d x-\int_{0}^{2 \pi} p(x) d x<\varepsilon\right)
$$

\begin{enumerate}
  \setcounter{enumi}{137}
  \item The $n$

Formalization notes: We formalize the statement: If f is continuous on [a, b] and all its moments vanish 
(i.e., ∫_a^b f(t) * t^n dt = 0 for all n : ℕ), then f is identically zero on [a, b].
-/

import Mathlib.Analysis.Calculus.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Topology.Algebra.Polynomial

/- Formalization notes:
We formalize the statement: If f is continuous on [a, b] and all its moments vanish 
(i.e., ∫_a^b f(t) * t^n dt = 0 for all n : ℕ), then f is identically zero on [a, b].

We use:
- `ContinuousOn f (Set.uIcc a b)` for continuity on the closed interval
- `intervalIntegral` for the definite integral over [a, b]
- The conclusion is `∀ x ∈ Set.uIcc a b, f x = 0`

Note: The problem statement in the book mentions "properly integrable" functions 
and approximation by polynomials, but the core theorem we formalize is the 
moment vanishing implication for continuous functions.
-/

theorem problem_137 {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ} 
    (hf_cont : ContinuousOn f (Set.uIcc a b)) 
    (h_moments : ∀ (n : ℕ), ∫ t in a..b, f t * t ^ n = 0) :
    ∀ x ∈ Set.uIcc a b, f x = 0 := by
  sorry

-- Proof attempt:
theorem problem_137 {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ} 
    (hf_cont : ContinuousOn f (Set.uIcc a b)) 
    (h_moments : ∀ (n : ℕ), ∫ t in a..b, f t * t ^ n = 0) :
    ∀ x ∈ Set.uIcc a b, f x = 0 := by
  -- First show that the integral of f * p is 0 for any polynomial p
  have h_integral_zero : ∀ (p : ℝ[X]), ∫ t in a..b, f t * p.eval t = 0 := by
    intro p
    let p_coeffs := p.coeffs
    have : p = ∑ i in Finset.range (p.natDegree + 1), monomial i (p.coeff i) := by
      simp only [Polynomial.as_sum_range]
    rw [this]
    simp_rw [Polynomial.eval_finset_sum, mul_sum]
    rw [intervalIntegral.integral_finset_sum]
    · simp_rw [mul_comm (f _), ← mul_assoc, intervalIntegral.integral_mul_const]
      apply Finset.sum_eq_zero
      intro n _
      rw [h_moments n]
      simp
    · intro i _
      exact ContinuousOn.mul hf_cont (Polynomial.continuousOn_eval _)
  
  -- By Weierstrass, f can be uniformly approximated by polynomials on [a, b]
  obtain ⟨p, hp⟩ : ∃ (p : ℝ[X]), ∀ x ∈ Set.uIcc a b, |f x - p.eval x| ≤ 1 := by
    have := ContinuousOn.weierstrass (s := Set.uIcc a b) hf_cont 1 one_pos
    simpa using this
  
  -- Let's consider the integral of f^2
  have hf_sq_int : ∫ t in a..b, f t * f t = 0 := by
    have h_approx : ∀ ε > 0, ∃ (p : ℝ[X]), ∀ x ∈ Set.uIcc a b, |f x - p.eval x| ≤ ε := by
      intro ε hε
      obtain ⟨p, hp⟩ := ContinuousOn.weierstrass hf_cont ε hε
      exact ⟨p, fun x hx => (hp x hx).le⟩
    
    have : ∫ t in a..b, f t * f t = ∫ t in a..b, f t * (f t - p.eval t) + ∫ t in a..b, f t * p.eval t := by
      rw [← integral_add]
      · ring_nf
      · exact ContinuousOn.mul hf_cont (hf_cont.sub (Polynomial.continuousOn_eval _))
      · exact ContinuousOn.mul hf_cont (Polynomial.continuousOn_eval _)
    
    rw [this, h_integral_zero p, add_zero]
    
    -- Estimate the remaining integral
    have h_bound : |∫ t in a..b, f t * (f t - p.eval t)| ≤ ∫ t in a..b, |f t| * |f t - p.eval t| :=
      intervalIntegral.norm_integral_le_integral_norm (by continuity)
    
    have h_eps : ∀ ε > 0, |∫ t in a..b, f t * f t| ≤ ε * (b - a) * (‖f‖[Set.uIcc a b]) := by
      intro ε hε
      obtain ⟨p, hp⟩ := h_approx ε hε
      refine le_trans h_bound ?_
      refine le_trans (intervalIntegral.integral_mono_on hab ?_ ?_ (fun _ _ => le_rfl)) ?_
      · exact ContinuousOn.aestronglyMeasurable
          (ContinuousOn.mul hf_cont (ContinuousOn.sub hf_cont (Polynomial.continuousOn_eval _)))
      · exact ContinuousOn.aestronglyMeasurable
          (ContinuousOn.mul (ContinuousOn.norm hf_cont) (ContinuousOn.const _))
      · apply intervalIntegral.integral_mono_on hab
        · exact ContinuousOn.aestronglyMeasurable
            (ContinuousOn.mul (ContinuousOn.norm hf_cont) (ContinuousOn.const _))
        · exact ContinuousOn.aestronglyMeasurable (ContinuousOn.const _)
        intro x hx
        rw [mul_comm (|f x|), ← mul_assoc]
        apply mul_le_mul le_rfl (hp x hx) (norm_nonneg _) (le_trans (norm_nonneg _) ?_)
        exact norm_le_norm_of_mem_uIcc hx
    
    -- Since this holds for all ε > 0, the integral must be 0
    by_contra h
    push_neg at h
    let M := ‖f‖[Set.uIcc a b]
    have hM : 0 ≤ M := norm_nonneg _
    have hb : b - a ≥ 0 := by linarith
    have : |∫ t in a..b, f t * f t| ≤ 0 := by
      refine le_of_forall_pos_le_add (fun ε hε => ?_)
      have := h_eps (ε / ((b - a) * (M + 1))) (by positivity)
      rw [mul_assoc] at this
      refine le_trans this ?_
      rw [div_mul_cancel]
      · exact le_of_lt hε
      · exact (mul_pos hb (lt_of_lt_of_le zero_lt_one (by simp [M, hM]))).ne'
    linarith [abs_nonneg (∫ t in a..b, f t * f t)]
  
  -- Now use that the integral of f^2 is 0 to conclude f is 0
  have hf_zero : ∀ x ∈ Set.uIcc a b, f x = 0 := by
    intro x hx
    by_contra hfx
    have hfx2 : 0 < f x ^ 2 := by nlinarith [sq_nonneg (f x)]
    have h_cont : ContinuousOn (fun t => f t ^ 2) (Set.uIcc a b) :=
      ContinuousOn.pow hf_cont 2
    have h_pos : ∀ᵐ t ∂volume.restrict (Set.uIcc a b), 0 ≤ f t ^ 2 :=
      ae_of_all _ (fun _ => sq_nonneg _)
    have h_int_pos : 0 < ∫ t in a..b, f t ^ 2 := by
      refine intervalIntegral.integral_pos_of_pos_on_of_nonempty h_cont ?_ ?_
      · exact Set.nonempty_uIcc.mpr hab
      · intro t ht
        exact hfx2.trans_eq (by simp [sq, ht.1, ht.2])
    rw [hf_sq_int] at h_int_pos
    linarith
  exact hf_zero