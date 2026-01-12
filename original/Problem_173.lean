/-
Polya-Szego Problem 173
Part One, Chapter 4

Original problem:
Let $\theta$ be an irrational number, $x_{n}=n \theta-[n \theta], n=1,2,3, \ldots$ and let $\alpha_{1}, \alpha_{2}, \alpha_{3}, \ldots, \alpha_{n}, \ldots$ be a monotone decreasing sequence of positive numbers whose sum diverges. Then we find for any properly integrable function $f(x)$ on $[0,1]$ that

$$
\lim _{n \rightarrow \infty} \frac{\alpha_{1} f\left(x_{1}\right)+\alpha_{2} f\left(x_{2}\right)+\cdots+\alpha_{n} f\left(x_{n}\right)}{\alpha_{1}+\alpha_{2}+\cdots+\alpha_{n}}=\int_{0}^{1} f(x

Formalization notes: -- 1. We formalize the equidistribution part of Problem 173
-- 2. We use `Equidistributed` from Mathlib's equidistribution theory
-- 3. The sequence `xₙ = g(n) - ⌊g(n)⌋` is formalized using `Int.floor`
-- 4. Conditions on g are formalized as hypotheses
-- 5. The conclusion is that the sequence is equidistributed on [0,1]
-/

import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.NumberTheory.Equidistribution
import Mathlib.Data.Set.Pointwise.Interval

-- Formalization notes:
-- 1. We formalize the equidistribution part of Problem 173
-- 2. We use `Equidistributed` from Mathlib's equidistribution theory
-- 3. The sequence `xₙ = g(n) - ⌊g(n)⌋` is formalized using `Int.floor`
-- 4. Conditions on g are formalized as hypotheses
-- 5. The conclusion is that the sequence is equidistributed on [0,1]

theorem problem_173 {g : ℝ → ℝ} (hg_cont_diff : ContDiff ℝ 1 g) 
    (hg_mono : Monotone g) (hg_tendsto : Tendsto g atTop atTop)
    (hg_deriv_mono : ∀ t ≥ 1, MonotoneOn (deriv g) (Set.Ici t))
    (hg_deriv_tendsto : Tendsto (deriv g) atTop (𝓝 0))
    (hg_deriv_growth : Tendsto (λ t : ℝ => t * deriv g t) atTop atTop) :
    Equidistributed (Set.uIcc (0 : ℝ) 1) (λ n : ℕ => g (n : ℝ) - (Int.floor (g (n : ℝ)) : ℝ)) := by
  sorry

-- Proof attempt:
theorem problem_173 {g : ℝ → ℝ} (hg_cont_diff : ContDiff ℝ 1 g) 
    (hg_mono : Monotone g) (hg_tendsto : Tendsto g atTop atTop)
    (hg_deriv_mono : ∀ t ≥ 1, MonotoneOn (deriv g) (Set.Ici t))
    (hg_deriv_tendsto : Tendsto (deriv g) atTop (𝓝 0))
    (hg_deriv_growth : Tendsto (λ t : ℝ => t * deriv g t) atTop atTop) :
    Equidistributed (Set.uIcc (0 : ℝ) 1) (λ n : ℕ => g (n : ℝ) - (Int.floor (g (n : ℝ)) : ℝ)) := by
  -- Apply the general equidistribution criterion for sequences of the form g(n) mod 1
  apply Equidistributed.of_forall_exp_bound
  intro k hk
  have hk_ne_zero : k ≠ 0 := by rw [ne_eq, Subtype.coe_eq_zero]; exact hk
  simp_rw [Function.periodic_mod_one, Complex.exp_eq_exp_ℝ_ℂ]
  rw [show ((k : ℤ) : ℂ) = ↑(k : ℝ) by simp]
  
  -- The key is to show the exponential sum tends to 0
  have : Tendsto (fun N ↦ (∑ n in Finset.range N, exp (2 * π * Complex.I * (k * g n))) / N) atTop (𝓝 0) := by
    -- Apply the van der Corput's exponential sum estimate
    refine van_der_corput_exp_sum_tendsto_zero ?_ ?_ ?_ ?_
    · exact hg_mono
    · exact hg_tendsto
    · intro t ht
      have : DifferentiableAt ℝ g t := by
        apply ContDiffAt.differentiableAt
        exact hg_cont_diff.contDiffAt (le_refl _)
      rw [deriv_of_differentiableAt this]
      exact hg_deriv_mono t ht
    · exact hg_deriv_tendsto
    · convert hg_deriv_growth using 1
      ext t
      rw [mul_comm]
  
  -- Convert the complex exponential sum to real terms
  simp_rw [← Complex.ofReal_mul, ← Complex.ofReal_natCast, ← Complex.ofReal_sum, Complex.ofReal_div]
  have : Tendsto (fun N ↦ Complex.ofReal ((∑ n in Finset.range N, Real.cos (2 * π * k * g n)) / N)) atTop (𝓝 0) := by
    convert this using 1
    ext N
    congr 1
    apply Finset.sum_congr rfl
    intro n _
    rw [Complex.exp_eq_cos_add_I_sin, ← mul_assoc]
    simp only [mul_zero, add_zero]
  
  -- Take the real part of the limit
  rw [← Complex.tendsto_zero_iff_real_tendsto_zero] at this
  exact this