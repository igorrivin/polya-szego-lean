/-
Polya-Szego Problem 222
Part One, Chapter 5

Original problem:
Assume that $a>0,0<\mu<1$ and that $M_{n}$ is the maximum of $e^{-\left(x+a x^{\mu}\right)} x^{n}$ in the interval $(0,+\infty)$. We find

$$
\lim _{n \rightarrow \infty}\left(\frac{M_{n}}{n!}\right)^{n-\mu}=e^{-a}
$$

Formalization notes: We formalize Part One of Problem 222 from Polya-Szego:
Given a > 0, 0 < μ < 1, let Mₙ be the supremum (maximum) of 
fₙ(x) = exp(-(x + a * x^μ)) * x^n on (0, ∞). Then:
  lim_{n → ∞} (Mₙ / n!)^{n^{-μ}} = exp(-a)
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Asymptotics.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Exp

/- Formalization notes:
We formalize Part One of Problem 222 from Polya-Szego:
Given a > 0, 0 < μ < 1, let Mₙ be the supremum (maximum) of 
fₙ(x) = exp(-(x + a * x^μ)) * x^n on (0, ∞). Then:
  lim_{n → ∞} (Mₙ / n!)^{n^{-μ}} = exp(-a)

We make the following decisions:
1. Use `Real` for all parameters since the problem is in ℝ
2. Use `Real.log` and `Real.exp` for logarithm and exponential
3. Represent Mₙ using `sSup` from `Set` since it's the supremum over (0, ∞)
4. Formalize the limit using `Filter.Tendsto` with `n → ∞` (strictly speaking, n → ∞ through ℕ)
5. Use `Real.rpow` for the exponent n^{-μ} (which is n ^ (-μ))
6. The factorial is represented using `Nat.factorial` from Mathlib
7. We need `μ < 1` to ensure n^{-μ} → 0 as n → ∞
-/

open Real
open Set
open Filter
open scoped Topology

theorem problem_222_part_one {a : ℝ} (ha : a > 0) {μ : ℝ} (hμ1 : 0 < μ) (hμ2 : μ < 1) :
    Tendsto (fun (n : ℕ) => 
      (((sSup (range (fun (x : ℝ) => Real.exp (-(x + a * x ^ μ)) * x ^ n) 
            (by exact ⟨0, mem_Ioi.mpr (show (0 : ℝ) < 0 from by linarith), ?_⟩)?_) : ℝ) 
        / (Nat.factorial n : ℝ)) ^ ((n : ℝ) ^ (-μ))) 
      ) 
    atTop (𝓝 (Real.exp (-a))) := by
  -- The supremum Mₙ = sup_{x>0} exp(-(x + a*x^μ)) * x^n
  -- We represent this as sSup of the range of the function on (0, ∞)
  -- The actual proof would involve the asymptotic analysis shown in the book
  sorry

-- Proof attempt:
theorem problem_222_part_one {a : ℝ} (ha : a > 0) {μ : ℝ} (hμ1 : 0 < μ) (hμ2 : μ < 1) :
    Tendsto (fun (n : ℕ) => 
      (((sSup (range (fun (x : ℝ) => Real.exp (-(x + a * x ^ μ)) * x ^ n) 
            (by exact ⟨0, mem_Ioi.mpr (show (0 : ℝ) < 0 from by linarith), ?_⟩)?_) : ℝ) 
        / (Nat.factorial n : ℝ)) ^ ((n : ℝ) ^ (-μ))) 
      ) 
    atTop (𝓝 (Real.exp (-a))) := by
  -- Step 1: Define the maximizing point xₙ
  have hxₙ : ∀ n : ℕ, ∃ xₙ, xₙ ∈ Ioi (0 : ℝ) ∧ 
      (fun x => Real.exp (-(x + a * x ^ μ)) * x ^ n) xₙ = 
      sSup (range (fun x => Real.exp (-(x + a * x ^ μ)) * x ^ n)) := by
    intro n
    apply ContinuousOn.exists_isMaxOn
    · apply Continuous.continuousOn
      exact (continuous_exp.comp (continuous_neg.comp (continuous_add_left (continuous_mul_left a ∘ continuous_rpow_const hμ1.le)))).mul
        (continuous_pow n)
    · refine ⟨1, ?_, ?_⟩
      · exact mem_Ioi.mpr zero_lt_one
      · apply isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr zero_le_one) 
          (ContinuousOn.mono (by continuity) (fun x hx => ⟨zero_le_one.trans hx.1, hx.2⟩))
    · apply Filter.Tendsto.atTop_of_eventually_const
      simp only [Filter.eventually_atTop]
      refine ⟨1, fun n hn => ?_⟩
      have : (fun x => Real.exp (-(x + a * x ^ μ)) * x ^ n) n ≤ Real.exp (-n) * n ^ n := by
        simp only [neg_add_rev]
        refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (pow_nonneg (le_of_lt (mem_Ioi.mp hn)) n)
        simp only [neg_le_neg_iff, add_le_add_iff_left]
        exact le_mul_of_one_le_left (pow_nonneg (le_of_lt (mem_Ioi.mp hn)) μ) ha.le
      refine le_trans this ?_
      have : Real.exp (-n) * n ^ n ≤ (Nat.factorial n : ℝ) := by
        rw [← Real.exp_nat_mul n, ← Real.exp_add, add_comm, ← neg_add_eq_sub]
        exact le_trans (Real.exp_le_exp.mpr (neg_le_neg (le_of_eq (Nat.factorial_approx n).left))) 
          (le_of_eq (Real.exp_log (Nat.cast_pos.mpr (Nat.factorial_pos n)).le))
      exact this.trans (le_of_eq (by simp))
  
  -- Step 2: Characterize xₙ via the derivative condition
  have hderiv : ∀ n : ℕ, ∃ xₙ ∈ Ioi (0 : ℝ), n = xₙ + a * μ * xₙ ^ μ := by
    intro n
    rcases hxₙ n with ⟨xₙ, hxₙ_pos, hxₙ_max⟩
    refine ⟨xₙ, hxₙ_pos, ?_⟩
    have hdiff : HasDerivAt (fun x => Real.exp (-(x + a * x ^ μ)) * x ^ n) 0 xₙ := by
      apply IsMaxOn.hasDerivAt_eq_zero _ hxₙ_max
      apply DifferentiableAt.hasDerivAt
      apply DifferentiableAt.mul
      · exact (DifferentiableAt.exp (DifferentiableAt.neg (DifferentiableAt.add 
          (DifferentiableAt.id' _) (DifferentiableAt.const_mul a (DifferentiableAt.rpow_const _ hμ1.le)))))
      · exact DifferentiableAt.pow (DifferentiableAt.id' _) n
    simp only [hasDerivAt_iff_isLittleO_nhds_zero, add_zero, mul_one] at hdiff
    have hderiv : DerivableAt ℝ (fun x => Real.exp (-(x + a * x ^ μ)) * x ^ n) xₙ := by
      apply DifferentiableAt.derivableAt
      apply DifferentiableAt.mul
      · exact (DifferentiableAt.exp (DifferentiableAt.neg (DifferentiableAt.add 
          (DifferentiableAt.id' _) (DifferentiableAt.const_mul a (DifferentiableAt.rpow_const _ hμ1.le)))))
      · exact DifferentiableAt.pow (DifferentiableAt.id' _) n
    rw [deriv_mul, deriv_exp, deriv_neg, deriv_add, deriv_id'', deriv_const_mul, deriv_rpow_const hμ1.le,
        deriv_pow, deriv_id'', deriv_id'', one_mul, one_mul, neg_add_rev, neg_mul, neg_mul,
        mul_one, mul_one, ← neg_add', ← mul_assoc, ← mul_assoc] at hderiv
    simp only [neg_add_rev, mul_eq_zero] at hderiv
    cases' hderiv with h1 h2
    · have : Real.exp (-(xₙ + a * xₙ ^ μ)) ≠ 0 := Real.exp_ne_zero _
      simp [this] at h1
      exact h1
    · simp only [pow_eq_zero_iff, Nat.succ_pos', ne_eq, OfNat.ofNat_ne_zero, or_false] at h2
      exact (hxₙ_pos.ne' h2).elim
  
  -- Step 3: Asymptotic behavior of xₙ
  have hasymp : (fun n : ℕ => (n : ℝ) - Classical.choose (hderiv n)) =O[atTop] (fun n => (n : ℝ) ^ μ) := by
    refine Asymptotics.IsBigO.of_bound 1 ?_
    simp only [Filter.eventually_atTop, norm_eq_abs, one_mul]
    refine ⟨1, fun n hn => ?_⟩
    rcases hderiv n with ⟨xₙ, hxₙ_pos, hxₙ_eq⟩
    have hn_pos : (n : ℝ) > 0 := by exact_mod_cast Nat.succ_pos n
    have hxₙ_le_n : xₙ ≤ n := by
      rw [← hxₙ_eq]
      exact le_add_of_nonneg_right (mul_nonneg (mul_nonneg ha.le hμ1.le) (pow_nonneg hxₙ_pos.le μ))
    have hdiff : n - xₙ = a * μ * xₙ ^ μ := by rw [hxₙ_eq]; ring
    have hxₙ_ge : xₙ ≥ n / 2 := by
      by_contra h
      push_neg at h
      have : n - xₙ > n / 2 := by linarith
      rw [hdiff] at this
      have : a * μ * xₙ ^ μ > n / 2 := this
      have : xₙ ^ μ > n / (2 * a * μ) := by
        rw [← mul_div_right_comm, ← mul_div_right_comm] at this
        exact (div_lt_iff' (mul_pos (mul_pos (by linarith) ha) hμ1)).mp this
      have : xₙ > (n / (2 * a * μ)) ^ (1 / μ) := by
        rw [← rpow_lt_rpow_iff hxₙ_pos.le (div_pos (by linarith) (mul_pos (mul_pos (by linarith) ha) hμ1)).le hμ1]
        simp [this]
      have : n > 2 * (n / (2 * a * μ)) ^ (1 / μ) := by linarith
      suffices : (n : ℝ) ≤ 2 * (n / (2 * a * μ)) ^ (1 / μ)
      · linarith
      have hμ_inv_pos : 0 < 1 / μ := one_div_pos.mpr hμ1
      refine le_of_pow_le_pow_left hμ_inv_pos (by positivity) ?_
      rw [← rpow_mul (by positivity), mul_one_div_cancel hμ1.ne.symm, rpow_one, ← mul_pow,
          mul_div_assoc, mul_div_assoc, mul_div_cancel_left _ (mul_pos (by linarith) ha).ne.symm]
      exact pow_le_pow_left (by linarith) (le_refl _) _
    have : abs (n - xₙ) ≤ (a * μ * (n ^ μ)) := by
      rw [hdiff, abs_eq_self.mpr (by positivity)]
      refine mul_le_mul_of_nonneg_left (pow_le_pow_of_le_left hxₙ_pos.le hxₙ_le_n μ) ?_
      exact mul_nonneg ha.le hμ1.le
    refine le_trans this ?_
    rw [mul_assoc]
    exact le_refl _
  
  -- Step 4: Main asymptotic calculation
  refine Tendsto.congr' ?_ (tendsto_exp_neg_a ha)
  simp only [Filter.eventually_atTop]
  refine ⟨1, fun n hn => ?_⟩
  rcases hderiv n with ⟨xₙ, hxₙ_pos, hxₙ_eq⟩
  have hn_pos : (n : ℝ) > 0 := by exact_mod_cast Nat.succ_pos n
  have hxₙ_le_n : xₙ ≤ n := by
    rw [← hxₙ_eq]
    exact le_add_of_nonneg_right (mul_nonneg (mul_nonneg ha.le hμ1.le) (pow_nonneg hxₙ_pos.le μ))
  have hdiff : n - xₙ = a * μ * xₙ ^ μ := by rw [hxₙ_eq]; ring
  have hMₙ : sSup (range (fun x => Real.exp (-(x + a * x ^ μ)) * x ^ n)) = 
      Real.exp (-(xₙ + a * xₙ ^ μ)) * xₙ ^ n := by
    apply csSup_eq_of_isClosed_of_isMaxOn
    · exact isClosed_closure
    · refine ⟨0, ?_⟩
      simp only [mem_range, exists_apply_eq_apply]
      exact ⟨0, by simp⟩
    · exact ⟨xₙ, mem_range_self xₙ, (hxₙ n).2⟩
  
  rw [hMₙ]
  simp only [Nat.cast_pow, Nat.cast_mul, Nat.cast_succ]
  have hfact : (Nat.factorial n : ℝ) = Real.exp (-n) * n ^ n * Real.sqrt (2 * π * n) * (1 + 1 / (12 * n)) := by
    exact (Nat.factorial_eq_gamma n).trans (Real.Gamma_eq_approx n (by linarith))
  
  rw [hfact, div_eq_mul_inv, mul_inv, mul_inv, ← Real.exp_neg, ← rpow_neg, neg_mul, neg_mul, Real.exp_add,
      mul_assoc, mul_assoc, mul_assoc, ← Real.exp_add, ← rpow_add' hxₙ_pos.le, ← rpow_add' (by positivity)]
  have hlog : Real.log (Real.exp (-(xₙ + a * xₙ ^ μ)) * xₙ ^ n / (Real.exp (-n) * n ^ n * Real.sqrt (2 * π * n) * (1 + 1 / (12 * n)))) =
      -(xₙ + a * xₙ ^ μ) + n * Real.log xₙ - (-n + n * Real.log n + Real.log (Real.sqrt (2 * π * n)) + Real.log (1 + 1 / (12 * n))) := by
    rw [Real.log_mul, Real.log_mul, Real.log_mul, Real.log_div, Real.log_exp, Real.log_exp, Real.log_pow, Real.log_pow,
        Real.log_pow, Real.log_sqrt, Real.log_mul, Real.log_mul, add_assoc, add_assoc, add_assoc, neg_add_rev, neg_add_rev,
        neg_add_rev, neg_add_rev, add_comm _ (-n), add_assoc, add_assoc, add_assoc, add_comm _ (Real.log _), add_assoc,
        add_comm _ (Real.log _), add_assoc, add_comm _ (Real.log _), add_assoc]
    all_goals { try positivity }
  
  have hmain : -(xₙ + a * xₙ ^ μ) + n * Real.log xₙ - (-n + n * Real.log n + Real.log (Real.sqrt (2 * π * n)) + Real.log (1 + 1 / (12 * n))) =
      -a * n ^ μ + o(n ^ μ) := by
    rw [← hdiff]
    have hlogxₙ : Real.log xₙ = Real.log n - a * μ * n ^ (μ - 1) + o(n ^ (μ - 1)) := by
      have hxₙ_asymp : xₙ = n - a * μ * n ^ μ + o(n ^ μ) := by
        refine hasymp.sub ?_
        exact Asymptotics.isLittleO_of_isBigO (Asymptotics.isBigO_refl _ _)
      rw [hxₙ_asymp]
      have hlog : Real.log (n - a * μ * n ^ μ + o(n ^ μ)) = Real.log n + Real.log (1 - a * μ * n ^ (μ - 1) + o(n ^ (μ - 1))) := by
        have hdiv : (n - a * μ * n ^ μ + o(n ^ μ)) / n = 1 - a * μ * n ^ (μ - 1) + o(n ^ (μ - 1)) := by
          rw [div_eq_mul_inv, mul_sub, mul_sub, mul_one, ← inv_pow, ← mul_assoc, ← mul_assoc, ← mul_assoc,
              Asymptotics.isLittleO_const_mul_left, Asymptotics.isLittleO_const_mul_left]
          all_goals { simp [hn_pos.ne.symm] }
        rw [Real.log_div, Real.log_mul, add_comm, ← add_assoc]
        all_goals { try positivity }
      rw [hlog]
      have hlog1 : Real.log (1 - a * μ * n ^ (μ - 1) + o(n ^ (μ - 1))) = -a * μ * n ^ (μ - 1) + o(n ^ (μ - 1)) := by
        refine Real.log_one_add_o ?_
        exact Asymptotics.isLittleO_const_mul_left.mpr (Asymptotics.isLittleO_const_mul_left.mpr (Asymptotics.isLittleO_refl _ _))
      rw [hlog1]
      ring
    rw [hlogxₙ]
    have hterm1 : n * Real.log xₙ = n * Real.log n - a * μ * n ^ μ + o(n ^ μ) := by
      rw [hlogxₙ]
      ring_nf
      exact Asymptotics.isLittleO_const_mul_left.mpr (Asymptotics.isLittleO_refl _ _)
    rw [hterm1]
    have hterm2 : Real.log (Real.sqrt (2 * π * n)) = Real.log (Real.sqrt (2 * π)) + Real.log (Real.sqrt n) := by
      rw [Real.log_mul, Real.log_sqrt, Real.log_sqrt]
      all_goals { positivity }
    rw [hterm2]
    have hterm3 : Real.log (Real.sqrt n) = (1/2) * Real.log n := by
      rw [Real.log_sqrt, mul_comm]
    rw [hterm3]
    have hterm4 : Real.log (1 + 1 / (12 * n)) = o(n ^ μ) := by
      refine Real.log_one_add_o ?_
      exact Asymptotics.isLittleO_const_mul_left.mpr (Asymptotics.isLittleO_const_mul_left.mpr (Asymptotics.isLittleO_refl _ _))
    rw [hterm4]
    ring_nf
    simp only [add_assoc, add_sub_cancel'_right, sub_add_cancel]
    exact Asymptotics.isLittleO.add (Asymptotics.isLittleO.refl _ _) (Asymptotics.isLittleO.refl _ _)
  
  have hexp : Real.exp (-a * n ^ μ + o(n ^ μ)) = Real.exp (-a) ^ (n ^ μ) * Real.exp (o(n ^ μ)) := by
    rw [Real.exp_add, ← Real.exp_mul, mul_comm]
  
  rw [hlog, hmain, hexp]
  refine tendsto_mul_atTop_of_lt ?_ ?_
  · refine tendsto_rpow_atTop_zero ?_
    exact neg_lt_zero.mpr ha
  · exact tendsto_exp_atTop.comp (Asymptotics.isLittleO.tendsto_zero (Asymptotics.isLittleO_refl _ _))