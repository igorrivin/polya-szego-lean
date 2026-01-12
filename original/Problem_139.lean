/-
Polya-Szego Problem 139
Part One, Chapter 3

Original problem:
If all the moments

$$
\int_{a}^{b} f(t) t^{n} d t, \quad n=0,1,2, \ldots
$$

of a function that is properly integrable over the interval $[a, b]$ vanish then the function $f(x)$ vanishes at every point of continuity.\\

Formalization notes: -- We formalize the statement: If f is integrable on [a, b] and all its moments ∫_a^b f(t) t^n dt = 0
-- for n = 0, 1, 2, ..., then f(x) = 0 at every point x ∈ [a, b] where f is continuous.
-- We use `intervalIntegral` for integration over [a, b].
-- The conclusion is that for all x in [a, b] where f is continuous at x, we have f(x) = 0.
-/

import Mathlib.Analysis.Calculus.FTC
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.MeasureTheory.Integral.IntervalIntegral

-- Formalization notes:
-- We formalize the statement: If f is integrable on [a, b] and all its moments ∫_a^b f(t) t^n dt = 0
-- for n = 0, 1, 2, ..., then f(x) = 0 at every point x ∈ [a, b] where f is continuous.
-- We use `intervalIntegral` for integration over [a, b].
-- The conclusion is that for all x in [a, b] where f is continuous at x, we have f(x) = 0.

theorem problem_139 {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ} 
    (hf_int : IntervalIntegrable f MeasureTheory.volume a b) 
    (h_moments : ∀ (n : ℕ), ∫ t in a..b, f t * (t : ℝ) ^ n = 0) :
    ∀ x ∈ Set.uIcc a b, ContinuousAt f x → f x = 0 := by
  sorry

-- Proof attempt:
import Mathlib.Analysis.Calculus.FTC
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Topology.ContinuousFunction.Algebra
import Mathlib.Analysis.InnerProductSpace.Basic

theorem problem_139 {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ} 
    (hf_int : IntervalIntegrable f MeasureTheory.volume a b) 
    (h_moments : ∀ (n : ℕ), ∫ t in a..b, f t * (t : ℝ) ^ n = 0) :
    ∀ x ∈ Set.uIcc a b, ContinuousAt f x → f x = 0 := by
  intro x hx hcont
  -- First show f is orthogonal to all polynomials
  have h_orth : ∀ (p : ℝ[X]), ∫ t in a..b, f t * p t = 0 := by
    intro p
    let n := p.natDegree
    have hp : ∃ (c : ℕ → ℝ), p = ∑ i in Finset.range (n+1), fun j => c j * (X : ℝ[X])^j := by
      exact Polynomial.mem_span_range_X_pow_of_degree_le p.le_natDegree
    rcases hp with ⟨c, hc⟩
    rw [hc]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_finset_sum]
    rw [intervalIntegral.integral_finset_sum]
    · apply Finset.sum_eq_zero
      intro i hi
      rw [mul_comm, ← smul_eq_mul, intervalIntegral.integral_smul]
      simp [h_moments i]
    · intro i hi
      apply IntervalIntegrable.mul hf_int
      apply Continuous.intervalIntegrable
      exact Polynomial.continuous _
  
  -- Use density of polynomials in C([a,b]) to show f is orthogonal to all continuous functions
  let I := Set.uIcc a b
  have hI : IsCompact I := isCompact_uIcc
  let C := ContinuousMap.restrict I ⟨f, ContinuousAt.continuousOn hcont⟩
  
  -- Show ∫ f^2 = 0
  have hf_sq : ∫ t in a..b, f t * f t = 0 := by
    let φ : ContinuousMap I ℝ := ContinuousMap.restrict I ⟨f, ContinuousAt.continuousOn hcont⟩
    have : φ ∈ Submodule.span ℝ (Set.range (fun n : ℕ ↦ ContinuousMap.restrict I ⟨fun t ↦ t^n, by continuity⟩)) := by
      apply ContinuousMap.starSubalgebra_topologicalClosure_eq_top.mp rfl ▸ ContinuousMap.mem_closure_range_polynomial _ hI
      exact ⟨x, hx⟩
    refine Submodule.span_induction this ?_ ?_ ?_ ?_
    · rintro - ⟨n, rfl⟩
      simp only [ContinuousMap.coe_restrict, ContinuousMap.coe_mk, Function.comp_apply]
      exact h_moments n
    · simp [integral_zero']
    · intro g hg
      simp [integral_add hg, hg]
    · intro c g hg
      simp [integral_smul, hg]
  
  -- Since f is continuous at x and ∫ f^2 = 0, we must have f(x) = 0
  by_contra hne
  have hpos : 0 < f x ^ 2 := pow_two_pos_of_ne_zero _ hne
  have hcont' : ContinuousAt (fun t ↦ f t ^ 2) x := ContinuousAt.pow hcont 2
  obtain ⟨ε, hε, hf_pos⟩ := eventually_nhds_iff.1 (hcont'.eventually_gt (f x ^ 2 / 2) (half_pos hpos))
  obtain ⟨δ, hδ, hδ'⟩ := Metric.eventually_nhds_iff_ball.1 hf_pos
  have hδ'' : 0 < δ := by linarith [dist_nonneg (a := x)]
  
  -- The integral of f^2 over [x - δ/2, x + δ/2] is positive
  have h_int_pos : 0 < ∫ t in max a (x - δ/2)..min b (x + δ/2), f t ^ 2 := by
    refine intervalIntegral.integral_pos_of_integrable_on_of_nonneg_of_nonneg_nonempty ?_ ?_ ?_ ?_
    · exact (IntervalIntegrable.mul hf_int hf_int).mono_fun (fun t ↦ by simp) measurableSet_Ioc
    · intro t ht; exact sq_nonneg (f t)
    · refine (Metric.ball_subset_ball (by linarith)).trans fun t ht ↦ ?_
      simp only [Real.ball_eq_Ioo, mem_Ioo] at ht ⊢
      exact ⟨(lt_sub_iff_add_lt.mp ht.1).trans (add_lt_add_left (by linarith) _),
             (add_lt_add_right (sub_lt_iff_lt_add.mp ht.2) _).trans (by linarith)⟩
    · refine nonempty_interval.mpr ?_
      simp only [min_lt_iff, lt_max_iff]
      exact Or.inl ⟨sub_lt_self x (half_pos hδ''), lt_add_of_pos_right _ (half_pos hδ'')⟩
  
  -- But we know ∫ f^2 = 0 on all subintervals
  have h_int_zero : ∫ t in max a (x - δ/2)..min b (x + δ/2), f t ^ 2 = 0 := by
    have := hf_sq
    rw [intervalIntegral.integral_of_le, integral_eq_zero_iff_of_nonneg_of_le] at this
    · exact this.1 (max a (x - δ/2)) (min b (x + δ/2)) (by simp [hab]) (by simp)
    · intro t; exact sq_nonneg (f t)
    · intro t ht; exact le_of_lt (hf_pos t (hδ' (by simp [dist_eq, abs_of_pos hδ'']; linarith [ht.1, ht.2])))
    · exact le_trans (le_max_left _ _) hab
  linarith