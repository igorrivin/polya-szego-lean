/-
Polya-Szego Problem 140
Part One, Chapter 3

Original problem:
If the first $n$ moments vanish,

$$
\int_{a}^{b} f(x) d x=\int_{a}^{b} f(x) x d x=\int_{a}^{b} f(x) x^{2} d x=\cdots=\int_{a}^{b} f(x) x^{n-1} d x=0
$$

of a function $f(x)$ defined and continuous on the finite or infinite interval $(a, b)$ then the function changes sign (V, Chap. 1, § 2) at least $n$ times in the interval $(a, b)$ unless it is identically 0.\\

Formalization notes: -- We formalize: If f is continuous on (a,b) and ∫_a^b f(x)x^k dx = 0 for k=0,...,n-1,
-- then f must have at least n sign changes (unless f ≡ 0).
-- "Sign changes at least n times" means: ∃ x₀ < x₁ < ... < x_n in (a,b) such that
-- f(x_i) * f(x_{i+1}) < 0 for i=0,...,n-1.
-- We use `ℝ` for finite intervals, but the theorem should work for a,b ∈ ℝ ∪ {±∞}.
-- We use `intervalIntegral` which handles finite intervals; for infinite intervals
-- we'd need improper integrals.
-/

import Mathlib.Analysis.Calculus.MeanInequalities
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Topology.Algebra.Order.IntermediateValue

-- Formalization notes:
-- We formalize: If f is continuous on (a,b) and ∫_a^b f(x)x^k dx = 0 for k=0,...,n-1,
-- then f must have at least n sign changes (unless f ≡ 0).
-- "Sign changes at least n times" means: ∃ x₀ < x₁ < ... < x_n in (a,b) such that
-- f(x_i) * f(x_{i+1}) < 0 for i=0,...,n-1.
-- We use `ℝ` for finite intervals, but the theorem should work for a,b ∈ ℝ ∪ {±∞}.
-- We use `intervalIntegral` which handles finite intervals; for infinite intervals
-- we'd need improper integrals.

theorem problem_140 {a b : ℝ} (hab : a < b) {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Ioo a b))
    (n : ℕ) (hzero : ∀ k : ℕ, k < n → ∫ x in a..b, f x * x ^ k = 0) :
    (∀ x ∈ Set.Ioo a b, f x = 0) ∨ 
    ∃ (xs : Fin (n + 1) → ℝ) (hxs : StrictMono xs), 
      (∀ i, xs i ∈ Set.Ioo a b) ∧ 
      ∀ i : Fin n, f (xs i) * f (xs (Fin.succ i)) < 0 := by
  sorry

-- Proof attempt:
theorem problem_140 {a b : ℝ} (hab : a < b) {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Ioo a b))
    (n : ℕ) (hzero : ∀ k : ℕ, k < n → ∫ x in a..b, f x * x ^ k = 0) :
    (∀ x ∈ Set.Ioo a b, f x = 0) ∨ 
    ∃ (xs : Fin (n + 1) → ℝ) (hxs : StrictMono xs), 
      (∀ i, xs i ∈ Set.Ioo a b) ∧ 
      ∀ i : Fin n, f (xs i) * f (xs (Fin.succ i)) < 0 := by
  by_contra h
  push_neg at h
  obtain ⟨h₁, h₂⟩ := h
  have : ∃ p : ℝ[X], p.degree ≤ n ∧ ∀ x ∈ Set.Ioo a b, p x ≠ 0 ∧ f x * p x ≥ 0
  · -- Construct a polynomial p of degree ≤ n that doesn't change sign on (a,b)
    -- This contradicts the orthogonality conditions unless f ≡ 0
    sorry -- This requires non-trivial construction using Chebyshev polynomials
  
  obtain ⟨p, hp_deg, hp_prop⟩ := this
  have hp_cont : ContinuousOn (fun x ↦ p x) (Set.Ioo a b) := 
    Polynomial.continuousOn _
  have hp_mul_cont : ContinuousOn (fun x ↦ f x * p x) (Set.Ioo a b) := 
    ContinuousOn.mul hf hp_cont
  
  -- Since f(x)p(x) ≥ 0 and continuous, the integral must be positive unless f ≡ 0
  have h_int : 0 ≤ ∫ x in a..b, f x * p x := by
    refine intervalIntegral.integral_nonneg_of_continuousOn_of_nonneg ?_
    · exact ContinuousOn.mul hf (Polynomial.continuousOn _)
    · intro x hx
      exact (hp_prop x hx).2
  
  -- Expand p(x) as ∑ c_k x^k
  let c := p.coeff
  have h_expand : ∀ x, p x = ∑ k in Finset.range (n+1), c k * x ^ k := by
    intro x
    exact Polynomial.as_sum_range p x
  
  -- Rewrite the integral using linearity
  have h_int_eq : ∫ x in a..b, f x * p x = ∑ k in Finset.range (n+1), c k * ∫ x in a..b, f x * x ^ k := by
    simp_rw [h_expand, mul_sum]
    rw [intervalIntegral.integral_finset_sum _ (fun k _ ↦ ?_)]
    · simp_rw [smul_eq_mul, mul_assoc]
      congr
      ext k
      rw [mul_comm]
    · intro k _
      exact (ContinuousOn.mul hf (ContinuousOn.pow hf _)).intervalIntegrable
  
  -- All terms vanish by orthogonality condition
  have h_terms_zero : ∀ k ∈ Finset.range n, ∫ x in a..b, f x * x ^ k = 0 := by
    intro k hk
    exact hzero k (Finset.mem_range.mp hk)
  
  -- The last term might be non-zero if p has degree exactly n
  have h_sum : ∑ k in Finset.range (n+1), c k * ∫ x in a..b, f x * x ^ k = 
               c n * ∫ x in a..b, f x * x ^ n := by
    rw [Finset.sum_range_succ']
    simp [h_terms_zero]
  
  -- Now we have a contradiction
  have h_final : 0 < ∫ x in a..b, f x * p x := by
    refine lt_of_le_of_ne h_int ?_
    intro heq
    have : ∀ x ∈ Set.Ioo a b, f x * p x = 0 := by
      apply ContinuousOn.eq_zero_of_nonneg_of_integral_eq_zero hp_mul_cont
      · exact fun x hx ↦ (hp_prop x hx).2
      · rwa [h_int_eq, h_sum] at heq
    have : ∀ x ∈ Set.Ioo a b, f x = 0 := by
      intro x hx
      have := this x hx
      cases' mul_eq_zero.mp this with hf hp
      · exact hf
      · exact False.elim ((hp_prop x hx).1 hp)
    exact h₁ this
  
  -- But the integral is zero by orthogonality
  have : ∫ x in a..b, f x * p x = 0 := by
    rw [h_int_eq, h_sum]
    by_cases hn : n < p.natDegree
    · simp [Polynomial.coeff_eq_zero_of_natDegree_lt hn]
    · push_neg at hn
      have : p.natDegree ≤ n := by
        rwa [Polynomial.natDegree_le_iff_degree_le, ← Polynomial.degree_le_iff_natDegree_le]
      simp [hzero n (Nat.lt_succ_self n)]
  
  linarith