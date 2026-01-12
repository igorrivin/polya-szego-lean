/-
Polya-Szego Problem 119
Part One, Chapter 3

Original problem:
For an everywhere convergent power series in $x$ which is not merely a polynomial the central subscript $v(x)$ tends to $\infty$ with $x$.\\

Formalization notes: We formalize Problem 119 from Polya-Szego "Problems and Theorems in Analysis" (Part One, Chapter 3).
-/

import Mathlib.Analysis.Complex.PowerSeries
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/- Formalization notes:
We formalize Problem 119 from Polya-Szego "Problems and Theorems in Analysis" (Part One, Chapter 3).

The problem concerns entire functions (everywhere convergent power series) that are not polynomials.
The "central subscript" v(x) refers to the index of the largest term in the power series expansion
when evaluated at a real number x. The theorem states that as |x| → ∞, this index v(x) → ∞.

We formalize this as:
For an entire function f : ℂ → ℂ that is not a polynomial, and for any M : ℕ, 
there exists R : ℝ such that for all x : ℝ with |x| > R, the index of the maximum term 
in the power series expansion of f at x is greater than M.

We use the following approach:
1. Represent f as an entire function (analytic on all ℂ)
2. Define the "central subscript" as the maximal index where |a_n * x^n| is maximized
3. State that this index tends to infinity as |x| → ∞

Note: The book's solution references Problem 118, which involves properties of 
the maximum term in power series expansions.
-/

open Complex
open Real
open Filter
open Topology

theorem problem_119 (f : ℂ → ℂ) (hf : AnalyticOn ℂ f ⊤) (hpoly : ¬∃ (p : Polynomial ℂ), f = p) :
    ∀ M : ℕ, ∃ R : ℝ, ∀ (x : ℝ) (hx : R < |x|), 
    let a : ℕ → ℂ := fun n => (hf.hasFPowerSeriesOnBall 0).coeff n
    let terms : ℕ → ℝ := fun n => Complex.abs (a n * (x : ℂ) ^ n)
    ∃ n > M, ∀ k, terms n ≥ terms k := by
  sorry

-- Proof attempt:
theorem problem_119 (f : ℂ → ℂ) (hf : AnalyticOn ℂ f ⊤) (hpoly : ¬∃ (p : Polynomial ℂ), f = p) :
    ∀ M : ℕ, ∃ R : ℝ, ∀ (x : ℝ) (hx : R < |x|), 
    let a : ℕ → ℂ := fun n => (hf.hasFPowerSeriesOnBall 0).coeff n
    let terms : ℕ → ℝ := fun n => Complex.abs (a n * (x : ℂ) ^ n)
    ∃ n > M, ∀ k, terms n ≥ terms k := by
  -- Get the power series expansion at 0
  have hfps := hf.hasFPowerSeriesOnBall 0
  let a : ℕ → ℂ := fun n => hfps.coeff n
  
  -- The function is not polynomial means infinitely many a_n are non-zero
  have h_inf_nonzero : ∀ N, ∃ n ≥ N, a n ≠ 0 := by
    intro N
    by_contra hc
    push_neg at hc
    have h_poly : ∃ p : Polynomial ℂ, f = p := by
      use Polynomial.ofFinsupp (Finsupp.ofSupportFinite (fun n => if n < N then a n else 0) 
        (by apply Set.Finite.subset (Set.finite_lt_nat N); simp))
      apply AnalyticOn.eqOn_of_frequently_eq hf (Polynomial.analyticOn _) 0
      apply eventually_of_forall
      intro z
      simp only [Polynomial.eval_eq_sum]
      rw [hfps.hasSum z]
      apply HasSum.sum_of_ne_finset_zero
      intro n hn
      simp only [Finsupp.mem_support_iff, ne_eq] at hn
      split_ifs at hn with h
      · exact hn
      · exact (hc n (by linarith)).symm ▸ zero_mul _
    exact hpoly h_poly
  
  intro M
  -- Choose N large enough so that for n ≥ N, |a_n|^(1/n) is small
  obtain ⟨N, hNM⟩ := exists_nat_gt M
  have h_nonzero : ∃ n ≥ N, a n ≠ 0 := h_inf_nonzero N
  
  -- The maximum term must eventually exceed M
  let R := (⨆ (n : ℕ) (hn : n ≤ M), if a n = 0 then 0 else (‖a n‖₊ / ‖a N‖₊) ^ (1 / (N - n : ℝ))) + 1
  
  refine ⟨R, fun x hx => ?_⟩
  let terms := fun n => Complex.abs (a n * (x : ℂ) ^ n)
  
  have h_R_large : ∀ n ≤ M, terms n ≤ terms N := by
    intro n hn
    simp [terms]
    rw [← NNReal.coe_le_coe, ← norm_eq_abs, ← norm_eq_abs, NNReal.coe_mul, NNReal.coe_mul, 
      NNReal.coe_pow, NNReal.coe_pow, mul_assoc, mul_assoc]
    gcongr
    · simp [norm_eq_abs]
    · have : (R - 1) ≤ |x| := by linarith
      rw [← NNReal.coe_le_coe, NNReal.coe_iSup] at this
      refine le_trans ?_ this
      refine le_ciSup ?_ n
      · apply Set.Finite.bddAbove
        exact Set.Finite.subset (Set.finite_le_nat M) (by simp [hn])
      · exact hn
  
  obtain ⟨n, hnN, hn_max⟩ := exists_maximal_term_of_not_polynomial hf hpoly x
  
  refine ⟨n, ?_, fun k => ?_⟩
  · by_contra h
    have h_le : n ≤ M := by linarith
    have := h_R_large n h_le
    have := hn_max N
    linarith [this, h_R_large n h_le]
  · exact hn_max k

where
  exists_maximal_term_of_not_polynomial {f : ℂ → ℂ} (hf : AnalyticOn ℂ f ⊤) (hpoly : ¬∃ p, f = p) (x : ℝ) :
    ∃ n, (∀ k, Complex.abs (hf.hasFPowerSeriesOnBall 0).coeff n * (x : ℂ) ^ n ≥ 
           Complex.abs (hf.hasFPowerSeriesOnBall 0).coeff k * (x : ℂ) ^ k) := by
    let a := fun n => (hf.hasFPowerSeriesOnBall 0).coeff n
    let terms := fun n => Complex.abs (a n * (x : ℂ) ^ n)
    have h_nonzero : ∃ n, a n ≠ 0 := by
      by_contra h; push_neg at h
      have : f = 0 := by
        apply AnalyticOn.eqOn_of_frequently_eq hf (analyticOn_const _ _) 0
        apply eventually_of_forall; intro z
        simp [h, hf.hasFPowerSeriesOnBall.hasSum z]
      exact hpoly ⟨0, by simp [this]⟩
    obtain ⟨N, hN⟩ := h_nonzero
    have : ∃ n, ∀ k, terms n ≥ terms k := by
      by_contra h; push_neg at h
      have h' : ∀ n, ∃ k, terms n < terms k := h
      choose g hg using h'
      let s : ℕ → ℕ := fun n => Nat.find (exists_gt_of_forall_exists_gt terms n)
      have hs : ∀ n, terms n < terms (s n) := fun n => Nat.find_spec (exists_gt_of_forall_exists_gt terms n)
      have : StrictMono (fun n => terms (Nat.iterate s n N)) := strictMono_nat_of_lt_succ fun n => hs _
      have : Tendsto (fun n => terms (Nat.iterate s n N)) atTop atTop :=
        tendsto_atTop_of_strictMono this
      have : ¬Tendsto (fun n => terms n) atTop atTop := by
        apply not_tendsto_atTop_of_tendsto
        · exact tendsto_abs_atTop_atTop.comp (tendsto_pow_atTop_nhds_0_of_lt_one (by norm_num))
        · apply Asymptotics.isLittleO_pow_pow_of_lt_left (by norm_num)
          exact (hf.hasFPowerSeriesOnBall 0).radius_eq_top.symm ▸ ENNReal.lt_top_iff_ne_top.2 (by simp)
      contradiction
    exact this