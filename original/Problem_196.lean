/-
Polya-Szego Problem 196
Part One, Chapter 5

Original problem:
Under the same hypotheses as in 195

$$
\lim _{n \rightarrow \infty} \frac{p_{1} a_{1}^{n+1}+p_{2} a_{2}^{n+1}+\cdots+p_{l} a_{l}^{n+1}}{p_{1} a_{1}^{n}+p_{2} a_{2}^{n}+\cdots+p_{l} a_{l}^{n}}=\max \left(a_{1}, a_{2}, \ldots, a_{l}\right) .
$$

\begin{enumerate}
  \setcounter{enumi}{196}
  \item Let $f(x)$ be an arbitrary polynomial whose zeros are all real and positive and for which
\end{enumerate}

$$
-\frac{f^{\prime}(x)}{f(x)}=c_{0}+c_{1} x+c_{2} x^{2}+\cdots+c_{n} x^{n} \cdots
$$

Show that

Formalization notes: We formalize Problem 196 from Polya-Szego:
   Let f be a polynomial with all real positive zeros.
   Suppose -f'(x)/f(x) = Σ_{n=0}^∞ c_n x^n (as a formal power series).
   Then:
     lim_{n→∞} (1 / (c_n)^{1/n}) = lim_{n→∞} (c_{n-1}/c_n)
   and this common limit equals the smallest zero of f.
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Asymptotics.Asymptotics

/- Formalization notes:
   We formalize Problem 196 from Polya-Szego:
   Let f be a polynomial with all real positive zeros.
   Suppose -f'(x)/f(x) = Σ_{n=0}^∞ c_n x^n (as a formal power series).
   Then:
     lim_{n→∞} (1 / (c_n)^{1/n}) = lim_{n→∞} (c_{n-1}/c_n)
   and this common limit equals the smallest zero of f.

   Important assumptions:
   1. f is a nonzero polynomial with positive real zeros
   2. The power series expansion exists (true for analytic functions near 0)
   3. For large n, c_n > 0 (follows from f having positive zeros)
   4. The limits exist (this is what we're proving exists)

   We'll use:
   - `Polynomial ℂ` for f, though zeros are real
   - `HasFPowerSeriesAt` for the power series expansion
   - `Tendsto` for limits
   - `Real.root` for n-th roots
-/

open Filter
open Real
open Complex
open Topology

theorem problem_196 {f : ℂ[X]} (hf : f ≠ 0) (hzeros : ∀ z : ℂ, f.IsRoot z → z ∈ Set.Ioo (0 : ℂ) ∞) 
    (hseries : ∃ (c : ℕ → ℂ) (r : ℝ≥0∞), HasFPowerSeriesAt (fun x : ℂ => -deriv f x / f x) c 0) :
    ∃ (α : ℝ) (hα : α > 0), 
      (∀ (c : ℕ → ℂ), (∃ (r : ℝ≥0∞), HasFPowerSeriesAt (fun x : ℂ => -deriv f x / f x) c 0) → 
        (Tendsto (λ n : ℕ => 1 / ((c n).re) ^ (1 / (n : ℝ))) atTop (𝓝 α)) ∧
        (Tendsto (λ n : ℕ => (c (n-1)).re / (c n).re) atTop (𝓝 α))) ∧
      α = (f.roots.filter (λ z => z ∈ Set.Ioo (0 : ℂ) ∞)).min' (by
        have : Finset.Nonempty (f.roots.filter (λ z => z ∈ Set.Ioo (0 : ℂ) ∞)) := by
          obtain ⟨z, hz⟩ := Polynomial.exists_root_of_degree_pos hf
          exact ⟨z, Finset.mem_filter.mpr ⟨hz, hzeros z hz⟩⟩
        exact this) |>.re := by
  sorry

-- Proof attempt:
obtain ⟨c, r, hseries⟩ := hseries
let roots := f.roots.filter (λ z => z ∈ Set.Ioo (0 : ℂ) ∞)
have h_nonempty : roots.Nonempty := by
  obtain ⟨z, hz⟩ := Polynomial.exists_root_of_degree_pos hf
  exact ⟨z, Finset.mem_filter.mpr ⟨hz, hzeros z hz⟩⟩
let α := roots.min' h_nonempty |>.re
have hα : α > 0 := by
  have := (Finset.mem_filter.mp (roots.min'_mem h_nonempty)).2
  exact this.1.re_pos

refine ⟨α, hα, ?_, rfl⟩
intro c' hc'
obtain ⟨r', hc'⟩ := hc'
have hc_eq : c = c' := HasFPowerSeriesAt.unique hseries hc'
rw [hc_eq]

have h_roots_eq : roots = f.roots := by
  ext z; simp only [Finset.mem_filter]
  exact ⟨fun h => h.1, fun h => ⟨h, hzeros z h⟩⟩

have hf_deg : f.degree ≠ 0 := by
  rw [Ne.def, Polynomial.degree_eq_bot]
  exact hf

have h_roots_ne_empty : f.roots.Nonempty :=
  Polynomial.roots_nonempty_iff_ne_zero.mpr hf

let a := roots.toFinset.image (λ z => (1/z).re)
have h_a_nonempty : a.Nonempty := by
  rw [← Finset.coe_nonempty]
  exact h_nonempty.toFinset

let β := a.max' h_a_nonempty
have hβ : β = 1/α := by
  simp only [α, Finset.max'_eq_sup', Finset.sup_image]
  rw [← inv_min' (by simp [h_nonempty]) (fun z => z.re)]
  congr
  ext z
  simp only [Finset.mem_image, Finset.mem_filter, exists_prop, Function.comp_apply, one_div]
  exact ⟨fun ⟨w, hw⟩ => ⟨w, hw.1, by rw [hw.2]⟩, 
         fun ⟨w, hw⟩ => ⟨w, hw.1, by rw [hw.2]⟩⟩

have hf_eq : f = Polynomial.C (f.leadingCoeff) * ∏ z in roots, (Polynomial.X - Polynomial.C z) := by
  rw [h_roots_eq, Polynomial.eq_prod_roots_of_splits_id hf]

have h_deriv_div : ∀ x ≠ 0, -deriv f x / f x = ∑ z in roots, 1 / (x - z) := by
  intro x hx
  rw [hf_eq, Polynomial.deriv_mul, Polynomial.deriv_prod, deriv_X, Polynomial.deriv_C, sub_zero]
  simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, zero_sub, neg_mul, mul_neg, 
             neg_div, neg_neg, Finset.sum_neg_distrib]
  rw [div_eq_mul_inv, mul_comm _ (f x)⁻¹, ← mul_assoc, ← neg_mul, mul_inv_cancel_right₀]
  · simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_prod]
    rw [Finset.prod_ne_zero_iff]
    intro z hz
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_ne_zero]
    exact (Finset.mem_filter.mp hz).2.ne'
  · rw [hf_eq, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod]
    refine mul_ne_zero ?_ (Finset.prod_ne_zero_iff.mpr ?_)
    · exact Polynomial.leadingCoeff_ne_zero.mpr hf
    · intro z hz
      simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_ne_zero]
      exact (Finset.mem_filter.mp hz).2.ne'

have h_pow_series : HasFPowerSeriesAt (fun x => ∑ z in roots, 1 / (x - z)) c 0 := by
  convert hseries
  ext x
  exact h_deriv_div x (by simp)

have h_cn_form : ∀ n, c n = ∑ z in roots, (1/z)^(n+1) := by
  intro n
  have := hasFPowerSeriesAt_pow_series (fun z => 1/z) roots 0 h_pow_series
  simp only [one_div, inv_pow] at this
  exact this n

have h_cn_pos : ∀ n, (c n).re > 0 := by
  intro n
  rw [h_cn_form]
  simp only [map_sum]
  refine Finset.sum_pos (fun z _ => ?_) h_nonempty
  have hz := (Finset.mem_filter.mp (Finset.mem_of_mem_filter z h_nonempty)).2
  simp only [one_div, Complex.re_inv, inv_pow, hz.1.re_pos, hz.2, inv_pos, pow_pos]

have h_ratio_tendsto : Tendsto (λ n => (c (n-1)).re / (c n).re) atTop (𝓝 α) := by
  simp_rw [h_cn_form, map_sum, ← Finset.sum_div]
  rw [tendsto_atTop_principal]
  refine tendsto_sum_ratio_of_dominant_term h_nonempty (fun z => (1/z).re) α ?_
  · simp [α, h_roots_eq, roots.min'_eq_inf' h_nonempty]
  · intro z hz
    exact (Finset.mem_filter.mp hz).2.re_pos

have h_root_tendsto : Tendsto (λ n => 1 / ((c n).re) ^ (1 / (n : ℝ))) atTop (𝓝 α) := by
  simp_rw [h_cn_form, map_sum]
  rw [tendsto_atTop_principal]
  refine tendsto_root_of_dominant_term h_nonempty (fun z => (1/z).re) α ?_
  · simp [α, h_roots_eq, roots.min'_eq_inf' h_nonempty]
  · intro z hz
    exact (Finset.mem_filter.mp hz).2.re_pos

exact ⟨h_root_tendsto, h_ratio_tendsto⟩