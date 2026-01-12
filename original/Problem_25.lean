/-
Polya-Szego Problem 25
Part Three, Chapter 1

Original problem:
We assume that all the zeros of the polynomial

$$
P(z)=a_{0} z^{n}+a_{1} z^{n-1}+\cdots+a_{n-1} z+a_{n}
$$

are in the upper half-plane $\Im z>0$. Let $a_{v}=\alpha_{v}+i \beta_{v}, \alpha_{v}, \beta_{v}$ real, $v=0,1,2, \ldots, n$, and

$$
\begin{aligned}
& U(z)=\alpha_{0} z^{n}+\alpha_{1} z^{n-1}+\cdots+\alpha_{n-1} z+\alpha_{n} \\
& V(z)=\beta_{0} z^{n}+\beta_{1} z^{n-1}+\cdots+\beta_{n-1} z+\beta_{n}
\end{aligned}
$$

Then the polynomials $U(z)$ and $V(z)$ have only real zeros.\\

Formalization notes: We formalize the statement that if a complex polynomial P(z) has all its roots in the upper half-plane
(Im z > 0), and we decompose it into real and imaginary parts as P(z) = U(z) + iV(z) where U and V
are polynomials with real coefficients, then both U and V have only real roots.
-/

import Mathlib.Analysis.Complex.Polynomial
import Mathlib.Analysis.Complex.Arg
import Mathlib.Data.Complex.Basic

/- Formalization notes:
We formalize the statement that if a complex polynomial P(z) has all its roots in the upper half-plane
(Im z > 0), and we decompose it into real and imaginary parts as P(z) = U(z) + iV(z) where U and V
are polynomials with real coefficients, then both U and V have only real roots.

We represent:
- P : ℂ[X] as a polynomial with complex coefficients
- The condition "all roots in upper half-plane" means ∀ z ∈ ℂ, P.IsRoot z → 0 < z.im
- U and V : ℝ[X] as polynomials with real coefficients obtained by taking real/imaginary parts
  of coefficients of P
- "Only real zeros" means ∀ z ∈ ℂ, (U.map (algebraMap ℝ ℂ)).IsRoot z → z.im = 0, and similarly for V
- We assume P is non-zero and has degree n
-/

open Complex Polynomial

theorem problem_25 (P : ℂ[X]) (hP : P ≠ 0) (h_roots : ∀ z : ℂ, P.IsRoot z → 0 < z.im) :
    let n := P.natDegree
    let a : ℕ → ℂ := fun v => P.coeff v
    let α : ℕ → ℝ := fun v => (a v).re
    let β : ℕ → ℝ := fun v => (a v).im
    let U : ℝ[X] := ∑ v in Finset.range (n + 1), monomial v (α v)
    let V : ℝ[X] := ∑ v in Finset.range (n + 1), monomial v (β v)
    let Uℂ : ℂ[X] := U.map (algebraMap ℝ ℂ)
    let Vℂ : ℂ[X] := V.map (algebraMap ℝ ℂ)
    (∀ z : ℂ, Uℂ.IsRoot z → z.im = 0) ∧ (∀ z : ℂ, Vℂ.IsRoot z → z.im = 0) := by
  sorry

-- Proof attempt:
theorem problem_25 (P : ℂ[X]) (hP : P ≠ 0) (h_roots : ∀ z : ℂ, P.IsRoot z → 0 < z.im) :
    let n := P.natDegree
    let a : ℕ → ℂ := fun v => P.coeff v
    let α : ℕ → ℝ := fun v => (a v).re
    let β : ℕ → ℝ := fun v => (a v).im
    let U : ℝ[X] := ∑ v in Finset.range (n + 1), monomial v (α v)
    let V : ℝ[X] := ∑ v in Finset.range (n + 1), monomial v (β v)
    let Uℂ : ℂ[X] := U.map (algebraMap ℝ ℂ)
    let Vℂ : ℂ[X] := V.map (algebraMap ℝ ℂ)
    (∀ z : ℂ, Uℂ.IsRoot z → z.im = 0) ∧ (∀ z : ℂ, Vℂ.IsRoot z → z.im = 0) := by
  let n := P.natDegree
  let a := fun v => P.coeff v
  let α := fun v => (a v).re
  let β := fun v => (a v).im
  let U := ∑ v in Finset.range (n + 1), monomial v (α v)
  let V := ∑ v in Finset.range (n + 1), monomial v (β v)
  let Uℂ := U.map (algebraMap ℝ ℂ)
  let Vℂ := V.map (algebraMap ℝ ℂ)
  
  have hdeg : P.degree = some n := degree_eq_natDegree hP
  have hdegU : Uℂ.degree ≤ some n := by
    simp [Uℂ, Polynomial.degree_map_le_of_injective (algebraMap ℝ ℂ).injective]
  
  have hdegV : Vℂ.degree ≤ some n := by
    simp [Vℂ, Polynomial.degree_map_le_of_injective (algebraMap ℝ ℂ).injective]
  
  have hP_eq : P = Uℂ + I • Vℂ := by
    ext k
    simp [Uℂ, Vℂ, algebraMap ℝ ℂ, ← Complex.ext_iff, α, β]
    rw [← mul_comm I]
    simp [mul_comm I]
  
  have hP_conj : Polynomial.conj P = Uℂ - I • Vℂ := by
    ext k
    simp [Polynomial.conj, Uℂ, Vℂ, algebraMap ℝ ℂ, ← Complex.ext_iff, α, β]
    rw [← mul_comm I]
    simp [mul_comm I]
  
  constructor
  · intro z hz
    have hU : Uℂ.eval z = 0 := hz
    have hV : Vℂ.eval z = 0 := by
      by_contra hV'
      have : P.eval z = Uℂ.eval z + I * Vℂ.eval z := by simp [hP_eq]
      rw [hU] at this
      simp [this] at hV'
      have : Polynomial.conj P = Uℂ - I • Vℂ := hP_conj
      have : (Polynomial.conj P).eval z = Uℂ.eval z - I * Vℂ.eval z := by simp [this]
      rw [hU] at this
      simp [this] at hV'
      have : P.eval (conj z) = conj (P.eval z) := Polynomial.eval_conj
      rw [this, ← Complex.ext_iff]
      simp [hV']
      exact hV'.1
    have : P.eval z = 0 := by simp [hP_eq, hU, hV]
    have : P.IsRoot z := this
    have hz_im_pos : 0 < z.im := h_roots z this
    have : (Polynomial.conj P).eval z = 0 := by
      rw [hP_conj, eval_sub, eval_smul, eval_map, hU, hV]
      simp
    have : P.eval (conj z) = 0 := by rwa [Polynomial.eval_conj, conj_eq_iff_im]
    have : P.IsRoot (conj z) := this
    have hz_im_neg : 0 < (conj z).im := h_roots (conj z) this
    simp at hz_im_neg
    linarith [hz_im_pos, hz_im_neg]
  
  · intro z hz
    have hV : Vℂ.eval z = 0 := hz
    have hU : Uℂ.eval z = 0 := by
      by_contra hU'
      have : P.eval z = Uℂ.eval z + I * Vℂ.eval z := by simp [hP_eq]
      rw [hV] at this
      simp [this] at hU'
      have : Polynomial.conj P = Uℂ - I • Vℂ := hP_conj
      have : (Polynomial.conj P).eval z = Uℂ.eval z - I * Vℂ.eval z := by simp [this]
      rw [hV] at this
      simp [this] at hU'
      have : P.eval (conj z) = conj (P.eval z) := Polynomial.eval_conj
      rw [this, ← Complex.ext_iff]
      simp [hU']
      exact hU'.1
    have : P.eval z = 0 := by simp [hP_eq, hU, hV]
    have : P.IsRoot z := this
    have hz_im_pos : 0 < z.im := h_roots z this
    have : (Polynomial.conj P).eval z = 0 := by
      rw [hP_conj, eval_sub, eval_smul, eval_map, hU, hV]
      simp
    have : P.eval (conj z) = 0 := by rwa [Polynomial.eval_conj, conj_eq_iff_im]
    have : P.IsRoot (conj z) := this
    have hz_im_neg : 0 < (conj z).im := h_roots (conj z) this
    simp at hz_im_neg
    linarith [hz_im_pos, hz_im_neg]