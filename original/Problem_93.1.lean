/-
Polya-Szego Problem 93.1
Part One, Chapter 2

Original problem:
The numbers $a_{1}, a_{2}, \ldots, a_{n}, r$, and $s$ are positive, $r<s, n>1$ and $\Sigma$ stands for $\sum_{v=1}^{n}$. Then

$$
\left(\sum a_{\nu}^{s}\right)^{\frac{1}{s}}<\left(\sum a_{\nu}^{r}\right)^{\frac{1}{r}}
$$

\begin{enumerate}
  \setcounter{enumi}{93}
  \item The function $f(x)$ is defined on $(0,1)$, non-decreasing, $f(x) \geqq 0$, but not identically zero. Let $0<a<b$. If all the integrals occurring exist we find the inequalities
\end{enumerate}

$$
1-\left(\frac{a-b}{a+b+1}\right

Formalization notes: We're formalizing the power mean inequality from Polya-Szego Problem 93.1:
   For positive numbers a₁, a₂, ..., aₙ, with 0 < r < s and n > 1,
   we have (∑_{ν=1}^n a_ν^s)^{1/s} < (∑_{ν=1}^n a_ν^r)^{1/r}
   
   We formalize this using Finset.sum over a Finset of size n, with explicit positivity conditions.
   The condition n > 1 is captured by requiring the Finset to have at least 2 elements.
   
   Note: Mathlib4 uses ℝ for exponents in pow, so we add type annotations.
-/
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.MeanInequalities

/- Formalization notes:
   We're formalizing the power mean inequality from Polya-Szego Problem 93.1:
   For positive numbers a₁, a₂, ..., aₙ, with 0 < r < s and n > 1,
   we have (∑_{ν=1}^n a_ν^s)^{1/s} < (∑_{ν=1}^n a_ν^r)^{1/r}
   
   We formalize this using Finset.sum over a Finset of size n, with explicit positivity conditions.
   The condition n > 1 is captured by requiring the Finset to have at least 2 elements.
   
   Note: Mathlib4 uses ℝ for exponents in pow, so we add type annotations.
-/

theorem power_mean_inequality_ps_93_1 (n : ℕ) (hn : 1 < n) (r s : ℝ) (hr : 0 < r) (hs : r < s) 
    (a : Fin n → ℝ) (hpos : ∀ i, 0 < a i) :
    (∑ i : Fin n, (a i) ^ s) ^ (1/s : ℝ) < (∑ i : Fin n, (a i) ^ r) ^ (1/r : ℝ) := by
  sorry

-- Proof attempt:
theorem power_mean_inequality_ps_93_1 (n : ℕ) (hn : 1 < n) (r s : ℝ) (hr : 0 < r) (hs : r < s) 
    (a : Fin n → ℝ) (hpos : ∀ i, 0 < a i) :
    (∑ i : Fin n, (a i) ^ s) ^ (1/s : ℝ) < (∑ i : Fin n, (a i) ^ r) ^ (1/r : ℝ) := by
  let R := ∑ i, (a i) ^ r
  have hR : 0 < R := by
    apply Finset.sum_pos
    intro i _
    exact Real.rpow_pos_of_pos (hpos i) r
  have hR' : R ≠ 0 := ne_of_gt hR
  have hs' : s ≠ 0 := ne_of_gt (lt_trans hr hs)
  have hr' : r ≠ 0 := ne_of_gt hr
  
  calc
    (∑ i, (a i) ^ s) ^ (1/s) = (R ^ (1/r)) * (∑ i, ((a i) ^ r / R) ^ (s/r)) ^ (1/s) := by
      rw [← Real.rpow_mul (le_of_lt hR), mul_comm, ← Real.rpow_add' hR']
      simp_rw [div_eq_mul_inv, Real.mul_rpow (Real.rpow_nonneg (le_of_lt (hpos i)) r) (inv_nonneg.mpr (le_of_lt hR))]
      field_simp [hs', hr']
      simp_rw [← Real.rpow_mul (le_of_lt (hpos i))]
      congr
      ext i
      rw [mul_comm, Real.rpow_mul (le_of_lt (hpos i))]
      ring
    _ < (R ^ (1/r)) * (∑ i, (a i) ^ r / R) ^ (1/s) := by
      gcongr
      apply Real.rpow_lt_rpow (sum_nonneg fun i _ => ?_) (sum_lt_sum_of_nonempty ?_ ?_) (div_pos hs hr)
      · exact div_nonneg (Real.rpow_nonneg (le_of_lt (hpos i)) r) (le_of_lt hR)
      · intro i _
        exact div_nonneg (Real.rpow_nonneg (le_of_lt (hpos i)) r) (le_of_lt hR)
      · exact Finset.nonempty_of_one_lt_card hn
      · intro i hi
        have := hpos i
        apply Real.rpow_lt_rpow (Real.rpow_nonneg (le_of_lt this) r) ?_ (div_pos hs hr)
        simp [div_lt_one_of_lt (hR), Real.rpow_lt_rpow (hpos i) hs]
    _ = (R ^ (1/r)) * (1) ^ (1/s) := by simp [sum_div, hR']
    _ = R ^ (1/r) := by simp [Real.one_rpow]
    _ = (∑ i, (a i) ^ r) ^ (1/r) := rfl