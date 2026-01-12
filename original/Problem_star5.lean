/-
Polya-Szego Problem *5
Part One, Chapter 4

Original problem:
We divide the interval $[1,2]$ into $n$ subintervals by the $n+1$ points

$$
\frac{n}{n}, \frac{n+1}{n}, \frac{n+2}{n}, \ldots, \frac{n+n}{n}
$$

and consider the lower sum $L_{n}$ and the upper sum $U_{n}$ for the function $f(x)=\frac{1}{x}$ that belong to this subdivision. Show that

$$
U_{1}=1, \quad L_{1}=1-\frac{1}{2}, \quad U_{2}=1-\frac{1}{2}+\frac{1}{3}, \cdots
$$

and generally that the sequence $U_{1}, L_{1}, U_{2}, L_{2}, \ldots, U_{n}, L_{n}, \ldots$ is identical with the sequence of

Formalization notes: We formalize the first part of Problem *5 from Polya-Szegő:
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic

/-!
## Formalization Notes

We formalize the first part of Problem *5 from Polya-Szegő:

Given the partition of [1,2] into n equal subintervals with points:
  x_k = (n + k)/n for k = 0,...,n  (so x_0 = 1, x_n = 2)

For f(x) = 1/x, we define:
  Lower sum L_n = ∑_{k=0}^{n-1} (x_{k+1} - x_k) * inf_{x∈[x_k,x_{k+1}]} f(x)
  Upper sum U_n = ∑_{k=0}^{n-1} (x_{k+1} - x_k) * sup_{x∈[x_k,x_{k+1}]} f(x)

Since f is decreasing on [1,2]:
  inf on [x_k, x_{k+1}] = f(x_{k+1}) = n/(n + k + 1)
  sup on [x_k, x_{k+1}] = f(x_k) = n/(n + k)

Thus:
  L_n = (1/n) * ∑_{k=0}^{n-1} n/(n + k + 1) = ∑_{j=1}^n 1/(n + j)
  U_n = (1/n) * ∑_{k=0}^{n-1} n/(n + k) = ∑_{j=0}^{n-1} 1/(n + j) = ∑_{j=n}^{2n-1} 1/j

The theorem states that the alternating sequence U₁, L₁, U₂, L₂, ... equals
the partial sums of the alternating harmonic series:
  1 - 1/2 + 1/3 - 1/4 + ... + (-1)^{k+1}/k + ...
Specifically:
  U_n = ∑_{k=1}^{2n-1} (-1)^{k+1}/k
  L_n = ∑_{k=1}^{2n} (-1)^{k+1}/k
-/

open Finset
open BigOperators

/-- Harmonic numbers H_n = 1 + 1/2 + ... + 1/n -/
noncomputable def harmonic (n : ℕ) : ℝ :=
  ∑ k in range n, 1 / ((k : ℝ) + 1)

/-- Lower sum for f(x) = 1/x on [1,2] with n subdivisions -/
noncomputable def lower_sum (n : ℕ) : ℝ :=
  ∑ j in range n, 1 / ((n : ℝ) + (j : ℝ) + 1)

/-- Upper sum for f(x) = 1/x on [1,2] with n subdivisions -/
noncomputable def upper_sum (n : ℕ) : ℝ :=
  ∑ j in range n, 1 / ((n : ℝ) + (j : ℝ))

/-- Partial sum of alternating harmonic series up to term 2n-1 -/
noncomputable def alt_harmonic_odd (n : ℕ) : ℝ :=
  ∑ k in range (2*n), (-1 : ℝ)^(k : ℕ) / ((k : ℝ) + 1)

/-- Partial sum of alternating harmonic series up to term 2n -/
noncomputable def alt_harmonic_even (n : ℕ) : ℝ :=
  ∑ k in range (2*n+1), (-1 : ℝ)^(k : ℕ) / ((k : ℝ) + 1)

theorem problem_5_part1 (n : ℕ) (hn : n ≥ 1) :
    upper_sum n = alt_harmonic_odd n ∧ lower_sum n = alt_harmonic_even n := by
  sorry

/-- Alternative formulation showing the sequence relationship -/
theorem problem_5_sequence (n : ℕ) (hn : n ≥ 1) :
    let seq : ℕ → ℝ := fun k =>
      match k with
      | 0 => upper_sum 1
      | 2*m => lower_sum (m+1)
      | 2*m+1 => upper_sum (m+2)
    in
    ∀ k : ℕ, seq k = ∑ j in range (k+1), (-1 : ℝ)^(j : ℕ) / ((j : ℝ) + 1) := by
  sorry

-- Proof attempt:
theorem problem_5_part1 (n : ℕ) (hn : n ≥ 1) :
    upper_sum n = alt_harmonic_odd n ∧ lower_sum n = alt_harmonic_even n := by
  constructor
  · -- Proof that upper_sum n = alt_harmonic_odd n
    unfold upper_sum alt_harmonic_odd harmonic
    have : range (2 * n) = range n ∪ (range (2 * n) \ range n) := by
      rw [← range_union_range_add n n]
      simp [Nat.mul_comm]
    rw [this, sum_union (disjoint_sdiff_self_right), sum_range_add]
    simp_rw [← add_assoc, Nat.cast_add, Nat.cast_one, one_div]
    have h₁ : ∑ x in range n, (-1 : ℝ) ^ (x + n) / (↑x + ↑n + 1) = 
              ∑ x in range n, (-1) ^ (x + n + 1) / (↑x + ↑n + 1) := by
      refine' sum_congr rfl fun x hx => _
      rw [← neg_div, pow_add, pow_one, mul_neg_one, neg_mul, one_mul]
    rw [h₁]
    have h₂ : ∀ k ∈ range n, (k : ℕ) + n = n + k := fun k _ => by rw [add_comm]
    simp_rw [h₂, add_assoc]
    rw [← sum_add_distrib]
    refine' sum_congr rfl fun k hk => _
    have : (-1 : ℝ) ^ (k : ℕ) + (-1) ^ (k + n + 1) = (-1) ^ k * (1 + (-1) ^ (n + 1)) := by
      rw [← mul_add, pow_add, pow_one]
    rw [this, ← add_div]
    have : n + 1 = 1 := by omega
    have : (-1 : ℝ) ^ (n + 1) = -1 := by
      rw [pow_add, pow_one, pow_eq_pow]
      simp [hn]
    simp [this]
    
  · -- Proof that lower_sum n = alt_harmonic_even n
    unfold lower_sum alt_harmonic_even harmonic
    have : range (2 * n + 1) = range n ∪ (range (2 * n + 1) \ range n) := by
      rw [← range_union_range_add_succ n n]
      simp [Nat.mul_comm]
    rw [this, sum_union (disjoint_sdiff_self_right), sum_range_add_succ]
    simp_rw [← add_assoc, Nat.cast_add, Nat.cast_one, one_div]
    have h₁ : ∑ x in range n, (-1 : ℝ) ^ (x + n + 1) / (↑x + ↑n + 1 + 1) = 
              ∑ x in range n, (-1) ^ (x + n + 1) / (↑x + ↑n + 2) := by
      refine' sum_congr rfl fun x hx => _
      rw [add_assoc]
    rw [h₁]
    have h₂ : ∀ k ∈ range n, (k : ℕ) + n = n + k := fun k _ => by rw [add_comm]
    simp_rw [h₂, add_assoc]
    rw [← sum_add_distrib]
    refine' sum_congr rfl fun k hk => _
    have : (-1 : ℝ) ^ (k : ℕ) + (-1) ^ (k + n + 1) = (-1) ^ k * (1 + (-1) ^ (n + 1)) := by
      rw [← mul_add, pow_add, pow_one]
    rw [this, ← add_div]
    have : n + 1 = 1 := by omega
    have : (-1 : ℝ) ^ (n + 1) = -1 := by
      rw [pow_add, pow_one, pow_eq_pow]
      simp [hn]
    simp [this]
    norm_num
    rw [add_comm _ (1 : ℝ), ← add_assoc, add_right_inj]
    simp [hn]