/-
Polya-Szego Problem 184
Part One, Chapter 4

Original problem:
Assume that the square roots of the logarithms of the natural numbers $1,2,3,4, \ldots$ are tabulated below each other in an infinite array. Consider the digits at the $j$-th decimal place (to the right of the decimal point) $j \geqq 1$. There exists no definite probability for the distribution of the digits $0,1,2, \ldots, 9$ at the $j$-th decimal place. More exactly: Let $v_{g}(n)$ denote the nùmber of integers $k$ among the first $n$ integers for which $\sqrt{\log k}$ has the digit $g$ at the

Formalization notes: We formalize Problem 184 from Polya-Szego about the decimal digits of √(log k).
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Digits
import Mathlib.Data.Set.Basic
import Mathlib.Topology.Algebra.Order.DenseInducing

/- Formalization notes:
We formalize Problem 184 from Polya-Szego about the decimal digits of √(log k).

Let:
  • j ≥ 1 be a fixed decimal place position (j-th digit after decimal point)
  • g ∈ {0,1,...,9} be a digit
  • v_g(n) = number of k ∈ {1,...,n} such that √(log k) has digit g at the j-th decimal place
  • The claim: The set {v_g(n)/n | n ∈ ℕ} is dense in [0,1]

We formalize this as: For any ε > 0 and any x ∈ [0,1], there exists n such that |v_g(n)/n - x| < ε.

Note: We need to handle the fact that √(log k) is only defined for k ≥ 1, and log 1 = 0.
We'll use Real.log for the natural logarithm and Real.sqrt for square root.
-/

open Set

theorem problem_184 (j : ℕ) (hj : j ≥ 1) (g : Fin 10) :
    Dense (Set.range (fun (n : ℕ) => 
      let v := Finset.card (Finset.filter (fun (k : ℕ) => 
        have hk : k ≥ 1 := by omega
        let x := Real.sqrt (Real.log (k : ℝ))
        let digits := Real.digits 10 (Int.ofNat (Nat.floor ((x - ⌊x⌋) * (10 : ℝ)^(j : ℕ))))
        (digits.get? (j - 1)).map (·.toNat) = some (g : ℕ)) (Finset.Icc 1 n))
      (v : ℝ) / (n : ℝ))) := by
  sorry

-- Proof attempt:
theorem problem_184 (j : ℕ) (hj : j ≥ 1) (g : Fin 10) :
    Dense (Set.range (fun (n : ℕ) => 
      let v := Finset.card (Finset.filter (fun (k : ℕ) => 
        have hk : k ≥ 1 := by omega
        let x := Real.sqrt (Real.log (k : ℝ))
        let digits := Real.digits 10 (Int.ofNat (Nat.floor ((x - ⌊x⌋) * (10 : ℝ)^(j : ℕ))))
        (digits.get? (j - 1)).map (·.toNat) = some (g : ℕ)) (Finset.Icc 1 n))
      (v : ℝ) / (n : ℝ))) := by
  rw [dense_iff_inter_open]
  intro U hU hU_nonempty
  obtain ⟨x, hx⟩ := hU_nonempty
  obtain ⟨ε, hε, hxε⟩ := Metric.isOpen_iff.mp hU x hx
  have hε_pos : 0 < ε := hε
  let δ := ε / 2
  have hδ_pos : 0 < δ := half_pos hε_pos
  
  -- Key step: fractional parts of √(log k) are dense in [0,1]
  have : Dense (Set.range (fun (k : ℕ) => Int.fract (Real.sqrt (Real.log (k : ℝ))))) := by
    apply Real.dense_of_fract_range_of_unbounded
    · intro M
      obtain ⟨k, hk⟩ := exists_nat_gt (Real.exp (M ^ 2))
      refine ⟨k, ?_⟩
      simp only [Nat.cast_le]
      refine le_trans ?_ hk
      rw [← Real.le_log_iff_exp_le (by positivity), Real.log_pow]
      ring_nf
      exact le_self_sq
    · intro k
      rw [Function.iterate_succ']
      simp only [Function.comp_apply]
      rw [Real.deriv_sqrt (Real.log_pos (by omega)), Real.deriv_log]
      field_simp
      positivity
  
  -- Now use density to approximate any x ∈ [0,1] with digit frequencies
  let target := x * 10^j
  let digit_width := 1 / 10^j
  let digit_start := g * digit_width
  let digit_end := (g + 1) * digit_width
  
  -- Find k where fractional part falls in appropriate interval
  obtain ⟨y, ⟨k, rfl⟩, hy⟩ : ∃ y ∈ Set.range (fun k => Int.fract (Real.sqrt (Real.log k))),
      |y - (target - ⌊target⌋)| < δ / (10^j) := by
    apply Metric.mem_closure_iff.mp (this.closure_eq ▸ mem_univ (target - ⌊target⌋))
    exact div_pos hδ_pos (by positivity)
  
  -- Construct sequence where fractional parts fill the digit interval
  let m := Nat.floor (10^j * (Int.fract (Real.sqrt (Real.log k))))
  let c := m - g
  let N := Nat.ceil (1 / (digit_width * δ))
  
  -- Main approximation
  refine ⟨N, ?_⟩
  simp only [Set.mem_range]
  let v := Finset.card (Finset.filter (fun (k : ℕ) => 
    have hk : k ≥ 1 := by omega
    let x := Real.sqrt (Real.log (k : ℝ))
    let digits := Real.digits 10 (Int.ofNat (Nat.floor ((x - ⌊x⌋) * (10 : ℝ)^(j : ℕ))))
    (digits.get? (j - 1)).map (·.toNat) = some (g : ℕ)) (Finset.Icc 1 N))
  show (v : ℝ) / N ∈ U
  
  -- Estimate the ratio
  have : |(v : ℝ)/N - x| < ε := by
    refine lt_of_le_of_lt ?_ hε_pos
    rw [← sub_zero x]
    refine le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_right (le_of_lt hy) (by positivity))
    field_simp [digit_width, δ]
    ring_nf
    rw [abs_div, abs_of_pos (by positivity), div_le_iff (by positivity)]
    refine le_trans ?_ (le_of_eq (by ring))
    norm_cast
    refine Nat.le_ceil _
  
  exact hxε this