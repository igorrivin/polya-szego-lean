/-
Polya-Szego Problem 99
Part One, Chapter 2

Original problem:
Let the fund

$$
f(x)=\left\{\begin{array}{l}
0 \\
\frac{1}{q}
\end{array}\right.
$$

Show that $f(x)$ is 이 every rational $x$ and\\

Formalization notes: This formalizes two properties of Thomae's function:
1. f is continuous at irrational points
2. f is Riemann integrable on [0,1]
-/

import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Data.Set.Pointwise.Basic
import Mathlib.Topology.Algebra.Order.IntermediateValue

/- Formalization notes:
This formalizes two properties of Thomae's function:
1. f is continuous at irrational points
2. f is Riemann integrable on [0,1]

Thomae's function is defined as:
  f(x) = 1/q if x = p/q in lowest terms with q > 0
  f(x) = 0 if x is irrational

We use Mathlib's `Rat.den` for the denominator and `Rat.reduce` to ensure the fraction is in lowest terms.
-/

open Set
open Classical

noncomputable section

/-- Thomae's function (popcorn function, ruler function) -/
def thomae (x : ℝ) : ℝ :=
  if h : ∃ (p : ℤ) (q : ℕ), q ≠ 0 ∧ ((x : ℚ) = Rat.mk p q) then
    let pz := Classical.choose h
    let qn : ℕ := Classical.choose (Classical.choose_spec h)
    have hq : qn ≠ 0 := (Classical.choose_spec (Classical.choose_spec h)).left
    have hxq : (x : ℚ) = Rat.mk pz qn := 
      (Classical.choose_spec (Classical.choose_spec h)).right
    have : Rat.den (Rat.mk pz qn) = qn := Rat.mk_den pz (by exact Nat.pos_of_ne_zero hq)
    1 / (qn : ℝ)
  else
    0

theorem thomae_integrable : IntegrableOn thomae (Set.Icc (0 : ℝ) 1) := by
  sorry

theorem thomae_continuous_at_irrational (x : ℝ) (hx : Irrational x) :
    ContinuousAt thomae x := by
  sorry

theorem thomae_discontinuous_at_rational (x : ℚ) (hx : 0 ≤ x ∧ x ≤ 1) :
    ¬ ContinuousAt thomae (x : ℝ) := by
  sorry

/-- Formalizing the calculation from the book's solution showing the upper sum estimate.
The book divides [0,1] into n³ equal parts and bounds the upper sum.
This captures the specific inequality mentioned in the solution. -/
theorem thomae_upper_sum_bound (k : ℕ) (hk : k ≥ 1) :
    let n := k^3
    let partition := uniformPartition (0:ℝ) 1 n
    let mesh := 1 / (n : ℝ)
    let S := upperSum thomae partition
    S ≤ (k * (k - 1)) / (2 * (k^3 : ℝ)) + 2 / (k^3 : ℝ) + 1 / k := by
  sorry

-- Proof attempt:
theorem thomae_integrable : IntegrableOn thomae (Set.Icc (0 : ℝ) 1) := by
  refine integrableOn_of_upper_sum_bound (fun ε hε ↦ ?_)
  let k := max (Nat.ceil (3/ε)) 1
  have hk : k ≥ 1 := by simp [k]
  let n := k^3
  let partition := uniformPartition (0:ℝ) 1 n
  use partition
  have mesh_eq : mesh partition = 1 / (n : ℝ) := by
    simp [partition, mesh_uniformPartition, norm_num]
  refine ⟨mesh_eq, ?_⟩
  have : upperSum thomae partition ≤ (k * (k - 1)) / (2 * (k^3 : ℝ)) + 2 / (k^3 : ℝ) + 1 / k :=
    thomae_upper_sum_bound k hk
  have hk' : (k : ℝ) ≥ 1 := by exact_mod_cast hk
  have : (k : ℝ) ≤ 3/ε := by
    refine le_trans (Nat.le_ceil (3/ε)) ?_
    simp [k]
  linarith