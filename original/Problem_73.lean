/-
Polya-Szego Problem 73
Part One, Chapter 2

Original problem:
Ta

WIS asse\\
E $\overline{N_{1}+1}$\\
Defee i a\\
14.1 Le\\
be drifoed

Then

$$
\lim _{n \rightarrow \infty} \frac{a_{0}+a_{1}+a_{2}+\cdots+a_{n}}{b_{0}+b_{1}+b_{2}+\cdots+b_{n}}=s .
$$

\begin{enumerate}
  \setcounter{enumi}{70}
  \item Assume $\alpha>0$. Reduce the computation of
\end{enumerate}

$$
\lim _{n \rightarrow \infty} \frac{1^{\alpha-1}+2^{\alpha-1}+3^{\alpha-1}+\cdots+n^{\alpha-1}}{n^{\alpha}}
$$

to the computation of

$$
\lim _{n \rightarrow \infty} \frac{(n+1)^{x}-n^{x}}{n^{\a

Formalization notes: 
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.MeanValue

/-!
Formalization of Problem 73 from Polya-Szego's "Problems and Theorems in Analysis"

The theorem states that for α > 0, the limit of the average of k^(α-1) divided by n^α
equals the limit of the difference quotient ((n+1)^α - n^α)/n^(α-1).

Both limits are known to equal 1/α from calculus, but here we only formalize
their equality, not their specific value.
-/

open Real
open Filter
open scoped Topology

theorem problem_73 (α : ℝ) (hα : α > 0) :
    Tendsto (λ n : ℕ ↦ (∑ k in Finset.range (n + 1), ((k : ℝ) ^ (α - 1))) / ((n : ℝ) ^ α)) 
      atTop (𝓝 (Tendsto.lim (atTop : Filter ℕ) 
        (λ n : ℕ ↦ ((((n : ℝ) + 1) ^ α) - ((n : ℝ) ^ α)) / ((n : ℝ) ^ (α - 1))))) := by
  sorry

-- Proof attempt:
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Real
open Filter
open scoped Topology

theorem problem_73 (α : ℝ) (hα : α > 0) :
    Tendsto (λ n : ℕ ↦ (∑ k in Finset.range (n + 1), ((k : ℝ) ^ (α - 1))) / ((n : ℝ) ^ α)) 
      atTop (𝓝 (Tendsto.lim (atTop : Filter ℕ) 
        (λ n : ℕ ↦ ((((n : ℝ) + 1) ^ α) - ((n : ℝ) ^ α)) / ((n : ℝ) ^ (α - 1))))) := by
  -- Define the sequences involved
  let a := fun n : ℕ ↦ ∑ k in Finset.range (n + 1), (k : ℝ) ^ (α - 1)
  let b := fun n : ℕ ↦ (n : ℝ) ^ α
  let c := fun n : ℕ ↦ (((n : ℝ) + 1) ^ α - (n : ℝ) ^ α) / (n : ℝ) ^ (α - 1)
  
  -- Apply Stolz-Cesaro theorem
  have h_stolz : Tendsto (fun n ↦ a n / b n) atTop (𝓝 (Tendsto.lim atTop c)) := by
    refine' Tendsto.congr' _ (stolzCesaro b a c _ _ _)
    · refine' eventually_atTop.2 ⟨1, fun n hn ↦ _⟩
      simp [a, b]
    · refine' eventually_atTop.2 ⟨1, fun n hn ↦ _⟩
      simp [b]
      exact rpow_pos_of_pos (Nat.cast_pos.mpr hn) α
    · refine' Tendsto.congr' _ (tendsto_const_div_rpow_nhds_zero_nhds_zero hα)
      refine' eventually_atTop.2 ⟨1, fun n hn ↦ _⟩
      simp [b]
      exact rpow_pos_of_pos (Nat.cast_pos.mpr hn) α
    · have h_mono : ∀ᶠ n in atTop, StrictMono b := by
        refine' eventually_atTop.2 ⟨1, fun n hn ↦ _⟩
        intro m k hmk
        simp [b]
        exact rpow_lt_rpow (Nat.cast_pos.mpr hn) (Nat.cast_lt.mpr hmk) hα
      refine' Tendsto.congr' _ (tendsto_iff_abs_sub_tendsto_zero.1 <| 
        Tendsto.congr' _ (tendsto_rpow_div_mul_add rpow_nhds_zero hα))
      · refine' eventually_atTop.2 ⟨1, fun n hn ↦ _⟩
        simp [c]
        congr 1
        field_simp [rpow_sub (Nat.cast_pos.mpr hn), rpow_one]
        ring
      · refine' eventually_atTop.2 ⟨1, fun n hn ↦ _⟩
        simp [a, b]
        rw [← Finset.sum_range_add_sum_Ico _ (Nat.lt_succ_self n)]
        simp
        rw [Finset.sum_Ico_eq_sum_range]
        simp
        congr
        ext k
        rw [Nat.cast_add, Nat.cast_one, add_comm]
  
  exact h_stolz