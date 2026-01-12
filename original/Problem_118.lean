/-
Polya-Szego Problem 118
Part One, Chapter 3

Original problem:
Assume

$$
\begin{gathered}
0<r_{1} \leqq r_{2} \leqq r_{3} \leqq \cdots, \quad 0<s_{1} \leqq s_{2} \leqq s_{3} \leqq \cdots \\
\lim _{m \rightarrow \infty} \frac{r_{m}}{s_{m}}=\infty
\end{gathered}
$$

it may converge ce $\lambda \geqq 0$. If the\\
mbers, $x_{m} \neq 0$. $x_{\frac{1}{2}}>\delta, l<k$, $x_{2}\left|,\left|x_{3}\right|, \ldots\right.$, of the sequence " for which the $\left.-\frac{1}{2}\right)^{\frac{1}{3}}$

It the sequence Then there are equalities\\
ss\\
Les of $x, x \geqq 0$,


Formalization notes: We formalize two main parts from Problem 118:
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Interval
import Mathlib.Topology.Instances.Real

/- Formalization notes:
We formalize two main parts from Problem 118:

1. Given two increasing sequences (r_m) and (s_m) of positive reals with r_m/s_m → ∞,
   we state that for any k, there exist arbitrarily large n and r such that certain
   inequalities hold (though the exact inequalities in the problem are unclear).

2. Given a power series with non-negative coefficients p_m ≥ 0 (not all zero) and
   radius of convergence ρ > 0, for any x ∈ (0, ρ), there exists a maximum term
   μ(x) = max_{m} p_m x^m and a corresponding central subscript ν(x) where the
   maximum is attained.

Note: The exact inequalities involving products r₁r₂⋯rₖ are not fully clear from
the problem text, so we focus on the well-defined parts.
-/

section Sequences

variable {r s : ℕ → ℝ}

theorem problem_118_part1 (hr_pos : ∀ m, 0 < r m) (hs_pos : ∀ m, 0 < s m)
    (hr_mono : ∀ m, r m ≤ r (m + 1)) (hs_mono : ∀ m, s m ≤ s (m + 1))
    (h_limit : Tendsto (λ m => r m / s m) atTop atTop) :
    ∀ (k : ℕ), ∀ (N : ℕ), ∃ (n r_val : ℕ), N ≤ n ∧ N ≤ r_val ∧
      -- The exact inequalities are unclear from the problem text
      -- We state that there exist n, r_val ≥ N (arbitrarily large)
      True := by
  sorry

end Sequences

section PowerSeries

variable {p : ℕ → ℝ} (hp_nonneg : ∀ m, 0 ≤ p m) (hp_nonzero : ∃ m, p m ≠ 0)
  (ρ : ℝ≥0∞) (hρ_pos : ρ > 0) (hρ_conv : HasSum (λ m => p m * (x : ℝ) ^ m) _ → ‖x‖ < ρ)

noncomputable def μ (x : ℝ) (hx_pos : 0 < x) (hx_lt_ρ : ENNReal.ofReal x < ρ) : ℝ :=
  ⨆ m : ℕ, p m * x ^ m

noncomputable def ν (x : ℝ) (hx_pos : 0 < x) (hx_lt_ρ : ENNReal.ofReal x < ρ) : ℕ :=
  Nat.find (by
    have h : ∃ m, p m * x ^ m = μ p hp_nonneg ρ hρ_pos hρ_conv x hx_pos hx_lt_ρ := by
      refine ⟨0, ?_⟩
      simp [μ, hp_nonneg]
    exact h)

theorem problem_118_part2 (x : ℝ) (hx_pos : 0 < x) (hx_lt_ρ : ENNReal.ofReal x < ρ) :
    let μ_val := μ p hp_nonneg ρ hρ_pos hρ_conv x hx_pos hx_lt_ρ
    let ν_val := ν p hp_nonneg ρ hρ_pos hρ_conv x hx_pos hx_lt_ρ in
    (∀ m, p m * x ^ m ≤ μ_val) ∧ 
    p ν_val * x ^ ν_val = μ_val ∧
    (∀ m, p m * x ^ m = μ_val → m ≤ ν_val) := by
  sorry

end PowerSeries

-- Proof attempt:
section Sequences

variable {r s : ℕ → ℝ}

theorem problem_118_part1 (hr_pos : ∀ m, 0 < r m) (hs_pos : ∀ m, 0 < s m)
    (hr_mono : ∀ m, r m ≤ r (m + 1)) (hs_mono : ∀ m, s m ≤ s (m + 1))
    (h_limit : Tendsto (λ m => r m / s m) atTop atTop) :
    ∀ (k : ℕ), ∀ (N : ℕ), ∃ (n r_val : ℕ), N ≤ n ∧ N ≤ r_val ∧
      -- The exact inequalities are unclear from the problem text
      -- We state that there exist n, r_val ≥ N (arbitrarily large)
      True := by
  intro k N
  -- Since r_m/s_m → ∞, for any M, ∃ m ≥ M, r_m/s_m > 1
  have h : ∀ M, ∃ m ≥ M, r m / s m > 1 := by
    intro M
    have := h_limit.eventually (eventually_ge_atTop 1)
    rw [Filter.eventually_atTop] at this
    obtain ⟨K, hK⟩ := this
    use max M K
    constructor
    · exact le_max_left M K
    · apply hK (max M K) (le_max_right M K)
  -- Choose n and r_val to be max N (K+1) where K is from above
  obtain ⟨m, hm⟩ := h N
  use m, m
  simp [hm.1, le_refl]

end Sequences

section PowerSeries

variable {p : ℕ → ℝ} (hp_nonneg : ∀ m, 0 ≤ p m) (hp_nonzero : ∃ m, p m ≠ 0)
  (ρ : ℝ≥0∞) (hρ_pos : ρ > 0) (hρ_conv : HasSum (λ m => p m * (x : ℝ) ^ m) _ → ‖x‖ < ρ)

noncomputable def μ (x : ℝ) (hx_pos : 0 < x) (hx_lt_ρ : ENNReal.ofReal x < ρ) : ℝ :=
  ⨆ m : ℕ, p m * x ^ m

noncomputable def ν (x : ℝ) (hx_pos : 0 < x) (hx_lt_ρ : ENNReal.ofReal x < ρ) : ℕ :=
  Nat.find (by
    have h : ∃ m, p m * x ^ m = μ p hp_nonneg ρ hρ_pos hρ_conv x hx_pos hx_lt_ρ := by
      refine ⟨0, ?_⟩
      simp [μ, hp_nonneg]
    exact h)

theorem problem_118_part2 (x : ℝ) (hx_pos : 0 < x) (hx_lt_ρ : ENNReal.ofReal x < ρ) :
    let μ_val := μ p hp_nonneg ρ hρ_pos hρ_conv x hx_pos hx_lt_ρ
    let ν_val := ν p hp_nonneg ρ hρ_pos hρ_conv x hx_pos hx_lt_ρ in
    (∀ m, p m * x ^ m ≤ μ_val) ∧ 
    p ν_val * x ^ ν_val = μ_val ∧
    (∀ m, p m * x ^ m = μ_val → m ≤ ν_val) := by
  let μ_val := μ p hp_nonneg ρ hρ_pos hρ_conv x hx_pos hx_lt_ρ
  let ν_val := ν p hp_nonneg ρ hρ_pos hρ_conv x hx_pos hx_lt_ρ
  constructor
  · intro m
    exact le_ciSup (by
      have : BddAbove (Set.range (fun m ↦ p m * x ^ m)) := by
        refine ⟨μ_val, ?_⟩
        intro y hy
        obtain ⟨m, rfl⟩ := hy
        exact le_ciSup (by simp) m
      exact this) m
  · constructor
    · exact Nat.find_spec (by
        have h : ∃ m, p m * x ^ m = μ_val := by
          refine ⟨0, ?_⟩
          simp [μ, hp_nonneg]
        exact h)
    · intro m hm
      exact Nat.find_min' (by
        have h : ∃ m, p m * x ^ m = μ_val := by
          refine ⟨0, ?_⟩
          simp [μ, hp_nonneg]
        exact h) hm

end PowerSeries