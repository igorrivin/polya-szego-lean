/-
Polya-Szego Problem 78
Part One, Chapter 2

Original problem:
Prove the following generalization of the proposition on the arithmetic, geometric and harmonic means: Let $p_{1}, p_{2}, \ldots, p_{n}, a_{1}, a_{2}, \ldots, a_{n}$ denote arbitrary positive numbers, $a_{i} \neq a_{j}$ for at least one pair $i \neq j$, $i, j=1,2, \ldots, n$; then the inequalities\\
$\frac{p_{1}+p_{2}+\cdots+p_{n}}{\frac{p_{1}}{a_{1}}+\frac{p_{2}}{a_{2}}+\cdots+\frac{p_{n}}{a_{n}}}<e^{\frac{p_{1} \log a_{1}+p_{2} \log a_{2}+\cdots+p_{n} \log a_{n}}{p_{1}+p_{2}+\cdots+p_{n}}}<\fr

Formalization notes: -- We formalize the discrete version of Problem 78 (the first set of inequalities).
-- The theorem states weighted inequalities between harmonic mean, geometric mean, and arithmetic mean.
-- We assume:
-- 1. All p_i and a_i are positive real numbers
-- 2. The a_i are not all equal (at least one pair i ≠ j with a_i ≠ a_j)
-- 3. The inequalities relate weighted harmonic mean < weighted geometric mean < weighted arithmetic mean
-- 4. Additional inequalities involving logarithmic means
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.MeanInequalities

-- Formalization notes:
-- We formalize the discrete version of Problem 78 (the first set of inequalities).
-- The theorem states weighted inequalities between harmonic mean, geometric mean, and arithmetic mean.
-- We assume:
-- 1. All p_i and a_i are positive real numbers
-- 2. The a_i are not all equal (at least one pair i ≠ j with a_i ≠ a_j)
-- 3. The inequalities relate weighted harmonic mean < weighted geometric mean < weighted arithmetic mean
-- 4. Additional inequalities involving logarithmic means

theorem problem_78 {n : ℕ} (p a : Fin n → ℝ) (hp_pos : ∀ i, 0 < p i) (ha_pos : ∀ i, 0 < a i) 
    (ha_not_constant : ∃ (i j : Fin n), i ≠ j ∧ a i ≠ a j) :
    let total_p := ∑ i, p i
    let harmonic_mean := total_p / (∑ i, p i / a i)
    let geometric_mean := Real.exp ((∑ i, p i * Real.log (a i)) / total_p)
    let arithmetic_mean := (∑ i, p i * a i) / total_p
    let weighted_log_mean := (∑ i, (p i / a i) * Real.log (a i)) / (∑ i, p i / a i)
    let weighted_arithmetic_log_mean := (∑ i, p i * a i * Real.log (a i)) / (∑ i, p i * a i) in
    harmonic_mean < geometric_mean ∧ 
    geometric_mean < arithmetic_mean ∧
    weighted_log_mean < harmonic_mean ∧
    arithmetic_mean < Real.exp weighted_arithmetic_log_mean := by
  sorry

-- Proof attempt:
theorem problem_78 {n : ℕ} (p a : Fin n → ℝ) (hp_pos : ∀ i, 0 < p i) (ha_pos : ∀ i, 0 < a i) 
    (ha_not_constant : ∃ (i j : Fin n), i ≠ j ∧ a i ≠ a j) :
    let total_p := ∑ i, p i
    let harmonic_mean := total_p / (∑ i, p i / a i)
    let geometric_mean := Real.exp ((∑ i, p i * Real.log (a i)) / total_p)
    let arithmetic_mean := (∑ i, p i * a i) / total_p
    let weighted_log_mean := (∑ i, (p i / a i) * Real.log (a i)) / (∑ i, p i / a i)
    let weighted_arithmetic_log_mean := (∑ i, p i * a i * Real.log (a i)) / (∑ i, p i * a i) in
    harmonic_mean < geometric_mean ∧ 
    geometric_mean < arithmetic_mean ∧
    weighted_log_mean < harmonic_mean ∧
    arithmetic_mean < Real.exp weighted_arithmetic_log_mean := by
  -- Setup definitions
  set total_p := ∑ i, p i with hp_def
  set harmonic_mean := total_p / (∑ i, p i / a i) with hh_def
  set geometric_mean := Real.exp ((∑ i, p i * Real.log (a i)) / total_p) with hg_def
  set arithmetic_mean := (∑ i, p i * a i) / total_p with ha_def
  set weighted_log_mean := (∑ i, (p i / a i) * Real.log (a i)) / (∑ i, p i / a i) with hl_def
  set weighted_arithmetic_log_mean := (∑ i, p i * a i * Real.log (a i)) / (∑ i, p i * a i) with hla_def

  have hp_total : 0 < total_p := by positivity
  have h_denom_pos : 0 < ∑ i, p i / a i := by positivity
  have h_sum_pos : 0 < ∑ i, p i * a i := by positivity

  -- First inequality: harmonic_mean < geometric_mean
  have h1 : harmonic_mean < geometric_mean := by
    rw [hh_def, hg_def, ← Real.exp_neg, Real.exp_lt_exp]
    apply div_lt_div_of_lt_of_pos hp_total
    · simp_rw [← mul_div_assoc, ← Finset.sum_div]
      apply strictConcaveOn_iff_log.1 (strictConcaveOn_log_Ioi) (fun i ↦ ha_pos i) 
        (fun i ↦ hp_pos i) hp_total ha_not_constant
    · positivity

  -- Second inequality: geometric_mean < arithmetic_mean
  have h2 : geometric_mean < arithmetic_mean := by
    rw [hg_def, ha_def, ← Real.exp_log (sum_pos_of_pos hp_pos (fun i ↦ mul_pos (hp_pos i) (ha_pos i))), 
        Real.exp_lt_exp]
    apply div_lt_div_of_lt_of_pos hp_total
    · exact strictConcaveOn_iff_log.1 (strictConcaveOn_log_Ioi) (fun i ↦ ha_pos i) 
        (fun i ↦ hp_pos i) hp_total ha_not_constant
    · positivity

  -- Third inequality: weighted_log_mean < harmonic_mean
  have h3 : weighted_log_mean < harmonic_mean := by
    rw [hl_def, hh_def]
    have : ∀ i, p i / a i * Real.log (a i) = p i * (Real.log (a i) / a i) := by
      intro i; field_simp [ha_pos i]
    simp_rw [this]
    have := strictConcaveOn_iff_log.1 (strictConcaveOn_log_Ioi) (fun i ↦ ha_pos i) 
      (fun i ↦ div_pos (hp_pos i) (ha_pos i)) h_denom_pos ha_not_constant
    simp_rw [← div_eq_inv_mul] at this
    apply div_lt_div_of_lt_of_pos h_denom_pos this
    positivity

  -- Fourth inequality: arithmetic_mean < exp weighted_arithmetic_log_mean
  have h4 : arithmetic_mean < Real.exp weighted_arithmetic_log_mean := by
    rw [ha_def, hla_def, ← Real.exp_log h_sum_pos, Real.exp_lt_exp]
    have : ∀ i, p i * a i * Real.log (a i) = p i * a i * (Real.log (a i) / a i) * a i := by
      intro i; field_simp [ha_pos i]
    simp_rw [this]
    have := strictConcaveOn_iff_log.1 (strictConcaveOn_log_Ioi) (fun i ↦ ha_pos i) 
      (fun i ↦ mul_pos (hp_pos i) (ha_pos i)) h_sum_pos ha_not_constant
    simp_rw [← div_eq_inv_mul] at this
    apply div_lt_div_of_lt_of_pos h_sum_pos this
    positivity

  -- Combine all results
  exact ⟨h1, h2, h3, h4⟩