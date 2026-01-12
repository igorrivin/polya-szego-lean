/-
Polya-Szego Problem 128
Part One, Chapter 3

Original problem:
If the fil\\
are continuous\\
then the terms

$$
\left.\int_{i}^{s} p_{1}(t)\right\}
$$

are between the\\
\href{http://MA.Cf}{MA.Cf}. I 65, 11\\

Formalization notes: -- This formalizes the theorem that if f is continuous on [a,b], then 
-- for any x ∈ [a,b], ∫_a^b f(t) dt / (b-a) lies between min_{t∈[a,b]} f(t) and max_{t∈[a,b]} f(t)
-- This is similar to the mean value theorem for integrals but stated as bounds
-- The notation (∫ x in a..b, f x) is Mathlib4's way of writing ∫_a^b f(x) dx
-/

import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral

-- Formalization notes:
-- This formalizes the theorem that if f is continuous on [a,b], then 
-- for any x ∈ [a,b], ∫_a^b f(t) dt / (b-a) lies between min_{t∈[a,b]} f(t) and max_{t∈[a,b]} f(t)
-- This is similar to the mean value theorem for integrals but stated as bounds
-- The notation (∫ x in a..b, f x) is Mathlib4's way of writing ∫_a^b f(x) dx

theorem problem_128 (a b : ℝ) (hab : a ≤ b) (f : ℝ → ℝ) 
    (hcont : ContinuousOn f (Set.uIcc a b)) :
    let m := sInf (f '' Set.uIcc a b) in
    let M := sSup (f '' Set.uIcc a b) in
    m * (b - a) ≤ ∫ x in a..b, f x ∧ ∫ x in a..b, f x ≤ M * (b - a) := by
  sorry

-- Proof attempt:
theorem problem_128 (a b : ℝ) (hab : a ≤ b) (f : ℝ → ℝ) 
    (hcont : ContinuousOn f (Set.uIcc a b)) :
    let m := sInf (f '' Set.uIcc a b) in
    let M := sSup (f '' Set.uIcc a b) in
    m * (b - a) ≤ ∫ x in a..b, f x ∧ ∫ x in a..b, f x ≤ M * (b - a) := by
  let I := Set.uIcc a b
  have hI : I = Set.Icc a b := by simp [Set.uIcc, hab]
  have hI_nonempty : I.Nonempty := by rw [hI]; exact Set.nonempty_Icc.mpr hab
  have hf_bdd : BddBelow (f '' I) ∧ BddAbove (f '' I) :=
    IsCompact.bddBelow_image (IsCompact.Icc hab) hcont (hI_nonempty.image f) ∧
    IsCompact.bddAbove_image (IsCompact.Icc hab) hcont (hI_nonempty.image f)
  
  let m := sInf (f '' I)
  let M := sSup (f '' I)
  
  have h1 : ∀ x ∈ I, m ≤ f x := by
    intro x hx
    apply csInf_le hf_bdd.1
    exact ⟨x, hx, rfl⟩
  
  have h2 : ∀ x ∈ I, f x ≤ M := by
    intro x hx
    apply le_csSup hf_bdd.2
    exact ⟨x, hx, rfl⟩
  
  have h3 : ContinuousOn (fun _ ↦ m) I := continuousOn_const
  have h4 : ContinuousOn (fun _ ↦ M) I := continuousOn_const
  
  have int_m : ∫ x in a..b, m = m * (b - a) := by simp; ring
  have int_M : ∫ x in a..b, M = M * (b - a) := by simp; ring
  
  constructor
  · rw [← int_m]
    apply intervalIntegral.integral_mono_on hab h3 hcont _ _
    · simp [h1]
    · exact (IsCompact.Icc hab).measurableSet
  · rw [← int_M]
    apply intervalIntegral.integral_mono_on hab hcont h4 _ _
    · simp [h2]
    · exact (IsCompact.Icc hab).measurableSet