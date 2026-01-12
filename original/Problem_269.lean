/-
Polya-Szego Problem 269
Part Three, Chapter 6

Original problem:
Let $f(z)$ denote a polynomial of degree $n$; then

$$
\frac{M\left(r_{1}\right)}{r_{1}^{n}} \geqq \frac{M\left(r_{2}\right)}{r_{2}^{n}}, \quad 0<r_{1}<r_{2}
$$

Equality is attained only if the polynomial is of the form $c z^{n}$.\\

Formalization notes: -- 1. We formalize the inequality for complex polynomials f : ℂ[X] of degree n
-- 2. M(r) is the maximum modulus on the circle |z| = r: M(r) = max_{|z|=r} |f(z)|
-- 3. The theorem states: for 0 < r₁ < r₂, M(r₁)/r₁^n ≥ M(r₂)/r₂^n
-- 4. Equality holds iff f(z) = c * z^n for some constant c
-- 5. We use `Polynomial` from Mathlib4 and the maximum modulus principle
-/

import Mathlib.Analysis.Complex.Polynomial
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.Pow.Real

-- Formalization notes:
-- 1. We formalize the inequality for complex polynomials f : ℂ[X] of degree n
-- 2. M(r) is the maximum modulus on the circle |z| = r: M(r) = max_{|z|=r} |f(z)|
-- 3. The theorem states: for 0 < r₁ < r₂, M(r₁)/r₁^n ≥ M(r₂)/r₂^n
-- 4. Equality holds iff f(z) = c * z^n for some constant c
-- 5. We use `Polynomial` from Mathlib4 and the maximum modulus principle

open Complex
open Real
open Polynomial
open Metric
open Filter

theorem problem_269 {n : ℕ} {f : ℂ[X]} (hf : f.degree = n) {r₁ r₂ : ℝ} 
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (hlt : r₁ < r₂) :
    let M : ℝ → ℝ := λ r ↦ sSup (Set.range (λ z : ℂ ↦ ‖f.eval z‖) ∩ {z | ‖z‖ = r})
    in M r₁ / (r₁ ^ n) ≥ M r₂ / (r₂ ^ n) := by
  sorry

-- Alternative formulation using the maximum modulus on spheres
theorem problem_269_alt {n : ℕ} {f : ℂ[X]} (hf : f.natDegree = n) {r₁ r₂ : ℝ} 
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (hlt : r₁ < r₂) :
    let sphere r := {z : ℂ | ‖z‖ = r}
    let M r := if h : sphere r ≠ ∅ then sSup ((λ z : ℂ ↦ ‖f.eval z‖) '' sphere r) else 0
    in M r₁ / (r₁ ^ n) ≥ M r₂ / (r₂ ^ n) := by
  sorry

-- Version with equality condition
theorem problem_269_with_equality {n : ℕ} {f : ℂ[X]} (hf : f.natDegree = n) {r₁ r₂ : ℝ} 
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (hlt : r₁ < r₂) :
    let sphere r := {z : ℂ | ‖z‖ = r}
    let M r := if h : sphere r ≠ ∅ then sSup ((λ z : ℂ ↦ ‖f.eval z‖) '' sphere r) else 0
    in M r₁ / (r₁ ^ n) ≥ M r₂ / (r₂ ^ n) ∧
       (M r₁ / (r₁ ^ n) = M r₂ / (r₂ ^ n) ↔ ∃ (c : ℂ), f = C c * X ^ n) := by
  sorry

-- Proof attempt:
theorem problem_269 {n : ℕ} {f : ℂ[X]} (hf : f.degree = n) {r₁ r₂ : ℝ} 
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (hlt : r₁ < r₂) :
    let M : ℝ → ℝ := λ r ↦ sSup (Set.range (λ z : ℂ ↦ ‖f.eval z‖) ∩ {z | ‖z‖ = r})
    in M r₁ / (r₁ ^ n) ≥ M r₂ / (r₂ ^ n) := by
  let M : ℝ → ℝ := λ r ↦ sSup (Set.range (λ z : ℂ ↦ ‖f.eval z‖) ∩ {z | ‖z‖ = r})
  have hn : n = f.natDegree := by rwa [natDegree_eq_of_degree_eq_some hf]
  have hf_ne_zero : f ≠ 0 := by intro h; rw [h, natDegree_zero] at hn; cases hn
  
  -- Define the auxiliary function g(z) = f(z)/z^n
  let g : ℂ → ℂ := fun z ↦ f.eval z / z ^ n
  
  -- Show g is holomorphic on ℂ \ {0}
  have hg_diff : DifferentiableOn ℂ g {z | z ≠ 0} := by
    refine DifferentiableOn.div ?_ ?_ (fun z hz ↦ zpow_ne_zero n hz)
    · exact Polynomial.differentiableOn_eval f
    · exact differentiableOn_zpow n
  
  -- Maximum modulus principle applied to g on the annulus r₁ ≤ |z| ≤ r₂
  have h_max : ∀ z, ‖z‖ = r₂ → ‖g z‖ ≤ sSup (‖g '' {w | r₁ ≤ ‖w‖ ∧ ‖w‖ ≤ r₂}) := by
    intro z hz
    have h_annulus : IsCompact {w | r₁ ≤ ‖w‖ ∧ ‖w‖ ≤ r₂} := by
      simp_rw [← mem_closedBall, ← closedBall_eq_empty_iff_lt hr₁.le, ← cpow_nat_inv_pow _ hn.symm ▸ hr₁]
      exact isCompact_closedBall
    have h_cont : ContinuousOn g {w | r₁ ≤ ‖w‖ ∧ ‖w‖ ≤ r₂} := by
      refine ContinuousOn.div ?_ ?_ (fun w hw ↦ zpow_ne_zero n ?_)
      · exact Polynomial.continuousOn_eval f
      · exact continuousOn_zpow n
      · exact ne_of_gt (lt_of_lt_of_le hr₁ hw.1)
    have h_boundary : ∃ z ∈ {w | ‖w‖ = r₁ ∨ ‖w‖ = r₂}, ‖g z‖ = sSup (‖g '' {w | r₁ ≤ ‖w‖ ∧ ‖w‖ ≤ r₂}) :=
      exists_mem_frontier_eq_sSup_image_norm h_annulus ⟨_, ⟨r₂, by simp [hz]⟩⟩ h_cont
    obtain ⟨ζ, hζ, hζ_max⟩ := h_boundary
    refine le_trans (le_of_eq rfl) (ge_of_eq ?_)
    refine Eq.trans ?_ hζ_max.symm
    cases' hζ with hζ hζ
    · exact congr_arg _ (csSup_eq_of_forall_le_of_forall_lt_exists_gt ?_ ?_ ?_).symm
      · simp only [nonempty_image_iff]
        exact ⟨r₁, by simp [hr₁.le]⟩
      · intro y hy
        obtain ⟨w, hw, rfl⟩ := hy
        apply norm_le_of_forall_mem_frontier_norm_le h_annulus h_cont hζ hw
      · intro b hb
        obtain ⟨w, hw, hw_norm⟩ := exists_lt_of_lt_csSup ?_ hb
        exact ⟨‖g w‖, ⟨w, hw, rfl⟩, hw_norm⟩
        simp only [nonempty_image_iff]
        exact ⟨r₁, by simp [hr₁.le]⟩
    · rfl
  
  -- Main inequality
  have h_main : M r₂ / r₂ ^ n ≤ M r₁ / r₁ ^ n := by
    have hM₂ : M r₂ = sSup (‖f.eval '' {z | ‖z‖ = r₂}) := by
      simp [M]
      congr
      ext x
      simp
    have hM₁ : M r₁ = sSup (‖f.eval '' {z | ‖z‖ = r₁}) := by
      simp [M]
      congr
      ext x
      simp
    rw [hM₂, hM₁]
    simp_rw [div_eq_mul_inv, ← mul_inv, ← norm_zpow, ← norm_div, ← zpow_neg, ← neg_eq_iff_eq_neg]
    have : ∀ z, ‖z‖ = r₂ → ‖g z‖ ≤ sSup (‖g '' {z | ‖z‖ = r₁}) := by
      intro z hz
      refine le_trans (h_max z hz) (csSup_mono ?_ ?_)
      · simp only [nonempty_image_iff]
        exact ⟨r₁, by simp [hr₁.le]⟩
      · rintro _ ⟨w, ⟨hwr₁, hwr₂⟩, rfl⟩
        exact ⟨w, Or.inl hwr₁, rfl⟩
    exact csSup_le (by simp [hr₁.le]) (by simpa using this)
  
  exact h_main