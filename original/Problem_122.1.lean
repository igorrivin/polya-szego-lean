/-
Polya-Szego Problem 122.1
Part One, Chapter 3

Original problem:
When is the mean value of a function in an interval a simple mean of those two values that the function takes at the endpoints of the interval?

Assume that $f(x)$ is defined, bounded and integrable in the interval $[a, b]$. Introduce the abbreviations

$$
\begin{aligned}
& f(u)=U, \quad f(v)=V \\
& \frac{1}{v-u} \int_{u}^{v} f(x) d x=W
\end{aligned}
$$

and determine the most general function $f(x)$ satisfying

$$
W=\frac{U+V}{2}
$$

for all $u$ and $v$ subject to the condition

$$
a \leqq u<v 

Formalization notes: -- We formalize Problem 122.1: Characterizing functions where the mean value over any interval
-- equals the arithmetic mean of endpoint values.
-- We assume f is integrable on [a, b] (using `IntervalIntegrable`).
-- The condition must hold for ALL u, v with a ≤ u < v ≤ b.
-- The solution states f must be linear: f(x) = αx + β.
-/

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Real

-- Formalization notes:
-- We formalize Problem 122.1: Characterizing functions where the mean value over any interval
-- equals the arithmetic mean of endpoint values.
-- We assume f is integrable on [a, b] (using `IntervalIntegrable`).
-- The condition must hold for ALL u, v with a ≤ u < v ≤ b.
-- The solution states f must be linear: f(x) = αx + β.

theorem problem_122_1 {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ} 
    (hf_int : ∀ u v, a ≤ u → v ≤ b → IntervalIntegrable f volume u v)
    (hf_bdd : BddAbove (Set.range f) ∧ BddBelow (Set.range f)) :
    (∀ u v, a ≤ u → v ≤ b → u < v → 
        (1 / (v - u)) * ∫ x in u..v, f x = ((f u) + (f v)) / 2) ↔
    ∃ (α β : ℝ), ∀ x, a ≤ x → x ≤ b → f x = α * x + β := by
  sorry

-- Proof attempt:
theorem problem_122_1 {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ} 
    (hf_int : ∀ u v, a ≤ u → v ≤ b → IntervalIntegrable f volume u v)
    (hf_bdd : BddAbove (Set.range f) ∧ BddBelow (Set.range f)) :
    (∀ u v, a ≤ u → v ≤ b → u < v → 
        (1 / (v - u)) * ∫ x in u..v, f x = ((f u) + (f v)) / 2) ↔
    ∃ (α β : ℝ), ∀ x, a ≤ x → x ≤ b → f x = α * x + β := by
  constructor
  · -- Forward direction: show f is linear
    intro h
    have h_cont : ∀ x, a ≤ x → x ≤ b → ContinuousAt f x := by
      intro x hx₁ hx₂
      refine continuousAt_iff_continuous_left_right.2 ⟨?_, ?_⟩
      · -- Left continuity
        refine continuousAt_of_integral_sub_linear_approx_eq_zero (by linarith) 
          (hf_int _ _ hx₁ hx₂) (hf_bdd.1) (fun u hu => ?_)
        specialize h u x hu.1 hx₂ hu.2
        rw [intervalIntegral.integral_of_le hu.2.le, sub_eq_zero] at h
        simp [h]
      · -- Right continuity
        refine continuousAt_of_integral_sub_linear_approx_eq_zero (by linarith) 
          (hf_int _ _ hx₁ hx₂) (hf_bdd.2) (fun v hv => ?_)
        specialize h x v hx₁ hv.1.2 hv.1.1
        rw [intervalIntegral.integral_of_le hv.1.1.le, sub_eq_zero] at h
        simp [h]
    
    -- Now apply the fundamental theorem of calculus
    have h_deriv : ∀ x ∈ Set.Ioo a b, HasDerivAt f ((f b - f a) / (b - a)) x := by
      intro x hx
      have hx' : a ≤ x ∧ x ≤ b := by linarith [hx.1, hx.2]
      have := hasDerivAt_of_integral_linear_approx (hf_int _ _ hx'.1 hx'.2) 
        (h_cont x hx'.1 hx'.2) (hf_bdd.1) (hf_bdd.2) (fun u v hu hv huv => ?_)
      · rw [this]
        field_simp [ne_of_gt (sub_pos.2 huv)]
        specialize h u v hu.1 hv.2 huv
        rw [intervalIntegral.integral_of_le huv.le] at h
        simp at h
        linear_combination h
      · specialize h u v hu.1 hv.2 huv
        rw [intervalIntegral.integral_of_le huv.le] at h
        simp at h
        linear_combination h
    
    -- f is differentiable with constant derivative, hence linear
    obtain ⟨α, β, hf⟩ : ∃ α β, ∀ x, f x = α * x + β := by
      have h_deriv_const : ∀ x ∈ Set.Ioo a b, deriv f x = (f b - f a) / (b - a) :=
        fun x hx => (h_deriv x hx).deriv
      have h_deriv_eq : ∀ x y ∈ Set.Ioo a b, deriv f x = deriv f y := by
        intro x y _ _; rw [h_deriv_const x, h_deriv_const y]
      obtain ⟨α, hα⟩ : ∃ α, ∀ x ∈ Set.Ioo a b, deriv f x = α := by
        use (f b - f a) / (b - a); exact h_deriv_const
      have h_eq_on : ∀ x ∈ Set.Icc a b, f x = f a + α * (x - a) := by
        intro x hx
        refine eq_of_hasDerivAt (fun y hy => ?_) (Continuous.continuousOn ?_) hx
        · exact (h_deriv y hy).congr_deriv (hα y hy).symm
        · exact ContinuousAt.continuousOn (h_cont · · ·)
      use α, f a - α * a
      intro x hx₁ hx₂
      rw [h_eq_on x ⟨hx₁, hx₂⟩]
      ring
    
    exact ⟨α, β, fun x _ _ => hf x⟩
  
  · -- Backward direction: linear functions satisfy the condition
    rintro ⟨α, β, hf⟩
    intro u v hu hv huv
    rw [hf u hu (le_trans hu hv), hf v (le_trans hu hv) hv]
    simp [intervalIntegral.integral_of_le huv.le]
    rw [integral_add, integral_mul_right]
    simp
    ring