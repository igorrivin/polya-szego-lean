/-
Polya-Szego Problem 304
Part Three, Chapter 6

Original problem:
Let the function $f(z)$ be regular in the disk $|z|<R$. Suppose

$$
0<r_{1}<r_{2}<r_{3}<R .
$$

Then

$$
\log M\left(r_{2}\right) \leqq \frac{\log r_{2}-\log r_{1}}{\log r_{3}-\log r_{1}} \log M\left(r_{3}\right)+\frac{\log r_{3}-\log r_{2}}{\log r_{3}-\log r_{1}} \log M\left(r_{1}\right) .
$$

This means that in an orthogonal system of coordinates the graph of $\log M(r)$ as a function of $\log r$ appears as a convex curve. (Hadamard's three circle theorem.) [Examine $z^{\alpha} f(z)$ with suit

Formalization notes: -- 1. We formalize Hadamard's three circle theorem for holomorphic functions
-- 2. M(r) is defined as the supremum of |f(z)| on the circle |z| = r
-- 3. We capture the inequality for log M(r) as stated in Problem 304
-- 4. r1, r2, r3 are positive real numbers with 0 < r1 < r2 < r3 < R
-- 5. The function f is holomorphic on the open disk of radius R
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.Complex.AbsMax

open Complex
open ComplexOrder
open Real

-- Formalization notes:
-- 1. We formalize Hadamard's three circle theorem for holomorphic functions
-- 2. M(r) is defined as the supremum of |f(z)| on the circle |z| = r
-- 3. We capture the inequality for log M(r) as stated in Problem 304
-- 4. r1, r2, r3 are positive real numbers with 0 < r1 < r2 < r3 < R
-- 5. The function f is holomorphic on the open disk of radius R

theorem hadamard_three_circle {R : ℝ} (hR_pos : 0 < R) (f : ℂ → ℂ) 
    (hf : DifferentiableOn ℂ f (Metric.ball (0 : ℂ) R)) :
    ∀ (r1 r2 r3 : ℝ) (hr1_pos : 0 < r1) (hr2_pos : 0 < r2) (hr3_pos : 0 < r3) 
      (h_order : r1 < r2 ∧ r2 < r3) (h_lt_R : r3 < R),
    let M : ℝ → ℝ := fun r ↦ sSup (Set.range (fun z : ℂ ↦ Complex.abs (f z) | Complex.abs z = r)) in
    log (M r2) ≤ ((log r2 - log r1) / (log r3 - log r1)) * log (M r3) + 
                ((log r3 - log r2) / (log r3 - log r1)) * log (M r1) := by
  intro r1 r2 r3 hr1_pos hr2_pos hr3_pos ⟨h12, h23⟩ h3R
  set M : ℝ → ℝ := fun r ↦ sSup (Set.range fun z : ℂ ↦ if Complex.abs z = r then Complex.abs (f z) else 0)
  sorry

-- Formalization notes:
-- This theorem states the strict convexity condition from Problem 305
-- The condition for equality occurs only when f(z) = a*z^α for constants a, α

theorem hadamard_strict_convexity {R : ℝ} (hR_pos : 0 < R) (f : ℂ → ℂ) 
    (hf : DifferentiableOn ℂ f (Metric.ball (0 : ℂ) R)) :
    ∀ (r1 r2 r3 : ℝ) (hr1_pos : 0 < r1) (hr2_pos : 0 < r2) (hr3_pos : 0 < r3) 
      (h_order : r1 < r2 ∧ r2 < r3) (h_lt_R : r3 < R),
    let M : ℝ → ℝ := fun r ↦ sSup (Set.range (fun z : ℂ ↦ Complex.abs (f z) | Complex.abs z = r)) in
    ((log (M r2) = ((log r2 - log r1) / (log r3 - log r1)) * log (M r3) + 
                    ((log r3 - log r2) / (log r3 - log r1)) * log (M r1)) ∧
     ∃ (r4 : ℝ) (hr4 : r1 < r4 ∧ r4 < r3), 
        log (M r4) < ((log r4 - log r1) / (log r3 - log r1)) * log (M r3) + 
                    ((log r3 - log r4) / (log r3 - log r1)) * log (M r1)) ↔
    (∃ (a : ℂ) (α : ℝ), ∀ (z : ℂ), Complex.abs z < R → f z = a * z ^ α) := by
  intro r1 r2 r3 hr1_pos hr2_pos hr3_pos ⟨h12, h23⟩ h3R
  sorry

-- Proof attempt:
theorem hadamard_three_circle {R : ℝ} (hR_pos : 0 < R) (f : ℂ → ℂ) 
    (hf : DifferentiableOn ℂ f (Metric.ball (0 : ℂ) R)) :
    ∀ (r1 r2 r3 : ℝ) (hr1_pos : 0 < r1) (hr2_pos : 0 < r2) (hr3_pos : 0 < r3) 
      (h_order : r1 < r2 ∧ r2 < r3) (h_lt_R : r3 < R),
    let M : ℝ → ℝ := fun r ↦ sSup (Set.range (fun z : ℂ ↦ Complex.abs (f z) | Complex.abs z = r)) in
    log (M r2) ≤ ((log r2 - log r1) / (log r3 - log r1)) * log (M r3) + 
                ((log r3 - log r2) / (log r3 - log r1)) * log (M r1) := by
  intro r1 r2 r3 hr1_pos hr2_pos hr3_pos ⟨h12, h23⟩ h3R
  set M : ℝ → ℝ := fun r ↦ sSup (Set.range fun z : ℂ ↦ if Complex.abs z = r then Complex.abs (f z) else 0)
  
  -- Define the convex combination parameter
  set t := (log r2 - log r1) / (log r3 - log r1)
  have ht : t ∈ Set.Icc 0 1 := by
    refine ⟨div_nonneg ?_ ?_, ?_⟩
    · exact sub_nonneg.mpr (le_of_lt (log_le_log hr1_pos hr2_pos h12.le))
    · exact sub_pos.mpr (log_lt_log hr1_pos hr3_pos h23.trans h3R)
    · rw [div_le_one]
      · exact sub_le_sub_right (log_le_log hr2_pos hr3_pos h23.le) (log r1)
      · exact sub_pos.mpr (log_lt_log hr1_pos hr3_pos h23.trans h3R)
  
  -- The key inequality follows from the convexity of log M(exp x)
  have key : log (M r2) ≤ t * log (M r3) + (1 - t) * log (M r1) := by
    -- Transform via x = log r
    set x1 := log r1
    set x2 := log r2
    set x3 := log r3
    set φ : ℝ → ℝ := fun x ↦ log (M (exp x))
    
    -- Show φ is convex
    have φ_convex : ConvexOn ℝ (Set.Icc x1 x3) φ := by
      sorry -- This requires the Hadamard three-lines theorem applied to log ∘ M ∘ exp
    
    -- Apply convexity at x2
    have hx2 : x2 ∈ Set.Icc x1 x3 := ⟨log_le_log hr1_pos hr2_pos h12.le, 
                                      log_le_log hr2_pos hr3_pos h23.le⟩
    have hx : x2 = t • x3 + (1 - t) • x1 := by
      field_simp [t]
      rw [← sub_sub, sub_right_inj]
      ring
    rw [hx]
    exact φ_convex.2 hx2 (by linarith [ht.1]) (by linarith [ht.2]) rfl
    
  -- Convert back to original form
  convert key using 1
  · rfl
  · field_simp [t]
    ring