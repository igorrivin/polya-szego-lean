/-
Polya-Szego Problem 133
Part One, Chapter 3

Original problem:
Let $f(x)$ denote a continuous function on $[0,1]$. The convergence of

$$
\lim _{n \rightarrow \infty} \frac{1}{2} \cdot \frac{3}{2} \cdot \frac{5}{4} \cdots \frac{2 n+1}{2 n} \int_{0}^{1} f(t)\left[1-(x-t)^{2}\right]^{n} d t=f(x)
$$

is uniform for $\varepsilon \leqq x \leqq 1-\varepsilon, 0<\varepsilon<\frac{1}{2}, \varepsilon$ fixed.\\

Formalization notes: -- We formalize the statement about uniform convergence of a convolution-type operator.
-- The expression is: 
--   K_n(f)(x) = (∏_{k=0}^{n-1} (2k+1)/(2k)) * ∫_[0,1] f(t) * [1 - (x-t)^2]^n dt
-- converges uniformly to f(x) on [ε, 1-ε] for any fixed ε ∈ (0, 1/2).
-- We assume f is continuous on [0,1].
-/

import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Calculus.ContDiff
import Mathlib.Analysis.SpecialFunctions.Gamma
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.MeasureTheory.Integral.SetIntegral

-- Formalization notes:
-- We formalize the statement about uniform convergence of a convolution-type operator.
-- The expression is: 
--   K_n(f)(x) = (∏_{k=0}^{n-1} (2k+1)/(2k)) * ∫_[0,1] f(t) * [1 - (x-t)^2]^n dt
-- converges uniformly to f(x) on [ε, 1-ε] for any fixed ε ∈ (0, 1/2).
-- We assume f is continuous on [0,1].

open Set
open Real
open Interval
open scoped Real
open ComplexConjugate
open BigOperators

theorem problem_133 (f : ℝ → ℝ) (hf : ContinuousOn f (Set.uIcc (0 : ℝ) 1)) 
    (ε : ℝ) (hε : 0 < ε) (hε_half : ε < 1/2) :
    TendstoUniformlyOn 
      (fun (n : ℕ) (x : ℝ) => 
        let I_n x := ∫ t in (0:ℝ)..1, f t * ((1 : ℝ) - (x - t)^2)^n
        let C_n := ∏ k in Finset.range n, ((2:ℝ) * k + 1) / ((2:ℝ) * k) 
        C_n * I_n x)
      (fun x : ℝ => f x)
      (Set.uIcc ε (1 - ε)) atTop := by
  sorry

-- Proof attempt:
theorem problem_133 (f : ℝ → ℝ) (hf : ContinuousOn f (Set.uIcc (0 : ℝ) 1)) 
    (ε : ℝ) (hε : 0 < ε) (hε_half : ε < 1/2) :
    TendstoUniformlyOn 
      (fun (n : ℕ) (x : ℝ) => 
        let I_n x := ∫ t in (0:ℝ)..1, f t * ((1 : ℝ) - (x - t)^2)^n
        let C_n := ∏ k in Finset.range n, ((2:ℝ) * k + 1) / ((2:ℝ) * k) 
        C_n * I_n x)
      (fun x : ℝ => f x)
      (Set.uIcc ε (1 - ε)) atTop := by
  -- Step 1: Show C_n behaves like √(n/π)
  have C_n_asymptotics : ∃ c₁ c₂, 0 < c₁ ∧ 0 < c₂ ∧ ∀ n, 
    c₁ * sqrt n ≤ C_n n ≤ c₂ * sqrt n := by
    sorry  -- This requires Stirling's formula approximation

  -- Step 2: Define the kernel Pₙ(x,t)
  let Pₙ (n : ℕ) (x t : ℝ) := ((1 - (x - t)^2)^n) / (I_n n x)

  -- Step 3: Show Pₙ is a positive kernel
  have Pₙ_pos : ∀ n x t, x ∈ uIcc ε (1 - ε) → t ∈ uIcc 0 1 → Pₙ n x t ≥ 0 := by
    intro n x t hx ht
    simp [Pₙ, I_n]
    apply div_nonneg
    · apply pow_nonneg
      linarith [sub_le_iff_le_add'.mpr (abs_le.mp (abs_sub_le_iff.mpr (le_of_lt (mem_uIcc.mp hx))))]
    · exact integral_nonneg (fun t _ => mul_nonneg (hf.nonneg_of_nonneg (by linarith) (mem_uIcc.mp ht)) 
        (pow_nonneg (by linarith) _))

  -- Step 4: Show the kernel integrates to 1
  have Pₙ_integral : ∀ n x, x ∈ uIcc ε (1 - ε) → ∫ t in 0..1, Pₙ n x t = 1 := by
    intro n x hx
    simp [Pₙ, I_n]
    field_simp
    exact integral_sub_interval (fun t => f t * (1 - (x - t)^2)^n) 0 1

  -- Step 5: Show the kernel concentrates at x as n → ∞
  have Pₙ_concentration : ∀ δ > 0, 
    TendstoUniformlyOn (fun n x => ∫ t in {t | |t - x| ≥ δ}, Pₙ n x t) (fun _ => 0) 
    (uIcc ε (1 - ε)) atTop := by
    sorry  -- Requires careful estimation of the integrals

  -- Step 6: Apply general approximation theorem
  refine TendstoUniformlyOn.of_approx_continuous hf.continuousOn ?_ Pₙ_pos Pₙ_integral Pₙ_concentration
  · intro n x hx
    simp [C_n, I_n]
    field_simp
    rw [mul_comm]
    congr
    -- Need to show C_n = 1 / ∫₀¹ (1 - (x - t)^2)^n dt
    sorry  -- Requires computation of the integral and relation to C_n