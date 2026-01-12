/-
Polya-Szego Problem 104
Part One, Chapter 3

Original problem:
We define

$$
4[x]-2[2 x]+1=s(x)
$$

Then we have ( $n$ integer) the limit relation

$$
\lim _{n \rightarrow \infty} \int_{0}^{1} f(x) s(n x) d x=0
$$

for any properly integrable function $f(x)$ on $[0,1]$. [Sketch $s(n x)$, VIII 3.]\\

Formalization notes: -- 1. We define s(x) = 4⌊x⌋ - 2⌊2x⌋ + 1 where ⌊·⌋ is the floor function
-- 2. We formalize the limit statement for Riemann integrable functions on [0,1]
-- 3. The theorem states that for any Riemann integrable function f on [0,1],
--    the integral of f(x) * s(n*x) over [0,1] tends to 0 as n → ∞
-- 4. We use `Tendsto` for the limit and `intervalIntegral` for ∫₀¹
-/

import Mathlib.Analysis.Calculus.FTC
import Mathlib.Analysis.SpecialFunctions.Int
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Data.Real.Floor

-- Formalization notes:
-- 1. We define s(x) = 4⌊x⌋ - 2⌊2x⌋ + 1 where ⌊·⌋ is the floor function
-- 2. We formalize the limit statement for Riemann integrable functions on [0,1]
-- 3. The theorem states that for any Riemann integrable function f on [0,1],
--    the integral of f(x) * s(n*x) over [0,1] tends to 0 as n → ∞
-- 4. We use `Tendsto` for the limit and `intervalIntegral` for ∫₀¹

noncomputable section

def s (x : ℝ) : ℝ := 4 * (Int.floor x : ℝ) - 2 * (Int.floor (2 * x) : ℝ) + 1

theorem problem_104 (f : ℝ → ℝ) (hf : IntegrableOn f (Set.Icc (0 : ℝ) 1) volume) 
    (hf_riemann : RiemannIntegrable f (0 : ℝ) 1) :
    Tendsto (λ (n : ℕ) => ∫ x in (0 : ℝ)..1, f x * s (n * x)) atTop (𝓝 0) := by
  sorry

-- Proof attempt:
theorem problem_104 (f : ℝ → ℝ) (hf : IntegrableOn f (Set.Icc (0 : ℝ) 1) volume) 
    (hf_riemann : RiemannIntegrable f (0 : ℝ) 1) :
    Tendsto (λ (n : ℕ) => ∫ x in (0 : ℝ)..1, f x * s (n * x)) atTop (𝓝 0) := by
  -- First, we'll show that s(n*x) is ±1 on intervals of length 1/(2n)
  have s_prop : ∀ (n : ℕ) (x : ℝ), x ∈ Set.Icc (0 : ℝ) 1 → 
      s (n * x) = if (Int.floor (2 * n * x) : ℤ) % 2 = 0 then 1 else -1 := by
    intro n x hx
    have nx_nonneg : 0 ≤ n * x := by nlinarith [hx.1, (Nat.cast_nonneg n)]
    have nx_le_n : n * x ≤ n := by nlinarith [hx.2, (Nat.cast_pos.mpr (Nat.succ_pos n))]
    simp [s]
    rw [Int.floor_eq_iff, Int.floor_eq_iff]
    · simp [← mul_assoc]
      constructor
      · linarith
      · linarith
    · simp [← mul_assoc]
      constructor
      · linarith
      · linarith
    all_goals { omega }

  -- The key step is to rewrite the integral as a sum of differences
  have integral_eq : ∀ (n : ℕ), ∫ x in (0:ℝ)..1, f x * s (n * x) = 
      ∑ v in Finset.range n, (∫ y in (0:ℝ)..(1/(2*n)), 
        f ((v : ℝ)/n + y) - f ((v : ℝ)/n + y + 1/(2*n)))) := by
    intro n
    sorry -- This requires careful interval decomposition and is non-trivial in Lean

  -- Now we estimate the absolute value of the integral
  have abs_integral_bound : ∀ (n : ℕ), 
      |∫ x in (0:ℝ)..1, f x * s (n * x)| ≤ ∑ v in Finset.range n, 
      (1/(2*n)) * (sSup (Set.image (λ x => |f x|) (Set.Icc ((v:ℝ)/n) ((v+1:ℝ)/n))) - 
      sInf (Set.image (λ x => |f x|) (Set.Icc ((v:ℝ)/n) ((v+1:ℝ)/n)))) := by
    intro n
    sorry -- This follows from the previous equality and properties of oscillation

  -- Since f is Riemann integrable, the oscillation tends to 0 as n → ∞
  have osc_tendsto_zero : Tendsto (λ (n : ℕ) => 
      ∑ v in Finset.range n, (1/(2*n)) * 
      (sSup (Set.image (λ x => |f x|) (Set.Icc ((v:ℝ)/n) ((v+1:ℝ)/n))) - 
      sInf (Set.image (λ x => |f x|) (Set.Icc ((v:ℝ)/n) ((v+1:ℝ)/n))))) atTop (𝓝 0) := by
    sorry -- This uses Riemann integrability condition

  -- Apply squeeze theorem to conclude
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds osc_tendsto_zero
  · intro n; exact abs_nonneg _
  · intro n; exact abs_integral_bound n