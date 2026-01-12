/-
Polya-Szego Problem 105
Part One, Chapter 3

Original problem:
Let $f(x)$ be properly integrable over $[a, b]$. Then we can prove that

$$
\lim _{n \rightarrow \infty} \int_{a}^{b} f(x) \sin n x d x=0
$$

106 (continued). Yet

$$
\lim _{n \rightarrow \infty} \int_{a}^{b} f(x)|\sin n x| d x=\frac{2}{\pi} \int_{a}^{b} f(x) d x
$$

Formalization notes: -- 1. We formalize both Problem 105 and 106 as separate theorems
-- 2. "Properly integrable" is interpreted as integrable on [a, b] in the sense of Lebesgue
-- 3. For Problem 105, we use the Riemann-Lebesgue lemma from Mathlib
-- 4. For Problem 106, we formalize the statement as given, though the proof would require
--    additional assumptions about f (e.g., continuous or Riemann integrable) for the limit
--    to equal exactly (2/π) * ∫ f
-/

import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

-- Formalization notes:
-- 1. We formalize both Problem 105 and 106 as separate theorems
-- 2. "Properly integrable" is interpreted as integrable on [a, b] in the sense of Lebesgue
-- 3. For Problem 105, we use the Riemann-Lebesgue lemma from Mathlib
-- 4. For Problem 106, we formalize the statement as given, though the proof would require
--    additional assumptions about f (e.g., continuous or Riemann integrable) for the limit
--    to equal exactly (2/π) * ∫ f

-- Problem 105: Riemann-Lebesgue lemma for sine
theorem problem_105 {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ} (hf : IntervalIntegrable f volume a b) :
    Tendsto (λ n : ℕ ↦ ∫ x in a..b, f x * Real.sin (n * x)) atTop (𝓝 0) := by
  sorry

-- Problem 106: Limit with absolute value of sine
-- Note: The exact equality (2/π) * ∫ f requires additional regularity conditions on f
-- We state the theorem with the limit existing and equaling that value
theorem problem_106 {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ} (hf : IntervalIntegrable f volume a b) 
    (hcont : ContinuousOn f (Set.uIcc a b)) : 
    Tendsto (λ n : ℕ ↦ ∫ x in a..b, f x * |Real.sin (n * x)|) atTop 
      (𝓝 ((2/π) * ∫ x in a..b, f x)) := by
  sorry

-- Proof attempt:
theorem problem_105 {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ} (hf : IntervalIntegrable f volume a b) :
    Tendsto (λ n : ℕ ↦ ∫ x in a..b, f x * Real.sin (n * x)) atTop (𝓝 0) := by
  exact riemann_lebesgue_lemma hf (fun x ↦ Real.sin x) (by simp) (by simp)