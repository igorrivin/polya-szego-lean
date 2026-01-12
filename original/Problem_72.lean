/-
Polya-Szego Problem 72
Part One, Chapter 2

Original problem:
Let $p_{0}, p_{1}, \ldots, p_{n}, \ldots$ be a sequence of positiv numbers that satisfy the condition

$$
\lim _{n \rightarrow \infty} \frac{p_{n}}{p_{0}+p_{1}+p_{2}+\cdots+p_{n}}=0 .
$$

The existence of $\lim _{n \rightarrow \infty} s_{n}=s$ implies

$$
\lim _{n \rightarrow \infty} \frac{s_{0} p_{n}+s_{1} p_{n-1}+\cdots+s_{n} p_{0}}{p_{0}+p_{1}+\cdots+p_{n}}=s .
$$

\begin{enumerate}
  \setcounter{enumi}{72}
  \item The two sequences of positive numbers
\end{enumerate}

$$
p_{0}, p_{1}, p_{2},

Formalization notes: -- We formalize Problem 74 which states that if φ is twice differentiable on [m, M]
-- with φ''(t) > 0 for all t ∈ [m, M], then for any t₁, t₂ ∈ [m, M] with t₁ < t₂,
-- we have φ(t₁) + φ(t₂) - 2φ((t₁ + t₂)/2) > 0.
-- This is a convexity condition: φ is strictly convex when φ'' > 0.
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.SecondDerivative

-- Formalization notes:
-- We formalize Problem 74 which states that if φ is twice differentiable on [m, M]
-- with φ''(t) > 0 for all t ∈ [m, M], then for any t₁, t₂ ∈ [m, M] with t₁ < t₂,
-- we have φ(t₁) + φ(t₂) - 2φ((t₁ + t₂)/2) > 0.
-- This is a convexity condition: φ is strictly convex when φ'' > 0.

theorem problem_74 {φ : ℝ → ℝ} {m M : ℝ} (hm : m < M) 
    (hderiv : ∀ x ∈ Set.Icc m M, DifferentiableAt ℝ φ x)
    (hderiv2 : ∀ x ∈ Set.Ioo m M, HasDerivAt (deriv φ) (deriv (deriv φ) x) x)
    (hpos : ∀ x ∈ Set.Icc m M, deriv (deriv φ) x > 0) :
    ∀ t₁ t₂ ∈ Set.Icc m M, t₁ < t₂ → φ t₁ + φ t₂ - 2 * φ ((t₁ + t₂)/2) > 0 := by
  sorry

-- Proof attempt:
theorem problem_74 {φ : ℝ → ℝ} {m M : ℝ} (hm : m < M) 
    (hderiv : ∀ x ∈ Set.Icc m M, DifferentiableAt ℝ φ x)
    (hderiv2 : ∀ x ∈ Set.Ioo m M, HasDerivAt (deriv φ) (deriv (deriv φ) x) x)
    (hpos : ∀ x ∈ Set.Icc m M, deriv (deriv φ) x > 0) :
    ∀ t₁ t₂ ∈ Set.Icc m M, t₁ < t₂ → φ t₁ + φ t₂ - 2 * φ ((t₁ + t₂)/2) > 0 := by
  intro t₁ ht₁ t₂ ht₂ hlt
  set a := (t₁ + t₂)/2
  have ha : a ∈ Set.Icc m M := by
    apply Set.mem_Icc.mpr
    constructor
    · apply le_trans (by linarith [ht₁.1, ht₂.1]) 
      simp [a]; ring
    · apply le_trans (by linarith [ht₁.2, ht₂.2])
      simp [a]; ring
  
  -- First Taylor expansion around a for t₁
  have hT₁ : ∃ τ₁ ∈ Set.Ioo t₁ a, φ t₁ = φ a + (t₁ - a) * deriv φ a + (t₁ - a)^2 / 2 * deriv (deriv φ) τ₁ := by
    refine exists_hasDerivAt_slope_of_hasDerivAt_of_lt ?_ ?_ ?_
    · intro x hx
      exact hderiv x ⟨by linarith [hx.1], by linarith [hx.2, ha.2]⟩
    · intro x hx
      exact hderiv2 x ⟨by linarith [hx.1], by linarith [hx.2, ha.2]⟩
    · linarith
  
  -- Second Taylor expansion around a for t₂
  have hT₂ : ∃ τ₂ ∈ Set.Ioo a t₂, φ t₂ = φ a + (t₂ - a) * deriv φ a + (t₂ - a)^2 / 2 * deriv (deriv φ) τ₂ := by
    refine exists_hasDerivAt_slope_of_hasDerivAt_of_lt ?_ ?_ ?_
    · intro x hx
      exact hderiv x ⟨by linarith [hx.1, ha.1], by linarith [hx.2]⟩
    · intro x hx
      exact hderiv2 x ⟨by linarith [hx.1, ha.1], by linarith [hx.2]⟩
    · linarith
  
  -- Extract the points τ₁ and τ₂
  rcases hT₁ with ⟨τ₁, hτ₁, eq₁⟩
  rcases hT₂ with ⟨τ₂, hτ₂, eq₂⟩
  
  -- Compute the main expression
  have key : φ t₁ + φ t₂ - 2 * φ a = 
      (t₁ - a)^2 / 2 * deriv (deriv φ) τ₁ + (t₂ - a)^2 / 2 * deriv (deriv φ) τ₂ := by
    rw [eq₁, eq₂]
    field_simp [a]
    ring
  
  -- Simplify the expression further
  have : (t₁ - a)^2 = (t₂ - a)^2 := by
    field_simp [a]
    ring
  rw [this] at key
  
  -- Final positivity argument
  rw [key]
  have hpos₁ : deriv (deriv φ) τ₁ > 0 := by
    apply hpos τ₁
    exact ⟨by linarith [hτ₁.1, ht₁.1], by linarith [hτ₁.2, ha.2]⟩
  have hpos₂ : deriv (deriv φ) τ₂ > 0 := by
    apply hpos τ₂
    exact ⟨by linarith [hτ₂.1, ha.1], by linarith [hτ₂.2, ht₂.2]⟩
  have sq_pos : (t₂ - a)^2 > 0 := by
    apply pow_two_pos_of_ne_zero
    field_simp [a]
    linarith
  apply add_pos
  · apply mul_pos
    · apply div_pos (by norm_num) (by norm_num)
      exact sq_pos
    · exact hpos₁
  · apply mul_pos
    · apply div_pos (by norm_num) (by norm_num)
      exact sq_pos
    · exact hpos₂