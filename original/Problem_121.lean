/-
Polya-Szego Problem 121
Part One, Chapter 3

Original problem:
The series

$$
p_{0}+p_{1} x+p_{2} x^{2}+\cdots+p_{m} x^{m}+\cdots
$$

with positive coefficients and finite radius of convergence $\varrho\left(p_{m}>0\right.$, $?>0$ ) is such that one term after the other, all terms in turn, become maximum term. Then $\frac{1}{\varrho}$ is the radius of convergence of the series

$$
\frac{1}{p_{0}}+\frac{x}{p_{1}}+\frac{x^{2}}{p_{2}}+\cdots+\frac{x^{m}}{p_{m}}+\cdots
$$

\begin{enumerate}
  \setcounter{enumi}{121}
  \item The dominance of the maximum term is 

Formalization notes: -- We formalize the main claim of Problem 121 from Polya-Szego.
-- The theorem states that given two power series with positive coefficients,
-- where the first has infinite radius of convergence and the second has finite
-- radius of convergence with each term becoming maximum in turn,
-- we can find corresponding x̄ and ȳ with a common "central subscript" n
-- such that specific inequalities hold between the normalized terms.
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.ENNReal

-- Formalization notes:
-- We formalize the main claim of Problem 121 from Polya-Szego.
-- The theorem states that given two power series with positive coefficients,
-- where the first has infinite radius of convergence and the second has finite
-- radius of convergence with each term becoming maximum in turn,
-- we can find corresponding x̄ and ȳ with a common "central subscript" n
-- such that specific inequalities hold between the normalized terms.

-- We define:
-- `a : ℕ → ℝ` and `b : ℕ → ℝ` are sequences of coefficients (aₘ ≥ 0, bₘ > 0)
-- `has_infinite_radius a` means the power series ∑ aₘ x^m converges for all x
-- `has_finite_radius b ρ` means the power series ∑ bₘ y^m has radius of convergence ρ
-- `terms_become_maximum b` formalizes that each term becomes maximum in turn
-- `central_subscript a b x y n` means n is a common index where the inequalities hold

open Filter
open Topology

-- Helper definitions for the problem conditions
def has_infinite_radius (a : ℕ → ℝ) : Prop :=
  ∀ (x : ℝ), Summable fun m : ℕ => a m * x ^ m

def has_finite_radius (b : ℕ → ℝ) (ρ : ℝ≥0∞) : Prop :=
  ρ > 0 ∧ ρ < ∞ ∧ 
  (∀ (y : ℝ), (y : ℝ≥0∞) < ρ → Summable fun m : ℕ => b m * y ^ m) ∧
  (∀ (y : ℝ), ρ < (y : ℝ≥0∞) → ¬Summable fun m : ℕ => b m * y ^ m)

def terms_become_maximum (b : ℕ → ℝ) : Prop :=
  ∀ (m : ℕ), b m > 0 ∧ 
    ∃ (y : ℝ) (h : y > 0), 
      (∀ (k : ℕ), b k * y ^ k ≤ b m * y ^ m) ∧
      (∀ (n : ℕ), n < m → ∃ (y' : ℝ) (h' : y' > 0), 
        (∀ (k : ℕ), b k * (y') ^ k ≤ b n * (y') ^ n) ∧ 
        ¬(∀ (k : ℕ), b k * (y') ^ k ≤ b m * (y') ^ m))

def central_subscript (a b : ℕ → ℝ) (x y : ℝ) (n : ℕ) : Prop :=
  x > 0 ∧ y > 0 ∧ a n * x ^ n > 0 ∧ b n * y ^ n > 0 ∧
  (∀ (k : ℕ), a k * x ^ k / (a n * x ^ n) ≤ b k * y ^ k / (b n * y ^ n)) ∧
  (∀ (k : ℕ), b k * y ^ k / (b n * y ^ n) ≤ 1)

theorem problem_121 (a b : ℕ → ℝ) (ha_pos : ∀ m, a m ≥ 0) (hb_pos : ∀ m, b m > 0)
    (ha_infinite : has_infinite_radius a) 
    (hb_finite : ∃ ρ, has_finite_radius b ρ)
    (hb_max_terms : terms_become_maximum b) :
    ∀ (x̄ : ℝ), x̄ > 0 → ∃ (ȳ : ℝ) (n : ℕ), 
      central_subscript a b x̄ ȳ n := by
  sorry

-- Proof attempt:
theorem problem_121 (a b : ℕ → ℝ) (ha_pos : ∀ m, a m ≥ 0) (hb_pos : ∀ m, b m > 0)
    (ha_infinite : has_infinite_radius a) 
    (hb_finite : ∃ ρ, has_finite_radius b ρ)
    (hb_max_terms : terms_become_maximum b) :
    ∀ (x̄ : ℝ), x̄ > 0 → ∃ (ȳ : ℝ) (n : ℕ), 
      central_subscript a b x̄ ȳ n := by
  intro x̄ hx̄
  -- Extract the radius ρ for series b
  obtain ⟨ρ, hρ⟩ := hb_finite
  -- Define the sequence of ratios (aₙ / bₙ) * x̄ⁿ
  let c (n : ℕ) := (a n / b n) * x̄ ^ n
  -- The sequence cₙ tends to 0 as n → ∞ since a has infinite radius and b has finite radius
  have hc_tendsto : Tendsto c atTop (𝓝 0) := by
    apply tendsto_pow_const_div_const_pow_of_lt_one (α := ℝ)
    · obtain ⟨_, hρ_lt_inf, _, _⟩ := hρ
      exact ENNReal.coe_lt_coe.1 (lt_of_lt_of_le (zero_lt_one) hρ_lt_inf)
    · exact ha_infinite x̄
  -- Since cₙ → 0, there exists a minimal n where cₙ is maximized
  have : ∃ n, ∀ k, c k ≤ c n := by
    by_cases h : ∀ n, c n = 0
    · use 0; intro k; rw [h k, h 0]
    · push_neg at h
      obtain ⟨n, hn⟩ := h
      have : ∃ n, IsMaxOn c (Set.Ici n) n := by
        apply exists_isMaxOn_of_tendsto_atTop
        · exact Filter.atTop_neBot
        · exact hc_tendsto
        · use n; exact hn
      obtain ⟨n, hn_max⟩ := this
      use n
      intro k
      by_cases hkn : k ≤ n
      · obtain ⟨y, hy_pos, hy_max, _⟩ := hb_max_terms n
        have hb_ratio : ∀ m, b m * y ^ m ≤ b n * y ^ n := by
          intro m; exact hy_max m
        have hc_eq : c n = (a n * x̄ ^ n) / (b n * y ^ n) * (y / x̄) ^ n := by
          field_simp [c, (hb_pos n).ne']
          ring
        refine le_trans ?_ (le_of_eq hc_eq.symm)
        sorry -- Need to show c k ≤ c n for k ≤ n
      · exact hn_max k (not_le.1 hkn).le
  obtain ⟨n, hn⟩ := this
  -- Construct ȳ as the value that makes bₙȳⁿ maximal
  obtain ⟨y, hy_pos, hy_max, _⟩ := hb_max_terms n
  use y, n
  refine ⟨hx̄, hy_pos, ?_, ?_, ?_, ?_⟩
  · have : a n * x̄ ^ n = b n * y ^ n * c n := by
      field_simp [c, (hb_pos n).ne']
      ring
    rw [this]
    exact mul_pos (mul_pos (hb_pos n) (pow_pos hy_pos n)) (by sorry) -- Need to show c n > 0
  · exact mul_pos (hb_pos n) (pow_pos hy_pos n)
  · intro k
    rw [div_le_div_iff (mul_pos (ha_pos n) (pow_pos hx̄ n)) (mul_pos (hb_pos n) (pow_pos hy_pos n))]
    simp [c] at hn
    have : a k * x̄ ^ k ≤ (a n / b n) * x̄ ^ n * b k * y ^ k := by
      rw [← mul_assoc, mul_comm _ (b k), mul_assoc]
      exact (hn k).trans (le_refl _)
    convert this using 1 <;> ring
  · intro k
    rw [div_le_one_iff (mul_pos (hb_pos k) (pow_pos hy_pos k)).le (mul_pos (hb_pos n) (pow_pos hy_pos n))]
    exact hy_max k