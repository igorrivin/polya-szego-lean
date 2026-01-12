/-
Polya-Szego Problem 188
Part One, Chapter 4

Original problem:
Let $r_{1 n}, r_{2 n}, r_{3 n}, \ldots, r_{\varphi n}$ denote the positive integers that are smaller than $n$ and relative prime to $n$; their number is $\varphi=\varphi(n)$ [VIII 25]. Then

$$
\lim _{n \rightarrow \infty} \frac{f\left(\frac{v_{1 n}}{n}\right)+f\left(\frac{r_{2 n}}{n}\right)+f\left(\frac{r_{3 n}}{n}\right)+\cdots+f\left(\frac{r_{4 n}}{n}\right)}{\varphi(n)}=\int_{0}^{1} f(x) d x
$$

holds for any properly integrable function $f(x)$ on [ 0,1 ]. [VIII 35.]\\

Formalization notes: -- 1. We formalize the limit statement for Riemann integrable functions on [0,1]
-- 2. The set {r : 1 ≤ r ≤ n | gcd r n = 1} represents the positive integers < n and coprime to n
-- 3. φ(n) is Nat.totient n
-- 4. We use `Tendsto` for the limit as n → ∞
-- 5. The integral is the Riemann integral on [0,1]
-/

import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Data.Nat.Totient

-- Formalization notes:
-- 1. We formalize the limit statement for Riemann integrable functions on [0,1]
-- 2. The set {r : 1 ≤ r ≤ n | gcd r n = 1} represents the positive integers < n and coprime to n
-- 3. φ(n) is Nat.totient n
-- 4. We use `Tendsto` for the limit as n → ∞
-- 5. The integral is the Riemann integral on [0,1]

theorem problem_188_part_one (f : ℝ → ℝ) 
    (hf_int : IntegrableOn f (Set.Icc (0 : ℝ) 1) volume) :
    Filter.Tendsto (λ (n : ℕ) => 
        if hn : n > 0 then 
          let coprime_numbers := (Finset.Icc 1 (n - 1)).filter (λ r => r.gcd n = 1) in
          ((coprime_numbers.sum (λ r => f (r / n : ℝ))) / (Nat.totient n : ℝ))
        else 0)
    Filter.atTop (𝓝 (∫ x in (0:ℝ)..1, f x)) := by
  sorry

-- Proof attempt:
theorem problem_188_part_one (f : ℝ → ℝ) 
    (hf_int : IntegrableOn f (Set.Icc (0 : ℝ) 1) volume) :
    Filter.Tendsto (λ (n : ℕ) => 
        if hn : n > 0 then 
          let coprime_numbers := (Finset.Icc 1 (n - 1)).filter (λ r => r.gcd n = 1) in
          ((coprime_numbers.sum (λ r => f (r / n : ℝ))) / (Nat.totient n : ℝ))
        else 0)
    Filter.atTop (𝓝 (∫ x in (0:ℝ)..1, f x)) := by
  simp only [ne_eq, Filter.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ_pos, hδ⟩ := hf_int.hasBoxIntegral (by norm_num) hε
  have hδ_pos' : 0 < δ := hδ_pos
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / δ)
  use N
  intro n hn
  by_cases hn' : n > 0
  · simp [hn']
    let coprime_numbers := (Finset.Icc 1 (n - 1)).filter (λ r => r.gcd n = 1)
    have : Nat.totient n = Fintype.card {r : ℕ | r ≤ n ∧ r.gcd n = 1} := by
      simp [Nat.totient_eq_card_lt_and_coprime]
    simp only [this]
    have : (Nat.totient n : ℝ) = (Finset.card coprime_numbers : ℝ) := by
      simp [coprime_numbers, Nat.totient_eq_card_lt_and_coprime]
    rw [this]
    simp only [div_eq_inv_mul]
    have h_partition : ∀ r ∈ coprime_numbers, r / n ∈ Set.Icc (0 : ℝ) 1 := by
      intro r hr
      simp at hr
      have hr1 : 1 ≤ r := hr.1.1
      have hr2 : r ≤ n - 1 := hr.1.2
      constructor
      · apply div_nonneg
        · exact Nat.cast_nonneg r
        · exact Nat.cast_pos.mpr hn'
      · rw [div_le_one (Nat.cast_pos.mpr hn')]
        exact Nat.cast_le.mpr (Nat.le_pred_of_lt (Nat.lt_of_le_of_lt hr2 (Nat.pred_lt hn'.ne')))
    have h_uniform : ∀ (x ∈ Set.Icc (0 : ℝ) 1), ∃ r ∈ coprime_numbers, |x - r / n| < δ := by
      intro x hx
      obtain ⟨r, hr, h⟩ := exists_nat_div_near x hn' hδ_pos'
      refine ⟨r, ?_, h⟩
      simp [coprime_numbers]
      constructor
      · constructor
        · exact hr.1
        · exact hr.2.le
      · exact hr.2.2
    have h_sum_eq : (coprime_numbers.sum (λ r => f (r / n))) / Finset.card coprime_numbers = 
        (Finset.card coprime_numbers)⁻¹ • (coprime_numbers.sum (λ r => f (r / n))) := by
      simp [smul_eq_mul, inv_mul_eq_div]
    rw [h_sum_eq]
    refine hδ (coprime_numbers) (λ r hr => ⟨r / n, h_partition r hr⟩) ?_
    intro x hx
    obtain ⟨r, hr, h⟩ := h_uniform x hx
    exact ⟨r, hr, h⟩
  · simp [hn']
    exact hε