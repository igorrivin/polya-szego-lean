/-
Polya-Szego Problem 46
Part Three, Chapter 1

Original problem:
What col in order that its

Pt. III, Chap. 1, No. 37-46

$$
-z_{n}^{2}+\cdots
$$

kretges too. for which all the

$$
k=1,2,3, \ldots
$$

$$
k=1,2,3, \ldots
$$

i numbers. If there -, $\geqq \delta$ for $l<k$, FCyence

$$
n=1,2,3, \ldots
$$

\# center at the origin.\\[0pt]
--: of rectangles.]\\
e complex sequence\\
$\left[-\frac{1}{n}\right)$.\\
$=$ 一 $_{\text {。 }}$\\
Ir Line. The distance Line connecting the A-chimedean spiral;\\
\includegraphics[max width=\textwidth, center]{c6efe72a-741b-450a

Formalization notes: -- We formalize Toeplitz's theorem on convergence-preserving triangular arrays.
-- A triangular array (a : ℕ → ℕ → ℝ) with a n ν = 0 when ν > n transforms sequences z : ℕ → ℝ
-- to w_n = Σ_{ν=0}^n a n ν * z ν.
-- The array is convergence-preserving if for every convergent sequence z, the transformed sequence w is also convergent.
-- The theorem states that this is equivalent to three conditions:
-- 1. For each fixed ν, lim_{n→∞} a n ν exists (call it a_ν)
-- 2. The row sums σ_n = Σ_{ν=0}^n a n ν converge as n → ∞
-- 3. The sums of absolute values ζ_n = Σ_{ν=0}^n |a n ν| are bounded
-/

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.NormedSpace.Basic
import Mathlib.Topology.Instances.Real

-- Formalization notes: 
-- We formalize Toeplitz's theorem on convergence-preserving triangular arrays.
-- A triangular array (a : ℕ → ℕ → ℝ) with a n ν = 0 when ν > n transforms sequences z : ℕ → ℝ
-- to w_n = Σ_{ν=0}^n a n ν * z ν.
-- The array is convergence-preserving if for every convergent sequence z, the transformed sequence w is also convergent.
-- The theorem states that this is equivalent to three conditions:
-- 1. For each fixed ν, lim_{n→∞} a n ν exists (call it a_ν)
-- 2. The row sums σ_n = Σ_{ν=0}^n a n ν converge as n → ∞
-- 3. The sums of absolute values ζ_n = Σ_{ν=0}^n |a n ν| are bounded

theorem toeplitz_convergence_preserving_iff (a : ℕ → ℕ → ℝ) 
    (ha_triangular : ∀ n ν, ν > n → a n ν = 0) : 
    (∀ (z : ℕ → ℝ) (L : ℝ), 
        Tendsto z atTop (𝓝 L) → 
        ∃ (M : ℝ), Tendsto (λ n => ∑ ν in Finset.range (n + 1), a n ν * z ν) atTop (𝓝 M)) 
    ↔ 
    (∃ (a_limit : ℕ → ℝ), 
        (∀ ν, Filter.Tendsto (λ n => a n ν) atTop (𝓝 (a_limit ν))) ∧
        (∃ (σ : ℝ), Filter.Tendsto (λ n => ∑ ν in Finset.range (n + 1), a n ν) atTop (𝓝 σ)) ∧
        (∃ (B : ℝ), ∀ n, ∑ ν in Finset.range (n + 1), |a n ν| ≤ B)) := by
  sorry

-- Proof attempt:
theorem toeplitz_convergence_preserving_iff (a : ℕ → ℕ → ℝ) 
    (ha_triangular : ∀ n ν, ν > n → a n ν = 0) : 
    (∀ (z : ℕ → ℝ) (L : ℝ), 
        Tendsto z atTop (𝓝 L) → 
        ∃ (M : ℝ), Tendsto (λ n => ∑ ν in Finset.range (n + 1), a n ν * z ν) atTop (𝓝 M)) 
    ↔ 
    (∃ (a_limit : ℕ → ℝ), 
        (∀ ν, Filter.Tendsto (λ n => a n ν) atTop (𝓝 (a_limit ν))) ∧
        (∃ (σ : ℝ), Filter.Tendsto (λ n => ∑ ν in Finset.range (n + 1), a n ν) atTop (𝓝 σ)) ∧
        (∃ (B : ℝ), ∀ n, ∑ ν in Finset.range (n + 1), |a n ν| ≤ B)) := by
  constructor
  · -- Forward direction: convergence-preserving implies the three conditions
    intro h
    -- First condition: limit of columns exists
    have h1 : ∀ ν, ∃ l, Tendsto (λ n => a n ν) atTop (𝓝 l) := by
      intro ν
      let z := fun n => if n = ν then 1 else 0
      have hz : Tendsto z atTop (𝓝 0) := by
        apply tendsto_const_nhds.congr'
        filter_upwards [Filter.eventually_ge_atTop (ν + 1)] with n hn
        simp [z, if_neg (by linarith)]
      obtain ⟨M, hM⟩ := h z 0 hz
      use M
      have : (λ n => a n ν) = λ n => ∑ μ in Finset.range (n + 1), a n μ * z μ := by
        ext n
        simp [z, Finset.sum_ite_eq, ha_triangular]
        split_ifs with hν
        · simp [hν]
        · have : ν > n := by linarith
          simp [ha_triangular n ν this]
      rw [this]
      exact hM
    let a_limit := fun ν => Classical.choose (h1 ν)
    have ha_limit : ∀ ν, Tendsto (λ n => a n ν) atTop (𝓝 (a_limit ν)) := 
      fun ν => Classical.choose_spec (h1 ν)
    
    -- Second condition: row sums converge
    let z := fun _ => 1
    have hz : Tendsto z atTop (𝓝 1) := tendsto_const_nhds
    obtain ⟨σ, hσ⟩ := h z 1 hz
    have : (λ n => ∑ ν in Finset.range (n + 1), a n ν) = λ n => ∑ ν in Finset.range (n + 1), a n ν * z ν := by
      simp [z]
    rw [this] at hσ
    
    -- Third condition: uniform boundedness of absolute sums
    let z := fun ν => (-1) ^ ν
    have hz : Tendsto z atTop (𝓝 0) := by
      apply tendsto_atTop_of_eventually_const
      use 0
      intro n hn
      simp [z]
    obtain ⟨M, hM⟩ := h z 0 hz
    have h_bdd : ∃ B, ∀ n, ∑ ν in Finset.range (n + 1), |a n ν| ≤ B := by
      refine ⟨M + 1, fun n => ?_⟩
      have hM' : ∀ᶠ m in atTop, |∑ ν in Finset.range (m + 1), a m ν * z ν| ≤ M + 1 :=
        eventually_ge_of_tendsto_atTop hM (M + 1)
      obtain ⟨N, hN⟩ := hM'.exists
      refine le_of_forall_ge_upperBound _ _ fun B hB => ?_
      apply Finset.induction (motive := fun s => ∑ ν in s, |a n ν| ≤ B)
      · simp
      · intro k s hks ih
        rw [Finset.sum_insert hks]
        refine le_trans ?_ hB
        by_cases hn : n ≤ N
        · exact (Finset.sum_le_sum fun ν _ => abs_nonneg _)
        · have : n > N := by linarith
          specialize hN n this.le
          have : ∑ ν in Finset.range (n + 1), a n ν * z ν = ∑ ν in s, a n ν * z ν + a n k * z k := by
            rw [← Finset.sum_insert hks, Finset.insert_eq, Finset.mem_range]
            simp [ha_triangular]
          rw [this] at hN
          sorry -- This part needs more work to complete the boundedness argument
    exact ⟨a_limit, ha_limit, ⟨σ, hσ⟩, h_bdd⟩
  
  · -- Reverse direction: the three conditions imply convergence-preserving
    rintro ⟨a_limit, ha_limit, ⟨σ, hσ⟩, ⟨B, hB⟩⟩ z L hz
    have h1 : ∀ ν, Tendsto (λ n => a n ν) atTop (𝓝 (a_limit ν)) := ha_limit
    have h2 : Tendsto (λ n => ∑ ν in Finset.range (n + 1), a n ν) atTop (𝓝 σ) := hσ
    
    -- Main convergence proof
    let w := λ n => ∑ ν in Finset.range (n + 1), a n ν * z ν
    have hw : ∃ M, Tendsto w atTop (𝓝 M) := by
      refine ⟨L * σ, ?_⟩
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le' ?_ ?_ ?_ ?_
      · -- Lower bound
        sorry
      · -- Upper bound
        sorry
      · -- Actual limit proof
        sorry
    exact hw