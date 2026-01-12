/-
Polya-Szego Problem 113
Part One, Chapter 3

Original problem:
If $f(x)$ is

Suppose that the function $f(x)$ is bounded on the interval $[a, b]$ and

Length converges to\\
$\mathrm{r}=\mathrm{r} d \mathrm{~d}$.\\
｜ower $-a, b]$ and $\varphi(x)$\\
$p=\dot{d x}$.\\
vess on $[a, b]$ ．There and $\Psi(x)$ ，such\\
points of discon－

F $\tau:$ and $\Psi(x)$ may Des the total varia－

Fretch $s(n x)$, VIII 3．］\\
T＝⿰扌⿰丿⿱丄𠃍⿴⿱冂一⿰丨丨寸犬 we can prove\\
be memerval $[a, b]$ and\\
$z_{1}, x_{2}, \ldots, x_{n-1}, x_{n}$ ，\\
whereby

$$
a=x_{0}<x_{1}<x_{2}<\cdots<x_{n-1}<x_{n

Formalization notes: -- We formalize the statement from Problem 113 about a monotone function f on [1, ∞)
-- with convergent integral ∫₁^∞ x^α f(x) dx, where the conclusion is:
--    lim_{x → ∞} x^{α+1} f(x) = 0
-- We use monotone to mean either non-decreasing or non-increasing.
-- We need to specify that f is integrable on every finite interval [1, X].
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.MeanInequalities
import Mathlib.MeasureTheory.Integral.IntervalIntegral

-- Formalization notes: 
-- We formalize the statement from Problem 113 about a monotone function f on [1, ∞)
-- with convergent integral ∫₁^∞ x^α f(x) dx, where the conclusion is:
--    lim_{x → ∞} x^{α+1} f(x) = 0
-- We use monotone to mean either non-decreasing or non-increasing.
-- We need to specify that f is integrable on every finite interval [1, X].

theorem problem_113 {α : ℝ} {f : ℝ → ℝ} (hmono : MonotoneOn f (Set.Ici 1)) 
    (hint : ∀ (X : ℝ), 1 ≤ X → IntervalIntegrable f MeasureTheory.volume 1 X)
    (hconv : ∃ (I : ℝ), Tendsto (λ (X : ℝ) ↦ ∫ x in 1..X, (x : ℝ)^α * f x) atTop (𝓝 I)) :
    Tendsto (λ (x : ℝ) ↦ (x : ℝ)^(α + 1) * f x) atTop (𝓝 0) := by
  sorry

-- Proof attempt:
theorem problem_113 {α : ℝ} {f : ℝ → ℝ} (hmono : MonotoneOn f (Set.Ici 1)) 
    (hint : ∀ (X : ℝ), 1 ≤ X → IntervalIntegrable f MeasureTheory.volume 1 X)
    (hconv : ∃ (I : ℝ), Tendsto (λ (X : ℝ) ↦ ∫ x in 1..X, (x : ℝ)^α * f x) atTop (𝓝 I)) :
    Tendsto (λ (x : ℝ) ↦ (x : ℝ)^(α + 1) * f x) atTop (𝓝 0) := by
  -- First, extract the limit I from hconv
  obtain ⟨I, hI⟩ := hconv
  
  -- Consider two cases: f is eventually non-increasing or eventually non-decreasing
  by_cases h_eventually_decreasing : ∃ M ≥ 1, ∀ x ≥ M, ∀ y ≥ x, f y ≤ f x
  · -- Case 1: f is eventually non-increasing
    obtain ⟨M, hM, hf_decr⟩ := h_eventually_decreasing
    -- We'll show that x^(α+1)*f(x) tends to 0
    refine tendsto_atTop_zero_of_nonpos_of_integral_bounded (fun x => (x^(α+1) * f x)) ?_ ?_ ?_
    · -- Show the function is eventually non-positive
      intro x hx
      have hx' : 1 ≤ x := le_trans hM hx
      rw [mul_nonpos_iff]
      right
      refine ⟨by positivity, ?_⟩
      have hf := hmono hx' (le_refl x) (le_refl x)
      have hMx : M ≤ x := hx
      have hfx := hf_decr x hMx x (le_refl x)
      exact hfx
    · -- Show integrability
      intro X hX
      have hX' : 1 ≤ X := le_trans hM hX
      exact IntervalIntegrable.mul_continuousOn (hint X hX') 
        (ContinuousOn.rpow continuousOn_id (fun _ _ => Or.inl (by linarith)) (by simp))
    · -- Show integral is bounded
      use I - ∫ x in 1..M, x^α * f x
      intro X hX
      have hM' : 1 ≤ M := hM
      have hX' : 1 ≤ X := le_trans hM hX
      have hMX : M ≤ X := hX
      rw [← intervalIntegral.integral_add_adjacent_intervals (hint M hM') (hint X hX') hMX]
      have hsplit : ∫ x in 1..X, x^α * f x = ∫ x in 1..M, x^α * f x + ∫ x in M..X, x^α * f x := by
        rw [← integral_union (by rw [interval_oc_union_interval_oc_eq_interval, min_eq_left hM'])]
        simp [hM']
      rw [hsplit]
      simp
      have h_tendsto : Tendsto (fun X => ∫ x in M..X, x^α * f x) atTop (𝓝 (I - ∫ x in 1..M, x^α * f x)) := by
        have := Tendsto.sub hI (tendsto_const_nhds (a := ∫ x in 1..M, x^α * f x))
        convert this using 2
        ext X
        rw [← integral_union (by rw [interval_oc_union_interval_oc_eq_interval, min_eq_left hM'])]
        simp [hM']
      exact tendsto_nhds_unique h_tendsto (tendsto_const_nhds (a := I - ∫ x in 1..M, x^α * f x))
  
  · -- Case 2: f is not eventually non-increasing, hence eventually non-decreasing
    push_neg at h_eventually_decreasing
    have h_eventually_increasing : ∀ M ≥ 1, ∃ x ≥ M, ∃ y ≥ x, f y > f x := by
      intro M hM
      specialize h_eventually_decreasing M hM
      push_neg at h_eventually_decreasing
      exact h_eventually_decreasing
    -- Now f is eventually non-decreasing
    -- We'll show that x^(α+1)*f(x) tends to 0
    refine tendsto_atTop_zero_of_nonneg_of_integral_bounded (fun x => (x^(α+1) * f x)) ?_ ?_ ?_
    · -- Show the function is eventually non-negative
      intro x hx
      have hx' : 1 ≤ x := hx
      rw [mul_nonneg_iff]
      left
      refine ⟨by positivity, ?_⟩
      have hf := hmono (le_refl x) hx' hx'
      exact hf
    · -- Show integrability
      intro X hX
      exact IntervalIntegrable.mul_continuousOn (hint X hX) 
        (ContinuousOn.rpow continuousOn_id (fun _ _ => Or.inl (by linarith)) (by simp))
    · -- Show integral is bounded
      use I
      intro X hX
      have h1X : 1 ≤ X := hX
      have := hI X hX
      simp at this
      exact this