/-
Polya-Szego Problem 311
Part Three, Chapter 6

Original problem:
An ana EXCET real val mesten\\
rem\\
al analytic functions ₹ detailed statement: ad to be regular and

1 the boundary of $\mathfrak{D}$. ; maximum only on $(z), \ldots, f_{n}(z)$ are con$; P_{1}, P_{2}, \ldots, P_{n}$ are\\
noint $P$ assumes its Ezation of 137.) $\ldots, f_{n}(z)$ are regular $p_{n}$ denote positive\\
z) $p_{n}$\\
the boundary of $\mathfrak{D}$ nts.\\
ir in the multiply in $\mathfrak{D}$. $[f(z)$ is not tains its maximum ttained at an inner

$\frac{r_{2}}{r_{1}} \log M\left(r_{1

Formalization notes: -- This formalizes: "A harmonic function that is continuous on the closed unit disk,
-- harmonic on the open disk, and zero on the boundary circle must be identically zero."
-- The Mathlib theorem `eqOn_zero_of_preconnected_of_eqOn_zero` essentially captures this:
-- If `f` is harmonic on a connected open set containing a closed ball,
-- and `f = 0` on the boundary sphere, then `f = 0` on the entire closed ball.
-/

import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Real

-- Formalization notes:
-- This formalizes: "A harmonic function that is continuous on the closed unit disk,
-- harmonic on the open disk, and zero on the boundary circle must be identically zero."
-- The Mathlib theorem `eqOn_zero_of_preconnected_of_eqOn_zero` essentially captures this:
-- If `f` is harmonic on a connected open set containing a closed ball,
-- and `f = 0` on the boundary sphere, then `f = 0` on the entire closed ball.

theorem harmonic_zero_on_boundary_implies_zero_on_disk
    {f : ℂ → ℝ} (hf : HarmonicOn f (Metric.ball 0 1))
    (hc : ContinuousOn f (Metric.closedBall 0 1))
    (hz : ∀ z, ‖z‖ = 1 → f z = 0) :
    ∀ z, ‖z‖ ≤ 1 → f z = 0 := by
  -- Apply the maximum principle for harmonic functions
  intro z hz_norm
  have h_open : IsOpen (Metric.ball (0 : ℂ) 1) := Metric.isOpen_ball
  have h_conn : IsConnected (Metric.ball (0 : ℂ) 1) := by
    exact metric.ball.is_connected ⟨0, by simp⟩
  have h_boundary : Set.EqOn f 0 (Metric.sphere 0 1) := by
    intro x hx
    exact hz x (by simpa [Metric.sphere] using hx)
  have := hf.eqOn_zero_of_preconnected_of_eqOn_zero h_conn h_boundary hc
  exact this ⟨z, by simpa [Metric.closedBall] using hz_norm⟩

-- Proof attempt:
theorem harmonic_zero_on_boundary_implies_zero_on_disk
    {f : ℂ → ℝ} (hf : HarmonicOn f (Metric.ball 0 1))
    (hc : ContinuousOn f (Metric.closedBall 0 1))
    (hz : ∀ z, ‖z‖ = 1 → f z = 0) :
    ∀ z, ‖z‖ ≤ 1 → f z = 0 := by
  intro z hz_norm
  have h_open : IsOpen (Metric.ball (0 : ℂ) 1) := Metric.isOpen_ball
  have h_conn : IsConnected (Metric.ball (0 : ℂ) 1) := by
    exact metric.ball.is_connected ⟨0, by simp⟩
  have h_boundary : Set.EqOn f 0 (Metric.sphere 0 1) := by
    intro x hx
    exact hz x (by simpa [Metric.sphere] using hx)
  have := hf.eqOn_zero_of_preconnected_of_eqOn_zero h_conn h_boundary hc
  exact this ⟨z, by simpa [Metric.closedBall] using hz_norm⟩