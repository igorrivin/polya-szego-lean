/-
Polya-Szego Problem 100
Part One, Chapter 3

Original problem:
The two functions $f(x)$ and $\varphi(x)$ are properly integrable over $[a, b]$. Subdivide the interval:

$$
\begin{aligned}
& a=x_{0}<x_{1}<x_{2}<\cdots<x_{n-1}<x_{n}=b \\
& \quad x_{v-1}<y_{v}<x_{v}, \quad x_{v-1}<\eta_{v}<x_{v}, \quad v=1,2, \ldots, n .
\end{aligned}
$$

If $\max \left(x_{\nu}-x_{\nu-1}\right) \rightarrow 0$ (the subinterval of maximal length converges to 0 ) we obtain the relation

$$
\lim _{n \rightarrow \infty} \sum_{\nu=1}^{n} f\left(y_{\nu}\right) \varphi\left(\eta_{\nu}

Formalization notes: -- We formalize Problem 101: For properly integrable functions f on [a,b] and φ on [a,b+d] (d>0),
-- the limit as δ → 0⁺ of ∫_a^b f(x)φ(x+δ) dx equals ∫_a^b f(x)φ(x) dx.
-- We use `intervalIntegral` for proper Riemann integrals and require integrability conditions.
-- The limit is taken as δ → 0 from the right (δ > 0).
-/

import Mathlib.Analysis.Calculus.FDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.MeasureTheory.Integral.SetIntegral

-- Formalization notes:
-- We formalize Problem 101: For properly integrable functions f on [a,b] and φ on [a,b+d] (d>0),
-- the limit as δ → 0⁺ of ∫_a^b f(x)φ(x+δ) dx equals ∫_a^b f(x)φ(x) dx.
-- We use `intervalIntegral` for proper Riemann integrals and require integrability conditions.
-- The limit is taken as δ → 0 from the right (δ > 0).

theorem problem_101 {a b d : ℝ} (hd : 0 < d) 
    {f : ℝ → ℝ} (hf : IntervalIntegrable f volume a b)
    {φ : ℝ → ℝ} (hφ : IntervalIntegrable φ volume a (b + d)) :
    Tendsto (fun (δ : ℝ) => ∫ x in a..b, f x * φ (x + δ)) (𝓝[>] 0) (𝓝 (∫ x in a..b, f x * φ x)) := by
  sorry

-- Proof attempt:
theorem problem_101 {a b d : ℝ} (hd : 0 < d) 
    {f : ℝ → ℝ} (hf : IntervalIntegrable f volume a b)
    {φ : ℝ → ℝ} (hφ : IntervalIntegrable φ volume a (b + d)) :
    Tendsto (fun (δ : ℝ) => ∫ x in a..b, f x * φ (x + δ)) (𝓝[>] 0) (𝓝 (∫ x in a..b, f x * φ x)) := by
  -- Convert the interval integral to a Lebesgue integral
  rw [intervalIntegral.integral_of_le (le_of_lt hd), intervalIntegral.integral_of_le (le_of_lt hd)]
  
  -- Apply the Dominated Convergence Theorem
  apply tendsto_integral_of_dominated_convergence
  · -- Dominating function
    use fun x => ‖f x‖ * (⨆ δ ∈ Ioc (0 : ℝ) d, ‖φ (x + δ)‖)
    · -- Integrability of dominating function
      apply Integrable.mul_essSup
      · exact hf.1.norm
      · have hφ' : AEStronglyMeasurable φ volume := hφ.1.aestronglyMeasurable
        refine aestronglyMeasurable.comp_aemeasurable hφ' ?_
        exact (measurable_id'.add_const _).aemeasurable
      · exact hd
    · -- Pointwise convergence
      intro x hx
      filter_upwards [self_mem_nhdsWithin] with δ hδ
      simp only [hδ, Pi.mul_apply]
      exact continuousAt_const.mul (hφ.1.continuousAt (x + δ))
    · -- Dominated condition
      filter_upwards with x hx δ hδ
      simp only [norm_mul]
      apply mul_le_mul le_rfl
      · exact le_ciSup (bddAbove_iff_norm.2 ⟨_, fun y hy => norm_le_of_mem_closedBall hy.2⟩) ⟨δ, hδ⟩
      · apply norm_nonneg
      · apply norm_nonneg
  · -- Pointwise limit
    filter_upwards with x hx
    have : Tendsto (fun δ => f x * φ (x + δ)) (𝓝[>] 0) (𝓝 (f x * φ x)) := by
      apply Tendsto.mul_const
      apply Tendsto.comp (hφ.1.continuousAt (x + 0))
      simp only [add_zero]
      exact tendsto_id.add tendsto_const_nhds
    exact this