/-
Polya-Szego Problem 279
Part Three, Chapter 6

Original problem:
Let $f(z)$ be regular and bounded on the disk $|z|<1$ and let

$$
\lim _{r \rightarrow 1} f\left(r e^{i \vartheta}\right)=0
$$

hold uniformly in a sector $\alpha \leqq \vartheta \leqq \beta, \alpha<\beta$. Then $f(z)$ vanishes identically.

\begin{enumerate}
  \setcounter{enumi}{279}
  \item The function $f(z)$ is assumed to be regular and $|f(z)|<1$ in the disk $|z|<1$. If $f(0)=0$ either the stricter inequality $|f(z)|<|z|$ holds for $z \neq 0$ or $f(z)=e^{i \alpha} z, \alpha=$ real.
  \item 

Formalization notes: -- We formalize the main statement of Problem 279:
-- Let f be holomorphic and bounded on the open unit disk 𝔻.
-- If f has radial limit 0 uniformly on a sector [α, β] (with α < β),
-- then f is identically zero on 𝔻.
-- We use:
--   𝔻 = Metric.ball (0 : ℂ) 1
--   Sector defined by angles α ≤ θ ≤ β
--   Uniform radial limit: ∀ ε > 0, ∃ δ > 0, ∀ r ∈ (1-δ, 1), ∀ θ ∈ [α, β], |f(r * exp(θ * I))| < ε
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.Calculus.UniformLimitsDeriv

-- Formalization notes:
-- We formalize the main statement of Problem 279:
-- Let f be holomorphic and bounded on the open unit disk 𝔻.
-- If f has radial limit 0 uniformly on a sector [α, β] (with α < β),
-- then f is identically zero on 𝔻.
-- We use:
--   𝔻 = Metric.ball (0 : ℂ) 1
--   Sector defined by angles α ≤ θ ≤ β
--   Uniform radial limit: ∀ ε > 0, ∃ δ > 0, ∀ r ∈ (1-δ, 1), ∀ θ ∈ [α, β], |f(r * exp(θ * I))| < ε

theorem problem_279 {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (Metric.ball (0 : ℂ) 1))
    (hbdd : ∃ M, ∀ z, ‖z‖ < 1 → ‖f z‖ ≤ M) (hαβ : α < β) 
    (hunif : ∀ ε > 0, ∃ δ > (0 : ℝ), ∀ (r : ℝ) (hr : 1 - δ < r ∧ r < 1) (θ : ℝ) (hθ : θ ∈ Set.Icc α β),
        ‖f (↑r * Complex.exp (θ * Complex.I))‖ < ε) :
    ∀ z, ‖z‖ < 1 → f z = 0 := by
  sorry

-- Proof attempt:
theorem problem_279 {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (Metric.ball (0 : ℂ) 1))
    (hbdd : ∃ M, ∀ z, ‖z‖ < 1 → ‖f z‖ ≤ M) (hαβ : α < β) 
    (hunif : ∀ ε > 0, ∃ δ > (0 : ℝ), ∀ (r : ℝ) (hr : 1 - δ < r ∧ r < 1) (θ : ℝ) (hθ : θ ∈ Set.Icc α β),
        ‖f (↑r * Complex.exp (θ * Complex.I))‖ < ε) :
    ∀ z, ‖z‖ < 1 → f z = 0 := by
  -- First show f is zero on the sector boundary
  have h_zero_on_sector_boundary : ∀ θ ∈ Set.Icc α β, ∀ᶠ r in 𝓝[<] (1 : ℝ), f (r * Complex.exp (θ * Complex.I)) = 0 := by
    intro θ hθ
    rw [Filter.eventually_nhdsWithin_iff]
    intro ε hε
    rcases hunif ε hε with ⟨δ, hδ, h⟩
    use δ
    constructor
    · exact hδ
    · intro r hr
      specialize h r hr.1 θ hθ
      norm_cast at h
      exact norm_le_zero_iff.1 (le_of_lt h)
  
  -- Apply the Phragmén-Lindelöf principle for sectors
  let D := Metric.ball (0 : ℂ) 1
  have hD : IsOpen D := Metric.isOpen_ball
  have hf_cont : ContinuousOn f D := hf.continuousOn
  rcases hbdd with ⟨M, hM⟩
  
  -- Define the sector
  let sector := {z | z ∈ D ∧ ∃ θ ∈ Set.Icc α β, z = Complex.exp (θ * Complex.I)}
  let sector_closure := closure sector ∩ D
  
  -- Show f is zero on the sector closure
  have h_zero_on_sector_closure : ∀ z ∈ sector_closure, f z = 0 := by
    intro z hz
    rcases hz with ⟨hz_mem, hz_D⟩
    apply norm_eq_zero.1
    apply le_antisymm (le_of_forall_pos_le_add fun ε hε => _) (norm_nonneg _)
    rcases Metric.mem_closure_iff.1 hz_mem (ε/2) (half_pos hε) with ⟨w, hw, hw_dist⟩
    have hw_D : w ∈ D := by
      rcases hw with ⟨hw_D, hw_theta⟩
      exact hw_D
    have hf_w : f w = 0 := by
      rcases hw with ⟨_, θ, hθ, rfl⟩
      exact h_zero_on_sector_boundary θ hθ self_mem_nhdsWithin
    have hf_z_norm : ‖f z‖ ≤ ‖f w‖ + ε := by
      have := norm_sub_le (f z) (f w)
      rw [← hf_w, norm_zero, add_zero] at this
      refine le_trans this ?_
      refine ContinuousOn.norm_le_of_dist_le hf_cont hz_D hw_D (le_of_lt ?_)
      exact lt_of_le_of_lt hw_dist (half_lt_self hε)
    rwa [hf_w, norm_zero, zero_add] at hf_z_norm
  
  -- Apply the maximum modulus principle to show f is identically zero
  apply funext fun z => fun hz => _
  apply norm_eq_zero.1
  apply le_antisymm (le_of_forall_pos_le_add fun ε hε => _) (norm_nonneg _)
  let r : ℝ := ‖z‖
  have hr : r < 1 := by rwa [norm_eq_abs, Complex.norm_eq_abs] at hz
  let z' := (1 - ε/(2*M)) • z
  have hz' : ‖z'‖ < 1 := by
    simp only [norm_smul, norm_eq_abs, Complex.norm_eq_abs]
    rw [mul_comm, ← mul_assoc]
    apply mul_lt_one_of_lt_of_le_of_lt_of_nonneg hr (le_refl _) ?_ (norm_nonneg _)
    exact sub_lt_self _ (div_pos hε (mul_pos two_pos (lt_of_le_of_lt (norm_nonneg _) hM)))
  have hf_z' : f z' = 0 := by
    apply h_zero_on_sector_closure
    refine ⟨Metric.mem_closure_iff.2 fun δ hδ => ?_, hz'⟩
    obtain ⟨θ, hθ⟩ : ∃ θ, z = r * Complex.exp (θ * Complex.I) := by
      exact Complex.exists_arg (ne_zero_of_norm_ne_zero (ne_of_lt hr).symm)
    refine ⟨(1 - ε/(2*M)) • (r * Complex.exp (θ * Complex.I)), ⟨?_, θ, hθ, rfl⟩, ?_⟩
    · simp [D, Metric.ball, dist, hz']
    · simp [dist, norm_smul, ← mul_assoc]
      rw [abs_of_pos (sub_pos_of_lt (div_pos hε (mul_pos two_pos (lt_of_le_of_lt (norm_nonneg _) hM)))),
          sub_self, zero_mul]
      exact lt_of_le_of_lt (norm_nonneg _) hδ
  have hf_z_norm : ‖f z‖ ≤ ‖f z'‖ + ε/2 := by
    have := norm_sub_le (f z) (f z')
    rw [← hf_z', norm_zero, add_zero] at this
    refine le_trans this ?_
    refine ContinuousOn.norm_le_of_dist_le hf_cont ?_ ?_ ?_
    · exact hz
    · exact hz'
    · simp [dist, norm_smul, ← mul_assoc]
      rw [abs_of_pos (sub_pos_of_lt (div_pos hε (mul_pos two_pos (lt_of_le_of_lt (norm_nonneg _) hM)))),
          sub_self, zero_mul]
      exact half_pos hε
  rwa [hf_z', norm_zero, zero_add] at hf_z_norm