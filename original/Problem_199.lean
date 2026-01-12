/-
Polya-Szego Problem 199
Part One, Chapter 5

Original problem:
Under the same hypothesis as in 198

$$
\lim _{n \rightarrow \infty} \frac{\int_{a}^{b} \varphi(x)[f(x)]^{n+1} d x}{\int_{a}^{b} \varphi(x)[f(x)]^{n} d x}=\max f(x)
$$

\begin{enumerate}
  \setcounter{enumi}{199}
  \item Let $k$ be a positive constant and $a<\xi<b$. Show that for $a, b, \xi, k$ fixed and $n \rightarrow \infty$
\end{enumerate}

$$
\int_{a}^{b} e^{-k n(x-\xi)^{2}} d x \sim \sqrt{\frac{\pi}{k n}}
$$

\begin{enumerate}
  \setcounter{enumi}{200}
  \item The functions $\varphi(x), h(x

Formalization notes: We formalize Problem 199 (Part One, Chapter 5) from Polya-Szego:
  Under the same hypothesis as in 198:
    lim_{n→∞} (∫_a^b φ(x)[f(x)]^{n+1} dx) / (∫_a^b φ(x)[f(x)]^n dx) = max_{x∈[a,b]} f(x)
-/

import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Analysis.Calculus.Deriv.Basic

/- Formalization notes:
We formalize Problem 199 (Part One, Chapter 5) from Polya-Szego:
  Under the same hypothesis as in 198:
    lim_{n→∞} (∫_a^b φ(x)[f(x)]^{n+1} dx) / (∫_a^b φ(x)[f(x)]^n dx) = max_{x∈[a,b]} f(x)

We assume:
  1. f is continuous on [a,b] (to ensure maximum exists)
  2. f is positive on [a,b] (to avoid division by zero and ensure integrability)
  3. φ is integrable and non-negative (or positive at maximum point)
  4. The integrals in the denominator are non-zero for large n

We use the following simplifications for formalization:
  - Use ℝ for real numbers
  - Use `intervalIntegral` for definite integrals
  - Assume f attains its maximum at a unique point (common in such problems)
  - The limit is taken over n ∈ ℕ → ∞
-/

open Real
open Set
open Filter
open Topology

theorem problem_199 {a b : ℝ} (hab : a < b) {φ f : ℝ → ℝ} 
    (hf_cont : ContinuousOn f (Set.uIcc a b)) 
    (hf_pos : ∀ x, x ∈ Set.uIcc a b → 0 < f x)
    (hφ_int : IntegrableOn φ (Set.uIcc a b)) 
    (hφ_nonneg : ∀ x, x ∈ Set.uIcc a b → 0 ≤ φ x)
    (h_max_exists : ∃ x₀ ∈ Set.uIcc a b, ∀ x ∈ Set.uIcc a b, f x ≤ f x₀)
    (h_denom_nonzero : ∀ᶠ n in atTop, 
        ∫ x in a..b, φ x * (f x) ^ n ≠ 0) :
    Tendsto (λ (n : ℕ) => 
        (∫ x in a..b, φ x * (f x) ^ (n + 1)) / 
        (∫ x in a..b, φ x * (f x) ^ n)) 
      atTop (𝓝 (sSup (f '' (Set.uIcc a b)))) := by
  sorry

-- Proof attempt:
obtain ⟨x₀, hx₀, hf_max⟩ := h_max_exists
let M := f x₀
have hM : M = sSup (f '' (Set.uIcc a b)) := by
  apply le_antisymm
  · exact csSup_le (Nonempty.image f (nonempty_uIcc.mpr hab)) 
      (hf_cont.image_isCompact isCompact_uIcc).bddAbove hf_max
  · refine le_csSup ?_ (mem_image_of_mem f hx₀)
    exact (hf_cont.image_isCompact isCompact_uIcc).bddAbove

have hM_pos : 0 < M := hf_pos x₀ hx₀

-- Step 1: Show integrals are dominated by behavior near maximum point
have main_estimate : ∀ ε > 0, ∃ δ > 0, 
    ∀ᶠ n in atTop, (1 - ε) * (M - ε) * ∫ x in Icc (x₀ - δ) (x₀ + δ) ∩ Set.uIcc a b, φ x * (f x)^n ≤ 
    ∫ x in a..b, φ x * (f x)^(n+1) ∧
    ∫ x in a..b, φ x * (f x)^(n+1) ≤ M * ∫ x in a..b, φ x * (f x)^n := by
  intro ε hε
  have hε' : 0 < ε / 2 := half_pos hε
  obtain ⟨δ, hδ_pos, hδ⟩ := ContinuousOn.exists_forall_ge_of_isCompact hf_cont isCompact_uIcc x₀ hx₀ (ε/2)
  refine ⟨δ, hδ_pos, ?_⟩
  filter_upwards [h_denom_nonzero] with n hn
  constructor
  · have h_int_pos : 0 < ∫ x in Icc (x₀ - δ) (x₀ + δ) ∩ Set.uIcc a b, φ x * (f x)^n := by
      refine set_integral_pos_of_nonneg_of_nonneg_interior' ?_ ?_ ?_ ?_ ?_
      · intro x hx; exact mul_nonneg (hφ_nonneg x hx.2) (pow_nonneg (hf_pos x hx.2).le n)
      · rw [interior_inter, interior_Icc, interior_uIcc]
        refine (nonempty_Ioc.2 ⟨max a (x₀ - δ), min b (x₀ + δ), ?_⟩).mono ?_
        · exact ⟨lt_min (by linarith [hδ_pos]) (by linarith [hδ_pos]), 
            max_lt (by linarith [hδ_pos]) (by linarith [hδ_pos])⟩
        · intro x hx
          simp only [mem_inter_iff, mem_Ioc, mem_Ioo] at hx ⊢
          exact ⟨⟨hx.1.1.le, hx.1.2.le⟩, hx.2⟩
      · exact (hφ_int.mono (inter_subset_right _ _)).integrableOn
      · intro x hx
        exact mul_pos (hφ_nonneg x hx.2.2) (pow_pos (hf_pos x hx.2.2) n)
    calc (1 - ε) * (M - ε) * ∫ x in Icc (x₀ - δ) (x₀ + δ) ∩ Set.uIcc a b, φ x * (f x)^n
        ≤ (1 - ε) * (M - ε) * ∫ x in Icc (x₀ - δ) (x₀ + δ) ∩ Set.uIcc a b, φ x * (f x)^n := by rfl
      _ ≤ ∫ x in Icc (x₀ - δ) (x₀ + δ) ∩ Set.uIcc a b, φ x * (f x)^(n+1) := ?_
      _ ≤ ∫ x in a..b, φ x * (f x)^(n+1) := set_integral_le_integral (hφ_int.mul (hf_cont.pow (n+1))).integrableOn
          (fun x hx => mul_nonneg (hφ_nonneg x hx) (pow_nonneg (hf_pos x hx).le _))
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (by linarith) h_int_pos.le)
    refine set_integral_mono_on (hφ_int.mul (hf_cont.pow n)).integrableOn 
      (hφ_int.mul (hf_cont.pow (n+1))).integrableOn _ (fun x hx => ?_)
    rw [← mul_assoc, mul_comm ((f x)^n), mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (hφ_nonneg x hx.2)
    rw [pow_succ, mul_comm]
    refine mul_le_of_le_one_left (pow_nonneg (hf_pos x hx.2).le _) ?_
    rw [← le_div_iff (pow_pos (hf_pos x hx.2) n)]
    refine (hδ x hx.1).le.trans ?_
    linarith [hM_pos]
  · rw [← integral_mul_left]
    refine integral_mono_on (hφ_int.mul (hf_cont.pow (n+1))).integrableOn 
      (hφ_int.mul (hf_cont.pow n)).integrableOn.mul_const M (by simp [uIcc_of_le hab.le]) 
      (fun x hx => ?_)
    rw [pow_succ, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (hφ_nonneg x hx)
    exact hf_max x hx

-- Step 2: Use squeeze theorem to conclude
refine tendsto_of_tendsto_of_tendsto_of_le_of_le' ?_ ?_ ?_ ?_
· -- Lower bound
  intro ε hε
  obtain ⟨δ, hδ_pos, hδ⟩ := main_estimate ε hε
  filter_upwards [hδ, h_denom_nonzero] with n hn hn'
  rw [div_eq_mul_inv]
  refine mul_le_mul_of_nonneg_right ?_ (inv_nonneg.mpr (integral_nonneg (fun x hx => ?_)))
  · exact hn.1
  · exact mul_nonneg (hφ_nonneg x (by simp at hx; exact hx)) (pow_nonneg (hf_pos x (by simp at hx; exact hx)).le _)
  · exact (M - ε) * (1 - ε)
· -- Upper bound is trivial
  filter_upwards [h_denom_nonzero] with n hn
  exact (div_le_iff hn).mpr (by exact (main_estimate 1 zero_lt_one).choose_spec.choose_spec n).2
· -- Lower bound tends to M
  suffices Tendsto (fun ε => (M - ε) * (1 - ε)) (𝓝[>] 0) (𝓝 M) by
    refine this.congr' ?_
    filter_upwards [main_estimate 1 zero_lt_one] with ε hε
    simp [hε]
  refine ((tendsto_const_nhds.sub tendsto_id).mul (tendsto_const_nhds.sub tendsto_id)).mono_left ?_
  simp only [sub_zero, mul_one, nhdsWithin_le_nhds]
· -- Upper bound is constant M
  exact tendsto_const_nhds