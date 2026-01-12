/-
Polya-Szego Problem 302
Part Three, Chapter 6

Original problem:
We assume that the functions $f_{1}(z), f_{2}(z), \ldots, f_{n}(z)$ are regular and single-valued in the domain $\mathfrak{D}$. Let $p_{1}, p_{2}, \ldots, p_{n}$ denote positive numbers. The function

$$
\varphi(z)=\left|f_{1}(z)\right|^{p_{1}}+\left|f_{2}(z)\right|^{p_{2}}+\cdots+\left|f_{n}(z)\right|^{p_{n}}
$$

is continuous in $\mathfrak{D}$. It reaches its maximum only on the boundary of $\mathfrak{D}$ unless all the functions $f_{1}(z), f_{2}(z), \ldots, f_{n}(z)$ are constants.\\

Formalization notes: -- 1. We formalize the statement for a connected, bounded, open domain D in ℂ
-- 2. "Regular and single-valued" means holomorphic on D
-- 3. The maximum principle is stated for the continuous extension to the closure
-- 4. We use `ℂ → ℂ` for holomorphic functions, with explicit holomorphy assumptions
-- 5. The conclusion: if φ attains maximum at interior point, then all fᵢ are constant
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.SpecialFunctions.Pow.Real

-- Formalization notes:
-- 1. We formalize the statement for a connected, bounded, open domain D in ℂ
-- 2. "Regular and single-valued" means holomorphic on D
-- 3. The maximum principle is stated for the continuous extension to the closure
-- 4. We use `ℂ → ℂ` for holomorphic functions, with explicit holomorphy assumptions
-- 5. The conclusion: if φ attains maximum at interior point, then all fᵢ are constant

open Complex
open Set
open Filter

theorem problem_302 {n : ℕ} {D : Set ℂ} (hD_open : IsOpen D) (hD_conn : IsConnected D) 
    (f : Fin n → ℂ → ℂ) (p : Fin n → ℝ) (hp_pos : ∀ i, p i > 0)
    (hf_hol : ∀ i, DifferentiableOn ℂ (f i) D) :
    let φ : ℂ → ℝ := fun z => ∑ i : Fin n, ‖f i z‖ ^ (p i : ℝ)
    let φ_cont : ContinuousOn φ (closure D) := by
      -- φ is continuous on closure D since each f i is holomorphic on D
      -- and thus continuous on D, and |·|^p is continuous
      sorry
    ∃ z_max ∈ frontier D, ∀ z ∈ closure D, φ z ≤ φ z_max := by
  -- The theorem states that the maximum of φ on closure D is attained on the frontier
  -- unless all f i are constant functions on D
  sorry

-- Proof attempt:
theorem problem_302 {n : ℕ} {D : Set ℂ} (hD_open : IsOpen D) (hD_conn : IsConnected D) 
    (f : Fin n → ℂ → ℂ) (p : Fin n → ℝ) (hp_pos : ∀ i, p i > 0)
    (hf_hol : ∀ i, DifferentiableOn ℂ (f i) D) :
    let φ : ℂ → ℝ := fun z => ∑ i : Fin n, ‖f i z‖ ^ (p i : ℝ)
    let φ_cont : ContinuousOn φ (closure D) := by
      apply ContinuousOn.sum
      intro i _
      refine (ContinuousOn.comp (hf_hol i).continuousOn (continuous_abs.comp_continuousOn ?_) ?_)
      · exact continuousOn_id
      · intro z hz; exact hz
      · exact fun z _ => Real.continuousAt_rpow_const (Or.inl (norm_ne_zero_iff.mpr ?_)).le
        -- Need to handle case when f i z = 0 separately
        simp only [norm_eq_zero]
        intro h; rw [h, Real.zero_rpow (hp_pos i).ne']; exact continuousAt_const
    ∃ z_max ∈ frontier D, ∀ z ∈ closure D, φ z ≤ φ z_max := by
  intro φ φ_cont
  -- First show φ attains its maximum on closure D
  have hD_bdd : Bounded D := sorry  -- Need to assume D is bounded
  have hD_closed : IsCompact (closure D) := isCompact_closure_of_bounded hD_bdd
  have hφ_max : ∃ z ∈ closure D, ∀ w ∈ closure D, φ w ≤ φ z :=
    exists_forall_ge_of_isCompact hD_closed φ_cont.continuousOn (closure D).nonempty_closure
  
  -- Now show the maximum must be on the frontier unless all f_i are constant
  by_cases h : ∀ i, ∃ c : ℂ, f i = fun _ => c
  · -- Case where all f_i are constant
    rcases h with ⟨c, hc⟩
    choose c hc using h
    have : φ = fun _ => ∑ i, ‖c i‖ ^ (p i : ℝ) := by
      ext z; simp [φ, hc]
    simp [this]
    obtain ⟨z, hz⟩ := frontier_nonempty_of_isOpen hD_open ⟨0, zero_mem_closure⟩
    exact ⟨z, hz, by simp [this]⟩
  
  · -- Case where at least one f_i is non-constant
    push_neg at h
    obtain ⟨i, hi⟩ := h
    have hf_nonconst : ¬∀ z w : ℂ, f i z = f i w := by
      contrapose! hi; exact ⟨f i 0, funext fun z => hi z 0⟩
    
    -- Apply maximum modulus principle to each component
    have h_max_on_frontier : ∀ z ∈ D, φ z < sSup (φ '' closure D) → z ∉ frontier D → False := by
      intro z hzD hφz hz_not_frontier
      have hz_interior : z ∈ interior D := by
        rw [mem_interior_iff_mem_nhds]
        exact hD_open.mem_nhds hzD
      
      -- At least one f_i is non-constant and attains maximum modulus at z
      have h_max : ∀ w ∈ D, ‖f i w‖ ≤ ‖f i z‖ := by
        have := Complex.norm_eq_norm_of_isMaxOn (hf_hol i).continuousOn.norm hD_conn hz_interior
        intro w hw
        specialize this w hw
        exact this
        
      -- But since f_i is holomorphic and non-constant, this violates the maximum modulus principle
      have : IsOpenMap (f i) := (hf_hol i).isOpenMap hD_open
      contrapose! hf_nonconst
      exact ⟨f i z, funext fun w => norm_eq_norm_of_isMaxOn (hf_hol i).continuousOn.norm hD_conn hz_interior w (mem_univ w)⟩
    
    obtain ⟨z_max, hz_max_mem, hφ_max⟩ := hφ_max
    refine ⟨z_max, ?_, hφ_max⟩
    by_contra hz_max_not_frontier
    exact h_max_on_frontier z_max (closure_subset_closure hD_open hz_max_mem) 
      (le_sSup hφ_max (mem_image_of_mem φ hz_max_mem)) hz_max_not_frontier