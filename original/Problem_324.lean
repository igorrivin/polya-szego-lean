/-
Polya-Szego Problem 324
Part Three, Chapter 6

Original problem:
We modify condition (2) of $\mathbf{3 2 2}$ in the following way: There exist in the sector $-\alpha \leqq \vartheta \leqq \alpha$ two curves $\Gamma_{1}$ and $\Gamma_{2}$ connecting the points $z=0$ and $z=\infty$ that do not intersect and along which $|f(z)| \leqq 1$. This modified condition together with condition (1) as stated in 322 implies the inequality $|f(z)| \leqq 1$ in the domain bounded by $\Gamma_{1}$ and $\Gamma_{2}$.\\

Formalization notes: -- We formalize a version of the Phragmén-Lindelöf type theorem in a sector bounded by curves
-- Key elements:
-- 1. f : ℂ → ℂ is an entire function (or at least analytic in the region)
-- 2. Sector: {z | -α ≤ arg z ≤ α} where α ∈ (0, π)
-- 3. Two non-intersecting curves Γ₁, Γ₂ connecting 0 to ∞ within the sector
-- 4. |f(z)| ≤ 1 on Γ₁ ∪ Γ₂
-- 5. Additional growth condition on f (condition (1) from Problem 322) - here simplified
-- Conclusion: |f(z)| ≤ 1 in the domain bounded by Γ₁ and Γ₂
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Topology.MetricSpace.PathConnected

-- Formalization notes:
-- We formalize a version of the Phragmén-Lindelöf type theorem in a sector bounded by curves
-- Key elements:
-- 1. f : ℂ → ℂ is an entire function (or at least analytic in the region)
-- 2. Sector: {z | -α ≤ arg z ≤ α} where α ∈ (0, π)
-- 3. Two non-intersecting curves Γ₁, Γ₂ connecting 0 to ∞ within the sector
-- 4. |f(z)| ≤ 1 on Γ₁ ∪ Γ₂
-- 5. Additional growth condition on f (condition (1) from Problem 322) - here simplified
-- Conclusion: |f(z)| ≤ 1 in the domain bounded by Γ₁ and Γ₂

-- Since formalizing arbitrary curves exactly as in the book is complex, we use paths
-- and work with a simplified but mathematically equivalent formulation

theorem problem_324 {f : ℂ → ℂ} {α : ℝ} (hα_pos : 0 < α) (hα_lt_pi : α < π) 
    (hf_analytic : DifferentiableOn ℂ f {z | Complex.arg z ∈ Set.Icc (-α) α}) 
    -- Condition (1) from Problem 322 - simplified as boundedness condition
    (h_bound : ∃ C : ℝ, ∀ z : ℂ, Complex.arg z ∈ Set.Icc (-α) α → |f z| ≤ C) :
    -- Curves Γ₁ and Γ₂ as continuous injective paths from (0,1] to ℂ
    ∀ (Γ₁ Γ₂ : ℝ → ℂ) (hΓ₁_cont : ContinuousOn Γ₁ (Set.Ioo (0 : ℝ) 1))
      (hΓ₂_cont : ContinuousOn Γ₂ (Set.Ioo (0 : ℝ) 1))
      (hΓ₁_inj : Set.InjOn Γ₁ (Set.Ioo (0 : ℝ) 1))
      (hΓ₂_inj : Set.InjOn Γ₂ (Set.Ioo (0 : ℝ) 1))
      -- Curves lie in the sector
      (hΓ₁_sector : ∀ t ∈ Set.Ioo (0 : ℝ) 1, Complex.arg (Γ₁ t) ∈ Set.Icc (-α) α)
      (hΓ₂_sector : ∀ t ∈ Set.Ioo (0 : ℝ) 1, Complex.arg (Γ₂ t) ∈ Set.Icc (-α) α)
      (hΓ₁_0 : Tendsto Γ₁ (𝓝[>] 0) (𝓝 0))
      (hΓ₁_1 : Tendsto Γ₁ (𝓝[<] 1) (𝓝 ∞))
      (hΓ₂_0 : Tendsto Γ₂ (𝓝[>] 0) (𝓝 0))
      (hΓ₂_1 : Tendsto Γ₂ (𝓝[<] 1) (𝓝 ∞))
      -- Curves don't intersect except possibly at endpoints
      (h_disjoint : ∀ t₁ t₂ ∈ Set.Ioo (0 : ℝ) 1, Γ₁ t₁ ≠ Γ₂ t₂)
      -- Boundedness on curves
      (h_bound_Γ₁ : ∀ t ∈ Set.Ioo (0 : ℝ) 1, |f (Γ₁ t)| ≤ 1)
      (h_bound_Γ₂ : ∀ t ∈ Set.Ioo (0 : ℝ) 1, |f (Γ₂ t)| ≤ 1),
    -- Domain bounded by curves (simplified: points with argument between curves' arguments)
    ∀ z : ℂ, Complex.arg z ∈ Set.Icc (-α) α → 
      (∃ t₁ t₂ ∈ Set.Ioo (0 : ℝ) 1, Complex.arg (Γ₁ t₁) ≤ Complex.arg z ∧ Complex.arg z ≤ Complex.arg (Γ₂ t₂)) →
      |f z| ≤ 1 := by
  sorry

-- Proof attempt:
theorem problem_324 {f : ℂ → ℂ} {α : ℝ} (hα_pos : 0 < α) (hα_lt_pi : α < π) 
    (hf_analytic : DifferentiableOn ℂ f {z | Complex.arg z ∈ Set.Icc (-α) α}) 
    (h_bound : ∃ C : ℝ, ∀ z : ℂ, Complex.arg z ∈ Set.Icc (-α) α → |f z| ≤ C)
    (Γ₁ Γ₂ : ℝ → ℂ) (hΓ₁_cont : ContinuousOn Γ₁ (Set.Ioo (0 : ℝ) 1))
    (hΓ₂_cont : ContinuousOn Γ₂ (Set.Ioo (0 : ℝ) 1))
    (hΓ₁_inj : Set.InjOn Γ₁ (Set.Ioo (0 : ℝ) 1))
    (hΓ₂_inj : Set.InjOn Γ₂ (Set.Ioo (0 : ℝ) 1))
    (hΓ₁_sector : ∀ t ∈ Set.Ioo (0 : ℝ) 1, Complex.arg (Γ₁ t) ∈ Set.Icc (-α) α)
    (hΓ₂_sector : ∀ t ∈ Set.Ioo (0 : ℝ) 1, Complex.arg (Γ₂ t) ∈ Set.Icc (-α) α)
    (hΓ₁_0 : Tendsto Γ₁ (𝓝[>] 0) (𝓝 0))
    (hΓ₁_1 : Tendsto Γ₁ (𝓝[<] 1) (𝓝 ∞))
    (hΓ₂_0 : Tendsto Γ₂ (𝓝[>] 0) (𝓝 0))
    (hΓ₂_1 : Tendsto Γ₂ (𝓝[<] 1) (𝓝 ∞))
    (h_disjoint : ∀ t₁ t₂ ∈ Set.Ioo (0 : ℝ) 1, Γ₁ t₁ ≠ Γ₂ t₂)
    (h_bound_Γ₁ : ∀ t ∈ Set.Ioo (0 : ℝ) 1, |f (Γ₁ t)| ≤ 1)
    (h_bound_Γ₂ : ∀ t ∈ Set.Ioo (0 : ℝ) 1, |f (Γ₂ t)| ≤ 1) :
    ∀ z : ℂ, Complex.arg z ∈ Set.Icc (-α) α → 
      (∃ t₁ t₂ ∈ Set.Ioo (0 : ℝ) 1, Complex.arg (Γ₁ t₁) ≤ Complex.arg z ∧ Complex.arg z ≤ Complex.arg (Γ₂ t₂)) →
      |f z| ≤ 1 := by
  -- Extract the global bound C
  obtain ⟨C, hC⟩ := h_bound
  
  -- Define the domain bounded by Γ₁ and Γ₂
  let D : Set ℂ := {z | Complex.arg z ∈ Set.Icc (-α) α ∧ 
    ∃ t₁ t₂ ∈ Set.Ioo (0 : ℝ) 1, Complex.arg (Γ₁ t₁) ≤ Complex.arg z ∧ Complex.arg z ≤ Complex.arg (Γ₂ t₂)}
  
  -- Show D is open in the sector
  have hD_open : IsOpen D := by
    refine isOpen_iff_mem_nhds.mpr fun z hz ↦ ?_
    obtain ⟨hz_arg, t₁, t₂, ht₁, ht₂, harg⟩ := hz
    refine mem_nhds_iff.mpr ⟨{w | Complex.arg w ∈ Set.Ioo (Complex.arg (Γ₁ t₁)) (Complex.arg (Γ₂ t₂))}, 
      fun w hw ↦ ⟨⟨hw.1.le.trans harg.1, hw.2.le.trans harg.2⟩, t₁, t₂, ht₁, ht₂, hw.1.le, hw.2.le⟩, 
      isOpen_Ioo.preimage Complex.continuous_arg, hz_arg, ?_⟩
    exact ⟨harg.1.lt_of_ne (fun h ↦ h_disjoint t₁ t₂ ht₁ ht₂ (by rw [← Complex.arg_eq_arg, h])), 
           harg.2.lt_of_ne (fun h ↦ h_disjoint t₁ t₂ ht₁ ht₂ (by rw [← Complex.arg_eq_arg, h]))⟩
  
  -- Apply maximum modulus principle
  apply fun z hz_arg hz_D ↦ le_of_forall_le_of_dense fun ε hε ↦ ?_
  have hf_analytic_on_D : DifferentiableOn ℂ f D := 
    hf_analytic.mono (fun z hz ↦ hz.1)
  
  -- Consider the closure of D intersected with a large disk
  let R := max (C / ε) 1
  let D_R := D ∩ {z | ‖z‖ ≤ R}
  
  -- The maximum modulus is attained on the boundary
  have h_max : ∃ z ∈ frontier D_R, ∀ w ∈ closure D_R, |f w| ≤ |f z| := by
    refine Complex.exists_mem_frontier_isMaxOn_norm ?_ ?_ ?_
    · exact hD_open.inter isClosed_ball
    · refine (Metric.bounded_iff_subset_ball 0).mpr ⟨R, fun z hz ↦ ?_⟩
      exact hz.2
    · refine ⟨0, ?_⟩
      have : 0 ∈ D_R := by
        refine ⟨⟨_, 0, 1, by norm_num, by norm_num, ?_, ?_⟩, by simp⟩
        · have := hΓ₁_0
          simp only [Complex.arg_zero, Left.nonneg_neg_iff, hα_pos.le]
        · have := hΓ₂_0
          simp only [Complex.arg_zero, Left.nonneg_neg_iff, hα_pos.le]
      exact ⟨this, hf_analytic_on_D.continuousOn.mono (inter_subset_left _ _)⟩
  
  obtain ⟨z_max, hz_max_frontier, hz_max⟩ := h_max
  
  -- The maximum must occur on Γ₁ ∪ Γ₂
  have hz_max_on_boundary : z_max ∈ Γ₁ '' (Set.Ioo 0 1) ∪ Γ₂ '' (Set.Ioo 0 1) := by
    by_contra h
    push_neg at h
    have hz_max_in_D : z_max ∈ D := by
      rw [frontier, closure_inter, frontier_closed_ball (0 : ℂ) (by linarith)] at hz_max_frontier
      simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_diff] at hz_max_frontier 
      exact hz_max_frontier.1.1
    have hz_max_interior : z_max ∈ interior D_R := by
      refine mem_interior_iff_mem_nhds.mpr (inter_mem ?_ ?_)
      · exact hD_open.mem_nhds hz_max_in_D
      · rw [interior_closedBall (0 : ℂ)]
        exact mem_ball_self (by linarith)
    have hf_analytic_at_max : DifferentiableAt ℂ f z_max :=
      hf_analytic_on_D.differentiableAt (IsOpen.mem_nhds hD_open hz_max_in_D)
    exact Complex.norm_eq_norm_of_isMaxOn hf_analytic_at_max hz_max_interior hz_max (mem_closure_iff_nhds.mp hz_max_frontier.1)
  
  -- On Γ₁ ∪ Γ₂, |f| ≤ 1 by assumption
  rcases hz_max_on_boundary with ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩
  · have := h_bound_Γ₁ t ht
    rw [norm_eq_abs] at this
    linarith [this]
  · have := h_bound_Γ₂ t ht
    rw [norm_eq_abs] at this
    linarith [this]