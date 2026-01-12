/-
Polya-Szego Problem *223
Part One, Chapter 5

Original problem:
The function $f(x, y)$ is continuous in the rectangle

$$
a \leqq x \leqq a^{\prime}, \quad \bar{b} \leqq y \leqq b^{\prime} .
$$

Then its maximum for a given $x$ and $b \leqq y \leqq b^{\prime}$ (along a segment parallel to the $y$-axis)

$$
\max _{y} f(x, y)=\varphi(x)
$$

is a continuous function of $x$.

We interpret the surface

$$
z=f(x, y)
$$

in a rectangular coordinate system $x, y, z$ with vertical $z$-axis as a topographical surface in a mountainous region. Then the curve

$$
z=\varp

Formalization notes: -- 1. We formalize the inequality max_y min_x f(x,y) ≤ min_x max_y f(x,y)
-- 2. We work with continuous functions f : ℝ × ℝ → ℝ on rectangle [a, a'] × [b, b']
-- 3. The maximum/minimum over intervals are taken as continuous suprema/infima
-- 4. We use `IsCompact` to ensure existence of maxima/minima on closed intervals
-- 5. The theorem statement captures the core inequality from Problem 224
-/

-- Imports
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Real.EReal
import Mathlib.Topology.Algebra.Order.Compact
import Mathlib.Topology.ContinuousFunction.Basic

-- Formalization notes:
-- 1. We formalize the inequality max_y min_x f(x,y) ≤ min_x max_y f(x,y)
-- 2. We work with continuous functions f : ℝ × ℝ → ℝ on rectangle [a, a'] × [b, b']
-- 3. The maximum/minimum over intervals are taken as continuous suprema/infima
-- 4. We use `IsCompact` to ensure existence of maxima/minima on closed intervals
-- 5. The theorem statement captures the core inequality from Problem 224

theorem polya_szego_224 {f : ℝ × ℝ → ℝ} {a a' b b' : ℝ} 
    (ha : a ≤ a') (hb : b ≤ b') (hf_cont : ContinuousOn f (Set.Icc a a' ×ˢ Set.Icc b b')) :
    let R : Set (ℝ × ℝ) := Set.Icc a a' ×ˢ Set.Icc b b' in
    haveI : IsCompact R := by
      exact isCompact_Icc.prod isCompact_Icc
    have h_max_min_exists : ∃ (x0 : ℝ) (hx0 : x0 ∈ Set.Icc a a'), 
        sSup (f '' ({x0} ×ˢ Set.Icc b b')) = ⨅ x ∈ Set.Icc a a', sSup (f '' ({x} ×ˢ Set.Icc b b')) := by
      -- Compactness ensures the infimum of suprema is attained
      sorry
    have h_min_max_exists : ∃ (y0 : ℝ) (hy0 : y0 ∈ Set.Icc b b'),
        sInf (f '' (Set.Icc a a' ×ˢ {y0})) = sSup (sInf (f '' (Set.Icc a a' ×ˢ {y})) | y ∈ Set.Icc b b') := by
      -- Similarly for supremum of infima
      sorry
    sSup (sInf (f '' (Set.Icc a a' ×ˢ {y})) | y ∈ Set.Icc b b') ≤ 
    ⨅ x ∈ Set.Icc a a', sSup (f '' ({x} ×ˢ Set.Icc b b')) := by
    intro R h_compact h_max_min_exists h_min_max_exists
    
    -- Main proof sketch:
    -- 1. Let g(y) = min_{x∈[a,a']} f(x,y) and h(x) = max_{y∈[b,b']} f(x,y)
    -- 2. For any specific y₀, g(y₀) = f(x₀,y₀) for some x₀
    -- 3. But f(x₀,y₀) ≤ max_{y} f(x₀,y) = h(x₀)
    -- 4. And h(x₀) ≥ min_{x} h(x)
    -- 5. Thus g(y₀) ≤ min_{x} h(x) for all y₀
    -- 6. Therefore max_{y} g(y) ≤ min_{x} h(x)
    
    obtain ⟨y0, hy0, hy0_max⟩ := h_min_max_exists
    obtain ⟨x0, hx0, hx0_min⟩ := h_max_min_exists
    
    calc
      sSup (sInf (f '' (Set.Icc a a' ×ˢ {y})) | y ∈ Set.Icc b b')
          = sInf (f '' (Set.Icc a a' ×ˢ {y0})) := by rw [hy0_max]
      _ = f (x0, y0) := by
          -- Since x0 is the minimizer for fixed y0
          sorry
      _ ≤ sSup (f '' ({x0} ×ˢ Set.Icc b b')) := by
          -- f(x0,y0) ≤ max_{y} f(x0,y)
          have : (x0, y0) ∈ {x0} ×ˢ Set.Icc b b' := by
            simp [hy0]
          sorry
      _ = ⨅ x ∈ Set.Icc a a', sSup (f '' ({x} ×ˢ Set.Icc b b')) := by rw [hx0_min]
      _ = ⨅ x ∈ Set.Icc a a', sSup (f '' ({x} ×ˢ Set.Icc b b')) := rfl

-- Proof attempt:
theorem polya_szego_224 {f : ℝ × ℝ → ℝ} {a a' b b' : ℝ} 
    (ha : a ≤ a') (hb : b ≤ b') (hf_cont : ContinuousOn f (Set.Icc a a' ×ˢ Set.Icc b b')) :
    let R : Set (ℝ × ℝ) := Set.Icc a a' ×ˢ Set.Icc b b' in
    haveI : IsCompact R := by
      exact isCompact_Icc.prod isCompact_Icc
    have h_max_min_exists : ∃ (x0 : ℝ) (hx0 : x0 ∈ Set.Icc a a'), 
        sSup (f '' ({x0} ×ˢ Set.Icc b b')) = ⨅ x ∈ Set.Icc a a', sSup (f '' ({x} ×ˢ Set.Icc b b')) := by
      apply IsCompact.exists_isInf
      · exact isCompact_Icc.image (continuous_snd.restrict continuousOn_id).continuousOn
      · rw [Set.nonempty_image_iff]
        exact ⟨a, ha, le_rfl⟩
    have h_min_max_exists : ∃ (y0 : ℝ) (hy0 : y0 ∈ Set.Icc b b'),
        sInf (f '' (Set.Icc a a' ×ˢ {y0})) = sSup (sInf (f '' (Set.Icc a a' ×ˢ {y})) | y ∈ Set.Icc b b') := by
      apply IsCompact.exists_isSup
      · exact isCompact_Icc.image (continuous_fst.restrict continuousOn_id).continuousOn
      · rw [Set.nonempty_image_iff]
        exact ⟨b, hb, le_rfl⟩
    sSup (sInf (f '' (Set.Icc a a' ×ˢ {y})) | y ∈ Set.Icc b b') ≤ 
    ⨅ x ∈ Set.Icc a a', sSup (f '' ({x} ×ˢ Set.Icc b b')) := by
    intro R h_compact h_max_min_exists h_min_max_exists
    
    obtain ⟨y0, hy0, hy0_max⟩ := h_min_max_exists
    obtain ⟨x0, hx0, hx0_min⟩ := h_max_min_exists
    
    calc
      sSup (sInf (f '' (Set.Icc a a' ×ˢ {y})) | y ∈ Set.Icc b b')
          = sInf (f '' (Set.Icc a a' ×ˢ {y0})) := by rw [hy0_max]
      _ = f (x0, y0) := by
          have h_inf : IsLeast (f '' (Set.Icc a a' ×ˢ {y0})) (f (x0, y0)) := by
            apply IsCompact.exists_isLeast
            · exact isCompact_Icc.image (hf_cont.mono (Set.prod_mono_right (singleton_subset_iff.2 hy0)))
            · rw [Set.nonempty_image_iff]
              exact ⟨(a, y0), ⟨⟨ha, le_rfl⟩, hy0⟩⟩
          rw [h_inf.isLeast.csInf_eq]
      _ ≤ sSup (f '' ({x0} ×ˢ Set.Icc b b')) := by
          have : (x0, y0) ∈ {x0} ×ˢ Set.Icc b b' := by
            simp [hy0]
          apply le_csSup
          · apply BddAbove.image (hf_cont.mono (Set.prod_mono_left (singleton_subset_iff.2 hx0))).continuousOn
            exact isCompact_Icc.bddAbove
          · exact ⟨(x0, y0), by simp [this], rfl⟩
      _ = ⨅ x ∈ Set.Icc a a', sSup (f '' ({x} ×ˢ Set.Icc b b')) := by rw [hx0_min]
      _ = ⨅ x ∈ Set.Icc a a', sSup (f '' ({x} ×ˢ Set.Icc b b')) := rfl