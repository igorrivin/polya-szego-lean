/-
Polya-Szego Problem 27
Part Three, Chapter 1

Original problem:
Suppose that the polynomial $P(z)$ of degree $n, n \geqq 2$, assumes the values $\alpha$ and $\beta$ for $z=a$ and $z=b$, respectively, where $a \neq b$ and $\alpha \neq \beta$. Let $\mathfrak{C}$ denote the closed domain bounded by two arcs of circle the boundary whereof is the set of those points at which the line segment $a, b$ subtends the angle $\frac{\pi}{n}$. Show that to each point $\gamma$ on the line connecting $\alpha$ and $\beta$ there exists a point $z$ in $\mathfrak{C}$ such that $

Formalization notes: -- We formalize the main statement of Problem 27 about polynomial values on a line segment
-- being attained within a specific circular domain.
-- The domain 𝔠 is defined as: the closed region bounded by two circular arcs where
-- the segment [a, b] subtends angle π/n.
-- We use `Set` to represent this domain and `ℂ` for complex numbers.
-/

import Mathlib.Analysis.Complex.Polynomial
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

-- Formalization notes:
-- We formalize the main statement of Problem 27 about polynomial values on a line segment
-- being attained within a specific circular domain.
-- The domain 𝔠 is defined as: the closed region bounded by two circular arcs where
-- the segment [a, b] subtends angle π/n.
-- We use `Set` to represent this domain and `ℂ` for complex numbers.

theorem problem_27 {n : ℕ} (hn : 2 ≤ n) (P : ℂ[X]) (hdeg : P.natDegree = n) 
    (a b : ℂ) (hab : a ≠ b) (α β : ℂ) (hαβ : α ≠ β) (hPa : P.eval a = α) (hPb : P.eval b = β) :
    let 𝔠 : Set ℂ := {z | -π/n ≤ Complex.arg ((a - z)/(b - z)) ∧ Complex.arg ((a - z)/(b - z)) ≤ π/n}
    ∀ (γ : ℂ), ∃ (z : ℂ), z ∈ 𝔠 ∧ P.eval z = γ := by
  sorry

-- Formalization notes for the additional problems:

-- Problem 28: If all complex numbers are on the same side of a line through origin,
-- then their sum and sum of reciprocals are nonzero.
theorem problem_28 {n : ℕ} (z : Fin n → ℂ) (l : ℂ → Prop) 
    (hl_line : ∃ (θ : ℝ), ∀ w : ℂ, l w ↔ Complex.arg w = θ) 
    (h_same_side : ∀ i j : Fin n, l (z i) ↔ l (z j)) 
    (h_not_all_zero : ∃ i, z i ≠ 0) :
    (∑ i, z i) ≠ 0 ∧ (∑ i, (z i)⁻¹) ≠ 0 := by
  sorry

-- Problem 29: If complex numbers sum to zero, any line through origin separates them
-- (unless all lie on the line).
theorem problem_29 {n : ℕ} (z : Fin n → ℂ) (hsum : ∑ i, z i = 0) (θ : ℝ) :
    let left_side := {w : ℂ | Complex.sin (Complex.arg w - θ) > 0}
    let right_side := {w : ℂ | Complex.sin (Complex.arg w - θ) < 0}
    (∃ i, z i ∈ left_side) ∧ (∃ i, z i ∈ right_side) ∨ 
    (∀ i, Complex.sin (Complex.arg (z i) - θ) = 0) := by
  sorry

-- Problem 30: Convex combination property
theorem problem_30 {n : ℕ} (z : Fin n → ℂ) (m : Fin n → ℝ) 
    (hm_pos : ∀ i, 0 < m i) (hsum : ∑ i, m i = 1) :
    let z_center := ∑ i, m i • z i
    ∀ (θ : ℝ) (d : ℝ), 
      let line := {w : ℂ | Complex.arg (w - z_center) = θ}
      (∃ i, Complex.sin (Complex.arg (z i - z_center) - θ) > 0) ∧ 
      (∃ i, Complex.sin (Complex.arg (z i - z_center) - θ) < 0) ∨ 
      (∀ i, z i ∈ line) := by
  sorry

-- Formalization notes for the center of gravity interpretation:
-- The convex hull of points z_i is the set of all convex combinations
theorem centers_of_gravity_form_convex_hull {n : ℕ} (z : Fin n → ℂ) :
    {w : ℂ | ∃ (m : Fin n → ℝ) (hm_pos : ∀ i, 0 ≤ m i) (hsum : ∑ i, m i = 1), w = ∑ i, m i • z i} = 
    convexHull ℝ (Set.range z) := by
  sorry

-- Proof attempt:
theorem problem_27 {n : ℕ} (hn : 2 ≤ n) (P : ℂ[X]) (hdeg : P.natDegree = n) 
    (a b : ℂ) (hab : a ≠ b) (α β : ℂ) (hαβ : α ≠ β) (hPa : P.eval a = α) (hPb : P.eval b = β) :
    let 𝔠 : Set ℂ := {z | -π/n ≤ Complex.arg ((a - z)/(b - z)) ∧ Complex.arg ((a - z)/(b - z)) ≤ π/n}
    ∀ (γ : ℂ), ∃ (z : ℂ), z ∈ 𝔠 ∧ P.eval z = γ := by
  intro 𝔠 γ
  -- First handle the case when γ is on the line segment between α and β
  by_cases hγ : ∃ (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1), γ = t • β + (1 - t) • α
  · rcases hγ with ⟨t, ht, hγ⟩
    have hμλ : t ≠ 0 ∧ t ≠ 1 := by
      refine ⟨fun h0 ↦ ?_, fun h1 ↦ ?_⟩
      · rw [h0, zero_smul, one_smul, zero_add] at hγ
        exact hαβ (hγ.symm.trans hPa)
      · rw [h1, one_smul, zero_smul, add_zero] at hγ
        exact hαβ (hγ.symm.trans hPb)
    let Q := P - C γ
    have hQ_deg : Q.natDegree = n := by
      simp [Q]
      rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt]
      · exact hdeg
      · simp [hdeg]
        exact WithBot.coe_lt_coe.mpr hn
    have hQa : Q.eval a = α - γ := by simp [Q, hPa]
    have hQb : Q.eval b = β - γ := by simp [Q, hPb]
    -- Suppose for contradiction all roots are outside 𝔠
    by_contra h
    push_neg at h
    have h_roots : ∀ z, Q.eval z = 0 → z ∉ 𝔠 := by
      intro z hz
      exact h z (by rwa [Q, Polynomial.eval_sub, sub_eq_zero])
    obtain ⟨z₁, hz₁⟩ := Polynomial.exists_root _ (hQ_deg ▸ hdeg) (by norm_num)
    have hz₁_notin : z₁ ∉ 𝔠 := h_roots z₁ hz₁
    rw [𝔠] at hz₁_notin
    simp at hz₁_notin
    -- Factor Q as (z - z₁)*...*(z - zₙ)
    obtain ⟨r, hr⟩ := Polynomial.exists_finset_roots (by rw [hQ_deg]; exact hn) Q
    have hQ_eq : Q = Polynomial.leadingCoeff Q * ∏ z in r, (Polynomial.X - C z) :=
      Polynomial.eq_prod_roots_of_splits (AlgebraicClosure.isAlgebraic ℂ) Q
    have h_roots' : ∀ z ∈ r, z ∉ 𝔠 := by
      intro z hz
      apply h_roots z
      rw [hQ_eq, Polynomial.eval_mul, Polynomial.eval_prod]
      simp [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, hz]
    -- Compute argument of (Q(a)/Q(b))
    have hQab : Q.eval a / Q.eval b = -(1 - t)/t := by
      rw [hQa, hQb, hγ]
      field_simp
      ring
    have h_arg : Complex.arg (Q.eval a / Q.eval b) = π := by
      rw [hQab]
      have : (1 - t)/t > 0 := by
        refine div_pos ?_ (hμλ.1.lt_of_le ht.1)
        exact sub_pos.mpr (ht.2.trans_lt (hμλ.2))
      simp [this, Real.pi_pos.le]
    -- Compute argument using product formula
    have h_arg' : Complex.arg (Q.eval a / Q.eval b) = 
        Complex.arg (Polynomial.leadingCoeff Q) - Complex.arg (Polynomial.leadingCoeff Q) +
        ∑ z in r, (Complex.arg (a - z) - Complex.arg (b - z)) := by
      rw [hQ_eq]
      simp only [Polynomial.eval_mul, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
      rw [Complex.arg_mul_cos_add_sin, Complex.arg_prod]
      · simp only [Finset.sum_sub_distrib]
      · intro z hz
        exact (sub_ne_zero.mpr hab).mpr (h_roots z (Polynomial.mem_roots.mp (hr z hz))).1
      · exact Polynomial.leadingCoeff_ne_zero.mpr (hQ_deg ▸ hdeg ▸ hn)
    simp at h_arg'
    rw [h_arg, h_arg']
    -- Get contradiction from angle bounds
    have h_sum_bounds : -π < ∑ z in r, (Complex.arg (a - z) - Complex.arg (b - z)) ∧
                        ∑ z in r, (Complex.arg (a - z) - Complex.arg (b - z)) < π := by
      refine Finset.sum_induction _ ?_ ?_ ?_ ?_ r
      · intro x hx
        have := h_roots' x hx
        rw [𝔠] at this
        simp at this
        rcases this with (hlt | hgt)
        · exact ⟨by linarith [hlt.1], by linarith [hlt.2]⟩
        · exact ⟨by linarith [hgt.1], by linarith [hgt.2]⟩
      · simp
      · intro a b ha hb
        cases' ha with ha1 ha2
        cases' hb with hb1 hb2
        constructor <;> linarith
    linarith [h_sum_bounds.1, h_sum_bounds.2]
  · -- When γ is not on the line segment, use continuity and intermediate value theorem
    have h_line : ∃ (t : ℝ), γ = t • β + (1 - t) • α := by
      simp only [exists_prop, Set.mem_Icc, ge_iff_le, not_exists, not_and] at hγ
      have h_linear : Function.Injective fun (t : ℝ) ↦ t • β + (1 - t) • α := by
        intro t₁ t₂ h
        simp only [add_right_inj, smul_eq_mul] at h
        rw [← sub_eq_zero, ← sub_mul, mul_eq_zero] at h
        exact h.resolve_right (sub_ne_zero.mpr hαβ)
      let f := fun (t : ℝ) ↦ t • β + (1 - t) • α
      have h_cont : Continuous f := by continuity
      have h_surj : Set.range f = Set.univ := by
        refine Function.Surjective.range_eq ?_
        intro γ
        obtain ⟨t, _⟩ := exists_ne (0 : ℝ)
        refine ⟨t, ?_⟩
        use t • β + (1 - t) • α
      sorry -- Need to fill in details for general γ case
    sorry -- Full proof would require more infrastructure