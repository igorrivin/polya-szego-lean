/-
Polya-Szego Problem 26
Part Three, Chapter 1

Original problem:
Let $P(z)=0$ stand for an algebraic equation of degree $n$ all the zeros of which are in the unit circle $|z|<1$. Replacing each coefficient of $P(z)$ by its conjugate we obtain the polynomial $\bar{P}(z)$. We define $P^{*}(z)=z^{n} \bar{P}\left(z^{-1}\right)$. The roots of the equation $P(z)+P^{*}(z)=0$ are all on the unit circle $|z|=1$.\\

Formalization notes: -- 1. We formalize the statement: If P is a polynomial of degree n with all roots in the open unit disk,
--    and P* is defined as z^n * conj(P(1/z̄)), then all roots of P + P* lie on the unit circle.
-- 2. We use ℂ for complex numbers, Polynomial ℂ for polynomials over ℂ
-- 3. We define P* as: P_star z = z^n * conj(P.eval (conj z⁻¹))
-- 4. The condition "all zeros in |z| < 1" becomes: ∀ z, P.IsRoot z → Complex.abs z < 1
-- 5. The conclusion "roots on |z| = 1" becomes: ∀ z, (P + P_star).IsRoot z → Complex.abs z = 1
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial
import Mathlib.Data.Complex.Basic

-- Formalization notes:
-- 1. We formalize the statement: If P is a polynomial of degree n with all roots in the open unit disk,
--    and P* is defined as z^n * conj(P(1/z̄)), then all roots of P + P* lie on the unit circle.
-- 2. We use ℂ for complex numbers, Polynomial ℂ for polynomials over ℂ
-- 3. We define P* as: P_star z = z^n * conj(P.eval (conj z⁻¹))
-- 4. The condition "all zeros in |z| < 1" becomes: ∀ z, P.IsRoot z → Complex.abs z < 1
-- 5. The conclusion "roots on |z| = 1" becomes: ∀ z, (P + P_star).IsRoot z → Complex.abs z = 1

theorem problem_26 (P : Polynomial ℂ) (hdeg : P.degree = some (P.natDegree)) 
    (hroots : ∀ z : ℂ, P.IsRoot z → Complex.abs z < 1) :
    let n := P.natDegree
    let P_star : Polynomial ℂ := 
      Polynomial.monomial n (1 : ℂ) * (Polynomial.map Complex.conj (Polynomial.reverse P))
    ∀ z : ℂ, (P + P_star).IsRoot z → Complex.abs z = 1 := by
  sorry

-- Proof attempt:
theorem problem_26 (P : Polynomial ℂ) (hdeg : P.degree = some (P.natDegree)) 
    (hroots : ∀ z : ℂ, P.IsRoot z → Complex.abs z < 1) :
    let n := P.natDegree
    let P_star : Polynomial ℂ := 
      Polynomial.monomial n (1 : ℂ) * (Polynomial.map Complex.conj (Polynomial.reverse P))
    ∀ z : ℂ, (P + P_star).IsRoot z → Complex.abs z = 1 := by
  intro n P_star z hz
  -- Express P as a product of roots
  have hlead := Polynomial.leadingCoeff_mul_X_pow_eq_self hdeg
  rw [Polynomial.eq_prod_roots_of_splits_id (isAlgClosed' ℂ)] at hlead
  obtain ⟨a, ha, hprod⟩ := hlead
  -- Show P_star can be written in terms of roots
  have hstar : ∀ w, P_star.eval w = a.conj * ∏ z in P.roots.toFinset, (1 - z.conj * w) := by
    intro w
    simp [P_star, Polynomial.eval_mul, Polynomial.eval_monomial, Polynomial.eval_map, 
          Polynomial.eval_reverse, Polynomial.eval₂_eq_eval_map, Polynomial.eval_prod]
    rw [hprod]
    simp [Complex.conj_prod, Complex.conj_sub, mul_comm (conj a), ← mul_assoc]
    congr
    ext z
    rw [mul_comm, ← mul_assoc]
    norm_num
  -- At root z of P + P_star, we have P(z) = -P_star(z)
  have hroot_eq : P.eval z = -P_star.eval z := by
    rwa [Polynomial.IsRoot.def, Polynomial.eval_add, add_eq_zero_iff_eq_neg] at hz
  -- Take absolute values and show |P(z)| = |P_star(z)|
  have h_abs_eq : Complex.abs (P.eval z) = Complex.abs (P_star.eval z) := by
    rw [hroot_eq, Complex.abs.map_neg]
  -- Express both sides in terms of roots
  rw [hprod, hstar z, Complex.abs.map_mul, Complex.abs.map_mul, Complex.abs.map_prod, 
      Complex.abs.map_prod, Complex.abs_conj] at h_abs_eq
  simp only [Complex.abs.map_one, Complex.abs.map_neg, Complex.abs.map_mul, Complex.abs.map_sub, 
             Complex.abs_conj, one_mul] at h_abs_eq
  -- Cancel the leading coefficient terms (nonzero since degree = natDegree)
  have ha_ne : a ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr (Polynomial.degree_eq_natDegree.mp hdeg)
  have ha_abs_ne : Complex.abs a ≠ 0 := by simp [ha_ne]
  rw [mul_eq_mul_right_iff, or_iff_left ha_abs_ne] at h_abs_eq
  -- Now we have the key equation: product of |z - zᵢ| = product of |1 - z̄ᵢ z|
  have key_eq : ∏ zᵢ in P.roots.toFinset, Complex.abs (z - zᵢ) = 
                ∏ zᵢ in P.roots.toFinset, Complex.abs (1 - zᵢ.conj * z) := h_abs_eq
  -- Show |z| = 1 by contradiction
  by_contra h
  rw [Complex.abs.norm_eq_abs] at h
  have h_abs : Complex.abs z ≠ 1 := by linarith [ne_comm.mp h]
  -- Case 1: |z| < 1
  have case1 : Complex.abs z < 1 → False := by
    intro hz_lt
    have : ∀ zᵢ ∈ P.roots.toFinset, Complex.abs (z - zᵢ) < Complex.abs (1 - zᵢ.conj * z) := by
      intro zᵢ hzᵢ
      have hzᵢ_lt : Complex.abs zᵢ < 1 := hroots zᵢ (Polynomial.mem_roots.mp (Multiset.mem_toFinset.mp hzᵢ)).1
      rw [← Complex.abs.map_mul, ← Complex.abs.map_neg, mul_comm, neg_mul, one_mul]
      exact Complex.abs_sub_lt_one_of_lt_one hzᵢ_lt hz_lt
    have prod_lt : ∏ zᵢ in P.roots.toFinset, Complex.abs (z - zᵢ) < 
                   ∏ zᵢ in P.roots.toFinset, Complex.abs (1 - zᵢ.conj * z) :=
      Finset.prod_lt_prod' (fun _ _ => by positivity) this
    linarith [key_eq.symm]
  -- Case 2: |z| > 1
  have case2 : Complex.abs z > 1 → False := by
    intro hz_gt
    have : ∀ zᵢ ∈ P.roots.toFinset, Complex.abs (z - zᵢ) > Complex.abs (1 - zᵢ.conj * z) := by
      intro zᵢ hzᵢ
      have hzᵢ_lt : Complex.abs zᵢ < 1 := hroots zᵢ (Polynomial.mem_roots.mp (Multiset.mem_toFinset.mp hzᵢ)).1
      rw [← Complex.abs.map_mul, ← Complex.abs.map_neg, mul_comm, neg_mul, one_mul]
      exact Complex.abs_sub_gt_one_of_gt_one hzᵢ_lt hz_gt
    have prod_gt : ∏ zᵢ in P.roots.toFinset, Complex.abs (z - zᵢ) > 
                   ∏ zᵢ in P.roots.toFinset, Complex.abs (1 - zᵢ.conj * z) :=
      Finset.prod_lt_prod' (fun _ _ => by positivity) this
    linarith [key_eq.symm]
  -- Eliminate remaining cases
  exact h_abs (lt_trichotomy (Complex.abs z) 1).elim case1 (fun h ↦ (h_abs h).elim) case2