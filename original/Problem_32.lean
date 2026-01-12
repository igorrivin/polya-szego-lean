/-
Polya-Szego Problem 32
Part Three, Chapter 1

Original problem:
Let $z_{1}, z_{2}, \ldots, z_{n}$ be arbitrary complex numbers, $z_{\mu} \neq z_{v}$ for all $\mu \neq v, \mu, v=1,2, \ldots, n$. We consider all the polynomials $P(z)$ that vanish only at the points $z_{1}, z_{2}, \ldots, z_{n}$ (having there zeros of arbitrary order). The set of the zeros of the derivatives $P^{\prime}(z)$ of all these polynomials is everywhere dense in the smallest convex polygon that contains $z_{1}, z_{2}, \ldots, z_{n}$.\\

Formalization notes: -- 1. We formalize the statement about density of zeros of derivatives P'(z)
-- 2. We consider polynomials over ℂ with roots exactly at given distinct points z₁,...,zₙ
-- 3. "Everywhere dense" means the closure of the set of zeros contains the convex hull
-- 4. We restrict to polynomials with roots only at the specified points (possibly with multiplicities)
-- 5. The convex polygon is the convex hull of {z₁,...,zₙ}
-/

import Mathlib.Analysis.Complex.Polynomial
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Hull
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Complex.Basic

-- Formalization notes:
-- 1. We formalize the statement about density of zeros of derivatives P'(z)
-- 2. We consider polynomials over ℂ with roots exactly at given distinct points z₁,...,zₙ
-- 3. "Everywhere dense" means the closure of the set of zeros contains the convex hull
-- 4. We restrict to polynomials with roots only at the specified points (possibly with multiplicities)
-- 5. The convex polygon is the convex hull of {z₁,...,zₙ}

theorem problem_32 (n : ℕ) (z : Fin n → ℂ) (h_distinct : Function.Injective z) :
    let S : Set ℂ := ⋃ (P : ℂ[X]) (hP_roots : ∀ w, P.IsRoot w → ∃ i, w = z i),
      {w | (derivative P).IsRoot w}
    let K : Set ℂ := convexHull ℝ (Set.range z)
    in Dense (K ∩ closure S) := by
  sorry

-- Proof attempt:
theorem problem_32 (n : ℕ) (z : Fin n → ℂ) (h_distinct : Function.Injective z) :
    let S : Set ℂ := ⋃ (P : ℂ[X]) (hP_roots : ∀ w, P.IsRoot w → ∃ i, w = z i),
      {w | (derivative P).IsRoot w}
    let K : Set ℂ := convexHull ℝ (Set.range z)
    in Dense (K ∩ closure S) := by
  intro S K
  rw [dense_iff_closure_eq]
  simp only [closure_inter, closure_closure]
  rw [inter_comm, ← dense_iff_closure_eq]
  intro ζ hζ
  rw [mem_closure_iff_frequently]
  intro U hU
  rcases hζ with ⟨t, ht, hsum, hpos⟩
  have h_nonzero : ∀ i, ζ ≠ z i := by
    intro i
    apply h_distinct.ne_of_ne_of_ne (i := i) (j := j)
    · exact hpos i
    · exact hpos j
    · exact hsum.symm ▸ one_ne_zero
  let m : Fin n → ℝ := fun i => t i / ∏ j in Finset.univ.erase i, ‖ζ - z j‖
  have hm_pos : ∀ i, 0 < m i := by
    intro i
    apply div_pos (hpos i)
    apply Finset.prod_pos
    intro j hj
    rw [Finset.mem_erase] at hj
    rw [norm_pos_iff]
    exact sub_ne_zero.2 (h_nonzero j)
  let P : ℂ[X] := ∏ i, (X - C (z i)) ^ (⌈m i⌉₊)
  have hP_roots : ∀ w, P.IsRoot w → ∃ i, w = z i := by
    intro w hw
    simp only [Polynomial.IsRoot.def, Polynomial.eval_prod, Polynomial.eval_pow, Polynomial.eval_sub, 
      Polynomial.eval_X, Polynomial.eval_C, Finset.prod_eq_zero_iff] at hw
    obtain ⟨i, _, hi⟩ := hw
    exact ⟨i, sub_eq_zero.1 (pow_eq_zero hi)⟩
  have hP' : derivative P = P * ∑ i, (⌈m i⌉₊ : ℂ) / (X - C (z i)) := by
    simp only [derivative_prod, derivative_pow, derivative_sub, derivative_X, derivative_C, sub_zero,
      one_mul, Polynomial.eval_prod, Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C, Polynomial.eval_one, Finset.prod_eq_mul_prod_erase, Finset.mul_sum]
    congr
    ext i
    rw [← mul_assoc, ← Polynomial.C_mul, ← Nat.cast_ceil_eq_ceil, ← mul_div_assoc]
    simp [mul_comm]
  have hζ_root : (derivative P).IsRoot ζ := by
    rw [hP', Polynomial.IsRoot.def, Polynomial.eval_mul, Polynomial.eval_sum]
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_self, Polynomial.eval_zero,
      zero_div, Finset.sum_const_zero, mul_zero]
  exact frequently_of_forall (fun P' hP' => ⟨ζ, hζ_root, hP_roots⟩) hU