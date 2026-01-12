/-
Polya-Szego Problem 288
Part Three, Chapter 6

Original problem:
Let\\
$f(0)=0$ the\\
holds: in add

Equality

$$
f(z)=\frac{R w_{0}+\left[w_{0}-2 A(R)\right] e^{i \alpha} z}{R-e^{i \alpha} z}, \quad \alpha \text { real. }
$$

284 (continued). The maximum $M(r)$ of the absolute value of $f(z)$ in the disk $|z| \leqq r$ is restricted by\\[0pt]
cronger than 275. ] b disk $|z|<1$ and let Then $f(z)$ vanishes idengular and $|f(z)|<1$ in : inequality $|f(z)|<|z|$ two schlicht maps of of the $z$ - and $w$-plane lents $z=z_{0}$ and $w=w_{0}$ the images of the disk a

Formalization notes: We formalize Hadamard's three-circle theorem for bounded analytic functions on a disk.
   
   Let f : ℂ → ℂ be analytic on the open disk of radius R > 0, non-zero, and bounded.
   Define M(r) = sup_{|z| ≤ r} |f(z)| for 0 ≤ r < R, and M(R) = lim_{r→R⁻} M(r).
   Then for 0 < r < R, we have:
     M(r) ≤ M(0)^{(R-r)/(R+r)} * M(R)^{(2r)/(R+r)}
   
   We use:
   - `Complex.analyticOn_ball` for analyticity on an open ball
   - `Metric.ball` for the open disk
   - `Real.rpow` for the real power operation
   - The supremum is taken over the closed ball
-/
-/

import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/- Formalization notes:
   We formalize Hadamard's three-circle theorem for bounded analytic functions on a disk.
   
   Let f : ℂ → ℂ be analytic on the open disk of radius R > 0, non-zero, and bounded.
   Define M(r) = sup_{|z| ≤ r} |f(z)| for 0 ≤ r < R, and M(R) = lim_{r→R⁻} M(r).
   Then for 0 < r < R, we have:
     M(r) ≤ M(0)^{(R-r)/(R+r)} * M(R)^{(2r)/(R+r)}
   
   We use:
   - `Complex.analyticOn_ball` for analyticity on an open ball
   - `Metric.ball` for the open disk
   - `Real.rpow` for the real power operation
   - The supremum is taken over the closed ball
-/

open Complex Set Metric

theorem problem_284 {f : ℂ → ℂ} {R : ℝ} (hR : 0 < R) 
    (h_analytic : AnalyticOn ℂ f (ball (0 : ℂ) R))
    (h_nonzero : ∀ z, z ∈ ball (0 : ℂ) R → f z ≠ 0)
    (h_bounded : ∃ B : ℝ, ∀ z, z ∈ ball (0 : ℂ) R → ‖f z‖ ≤ B) :
    ∀ r : ℝ, 0 < r → r < R → 
    let M : ℝ → ℝ := fun t => sSup (‖f '' (closedBall (0 : ℂ) t))
    let M_R := liminf (fun (r' : ℝ) => M r') (𝓝[<] R)
    in M r ≤ (M 0) ^ ((R - r)/(R + r)) * M_R ^ ((2 * r)/(R + r)) := by
  sorry

-- Proof attempt:
theorem problem_284 {f : ℂ → ℂ} {R : ℝ} (hR : 0 < R) 
    (h_analytic : AnalyticOn ℂ f (ball (0 : ℂ) R))
    (h_nonzero : ∀ z, z ∈ ball (0 : ℂ) R → f z ≠ 0)
    (h_bounded : ∃ B : ℝ, ∀ z, z ∈ ball (0 : ℂ) R → ‖f z‖ ≤ B) :
    ∀ r : ℝ, 0 < r → r < R → 
    let M : ℝ → ℝ := fun t => sSup (‖f '' (closedBall (0 : ℂ) t))
    let M_R := liminf (fun (r' : ℝ) => M r') (𝓝[<] R)
    in M r ≤ (M 0) ^ ((R - r)/(R + r)) * M_R ^ ((2 * r)/(R + r)) := by
  intro r hr h_rR
  let M := fun t => sSup (‖f '' (closedBall (0 : ℂ) t))
  let M_R := liminf (fun (r' : ℝ) => M r') (𝓝[<] R)
  
  -- First show log ∘ M is convex
  have h_convex : ConvexOn ℝ (Ioo 0 R) (fun t => log (M t)) := by
    apply ConvexOn.log_of_isBoundedUnder_comp
    · exact fun t ht => sSup_nonempty (Nonempty.image _ (nonempty_closedBall.2 ht.1.le))
    · intro t ht
      exact (M t).le.trans (h_bounded.choose_spec _ (ball_subset_ball ht.2.le (mem_ball_self hR)))
    · apply ConvexOn.isBoundedUnder_comp_sSup_of_convexOn_norm
      exact h_analytic.norm_subharmonicOn_ball hR h_nonzero
  
  -- Specialize convexity to the points 0, r, R
  have h := h_convex.le_left_liminf (left_mem_Icc.mpr (le_of_lt hR)) ⟨hr, h_rR⟩
  
  -- Rewrite the inequality in terms of M
  have key_ineq : log (M r) ≤ ((R - r)/(R + r)) * log (M 0) + ((2 * r)/(R + r)) * log M_R := by
    have : (R - r)/(R + r) + (2 * r)/(R + r) = 1 := by field_simp; rw [← add_sub]; ring
    convert h using 1
    · simp only [smul_eq_mul]
      rw [mul_comm, mul_comm ((2 * r)/(R + r))]
    · simp [this]
  
  -- Exponentiate both sides to get the desired inequality
  rw [← Real.exp_le_exp, Real.exp_add, Real.exp_mul, Real.exp_mul]
  simp_rw [Real.exp_log]
  · exact key_ineq
  · exact le_sSup ⟨0, by simp [M]⟩ (h_bounded.choose_spec _ (mem_ball_self hR))
  · refine sSup_nonempty ?_
    simp only [M, image_nonempty]
    exact nonempty_closedBall.2 hr.le