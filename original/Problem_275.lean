/-
Polya-Szego Problem 275
Part Three, Chapter 6

Original problem:
The function $f(z)$ is regular and single-valued in the interior of the closed domain $\mathfrak{D}$ and continuous in $\mathfrak{D}$, boundary included; the maximum of $|f(z)|$ on the boundary of $\mathfrak{D}$ is called $M$. Under these conditions we have the inequality

$$
|f(z)|<M
$$

in the interior of $\mathfrak{D}$ unless $f(z)$ is a constant. [This statement is stronger than 135.]\\

Formalization notes: -- We formalize the key insight from Problem 275: for a holomorphic function f on a compact domain D,
-- if f attains its maximum modulus at an interior point, then f must be constant.
-- We assume D is a connected, bounded, open set in ℂ with piecewise smooth boundary.
-- The original statement "|f(z)| < M in the interior unless f(z) is constant" is equivalent to:
-- "If f is not constant, then |f| cannot attain its maximum at any interior point."
-/

import Mathlib.Analysis.Complex.MaximumModulus
import Mathlib.Topology.Algebra.Order.Compact

-- Formalization notes:
-- We formalize the key insight from Problem 275: for a holomorphic function f on a compact domain D,
-- if f attains its maximum modulus at an interior point, then f must be constant.
-- We assume D is a connected, bounded, open set in ℂ with piecewise smooth boundary.
-- The original statement "|f(z)| < M in the interior unless f(z) is constant" is equivalent to:
-- "If f is not constant, then |f| cannot attain its maximum at any interior point."

theorem problem_275 (f : ℂ → ℂ) (D : Set ℂ) 
    (hcont : ContinuousOn f (closure D)) (hdiff : DifferentiableOn ℂ f (interior D))
    (hconn : IsConnected D) (hbounded : Bornology.IsBounded D) :
    ∀ z ∈ interior D, Set.Subsingleton (f '' (boundary D)) ∨ 
    ∃ w ∈ boundary D, ‖f z‖ < ‖f w‖ := by
  sorry

-- Proof attempt:
theorem problem_275 (f : ℂ → ℂ) (D : Set ℂ) 
    (hcont : ContinuousOn f (closure D)) (hdiff : DifferentiableOn ℂ f (interior D))
    (hconn : IsConnected D) (hbounded : Bornology.IsBounded D) :
    ∀ z ∈ interior D, Set.Subsingleton (f '' (boundary D)) ∨ 
    ∃ w ∈ boundary D, ‖f z‖ < ‖f w‖ := by
  intro z hz
  by_cases hconst : ∀ w ∈ D, f w = f z
  · left
    apply Set.subsingleton_of_forall_eq (f z)
    intro y hy
    obtain ⟨w, hw, rfl⟩ := hy
    exact hconst w (subset_closure hw)
  
  · right
    push_neg at hconst
    obtain ⟨w₀, hw₀, hne⟩ := hconst
    have hD : IsCompact (closure D) := hbounded.isCompact_closure
    have hf : ContinuousOn (fun z ↦ ‖f z‖) (closure D) :=
      continuous_norm.comp_continuousOn hcont
    obtain ⟨w, hw, hmax⟩ := hf.exists_forall_ge (nonempty_closure.mpr ⟨w₀, hw₀⟩) hD
    have hw_boundary : w ∈ boundary D := by
      by_contra hw_int
      have hw_mem : w ∈ interior D := by
        rw [← closure_diff_interior] at hw_int
        exact (mem_diff w).mp hw_int |>.2
      exact (Complex.norm_eq_norm_of_mem_maximum_modulus_on_open hdiff hw_mem hconn hmax).mp hne
    use w, hw_boundary
    have : ‖f z‖ ≤ ‖f w‖ := hmax z (subset_closure (interior_subset hz))
    refine lt_of_le_of_ne this ?_
    intro heq
    have := Complex.norm_eq_norm_of_mem_maximum_modulus_on_open hdiff hz hconn hmax
    rw [heq] at this
    exact hne (this w₀ hw₀)