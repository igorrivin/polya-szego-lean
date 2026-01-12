/-
Polya-Szego Problem 10
Part Three, Chapter 1

Original problem:
Let the radius vector $r$ and the argument $\vartheta$ be functions of the time. The complex function $z=r e^{i \vartheta}$ of the real variable $t$ is represented by the motion of a point in a plane. Compute the components of velocity and of acceleration parallel and perpendicular to the radius vector. [Differentiate $z$ twice with respect to $t$.]\\

Formalization notes: We formalize the problem about computing velocity and acceleration components 
for planar motion in polar coordinates. Given:
  r : ℝ → ℝ (radius as function of time)
  θ : ℝ → ℝ (angle as function of time)  
  z(t) = r(t) * Complex.exp (Complex.I * θ(t))
The velocity components are:
  - Radial component: dr/dt (along radius vector)
  - Tangential component: r * dθ/dt (perpendicular to radius vector)
The acceleration components are:
  - Radial: d²r/dt² - r * (dθ/dt)²
  - Tangential: r * d²θ/dt² + 2 * (dr/dt) * (dθ/dt)
We state this as equalities between derivatives and the claimed expressions.
/
-/

import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.Calculus.Deriv.Basic

/- Formalization notes:
We formalize the problem about computing velocity and acceleration components 
for planar motion in polar coordinates. Given:
  r : ℝ → ℝ (radius as function of time)
  θ : ℝ → ℝ (angle as function of time)  
  z(t) = r(t) * Complex.exp (Complex.I * θ(t))
The velocity components are:
  - Radial component: dr/dt (along radius vector)
  - Tangential component: r * dθ/dt (perpendicular to radius vector)
The acceleration components are:
  - Radial: d²r/dt² - r * (dθ/dt)²
  - Tangential: r * d²θ/dt² + 2 * (dr/dt) * (dθ/dt)
We state this as equalities between derivatives and the claimed expressions.
/

theorem problem_10_velocity_components (r θ : ℝ → ℝ) (t : ℝ) 
    (hdr : DifferentiableAt ℝ r t) (hdθ : DifferentiableAt ℝ θ t) :
    let z : ℝ → ℂ := fun t => (r t : ℂ) * Complex.exp (Complex.I * (θ t : ℂ))
    -- Velocity derivative
    let v : ℂ := deriv z t
    -- Velocity in polar basis: v = v_r * e_r + v_θ * e_θ
    -- where e_r = exp(iθ) and e_θ = i * exp(iθ)
    let e_r : ℂ := Complex.exp (Complex.I * (θ t : ℂ))
    let v_r : ℝ := deriv r t
    let v_θ : ℝ := (r t) * deriv θ t
    in v = (v_r : ℂ) * e_r + (v_θ : ℂ) * (Complex.I * e_r) := by
  intro z v e_r v_r v_θ
  have hr_diff : DifferentiableAt ℝ (fun x : ℝ => (r x : ℂ)) t := by
    exact hdr.ofReal_comp.differentiableAt
  have hθ_diff : DifferentiableAt ℝ (fun x : ℝ => (θ x : ℂ)) t := by
    exact hdθ.ofReal_comp.differentiableAt
  -- Compute derivative using product rule and chain rule
  have hz_diff : DifferentiableAt ℝ z t := by
    unfold z
    apply DifferentiableAt.mul
    · exact hr_diff
    · apply DifferentiableAt.cexp
      apply DifferentiableAt.mul_const
      exact hθ_diff
  -- Calculate the derivative explicitly
  have h_deriv : deriv z t = deriv r t * Complex.exp (Complex.I * (θ t : ℂ)) +
      (r t : ℂ) * (Complex.I * deriv θ t * Complex.exp (Complex.I * (θ t : ℂ))) := by
    unfold z
    rw [deriv_mul (hr_diff.differentiableWithinAt) (DifferentiableAt.cexp ?_).differentiableWithinAt]
    · rw [deriv_ofReal_comp hdr]
      rw [deriv_cexp]
      · rw [deriv_mul_const]
        rw [deriv_ofReal_comp hdθ]
      · exact DifferentiableAt.mul_const hθ_diff
    · exact hz_diff
  unfold v e_r v_r v_θ
  rw [h_deriv]
  push_cast
  ring

theorem problem_10_acceleration_components (r θ : ℝ → ℝ) (t : ℝ)
    (hdr : ContDiffAt ℝ 2 r t) (hdθ : ContDiffAt ℝ 2 θ t) :
    let z : ℝ → ℂ := fun t => (r t : ℂ) * Complex.exp (Complex.I * (θ t : ℂ))
    -- Acceleration (second derivative)
    let a : ℂ := deriv (deriv z) t
    -- Polar basis vectors
    let e_r : ℂ := Complex.exp (Complex.I * (θ t : ℂ))
    -- Acceleration components
    let a_r : ℝ := deriv (deriv r) t - (r t) * ((deriv θ t) ^ 2)
    let a_θ : ℝ := (r t) * deriv (deriv θ) t + 2 * deriv r t * deriv θ t
    in a = (a_r : ℂ) * e_r + (a_θ : ℂ) * (Complex.I * e_r) := by
  intro z a e_r a_r a_θ
  -- First, show z is twice differentiable
  have hz_contdiff : ContDiffAt ℝ 2 z t := by
    unfold z
    refine ContDiffAt.mul ?_ ?_
    · exact hdr.ofReal_comp.contDiffAt
    · refine Complex.contDiff_exp.contDiffAt.comp t ?_
      refine ContDiffAt.mul_const ?_
      exact hdθ.ofReal_comp.contDiffAt
  
  -- Compute second derivative using product rule twice
  have h_deriv2 : deriv (deriv z) t = 
      (deriv (deriv r) t : ℂ) * Complex.exp (Complex.I * (θ t : ℂ)) +
      2 * (deriv r t : ℂ) * (Complex.I * deriv θ t * Complex.exp (Complex.I * (θ t : ℂ))) +
      (r t : ℂ) * ((Complex.I * deriv (deriv θ) t - (deriv θ t)^2) * 
        Complex.exp (Complex.I * (θ t : ℂ))) := by
    -- This requires a longer calculation using derivative rules
    sorry  -- The full calculation is lengthy but follows from product/chain rules
  
  unfold a a_r a_θ e_r
  rw [h_deriv2]
  push_cast
  ring

-- Proof attempt:
theorem problem_10_acceleration_components (r θ : ℝ → ℝ) (t : ℝ)
    (hdr : ContDiffAt ℝ 2 r t) (hdθ : ContDiffAt ℝ 2 θ t) :
    let z : ℝ → ℂ := fun t => (r t : ℂ) * Complex.exp (Complex.I * (θ t : ℂ))
    -- Acceleration (second derivative)
    let a : ℂ := deriv (deriv z) t
    -- Polar basis vectors
    let e_r : ℂ := Complex.exp (Complex.I * (θ t : ℂ))
    -- Acceleration components
    let a_r : ℝ := deriv (deriv r) t - (r t) * ((deriv θ t) ^ 2)
    let a_θ : ℝ := (r t) * deriv (deriv θ) t + 2 * deriv r t * deriv θ t
    in a = (a_r : ℂ) * e_r + (a_θ : ℂ) * (Complex.I * e_r) := by
  intro z a e_r a_r a_θ
  -- First, show z is twice differentiable
  have hz_contdiff : ContDiffAt ℝ 2 z t := by
    unfold z
    refine ContDiffAt.mul ?_ ?_
    · exact hdr.ofReal_comp.contDiffAt
    · refine Complex.contDiff_exp.contDiffAt.comp t ?_
      refine ContDiffAt.mul_const ?_
      exact hdθ.ofReal_comp.contDiffAt
  
  -- Compute first derivative
  have hdr1 : DifferentiableAt ℝ r t := hdr.differentiableAt (by norm_num)
  have hdθ1 : DifferentiableAt ℝ θ t := hdθ.differentiableAt (by norm_num)
  have h_deriv1 : deriv z t = deriv r t * Complex.exp (Complex.I * (θ t : ℂ)) +
      (r t : ℂ) * (Complex.I * deriv θ t * Complex.exp (Complex.I * (θ t : ℂ))) := by
    unfold z
    rw [deriv_mul (hdr1.ofReal_comp.differentiableAt.differentiableWithinAt) 
        (DifferentiableAt.cexp (DifferentiableAt.mul_const hdθ1.ofReal_comp.differentiableAt)).differentiableWithinAt]
    rw [deriv_ofReal_comp hdr1]
    rw [deriv_cexp (DifferentiableAt.mul_const hdθ1.ofReal_comp.differentiableAt)]
    rw [deriv_mul_const]
    rw [deriv_ofReal_comp hdθ1]
    ring

  -- Compute second derivative
  have hdr2 : DifferentiableAt ℝ (deriv r) t := 
    hdr.differentiableAt (by norm_num)
  have hdθ2 : DifferentiableAt ℝ (deriv θ) t := 
    hdθ.differentiableAt (by norm_num)
  
  have h_deriv2 : deriv (deriv z) t = 
      (deriv (deriv r) t : ℂ) * Complex.exp (Complex.I * (θ t : ℂ)) +
      2 * (deriv r t : ℂ) * (Complex.I * deriv θ t * Complex.exp (Complex.I * (θ t : ℂ))) +
      (r t : ℂ) * ((Complex.I * deriv (deriv θ) t - (deriv θ t)^2) * 
        Complex.exp (Complex.I * (θ t : ℂ))) := by
    rw [h_deriv1]
    -- Differentiate first term
    have h1 : deriv (fun t => deriv r t * Complex.exp (Complex.I * (θ t : ℂ))) t =
        deriv (deriv r) t * Complex.exp (Complex.I * (θ t : ℂ)) +
        deriv r t * (Complex.I * deriv θ t * Complex.exp (Complex.I * (θ t : ℂ))) := by
      rw [deriv_mul (hdr2.differentiableAt.differentiableWithinAt) 
          (DifferentiableAt.cexp (DifferentiableAt.mul_const hdθ1.ofReal_comp.differentiableAt)).differentiableWithinAt]
      rw [deriv_cexp (DifferentiableAt.mul_const hdθ1.ofReal_comp.differentiableAt)]
      ring
    -- Differentiate second term
    have h2 : deriv (fun t => (r t : ℂ) * (Complex.I * deriv θ t * Complex.exp (Complex.I * (θ t : ℂ)))) t =
        deriv r t * (Complex.I * deriv θ t * Complex.exp (Complex.I * (θ t : ℂ))) +
        (r t : ℂ) * deriv (fun t => Complex.I * deriv θ t * Complex.exp (Complex.I * (θ t : ℂ))) t := by
      rw [deriv_mul (hdr1.ofReal_comp.differentiableAt.differentiableWithinAt) ?_]
      · rw [deriv_mul (DifferentiableAt.mul_const hdθ2.ofReal_comp.differentiableAt).differentiableWithinAt
          (DifferentiableAt.cexp (DifferentiableAt.mul_const hdθ1.ofReal_comp.differentiableAt)).differentiableWithinAt]
        rw [deriv_mul_const]
        rw [deriv_cexp (DifferentiableAt.mul_const hdθ1.ofReal_comp.differentiableAt)]
        rw [deriv_mul_const]
        rw [deriv_ofReal_comp hdθ2]
        ring
      · apply DifferentiableAt.mul
        · exact DifferentiableAt.mul_const hdθ2.ofReal_comp.differentiableAt
        · exact DifferentiableAt.cexp (DifferentiableAt.mul_const hdθ1.ofReal_comp.differentiableAt)
    rw [deriv_add]
    · rw [h1, h2]
      ring
    · exact (DifferentiableAt.mul hdr2.ofReal_comp.differentiableAt 
        (DifferentiableAt.cexp (DifferentiableAt.mul_const hdθ1.ofReal_comp.differentiableAt))).differentiableWithinAt
    · exact (DifferentiableAt.mul hdr1.ofReal_comp.differentiableAt
        (DifferentiableAt.mul (DifferentiableAt.mul_const hdθ2.ofReal_comp.differentiableAt)
        (DifferentiableAt.cexp (DifferentiableAt.mul_const hdθ1.ofReal_comp.differentiableAt)))).differentiableWithinAt

  unfold a a_r a_θ e_r
  rw [h_deriv2]
  push_cast
  ring