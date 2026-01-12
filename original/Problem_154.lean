/-
Polya-Szego Problem 154
Part One, Chapter 4

Original problem:
The counting function of a regular sequence with convergence exponent $\lambda$ satisfies the relation

$$
\lim _{r \rightarrow \infty} \frac{N(c r)}{N(r)}=c^{\lambda}, \quad c>0
$$

\begin{enumerate}
  \setcounter{enumi}{154}
  \item Let $N(r)$ be the counting function of the regular sequence $r_{1}, r_{2}, r_{3}, \ldots, r_{n}, \ldots$ with convergence exponent $\lambda$ and $f(x)$ be a piecewise constant function on the interval $(0, c], c>0$. Then
\end{enumerate}

$$
\lim _{r \rightarrow \in

Formalization notes: -- We formalize part 157 of Polya-Szego Problem 154:
-- Let N(r) be the counting function of a regular sequence {r_n} with 
-- convergence exponent λ, and let α > 0. Then:
-- lim_{r→∞} (1/N(r)) ∑_{r_n ≤ r} (r_n/r)^{α-λ} = ∫₀¹ x^{(α-λ)/λ} dx = λ/α
--
-- We make several assumptions about the sequence and its counting function:
-- 1. The sequence (r_n) is strictly increasing and tends to infinity
-- 2. The counting function N(r) = #{n : r_n ≤ r}
-- 3. The sequence is "regular" with convergence exponent λ, which means:
--    lim_{r→∞} N(cr)/N(r) = c^λ for all c > 0
-- 4. We assume λ > 0 and α > 0
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Integral.FundThmCalculus
import Mathlib.Analysis.Asymptotics.Asymptotics
import Mathlib.Order.Filter.AtTopBot

-- Formalization notes:
-- We formalize part 157 of Polya-Szego Problem 154:
-- Let N(r) be the counting function of a regular sequence {r_n} with 
-- convergence exponent λ, and let α > 0. Then:
-- lim_{r→∞} (1/N(r)) ∑_{r_n ≤ r} (r_n/r)^{α-λ} = ∫₀¹ x^{(α-λ)/λ} dx = λ/α
--
-- We make several assumptions about the sequence and its counting function:
-- 1. The sequence (r_n) is strictly increasing and tends to infinity
-- 2. The counting function N(r) = #{n : r_n ≤ r}
-- 3. The sequence is "regular" with convergence exponent λ, which means:
--    lim_{r→∞} N(cr)/N(r) = c^λ for all c > 0
-- 4. We assume λ > 0 and α > 0

variable {r_n : ℕ → ℝ} (h_seq : StrictMono r_n) (h_tendsto : Tendsto r_n atTop atTop)

-- Counting function for the sequence
noncomputable def N (r : ℝ) : ℕ :=
  Finset.card (Finset.filter (fun n => r_n n ≤ r) Finset.univ)

-- Assumption that the sequence is regular with convergence exponent λ
variable (λ : ℝ) (hλ_pos : 0 < λ)
variable (h_regular : ∀ (c : ℝ) (hc : 0 < c), 
  Tendsto (fun (r : ℝ) => (N (c * r) : ℝ) / (N r : ℝ)) atTop (𝓝 (c ^ λ)))

theorem problem_157_part1 (α : ℝ) (hα_pos : 0 < α) :
  Tendsto (fun (r : ℝ) => 
    (∑ n in Finset.filter (fun n => r_n n ≤ r) Finset.univ, 
      ((r_n n : ℝ) / r) ^ (α - λ)) / (N r : ℝ))
    atTop (𝓝 (λ / α)) := by
  sorry

theorem problem_157_part2 (α : ℝ) (hα_pos : 0 < α) :
  ∫ x in (0:ℝ)..1, x ^ ((α - λ) / λ) = λ / α := by
  have : (α - λ) / λ + 1 = α / λ := by
    field_simp [ne_of_gt hλ_pos]
    ring
  calc
    ∫ x in (0:ℝ)..1, x ^ ((α - λ) / λ) = 
      (λ / α) * (1 ^ (α / λ) - 0 ^ (α / λ)) := by
      refine integral_rpow (show (α - λ) / λ > -1 from ?_) 
      -- Need to show (α - λ)/λ > -1, which follows from α > 0 and λ > 0
    _ = λ / α := by simp [hα_pos, hλ_pos]
  sorry

-- Combined theorem statement
theorem problem_157 (α : ℝ) (hα_pos : 0 < α) :
  Tendsto (fun (r : ℝ) => 
    (∑ n in Finset.filter (fun n => r_n n ≤ r) Finset.univ, 
      ((r_n n : ℝ) / r) ^ (α - λ)) / (N r : ℝ))
    atTop (𝓝 (∫ x in (0:ℝ)..1, x ^ ((α - λ) / λ))) ∧
  ∫ x in (0:ℝ)..1, x ^ ((α - λ) / λ) = λ / α := by
  constructor
  · exact problem_157_part1 r_n h_seq h_tendsto λ hλ_pos h_regular α hα_pos
  · exact problem_157_part2 λ hλ_pos α hα_pos

-- Proof attempt:
theorem problem_157_part1 (α : ℝ) (hα_pos : 0 < α) :
  Tendsto (fun (r : ℝ) => 
    (∑ n in Finset.filter (fun n => r_n n ≤ r) Finset.univ, 
      ((r_n n : ℝ) / r) ^ (α - λ)) / (N r : ℝ))
    atTop (𝓝 (λ / α)) := by
  -- First rewrite the goal using the counting function N(r)
  simp_rw [N]
  -- Let's define the normalized sequence t_n = r_n / r
  set t_n := fun r n => r_n n / r with ht_n_def
  -- The sum can be seen as a Riemann sum for the integral ∫₀¹ x^(α-λ) dN(rx)/N(r)
  -- Using the regularity condition, we can show this converges to ∫₀¹ x^(α-λ) λx^{λ-1} dx
  -- Which equals λ/α after calculation

  -- Step 1: Rewrite the sum as a weighted sum of the t_n terms
  have sum_eq : ∀ r, (∑ n in Finset.filter (fun n => r_n n ≤ r) Finset.univ, (t_n r n) ^ (α - λ)) / N r =
    ∑ n in Finset.filter (fun n => r_n n ≤ r) Finset.univ, (t_n r n) ^ (α - λ) * (1 / N r) := by
    intro r; field_simp

  -- Step 2: The counting function N(r) tends to infinity
  have N_tendsto : Tendsto (N ·) atTop atTop := by
    refine tendsto_atTop_atTop_of_monotone' ?_ ?_
    · intro r₁ r₂ h
      exact Finset.card_mono (Finset.filter_mono (fun n => by simp; intro h'; exact le_trans h' h))
    · intro b
      obtain ⟨n, hn⟩ := h_tendsto (eventually_ge_atTop b)
      use r_n n
      simp [N]
      refine ⟨n, ?_, rfl⟩
      simp [hn.le]

  -- Step 3: Apply the regularity condition to get the limiting density
  -- We need to show the sum approximates the integral ∫₀¹ x^(α-λ) d(cardinality measure)
  -- This is the most technical part - we'll use the fact that under regularity,
  -- the counting measure rescaled by N(r) converges to λx^{λ-1} dx

  -- For simplicity, we'll use the following approach:
  -- 1. The sum can be seen as a Stieltjes integral ∫₀¹ x^(α-λ) dF_r(x) where F_r(x) = N(rx)/N(r)
  -- 2. By regularity, F_r(x) → x^λ pointwise
  -- 3. The derivative converges to λx^{λ-1}
  -- 4. Therefore the integral converges to ∫₀¹ x^(α-λ) * λx^{λ-1} dx = λ/α

  -- For a formal proof, we would need to:
  -- - Define the empirical measure μ_r = (1/N(r)) ∑_{n ≤ N(r)} δ_{t_n}
  -- - Show weak convergence to the limit measure μ = λx^{λ-1} dx
  -- - Apply the continuous mapping theorem with f(x) = x^{α-λ}

  -- Since this is quite involved, we'll outline the key steps:

  -- First, define the step function version of N(rx)/N(r)
  let F_r (r : ℝ) (x : ℝ) : ℝ := N (x * r) / N r

  -- By regularity, F_r(x) → x^λ pointwise
  have F_r_converges : ∀ x ∈ Ioc (0:ℝ) 1, Tendsto (fun r => F_r r x) atTop (𝓝 (x^λ)) := by
    intro x hx
    simp [F_r]
    exact h_regular x hx.1

  -- The sum can be written as a Stieltjes integral ∫₀¹ x^(α-λ) dF_r(x)
  -- We would then use integration by parts or a suitable limit theorem
  -- to show the integral converges to ∫₀¹ x^(α-λ) * λx^{λ-1} dx

  -- After calculation:
  have integral_calc : ∫ x in (0:ℝ)..1, x^(α - λ) * (λ * x^(λ - 1)) = λ / α := by
    have : ∀ x ∈ Set.Ioo (0:ℝ) 1, x^(α - λ) * (λ * x^(λ - 1)) = λ * x^(α - 1) := by
      intro x hx
      rw [← mul_assoc, ← rpow_add (hx.1.le)]
      congr 1
      field_simp [hλ_pos.ne']
      ring
    rw [intervalIntegral.integral_congr this]
    have : ∫ x in (0:ℝ)..1, λ * x^(α - 1) = λ * ∫ x in (0:ℝ)..1, x^(α - 1) := by
      apply intervalIntegral.integral_const_mul
    rw [this, integral_rpow]
    simp [hα_pos, hλ_pos]
    norm_num
    left
    linarith

  -- The actual proof would require establishing the weak convergence
  -- For now, we'll admit this step
  sorry