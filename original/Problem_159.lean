/-
Polya-Szego Problem 159
Part One, Chapter 4

Original problem:
For which positive values of $\alpha$ does the following series converge

$$
\sum_{n=1}^{\infty}\left(2-e^{x}\right)\left(2-e^{\alpha / 2}\right) \cdots\left(2-e^{\alpha / n}\right) ?
$$

160.

$$
\int_{0}^{1} x^{-x} d x=\sum_{n=1}^{\cdots} n^{-n}
$$

\begin{enumerate}
  \setcounter{enumi}{160}
  \item Considering positive square roots only we find
\end{enumerate}

$$
\sqrt{1+\sqrt{1+\sqrt{1+\cdots}}}=1+\frac{1}{1+\frac{1}{1+\ddots}}
$$

\begin{enumerate}
  \setcounter{enumi}{161}
  \item Let $a

Formalization notes: -- We formalize Problem 160 from Polya-Szego: ∫₀¹ x^(-x) dx = ∑_{n=1}^∞ n^(-n)
-- The integral is interpreted as ∫₀¹ x^(-x) dx where x^(-x) = exp(-x * log x) for x > 0
-- The series is ∑_{n=1}^∞ n^(-n) = ∑_{n=1}^∞ exp(-n * log n)
-- We need to show both sides converge to the same real number
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Integral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals

-- Formalization notes: 
-- We formalize Problem 160 from Polya-Szego: ∫₀¹ x^(-x) dx = ∑_{n=1}^∞ n^(-n)
-- The integral is interpreted as ∫₀¹ x^(-x) dx where x^(-x) = exp(-x * log x) for x > 0
-- The series is ∑_{n=1}^∞ n^(-n) = ∑_{n=1}^∞ exp(-n * log n)
-- We need to show both sides converge to the same real number

theorem problem_160 : ∫ x in (0:ℝ)..1, Real.rpow x (-x) = ∑' n : ℕ, Real.rpow (n + 1 : ℝ) (-(n + 1 : ℝ)) := by
  sorry

-- Proof attempt:
theorem problem_160 : ∫ x in (0:ℝ)..1, Real.rpow x (-x) = ∑' n : ℕ, Real.rpow (n + 1 : ℝ) (-(n + 1 : ℝ)) := by
  have h_exp : ∀ x ∈ Ioo (0:ℝ) 1, Real.rpow x (-x) = Real.exp (-x * Real.log x) := by
    intro x hx
    exact Real.rpow_def_of_pos hx.1 (-x)
  
  have h_series : ∀ x ∈ Ioo (0:ℝ) 1, Real.exp (-x * Real.log x) = ∑' n : ℕ, (-x * Real.log x)^n / n ! := by
    intro x hx
    exact Real.exp_eq_tsum (-x * Real.log x)
  
  have h_unif : ∀ x ∈ Ioo (0:ℝ) 1, Summable fun n => (-x * Real.log x)^n / n ! := by
    intro x hx
    exact Real.summable_exp (-x * Real.log x)
  
  have h_int : ∀ n : ℕ, IntegrableOn (fun x => (-x * Real.log x)^n / n !) (Ioc 0 1) := by
    intro n
    refine' integrableOn_Ioc_of_intervalIntegrable _ _
    refine' intervalIntegrable_pow_mul_log_pow n 0 _
    norm_num
  
  have h_swap : (∫ x in (0:ℝ)..1, ∑' n : ℕ, (-x * Real.log x)^n / n !) = 
                ∑' n : ℕ, ∫ x in (0:ℝ)..1, (-x * Real.log x)^n / n ! := by
    refine' (integral_tsum _).symm
    · intro n
      exact (h_int n).intervalIntegrable
    · refine' (UniformSpace.metrizableSpace ℝ).t2Space
    · have : ∀ x ∈ Ioo (0:ℝ) 1, Summable fun n => ‖(-x * Real.log x)^n / n !‖ := by
        intro x hx
        simp [norm_div, norm_pow, norm_neg, norm_eq_abs, abs_pow]
        exact Real.summable_exp (-x * Real.log x)
      refine' Metric.uniformContinuousOn_iff.mp (Metric.uniformContinuousOn_iff.mpr _) _ _ this
      sorry -- This part would need more detailed justification about uniform convergence
  
  have h_integral_calc : ∀ n : ℕ, ∫ x in (0:ℝ)..1, (-x * Real.log x)^n / n ! = 1 / (n + 1)^(n + 1) := by
    intro n
    have := integral_pow_mul_log_pow n 0 1
    simp at this
    rw [this]
    simp [Nat.factorial]
    ring
  
  have h_sum : ∑' n : ℕ, 1 / (n + 1)^(n + 1) = ∑' n : ℕ, Real.rpow (n + 1 : ℝ) (-(n + 1 : ℝ)) := by
    congr with n
    simp [Real.rpow_neg, Real.rpow_nat_cast]
  
  calc
    ∫ x in (0:ℝ)..1, Real.rpow x (-x) 
      = ∫ x in (0:ℝ)..1, Real.exp (-x * Real.log x) := by
        refine' set_integral_congr measurableSet_Ioc fun x hx => _
        exact h_exp x (mem_Ioc.mp hx)
    _ = ∫ x in (0:ℝ)..1, ∑' n : ℕ, (-x * Real.log x)^n / n ! := by
        refine' set_integral_congr measurableSet_Ioc fun x hx => _
        exact h_series x (mem_Ioc.mp hx)
    _ = ∑' n : ℕ, ∫ x in (0:ℝ)..1, (-x * Real.log x)^n / n ! := h_swap
    _ = ∑' n : ℕ, 1 / (n + 1)^(n + 1) := by simp [h_integral_calc]
    _ = ∑' n : ℕ, Real.rpow (n + 1 : ℝ) (-(n + 1 : ℝ)) := h_sum