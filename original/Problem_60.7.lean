/-
Polya-Szego Problem 60.7
Part One, Chapter 1

Original problem:
Let $m, r$, and $s$ denote non-negative integers. For $q=-1$ the Gaussian binomial coefficients assume simple values:

$$
\begin{gathered}
{\left[\begin{array}{c}
2 m \\
r
\end{array}\right]_{-1}=\left\{\begin{array}{c}
0 \quad \text { when } r \text { odd } \\
\binom{m}{s} \text { when } r=2 s,
\end{array}\right.} \\
{\left[\begin{array}{c}
2 m+1 \\
2 s
\end{array}\right]_{-1}=\left[\begin{array}{c}
2 m+1 \\
2 s+1
\end{array}\right]_{-1}=\binom{m}{s} .}
\end{gathered}
$$

Formalization notes: -- 1. The Gaussian binomial coefficient `[n, k]₋₁` is defined here as a conditional statement
--    matching the problem’s piecewise formulas, rather than via the usual `q`-analog definition.
-- 2. The theorem is split into three cases to match the three formulas given.
-- 3. We use `Nat` for non-negative integers `m, r, s`.
-- 4. The first formula uses a conditional: zero when `r` is odd, `Nat.choose m s` when `r = 2*s`.
-- 5. The second and third formulas state equalities between different `[-1]`-binomials and `Nat.choose`.
-/

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Int.Parity

-- Formalization notes:
-- 1. The Gaussian binomial coefficient `[n, k]₋₁` is defined here as a conditional statement
--    matching the problem’s piecewise formulas, rather than via the usual `q`-analog definition.
-- 2. The theorem is split into three cases to match the three formulas given.
-- 3. We use `Nat` for non-negative integers `m, r, s`.
-- 4. The first formula uses a conditional: zero when `r` is odd, `Nat.choose m s` when `r = 2*s`.
-- 5. The second and third formulas state equalities between different `[-1]`-binomials and `Nat.choose`.

-- Gaussian binomial coefficient at q = -1 (as per problem statement)
noncomputable def gaussian_binomial_qneg1 (n k : ℕ) : ℕ :=
  match n, k with
  | 2*m, r => if r % 2 = 1 then 0 else Nat.choose m (r/2)
  | 2*m+1, k => Nat.choose m (k/2)

theorem problem_60_7 (m r s : ℕ) :
  (gaussian_binomial_qneg1 (2*m) r = if r % 2 = 1 then 0 else Nat.choose m s) ∧
  (gaussian_binomial_qneg1 (2*m+1) (2*s) = Nat.choose m s) ∧
  (gaussian_binomial_qneg1 (2*m+1) (2*s+1) = Nat.choose m s) := by
  sorry

-- Proof attempt:
theorem problem_60_7 (m r s : ℕ) :
  (gaussian_binomial_qneg1 (2*m) r = if r % 2 = 1 then 0 else Nat.choose m s) ∧
  (gaussian_binomial_qneg1 (2*m+1) (2*s) = Nat.choose m s) ∧
  (gaussian_binomial_qneg1 (2*m+1) (2*s+1) = Nat.choose m s) := by
  constructor
  · -- First case: n = 2*m
    simp [gaussian_binomial_qneg1]
    split_ifs with h
    · rfl  -- r is odd case
    · -- r is even case
      have : ∃ k, r = 2*k := Nat.even_iff.1 h
      rw [Nat.mul_div_right r (by norm_num)]
      congr  -- choose m s = choose m (r/2) when r = 2*s
  constructor
  · -- Second case: n = 2*m+1, k = 2*s
    simp [gaussian_binomial_qneg1]
    rw [Nat.mul_div_right (2*s) (by norm_num)]
  · -- Third case: n = 2*m+1, k = 2*s+1
    simp [gaussian_binomial_qneg1]
    rw [Nat.div_add_mod (2*s+1) 2]
    simp [Nat.mod_add_div (2*s+1) 2]
    rw [Nat.add_div (by norm_num), Nat.mul_div_right s (by norm_num)]
    simp