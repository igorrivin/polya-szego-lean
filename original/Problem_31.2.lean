/-
Polya-Szego Problem 31.2
Part One, Chapter 1

Original problem:
Prove that

$$
\binom{n}{0}-\binom{n}{1}+\binom{n}{2}-\cdots+(-1)^{r}\binom{n}{r}=(-1)^{r}\binom{n-1}{r} .
$$

\begin{enumerate}
  \setcounter{enumi}{31}
  \item $\binom{n}{0}^{2}+\binom{n}{1}^{2}+\binom{n}{2}^{2}+\cdots+\binom{n}{n}^{2}=\binom{2 n}{n}$.
  \item $\binom{2 n}{0}^{2}-\binom{2 n}{1}^{2}+\binom{2 n}{2}^{2}-\cdots-\binom{2 n}{2 n-1}^{2}+\binom{2 n}{2 n}^{2}=(-1)^{n}\binom{2 n}{n}$.
  \item Put
\end{enumerate}

$$
\begin{aligned}
\sum_{k=0}^{\infty} a_{k} z^{k} \sum_{l=0}^{\infty} b_{

Formalization notes: -- We formalize the alternating sum of binomial coefficients identity:
-- ∑_{k=0}^r (-1)^k * C(n, k) = (-1)^r * C(n-1, r)
-- This holds for all natural numbers n and r with r ≤ n
-- We use Finset.sum over the range [0, r] for the left-hand side
-/

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Real.Basic

-- Formalization notes:
-- We formalize the alternating sum of binomial coefficients identity:
-- ∑_{k=0}^r (-1)^k * C(n, k) = (-1)^r * C(n-1, r)
-- This holds for all natural numbers n and r with r ≤ n
-- We use Finset.sum over the range [0, r] for the left-hand side

theorem problem_31_2 (n r : ℕ) (hr : r ≤ n) : 
    ∑ k in Finset.range (r + 1), (-1 : ℤ) ^ k * (Nat.choose n k) = 
    (-1 : ℤ) ^ r * (Nat.choose (n - 1) r) := by
  sorry

-- Proof attempt:
theorem problem_31_2 (n r : ℕ) (hr : r ≤ n) : 
    ∑ k in Finset.range (r + 1), (-1 : ℤ) ^ k * (Nat.choose n k) = 
    (-1 : ℤ) ^ r * (Nat.choose (n - 1) r) := by
  induction r with
  | zero =>
    simp [Finset.range_one, Nat.choose_zero_right]
  | succ r ih =>
    rw [Finset.sum_range_succ, ih (Nat.le_of_succ_le hr)]
    rw [Nat.succ_eq_add_one, ← mul_add, ← sub_eq_add_neg]
    have h : n - 1 - r = n - (r + 1) := by
      rw [Nat.sub_sub, Nat.add_comm]
      exact Nat.sub_le_sub_left hr (r + 1)
    rw [← Nat.choose_succ_succ (n - 1) r, h]
    ring_nf
    simp only [pow_succ, neg_mul, one_mul, mul_neg, neg_neg]
    rw [Nat.choose_succ_succ, Nat.sub_sub]
    ring