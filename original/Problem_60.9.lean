/-
Polya-Szego Problem 60.9
Part One, Chapter 1

Original problem:
The number of zig-zag paths between the street corners $(0,0)$ and ( $r, s$ ) is

$$
\binom{n}{r} .
$$

Formalization notes: We formalize "zig-zag paths" as monotonic lattice paths from (0,0) to (r,s) that only move
right (east) or up (north). These are standard combinatorial objects where:
- Total steps needed: n = r + s
- Exactly r right moves and s up moves
- Number of such paths: choose (r + s) r = binomial(n, r)
  where n = r + s
-/

import Mathlib.Combinatorics.Dyck
import Mathlib.Combinatorics.Catalan
import Mathlib.Data.Nat.Choose.Basic

/-!
Formalization notes:
We formalize "zig-zag paths" as monotonic lattice paths from (0,0) to (r,s) that only move
right (east) or up (north). These are standard combinatorial objects where:
- Total steps needed: n = r + s
- Exactly r right moves and s up moves
- Number of such paths: choose (r + s) r = binomial(n, r)
  where n = r + s

We use `Nat` for coordinates since the problem deals with non-negative integer grid points.
-/

/-- The number of monotonic lattice paths from (0,0) to (r,s) using only right and up moves. -/
theorem problem_60_9 (r s : ℕ) : 
    Finset.card (Finset.filter (fun (p : List (Fin 2)) => 
      let steps := p.map (fun d => if d = 0 then (1, 0) else (0, 1))
      let pos := steps.scanl (fun (x, y) (dx, dy) => (x + dx, y + dy)) (0, 0)
      (0, 0) ∈ pos ∧ (r, s) ∈ pos ∧ 
      pos.getLast (0, 0) ⟨by simp⟩ = (r, s) ∧ 
      p.length = r + s) 
      (Finset.univ : Finset (List (Fin 2)))) = Nat.choose (r + s) r := by
  sorry

-- Proof attempt:
theorem problem_60_9 (r s : ℕ) : 
    Finset.card (Finset.filter (fun (p : List (Fin 2)) => 
      let steps := p.map (fun d => if d = 0 then (1, 0) else (0, 1))
      let pos := steps.scanl (fun (x, y) (dx, dy) => (x + dx, y + dy)) (0, 0)
      (0, 0) ∈ pos ∧ (r, s) ∈ pos ∧ 
      pos.getLast (0, 0) ⟨by simp⟩ = (r, s) ∧ 
      p.length = r + s) 
      (Finset.univ : Finset (List (Fin 2)))) = Nat.choose (r + s) r := by
  simp only [Finset.card_univ, Finset.mem_univ, Finset.filter_true]
  let f : List (Fin 2) → List (Fin 2) := fun p => p
  have bij : Function.Bijective f := by
    constructor
    · exact fun _ _ h => h
    · exact fun p => ⟨p, rfl⟩
  rw [Fintype.card_congr (Equiv.ofBijective f bij)]
  simp only [List.length_eq_sum_card_fin, Fintype.card_fin]
  convert Nat.choose_choose_add _ _
  simp [add_comm]