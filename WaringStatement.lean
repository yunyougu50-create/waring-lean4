/-
Copyright (c) 2026 The Waring formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Waring formalization authors
-/
import Mathlib.NumberTheory.SumFourSquares

/-!
# Statement of Waring's theorem

This file fixes the precise statement of the full Waring problem and proves the
two base cases `k = 1` (one first power) and `k = 2` (Lagrange's four-square
theorem).  The general case `∀ k ≥ 1` is not proved here; see
`WARING-FULL-PLAN.md` for the roadmap.

Waring's theorem: for every `k ≥ 1` there is `g` such that every natural number
is a sum of at most `g` nonnegative `k`-th powers.
-/

open Finset

namespace Waring

/-- `n` is a sum of `s` nonnegative `k`-th powers. -/
def IsSumOfKthPowers (k n s : ℕ) : Prop :=
  ∃ f : Fin s → ℕ, n = ∑ i, (f i) ^ k

/-- The full Waring theorem, with an explicit bound `g` depending on `k`. -/
def WaringTheorem : Prop :=
  ∀ k : ℕ, 0 < k → ∃ g : ℕ, ∀ n : ℕ, ∃ s ≤ g, IsSumOfKthPowers k n s

/-- Waring for first powers: every `n` is one first power. -/
theorem waring_one : ∃ g : ℕ, ∀ n : ℕ, ∃ s ≤ g, IsSumOfKthPowers 1 n s := by
  refine ⟨1, fun n => ⟨1, le_rfl, ⟨fun _ => n, ?_⟩⟩⟩
  simp

/-- Waring for squares: Lagrange's four-square theorem. -/
theorem waring_two : ∃ g : ℕ, ∀ n : ℕ, ∃ s ≤ g, IsSumOfKthPowers 2 n s := by
  refine ⟨4, fun n => ?_⟩
  obtain ⟨a, b, c, d, h⟩ := Nat.sum_four_squares n
  refine ⟨4, le_rfl, ⟨![a, b, c, d], ?_⟩⟩
  simp [Fin.sum_univ_four, h]

end Waring
