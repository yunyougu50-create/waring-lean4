/-
Copyright (c) 2026 The Waring formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Waring formalization authors
-/
import WaringBound

/-!
# The `G` side: Waring's problem for all sufficiently large integers

`WaringBound.lean` proves lower bounds for Waring's function `g(k)`, the least
number of `k`-th powers needed for *all* natural numbers.  The other classical
function is `G(k)`, the least number needed for all *sufficiently large*
natural numbers.  Clearly `G(k) ≤ g(k)`.

This file proves the `k = 1` and `k = 2` entries of the `G` column:

```text
G(1) = 1,   G(2) = 4.
```

The upper bound `G(2) ≤ 4` is Lagrange's theorem; the lower bound `G(2) ≥ 4`
is the classical obstruction `n ≡ 7 (mod 8)`: no sum of three squares is
congruent to `7` modulo `8`, and there are arbitrarily large such `n`.

The higher entries `G(3) ∈ [4, 7]` and `G(5) ∈ [6, 17]` are not accessible
here; even `G(3) ≤ 7` (Linnik) is research-level.
-/

open Finset

namespace Waring

/-- `s` is an eventual Waring bound for exponent `k`: every sufficiently large
natural number is a sum of at most `s` `k`-th powers. -/
def IsEventuallyWaringBound (k s : ℕ) : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∃ t ≤ s, IsSumOfKthPowers k n t

/-- A Waring bound is an eventual Waring bound.  This is `G(k) ≤ g(k)`. -/
theorem isEventuallyWaringBound_of_isWaringBound {k g : ℕ} (h : IsWaringBound k g) :
    IsEventuallyWaringBound k g :=
  ⟨0, fun n _ => h n⟩

/-- Every eventual Waring bound yields a Waring bound: the finitely many integers
below the threshold are sums of `1^k`, since `1` is a `k`-th power. -/
theorem isWaringBound_of_isEventuallyWaringBound {k s : ℕ} (h : IsEventuallyWaringBound k s) :
    ∃ g : ℕ, IsWaringBound k g := by
  obtain ⟨N, hN⟩ := h
  refine ⟨max s (N - 1), fun n => ?_⟩
  by_cases hn : N ≤ n
  · obtain ⟨t, ht, hrepr⟩ := hN n hn
    exact ⟨t, le_trans ht (le_max_left _ _), hrepr⟩
  · refine ⟨n, le_trans ?_ (le_max_right _ _), ⟨fun _ => 1, ?_⟩⟩
    · omega
    · simp

/-! ## `G(1) = 1` -/

theorem isEventuallyWaringBound_one : IsEventuallyWaringBound 1 1 :=
  isEventuallyWaringBound_of_isWaringBound isWaringBound_one

theorem one_le_of_isEventuallyWaringBound_one {s : ℕ} (h : IsEventuallyWaringBound 1 s) :
    1 ≤ s := by
  obtain ⟨N, hN⟩ := h
  by_contra hs
  have hs0 : s = 0 := by omega
  obtain ⟨t, ht, f, hf⟩ := hN (N + 1) (by omega)
  have ht0 : t = 0 := by omega
  subst ht0
  have h0 : (∑ i : Fin 0, (f i) ^ 1) = 0 := by simp
  have hzero : N + 1 = 0 := by rw [hf, h0]
  omega

theorem G_one : IsEventuallyWaringBound 1 1 ∧ ∀ s : ℕ, IsEventuallyWaringBound 1 s → 1 ≤ s :=
  ⟨isEventuallyWaringBound_one, fun s => one_le_of_isEventuallyWaringBound_one⟩

/-! ## `G(2) = 4` -/

/-- A square in `ZMod 8` is `0`, `1` or `4`. -/
theorem sq_zmod_eight (x : ZMod 8) : x ^ 2 = 0 ∨ x ^ 2 = 1 ∨ x ^ 2 = 4 := by
  fin_cases x <;> decide

/-- No integer congruent to `7` modulo `8` is a sum of three squares. -/
theorem not_three_squares_mod_eight_seven {n : ℕ} (hn : n % 8 = 7) :
    ¬ ∃ a b c : ℕ, a ^ 2 + b ^ 2 + c ^ 2 = n := by
  rintro ⟨a, b, c, h⟩
  have hz : (a : ZMod 8) ^ 2 + (b : ZMod 8) ^ 2 + (c : ZMod 8) ^ 2 = (n : ZMod 8) := by
    have h' := congrArg (fun x : ℕ => (x : ZMod 8)) h
    simpa using h'
  have hnz : (n : ZMod 8) = ((7 : ℕ) : ZMod 8) := by
    rw [ZMod.natCast_eq_natCast_iff']
    simpa using hn
  rcases sq_zmod_eight (a : ZMod 8) with ha | ha | ha <;>
  rcases sq_zmod_eight (b : ZMod 8) with hb | hb | hb <;>
  rcases sq_zmod_eight (c : ZMod 8) with hc | hc | hc <;>
  rw [ha, hb, hc, hnz] at hz <;>
  exact absurd hz (by decide)

/-- `n ≡ 7 (mod 8)` is never a sum of three squares. -/
theorem not_three_squares_of_mod_seven {n : ℕ} (hn : n % 8 = 7) :
    ¬ ∃ s ≤ 3, IsSumOfKthPowers 2 n s := by
  rintro ⟨s, hs, f, hf⟩
  obtain ⟨a, b, c, habc⟩ := eq_three_squares_of_sum_fin_le_three hs f
  exact not_three_squares_mod_eight_seven hn ⟨a, b, c, by rw [← habc]; exact hf.symm⟩

/-- There are arbitrarily large integers that are not sums of three squares. -/
theorem exists_large_not_three_squares (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ ¬ ∃ s ≤ 3, IsSumOfKthPowers 2 n s := by
  refine ⟨8 * (N + 1) + 7, by omega, ?_⟩
  refine not_three_squares_of_mod_seven ?_
  omega

theorem isEventuallyWaringBound_two : IsEventuallyWaringBound 2 4 :=
  isEventuallyWaringBound_of_isWaringBound isWaringBound_two

theorem four_le_of_isEventuallyWaringBound_two {s : ℕ} (h : IsEventuallyWaringBound 2 s) :
    4 ≤ s := by
  obtain ⟨N, hN⟩ := h
  obtain ⟨n, hnN, hn⟩ := exists_large_not_three_squares N
  by_contra hs
  have hs3 : s ≤ 3 := by omega
  obtain ⟨t, ht, hrepr⟩ := hN n hnN
  exact hn ⟨t, by omega, hrepr⟩

theorem G_two : IsEventuallyWaringBound 2 4 ∧ ∀ s : ℕ, IsEventuallyWaringBound 2 s → 4 ≤ s :=
  ⟨isEventuallyWaringBound_two, fun s => four_le_of_isEventuallyWaringBound_two⟩

/-- The `G` column for `k ≤ 2`, matching `g_lower_bounds` on the `g` side. -/
theorem G_values :
    (IsEventuallyWaringBound 1 1 ∧ ∀ s : ℕ, IsEventuallyWaringBound 1 s → 1 ≤ s) ∧
    (IsEventuallyWaringBound 2 4 ∧ ∀ s : ℕ, IsEventuallyWaringBound 2 s → 4 ≤ s) :=
  ⟨G_one, G_two⟩

end Waring
