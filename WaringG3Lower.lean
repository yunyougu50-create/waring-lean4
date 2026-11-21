import Mathlib

/-!
# `g(3) ≥ 9`: 23 is not a sum of at most eight nonnegative cubes

This file supplies the easy half of Wieferich–Kempner (`g(3) = 9`): the lower bound.

The obstruction is elementary. The only cubes that can occur in a representation of
`23` are `0³ = 0`, `1³ = 1` and `2³ = 8` (since `3³ = 27 > 23`).  If `a` counts the
summands equal to `2³` and `b` those equal to `1³`, a representation by at most eight
cubes would need

  `8 * a + b = 23`  and  `a + b ≤ 8`,

which has no solution: `8a ≤ 23` forces `a ≤ 2`, and `a = 0, 1, 2` give `b = 23, 15, 7`,
all violating `a + b ≤ 8`.  (And indeed `23 = 2·2³ + 7·1³` needs nine cubes.)

The upper bound `g(3) ≤ 9` is **not** proved here: the Wieferich–Kempner argument
needs results Mathlib does not yet have (see the repository README).
-/

namespace Waring

/-- `n` is a sum of at most `k` nonnegative cubes: a finitely supported `f : ℕ → ℕ`
with `f i = 0` for `i ≥ k`.  This is equivalent to `∃ x : Fin k → ℕ, ∑ i, (x i)^3 = n`. -/
def IsSumOfCubesAtMost (k n : ℕ) : Prop :=
  ∃ f : ℕ → ℕ, (∀ i, k ≤ i → f i = 0) ∧ ∑ i ∈ Finset.range k, (f i) ^ 3 = n

/-- The cube of a summand in a representation of `23` by at most `8` cubes is `0`, `1`
or `8`, i.e. the summand itself is at most `2`. -/
lemma cube_le_two_of_atMost {k : ℕ} {f : ℕ → ℕ}
    (hf : ∑ i ∈ Finset.range k, (f i) ^ 3 = 23) {i : ℕ} (hi : i < k) : f i ≤ 2 := by
  have hmem : i ∈ Finset.range k := Finset.mem_range.mpr hi
  have h1 : (f i) ^ 3 ≤ 23 := by
    have hle : (f i) ^ 3 ≤ ∑ j ∈ Finset.range k, (f j) ^ 3 :=
      Finset.single_le_sum (f := fun j => (f j) ^ 3) (fun j _ => Nat.zero_le _) hmem
    omega
  by_contra h2
  push Not at h2
  have h3 : 3 ≤ f i := by omega
  have h4 : (3 : ℕ) ^ 3 ≤ (f i) ^ 3 := Nat.pow_le_pow_left h3 3
  norm_num at h4
  omega

/-- **`23` is not a sum of at most eight cubes.** -/
theorem not_atMost_eight_23 : ¬ IsSumOfCubesAtMost 8 23 := by
  rintro ⟨f, _hzero, hf⟩
  -- every summand is `0`, `1` or `2`
  have hle : ∀ i < 8, f i ≤ 2 := fun i hi => cube_le_two_of_atMost hf hi
  -- count the `2`s and the `1`s among the first eight positions
  set A : Finset ℕ := (Finset.range 8).filter (fun i => f i = 2) with hA_def
  set B : Finset ℕ := (Finset.range 8).filter (fun i => f i = 1) with hB_def
  -- pointwise decomposition
  have hpt : ∀ i ∈ Finset.range 8,
      (f i) ^ 3 = 8 * (if f i = 2 then 1 else 0) + (if f i = 1 then 1 else 0) := by
    intro i hi
    have hi8 : i < 8 := Finset.mem_range.mp hi
    have := hle i hi8
    interval_cases f i <;> simp
  -- total mass is `8 * |A| + |B|`
  have hsum : ∑ i ∈ Finset.range 8, (f i) ^ 3 = 8 * A.card + B.card := by
    calc ∑ i ∈ Finset.range 8, (f i) ^ 3
        = ∑ i ∈ Finset.range 8,
            (8 * (if f i = 2 then 1 else 0) + (if f i = 1 then 1 else 0)) :=
          Finset.sum_congr rfl hpt
      _ = 8 * (∑ i ∈ Finset.range 8, (if f i = 2 then 1 else 0))
            + ∑ i ∈ Finset.range 8, (if f i = 1 then 1 else 0) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ = 8 * A.card + B.card := by
          rw [hA_def, hB_def, Finset.card_filter, Finset.card_filter]
  -- the two filters are disjoint, so `|A| + |B| ≤ 8`
  have hdisj : A.card + B.card ≤ 8 := by
    have hunion : A.card + B.card = (A ∪ B).card := by
      rw [Finset.card_union_of_disjoint]
      exact Finset.disjoint_filter.mpr (fun _ _ h2 h1 => by omega)
    rw [hunion]
    have hsub : A ∪ B ⊆ Finset.range 8 := by
      intro x hx
      simp only [Finset.mem_union, hA_def, hB_def, Finset.mem_filter] at hx
      rcases hx with ⟨hx1, -⟩ | ⟨hx1, -⟩
      · exact hx1
      · exact hx1
    calc (A ∪ B).card ≤ (Finset.range 8).card := Finset.card_le_card hsub
      _ = 8 := Finset.card_range 8
  -- `8a + b = 23` and `a + b ≤ 8` are contradictory
  have h23 : 8 * A.card + B.card = 23 := by
    rw [← hsum, hf]
  omega

/-- **`g(3) ≥ 9`** (contrapositive form): if `23` is a sum of at most `k` cubes then
`k ≥ 9`. -/
theorem g3_lower (k : ℕ) (h : IsSumOfCubesAtMost k 23) : 9 ≤ k := by
  by_contra hk
  push Not at hk
  have hk8 : k ≤ 8 := by omega
  obtain ⟨f, hzero, hf⟩ := h
  -- `k ≤ 8`: extend `f` by zeros to eight positions
  refine not_atMost_eight_23 ⟨f, ?_, ?_⟩
  · intro i hi
    exact hzero i (by omega)
  · -- the sum over `range 8` equals the sum over `range k` because the tail is zero
    have htail : ∑ i ∈ Finset.range k, (f i) ^ 3 = ∑ i ∈ Finset.range 8, (f i) ^ 3 := by
      apply Finset.sum_subset
      · intro x hx
        exact Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) hk8)
      · intro x _hx8 hxk
        have hkx : k ≤ x := by
          by_contra h
          exact hxk (Finset.mem_range.mpr (by omega))
        simp [hzero x hkx]
    rw [← htail, hf]

end Waring
