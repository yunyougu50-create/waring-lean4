import Mathlib

/-!
# The general lower bound `g(k) ≥ 2^k + ⌊(3/2)^k⌋ - 2`

For every `k ≥ 1` there is a natural number — namely `n = 2^k * ⌊(3/2)^k⌋ - 1` — that
cannot be written as a sum of fewer than `2^k + ⌊(3/2)^k⌋ - 2` nonnegative `k`-th powers.

Here `⌊(3/2)^k⌋` is represented as the natural-number division `3^k / 2^k`.

## Argument

Put `m = 3^k / 2^k` and `n = 2^k * m - 1`.  Then

* `2^k * m ≤ 3^k`, hence `n < 3^k`;
* so every summand `x` in a representation of `n` satisfies `x^k < 3^k`, i.e. `x ≤ 2`;
* writing `a` for the number of `2^k` summands and `b` for the number of `1^k` summands,
  `a * 2^k + b = n = 2^k * m - 1`;
* `a * 2^k < 2^k * m` gives `a ≤ m - 1`; then
  `a + b = 2^k * m - 1 - a * (2^k - 1) ≥ 2^k + m - 2` because `a ≤ m - 1`.

This is the classical lower bound (Dickson 1936; see also Waldschmidt's notes), stated
here in Lean.  The matching upper bound `g(k) ≤ 2^k + ⌊(3/2)^k⌋ - 2` is **not** proved:
it requires the circle method.
-/

namespace Waring

/-- `n` is a sum of at most `k` nonnegative `d`-th powers. -/
def IsSumOfPowersAtMost (d k n : ℕ) : Prop :=
  ∃ f : ℕ → ℕ, (∀ i, k ≤ i → f i = 0) ∧ ∑ i ∈ Finset.range k, (f i) ^ d = n

/-- The candidate extremal number `n = 2^k * ⌊(3/2)^k⌋ - 1`. -/
def waringLowerNum (k : ℕ) : ℕ := 2 ^ k * (3 ^ k / 2 ^ k) - 1

/-- **Lemma 1.** `x^k < 3^k` and `k ≠ 0` imply `x ≤ 2`. -/
theorem pow_lt_three_pow_imp_le_two {k x : ℕ} (hk : k ≠ 0) (h : x ^ k < 3 ^ k) : x ≤ 2 := by
  have hx3 : x < 3 := (Nat.pow_lt_pow_iff_left hk).mp h
  omega

/-- **Lemma 2.** `2^k * (3^k / 2^k) ≤ 3^k`. -/
theorem pow_two_mul_div_le (k : ℕ) : 2 ^ k * (3 ^ k / 2 ^ k) ≤ 3 ^ k := by
  have := Nat.div_mul_le_self (3 ^ k) (2 ^ k)
  rw [Nat.mul_comm] at this
  exact this

/-- **Lemma 3.** The candidate is `< 3^k`. -/
theorem waringLowerNum_lt_three_pow (k : ℕ) : waringLowerNum k < 3 ^ k := by
  unfold waringLowerNum
  have h := pow_two_mul_div_le k
  have hpos : 0 < 3 ^ k := by positivity
  omega

/-- **Lemma 4.** `3^k / 2^k ≤ 2^k + 1` for `k ≥ 1`. -/
theorem div_three_pow_two_pow_le (k : ℕ) (hk : 1 ≤ k) : 3 ^ k / 2 ^ k ≤ 2 ^ k + 1 := by
  by_contra h
  push Not at h
  have h1 : 2 ^ k * (2 ^ k + 2) ≤ 2 ^ k * (3 ^ k / 2 ^ k) := by
    apply Nat.mul_le_mul_left
    omega
  have h2 := pow_two_mul_div_le k
  have hfour : (4 : ℕ) ^ k = 2 ^ k * 2 ^ k := by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, mul_pow]
  have h3 : 2 ^ k * (2 ^ k + 2) = 4 ^ k + 2 * 2 ^ k := by
    rw [hfour]; ring
  have h4 : 3 ^ k < 4 ^ k := Nat.pow_lt_pow_left (by norm_num) (by omega)
  have h5 : 3 ^ k < 2 ^ k * (2 ^ k + 2) := by
    rw [h3]; omega
  omega

/-- **The lower bound.** For `k ≥ 1`, `waringLowerNum k` is not a sum of fewer than
`2^k + ⌊(3/2)^k⌋ - 2` nonnegative `k`-th powers. -/
theorem gk_lower_bound (k : ℕ) (hk : 1 ≤ k)
    {s : ℕ} (h : IsSumOfPowersAtMost k s (waringLowerNum k)) :
    2 ^ k + 3 ^ k / 2 ^ k - 2 ≤ s := by
  obtain ⟨f, hzero, hf⟩ := h
  have hk0 : k ≠ 0 := by omega
  -- every summand is `0`, `1` or `2`
  have hle : ∀ i, f i ≤ 2 := by
    intro i
    by_cases hi : i < s
    · have hmem : i ∈ Finset.range s := Finset.mem_range.mpr hi
      have h1 : (f i) ^ k ≤ ∑ j ∈ Finset.range s, (f j) ^ k :=
        Finset.single_le_sum (f := fun j => (f j) ^ k) (fun j _ => Nat.zero_le _) hmem
      rw [hf] at h1
      exact pow_lt_three_pow_imp_le_two hk0 (lt_of_le_of_lt h1 (waringLowerNum_lt_three_pow k))
    · exact le_trans (le_of_eq (hzero i (by omega))) (by omega)
  -- count `2`-summands and `1`-summands
  set A : Finset ℕ := (Finset.range s).filter (fun i => f i = 2) with hA_def
  set B : Finset ℕ := (Finset.range s).filter (fun i => f i = 1) with hB_def
  -- pointwise decomposition
  have hpt : ∀ i ∈ Finset.range s,
      (f i) ^ k = (if f i = 2 then 2 ^ k else 0) + (if f i = 1 then 1 else 0) := by
    intro i hi
    have hfi := hle i
    interval_cases f i <;> simp [hk0]
  have hsum : ∑ i ∈ Finset.range s, (f i) ^ k = A.card * 2 ^ k + B.card := by
    calc ∑ i ∈ Finset.range s, (f i) ^ k
        = ∑ i ∈ Finset.range s,
            ((if f i = 2 then 2 ^ k else 0) + (if f i = 1 then 1 else 0)) :=
          Finset.sum_congr rfl hpt
      _ = (∑ i ∈ Finset.range s, (if f i = 2 then 2 ^ k else 0))
            + ∑ i ∈ Finset.range s, (if f i = 1 then 1 else 0) := Finset.sum_add_distrib
      _ = A.card * 2 ^ k + B.card := by
          rw [hA_def, hB_def]
          congr 1
          · rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_comm]
          · rw [← Finset.sum_filter]
            simp
  -- `A` and `B` are disjoint subsets of `range s`
  have hdisj : A.card + B.card ≤ s := by
    have hunion : A.card + B.card = (A ∪ B).card := by
      rw [Finset.card_union_of_disjoint]
      exact Finset.disjoint_filter.mpr (fun _ _ h2 h1 => by omega)
    rw [hunion]
    have hsub : A ∪ B ⊆ Finset.range s := by
      intro x hx
      simp only [Finset.mem_union, hA_def, hB_def, Finset.mem_filter] at hx
      rcases hx with ⟨hx1, -⟩ | ⟨hx1, -⟩
      · exact hx1
      · exact hx1
    calc (A ∪ B).card ≤ (Finset.range s).card := Finset.card_le_card hsub
      _ = s := Finset.card_range s
  -- `A.card ≤ m - 1`, since `n = 2^k·m - 1` and `A.card·2^k ≤ n`
  have hone : 1 ≤ 2 ^ k * (3 ^ k / 2 ^ k) := by
    have hk2 : 2 ≤ 2 ^ k := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    have hm1 : 1 ≤ 3 ^ k / 2 ^ k := by
      have h2 : 2 ^ k ≤ 3 ^ k := Nat.pow_le_pow_left (by norm_num) k
      have hpos : 0 < 3 ^ k / 2 ^ k := Nat.div_pos h2 (by positivity)
      omega
    calc 1 ≤ 2 * 1 := by norm_num
      _ ≤ 2 ^ k * (3 ^ k / 2 ^ k) := Nat.mul_le_mul hk2 hm1
  have hmul : A.card * 2 ^ k + B.card + 1 = 2 ^ k * (3 ^ k / 2 ^ k) := by
    have h1 : A.card * 2 ^ k + B.card = waringLowerNum k := by rw [← hsum, hf]
    unfold waringLowerNum at h1
    omega
  -- auxiliary bounds
  have hk1' : 1 ≤ 2 ^ k := by
    have h : 0 < 2 ^ k := by positivity
    omega
  -- `A.card + 1 ≤ m`, where `m = 3^k / 2^k`
  have hA'' : A.card + 1 ≤ 3 ^ k / 2 ^ k := by
    have hcomm : A.card * 2 ^ k = 2 ^ k * A.card := Nat.mul_comm _ _
    rw [hcomm] at hmul
    by_contra hcon
    push Not at hcon
    have hmono : 2 ^ k * (3 ^ k / 2 ^ k) ≤ 2 ^ k * A.card :=
      Nat.mul_le_mul_left _ (by omega)
    have hmulZ : (2 : ℤ) ^ k * A.card + B.card + 1 = (2 : ℤ) ^ k * (3 ^ k / 2 ^ k) := by
      exact_mod_cast hmul
    have hmonoZ : (2 : ℤ) ^ k * (3 ^ k / 2 ^ k) ≤ (2 : ℤ) ^ k * A.card := by
      exact_mod_cast hmono
    nlinarith [hmulZ, hmonoZ]
  -- the combined count is at least `2^k + m - 2`
  have hAB : 2 ^ k + 3 ^ k / 2 ^ k - 2 ≤ A.card + B.card := by
    have hcomm : A.card * 2 ^ k = 2 ^ k * A.card := Nat.mul_comm _ _
    rw [hcomm] at hmul
    have hmulZ : (2 : ℤ) ^ k * A.card + B.card + 1 = (2 : ℤ) ^ k * (3 ^ k / 2 ^ k) := by
      exact_mod_cast hmul
    have hA''Z : (A.card : ℤ) + 1 ≤ (3 ^ k / 2 ^ k : ℤ) := by exact_mod_cast hA''
    have hgoalZ : (2 : ℤ) ^ k + (3 ^ k / 2 ^ k : ℤ) ≤ (A.card : ℤ) + B.card + 2 := by
      nlinarith [hmulZ, hA''Z]
    have hfin : 2 ≤ 2 ^ k + 3 ^ k / 2 ^ k := by omega
    have hcast : ((2 ^ k + 3 ^ k / 2 ^ k - 2 : ℕ) : ℤ)
        = (2 : ℤ) ^ k + (3 ^ k / 2 ^ k : ℤ) - 2 := by
      rw [Nat.cast_sub (by omega : 2 ≤ 2 ^ k + 3 ^ k / 2 ^ k)]
      push_cast
      ring
    have hZ : ((2 ^ k + 3 ^ k / 2 ^ k - 2 : ℕ) : ℤ) ≤ ((A.card + B.card : ℕ) : ℤ) := by
      rw [hcast]
      push_cast
      omega
    exact Nat.cast_le.mp hZ
  omega

end Waring
