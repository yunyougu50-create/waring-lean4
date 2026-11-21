/-
Copyright (c) 2026 The Waring formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Waring formalization authors
-/
import WaringFiniteDifference

/-!
# Waring's problem with signs allowed

Hilbert's identity `Δ^k x^k = k!` (`Waring.diffN_pow_self`) gives, for every
`k ≥ 1`, the linear identity

```text
Δ^(k-1) (x ↦ x^k) = k! * x + (constant),
```

and `Δ^(k-1) (x ↦ x^k)` is the alternating binomial sum

```text
∑ i, (-1)^(k-1-i) * C(k-1,i) * (x+i)^k.
```

Separating even and odd `i` and evaluating at `x = q` and at `x = 0` gives

```text
k! * q = (E(q) + O(0)) - (O(q) + E(0)),
```

where `E(x)` and `O(x)` are sums of `k`-th powers with positive binomial
coefficients.  Every integer is `k! * q + r` with `0 ≤ r < k!`, and `r` is a sum
of `r` copies of `1^k`.  Hence **every integer is a signed sum of at most
`2^k + k! - 1` many `k`-th powers**, for every `k ≥ 1`.

This is Waring's problem in the relaxed sense where both signs are allowed.  It
shows that the whole difficulty of Waring's theorem lies in the *positivity*:
allowing differences makes the problem elementary.  The unsigned statement is
`Waring.WaringTheorem` in `WaringStatement.lean` and remains open here.
-/

open Finset

namespace Waring

/-- The value of a list of bases as a sum of `k`-th powers in `ℤ`. -/
def kthPowerSum (k : ℕ) (l : List ℕ) : ℤ := (l.map (fun x : ℕ => ((x : ℤ)) ^ k)).sum

theorem kthPowerSum_nil (k : ℕ) : kthPowerSum k [] = 0 := by
  simp [kthPowerSum]

theorem kthPowerSum_append (k : ℕ) (l₁ l₂ : List ℕ) :
    kthPowerSum k (l₁ ++ l₂) = kthPowerSum k l₁ + kthPowerSum k l₂ := by
  simp [kthPowerSum, List.map_append, List.sum_append]

theorem kthPowerSum_replicate (k c x : ℕ) :
    kthPowerSum k (List.replicate c x) = (c : ℤ) * (x : ℤ) ^ k := by
  simp [kthPowerSum, List.map_replicate, List.sum_replicate]

/-- `n` is a signed sum of `s` many `k`-th powers: a difference of two sums of
nonnegative `k`-th powers with at most `s` terms in total. -/
def IsSignedSumOfKthPowers (k : ℕ) (n : ℤ) (s : ℕ) : Prop :=
  ∃ A B : List ℕ, A.length + B.length ≤ s ∧ n = kthPowerSum k A - kthPowerSum k B

namespace IsSignedSumOfKthPowers

variable {k : ℕ}

theorem zero : IsSignedSumOfKthPowers k 0 0 :=
  ⟨[], [], by simp⟩

theorem mono {n s : ℕ} {x : ℤ} (h : IsSignedSumOfKthPowers k x n) (hst : n ≤ s) :
    IsSignedSumOfKthPowers k x s := by
  obtain ⟨A, B, hAB, hval⟩ := h
  exact ⟨A, B, le_trans hAB hst, hval⟩

theorem add {x y : ℤ} {s t : ℕ} (h₁ : IsSignedSumOfKthPowers k x s)
    (h₂ : IsSignedSumOfKthPowers k y t) : IsSignedSumOfKthPowers k (x + y) (s + t) := by
  obtain ⟨A₁, B₁, hAB₁, hv₁⟩ := h₁
  obtain ⟨A₂, B₂, hAB₂, hv₂⟩ := h₂
  refine ⟨A₁ ++ A₂, B₁ ++ B₂, ?_, ?_⟩
  · rw [List.length_append, List.length_append]
    omega
  · rw [kthPowerSum_append, kthPowerSum_append, hv₁, hv₂]
    ring

theorem neg {x : ℤ} {s : ℕ} (h : IsSignedSumOfKthPowers k x s) :
    IsSignedSumOfKthPowers k (-x) s := by
  obtain ⟨A, B, hAB, hv⟩ := h
  refine ⟨B, A, by omega, ?_⟩
  rw [hv]
  ring

theorem of_replicate (c x : ℕ) :
    IsSignedSumOfKthPowers k ((c : ℤ) * (x : ℤ) ^ k) c := by
  refine ⟨List.replicate c x, [], by simp, ?_⟩
  rw [kthPowerSum_replicate, kthPowerSum_nil, sub_zero]

/-- A finite sum of `k`-th powers with nonnegative multiplicities is realized by
a list of bases repeated with multiplicity. -/
theorem exists_list_of_finset_sum {ι : Type} [DecidableEq ι] (s : Finset ι) (d g : ι → ℕ) :
    ∃ A : List ℕ, A.length = ∑ i ∈ s, d i ∧
      kthPowerSum k A = ∑ i ∈ s, (d i : ℤ) * ((g i : ℤ) ^ k) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨[], by simp, by simp [kthPowerSum]⟩
  | insert a s ha ih =>
    obtain ⟨A, hlen, hval⟩ := ih
    refine ⟨List.replicate (d a) (g a) ++ A, ?_, ?_⟩
    · rw [List.length_append, List.length_replicate, hlen, Finset.sum_insert ha]
    · rw [kthPowerSum_append, kthPowerSum_replicate, hval,
        Finset.sum_insert ha]

end IsSignedSumOfKthPowers

/-! ## The even and odd parts of `Δ^(k-1) (x ↦ x^k)` -/

/-- The positive (even) part of the alternating binomial sum for `Δ^(k-1) x^k`. -/
def hilbertEven (k q : ℕ) : ℤ :=
  ∑ i ∈ (Finset.range k).filter (fun i => Even (k - 1 - i)),
    (((k - 1).choose i : ℕ) : ℤ) * ((q + i : ℕ) : ℤ) ^ k

/-- The negative (odd) part of the alternating binomial sum for `Δ^(k-1) x^k`. -/
def hilbertOdd (k q : ℕ) : ℤ :=
  ∑ i ∈ (Finset.range k).filter (fun i => Odd (k - 1 - i)),
    (((k - 1).choose i : ℕ) : ℤ) * ((q + i : ℕ) : ℤ) ^ k

/-- `Δ^(k-1) x^k = E - O` at `x = q`, with `E` and `O` the even and odd parts. -/
theorem diffN_eq_hilbert (k : ℕ) (hk : 0 < k) (q : ℕ) :
    diffN (k - 1) (fun z : ℤ => z ^ k) (q : ℤ) = hilbertEven k q - hilbertOdd k q := by
  classical
  have hk1 : k - 1 + 1 = k := Nat.sub_add_cancel hk
  have hcast : ∀ i : ℕ, ((q : ℤ) + (i : ℤ)) = ((q + i : ℕ) : ℤ) := by
    intro i
    push_cast
    ring
  have hP : diffN (k - 1) (fun z : ℤ => z ^ k) (q : ℤ)
      = ∑ i ∈ range k,
          (-1 : ℤ) ^ (k - 1 - i) * (((k - 1).choose i : ℕ) : ℤ) * ((q + i : ℕ) : ℤ) ^ k := by
    rw [diffN_apply, hk1]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [hcast i]
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.range k) (fun i => Even (k - 1 - i))
    (fun i => (-1 : ℤ) ^ (k - 1 - i) * (((k - 1).choose i : ℕ) : ℤ) * ((q + i : ℕ) : ℤ) ^ k)
  have heven : (∑ i ∈ (range k).filter (fun i => Even (k - 1 - i)),
      (-1 : ℤ) ^ (k - 1 - i) * (((k - 1).choose i : ℕ) : ℤ) * ((q + i : ℕ) : ℤ) ^ k)
      = hilbertEven k q := by
    rw [hilbertEven]
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [Even.neg_one_pow (Finset.mem_filter.mp hi).2, one_mul]
  have hodd : (∑ i ∈ (range k).filter (fun i => Odd (k - 1 - i)),
      (-1 : ℤ) ^ (k - 1 - i) * (((k - 1).choose i : ℕ) : ℤ) * ((q + i : ℕ) : ℤ) ^ k)
      = - hilbertOdd k q := by
    rw [hilbertOdd, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [Odd.neg_one_pow (Finset.mem_filter.mp hi).2]
    ring
  have hnot : (range k).filter (fun i => Odd (k - 1 - i)) =
      (range k).filter (fun i => ¬ Even (k - 1 - i)) := by
    refine Finset.filter_congr ?_
    intro i _
    exact (Nat.not_even_iff_odd).symm
  rw [hP, ← hsplit, heven, ← hnot, hodd]
  ring

/-- `Δ^(k-1) (x ↦ x^k)` is `k! * x` up to an additive constant. -/
theorem diffN_linear (k : ℕ) (hk : 0 < k) (q : ℕ) :
    diffN (k - 1) (fun z : ℤ => z ^ k) (q : ℤ)
      = diffN (k - 1) (fun z : ℤ => z ^ k) 0 + (q : ℤ) * (k.factorial : ℤ) := by
  have hstep : ∀ x : ℤ, diffN (k - 1) (fun z : ℤ => z ^ k) (x + 1)
      = diffN (k - 1) (fun z : ℤ => z ^ k) x + (k.factorial : ℤ) := by
    intro x
    have h1 := congrFun (diffN_pow_self k) x
    have h2 : diffN k (fun z : ℤ => z ^ k) x
        = diffN (k - 1) (fun z : ℤ => z ^ k) (x + 1) -
          diffN (k - 1) (fun z : ℤ => z ^ k) x := by
      have hk1 : k - 1 + 1 = k := Nat.sub_add_cancel hk
      rw [← hk1, diffN, Function.iterate_succ_apply']
      rfl
    linarith [h1, h2]
  induction q with
  | zero => simp
  | succ m ih =>
    have h := hstep (m : ℤ)
    push_cast at h ⊢
    linarith

/-! ## The block `k! * q` -/

/-- `k! * q` is a signed sum of at most `2^k` `k`-th powers. -/
theorem exists_block (k : ℕ) (hk : 0 < k) (q : ℕ) :
    ∃ A B : List ℕ, A.length + B.length ≤ 2 ^ k ∧
      kthPowerSum k A - kthPowerSum k B = (q : ℤ) * (k.factorial : ℤ) := by
  classical
  have hk1 : k - 1 + 1 = k := Nat.sub_add_cancel hk
  obtain ⟨Ae, hAelen, hAeval⟩ :=
    IsSignedSumOfKthPowers.exists_list_of_finset_sum (k := k)
      ((Finset.range k).filter (fun i => Even (k - 1 - i)))
      (fun i => (k - 1).choose i) (fun i => q + i)
  obtain ⟨Ao, hAolen, hAoval⟩ :=
    IsSignedSumOfKthPowers.exists_list_of_finset_sum (k := k)
      ((Finset.range k).filter (fun i => Odd (k - 1 - i)))
      (fun i => (k - 1).choose i) (fun i => q + i)
  obtain ⟨Be, hBelen, hBeval⟩ :=
    IsSignedSumOfKthPowers.exists_list_of_finset_sum (k := k)
      ((Finset.range k).filter (fun i => Even (k - 1 - i)))
      (fun i => (k - 1).choose i) (fun i => 0 + i)
  obtain ⟨Bo, hBolen, hBoval⟩ :=
    IsSignedSumOfKthPowers.exists_list_of_finset_sum (k := k)
      ((Finset.range k).filter (fun i => Odd (k - 1 - i)))
      (fun i => (k - 1).choose i) (fun i => 0 + i)
  refine ⟨Ae ++ Bo, Ao ++ Be, ?_, ?_⟩
  · have hchoose : (∑ i ∈ Finset.range k, (k - 1).choose i) = 2 ^ (k - 1) := by
      rw [← hk1]
      exact Nat.sum_range_choose (k - 1)
    have hnot : (range k).filter (fun i => Odd (k - 1 - i)) =
        (range k).filter (fun i => ¬ Even (k - 1 - i)) := by
      refine Finset.filter_congr ?_
      intro i _
      exact (Nat.not_even_iff_odd).symm
    have hsplit' := Finset.sum_filter_add_sum_filter_not (Finset.range k)
      (fun i => Even (k - 1 - i)) (fun i => (k - 1).choose i)
    rw [← hnot] at hsplit'
    rw [hchoose] at hsplit'
    have hpow : 2 ^ k = 2 ^ (k - 1) + 2 ^ (k - 1) := by
      conv_lhs => rw [← hk1, pow_succ]
      ring
    rw [List.length_append, List.length_append, hAelen, hBolen, hAolen, hBelen]
    omega
  · rw [kthPowerSum_append, kthPowerSum_append, hAeval, hBoval, hAoval, hBeval]
    have hgoal : (hilbertEven k q + hilbertOdd k 0) - (hilbertOdd k q + hilbertEven k 0)
        = (q : ℤ) * (k.factorial : ℤ) := by
      have h1 := diffN_eq_hilbert k hk q
      have h2 := diffN_eq_hilbert k hk 0
      have h3 := diffN_linear k hk q
      have h3' : diffN (k - 1) (fun z : ℤ => z ^ k) ((q : ℕ) : ℤ)
          = diffN (k - 1) (fun z : ℤ => z ^ k) (((0 : ℕ)) : ℤ)
            + (q : ℤ) * (k.factorial : ℤ) := by
        simpa using h3
      linarith [h1, h2, h3']
    simpa only [hilbertEven, hilbertOdd] using hgoal

/-! ## The main theorem -/

/-- **Waring's problem with signs.**  For every `k ≥ 1` every integer is a signed
sum of at most `2^k + k! - 1` many `k`-th powers. -/
theorem signed_waring (k : ℕ) (hk : 0 < k) :
    ∃ s : ℕ, ∀ n : ℤ, IsSignedSumOfKthPowers k n s := by
  classical
  have hblk : ∀ q : ℕ, ∃ A B : List ℕ, A.length + B.length ≤ 2 ^ k ∧
      kthPowerSum k A - kthPowerSum k B = (q : ℤ) * (k.factorial : ℤ) :=
    fun q => exists_block k hk q
  have hfact : 0 < k.factorial := Nat.factorial_pos k
  have hnonneg : ∀ m : ℕ, IsSignedSumOfKthPowers k (m : ℤ) (2 ^ k + (k.factorial - 1)) := by
    intro m
    have hm : k.factorial * (m / k.factorial) + m % k.factorial = m :=
      Nat.div_add_mod m k.factorial
    have hrlt : m % k.factorial < k.factorial := Nat.mod_lt _ hfact
    have hrle : m % k.factorial ≤ k.factorial - 1 := by omega
    obtain ⟨Ablk, Bblk, hblklen, hblkval⟩ := hblk (m / k.factorial)
    have h1 : IsSignedSumOfKthPowers k
        (((m / k.factorial : ℕ) : ℤ) * (k.factorial : ℤ)) (2 ^ k) :=
      ⟨Ablk, Bblk, hblklen, hblkval.symm⟩
    have h2 : IsSignedSumOfKthPowers k (((m % k.factorial : ℕ) : ℤ)) (m % k.factorial) := by
      have h := IsSignedSumOfKthPowers.of_replicate (k := k) (m % k.factorial) 1
      simpa using h
    have h3 := IsSignedSumOfKthPowers.add h1 h2
    have hval : ((m / k.factorial : ℕ) : ℤ) * (k.factorial : ℤ) + ((m % k.factorial : ℕ) : ℤ)
        = (m : ℤ) := by
      have hcast : ((k.factorial * (m / k.factorial) + m % k.factorial : ℕ) : ℤ) = (m : ℤ) := by
        rw [hm]
      push_cast at hcast ⊢
      linarith
    have hlen : 2 ^ k + m % k.factorial ≤ 2 ^ k + (k.factorial - 1) := by omega
    rw [hval] at h3
    exact h3.mono hlen
  refine ⟨2 ^ k + (k.factorial - 1), ?_⟩
  intro n
  by_cases hn : 0 ≤ n
  · have hmn : ((n.toNat : ℕ) : ℤ) = n := Int.toNat_of_nonneg hn
    rw [← hmn]
    exact hnonneg n.toNat
  · have hneg : n < 0 := by omega
    have hpos : 0 ≤ -n := by omega
    have hmn : (((-n).toNat : ℕ) : ℤ) = -n := Int.toNat_of_nonneg hpos
    have h := hnonneg (-n).toNat
    rw [hmn] at h
    simpa using h.neg

end Waring
