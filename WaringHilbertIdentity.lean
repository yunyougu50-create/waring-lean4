/-
Copyright (c) 2026 The Waring formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Waring formalization authors
-/
import WaringFiniteDifference

/-!
# Hilbert's identity (positive form)

The finite-difference identity `Δ^k x^k = k!` says

```text
k! = ∑ i, (-1)^(k-i) * C(k,i) * (x+i)^k.
```

Separating the even and odd terms gives Hilbert's positive identity

```text
∑_{k-i even} C(k,i) * (x+i)^k
  = ∑_{k-i odd} C(k,i) * (x+i)^k + k!.
```

Both sides are sums of `k`-th powers with positive binomial coefficients.  This
is the algebraic input to Hilbert's descent.
-/

open Finset

namespace Waring

/-- Hilbert's identity in positive form. -/
theorem hilbert_identity (k : ℕ) (x : ℤ) :
    (∑ i ∈ (range (k + 1)).filter (fun i => Even (k - i)),
        (k.choose i : ℤ) * (x + i) ^ k) =
      (∑ i ∈ (range (k + 1)).filter (fun i => Odd (k - i)),
        (k.choose i : ℤ) * (x + i) ^ k) + (k.factorial : ℤ) := by
  classical
  set S := range (k + 1) with hS
  have hx := congrFun (diffN_pow_self k) x
  rw [diffN_apply] at hx
  have hsplit :
      (∑ i ∈ S.filter (fun i => Even (k - i)),
          (-1 : ℤ) ^ (k - i) * ((k.choose i : ℤ) * (x + i) ^ k)) +
        (∑ i ∈ S.filter (fun i => ¬ Even (k - i)),
          (-1 : ℤ) ^ (k - i) * ((k.choose i : ℤ) * (x + i) ^ k)) =
      (k.factorial : ℤ) := by
    rw [Finset.sum_filter_add_sum_filter_not S (fun i => Even (k - i))]
    simpa [S, mul_assoc] using hx
  have hEven : ∀ i ∈ S.filter (fun i => Even (k - i)),
      (-1 : ℤ) ^ (k - i) * ((k.choose i : ℤ) * (x + i) ^ k) =
        (k.choose i : ℤ) * (x + i) ^ k := by
    intro i hi
    rw [Even.neg_one_pow (Finset.mem_filter.mp hi).2, one_mul]
  have hOdd : ∀ i ∈ S.filter (fun i => ¬ Even (k - i)),
      (-1 : ℤ) ^ (k - i) * ((k.choose i : ℤ) * (x + i) ^ k) =
        -((k.choose i : ℤ) * (x + i) ^ k) := by
    intro i hi
    have hodd : Odd (k - i) := Nat.not_even_iff_odd.mp (Finset.mem_filter.mp hi).2
    rw [Odd.neg_one_pow hodd]
    ring
  rw [Finset.sum_congr rfl hEven, Finset.sum_congr rfl hOdd,
    Finset.sum_neg_distrib] at hsplit
  have hfilter : S.filter (fun i => Odd (k - i)) =
      S.filter (fun i => ¬ Even (k - i)) := by
    apply Finset.filter_congr
    intro i hi
    exact (Nat.not_even_iff_odd).symm
  rw [← hfilter] at hsplit
  linarith

/-- The `k = 3` instance:
`(x+3)^3 + 3(x+1)^3 = x^3 + 3(x+2)^3 + 6`. -/
example (x : ℤ) :
    (x + 3) ^ 3 + 3 * (x + 1) ^ 3 = x ^ 3 + 3 * (x + 2) ^ 3 + 6 := by
  have h := hilbert_identity 3 x
  norm_num [Finset.sum_range_succ, Nat.choose] at h
  linarith

end Waring
