# Mathlib patch draft

This folder contains a draft script for moving the Gaussian development into a
Mathlib checkout.  It is **not** run automatically; review the paths first.

## Proposed destination

```
Mathlib/NumberTheory/SumTwoSquares/
  GaussianUnits.lean
  GaussianTwo.lean
  GaussianSplit.lean
  GaussianInert.lean
  GaussianFactorization.lean
  GaussianDivisorCount.lean
  GaussianClassCount.lean
  GaussianPrimePowerDivisor.lean
  GaussianGCDNorm.lean
  GaussianClassMul.lean
  GaussianMain.lean
```

The imports change from

```lean
import GaussianUnits
import GaussianTwo
...
```

to

```lean
import Mathlib.NumberTheory.SumTwoSquares.GaussianUnits
import Mathlib.NumberTheory.SumTwoSquares.GaussianTwo
...
```

## Umbrella import

Add to `Mathlib.lean` (or to the `NumberTheory/SumTwoSquares` umbrella, if one
is added):

```lean
import Mathlib.NumberTheory.SumTwoSquares.GaussianMain
```

## Suggested commit message

```
feat(NumberTheory/SumTwoSquares): bound r2 m by four times the divisor count

Prove `r2 m ≤ 4 * m.divisors.card` for `m ≠ 0`, where `r2 m` is the number of
ordered nonnegative representations of `m` as a sum of two squares.  The proof
uses the Gaussian integers, the three prime-power class counts, and a global
`gcd` decomposition.  The unconditional form is `r2 m ≤ 4 * d(m) + 1`.
```

## Review checklist

- [ ] `lake build` passes after the move.
- [ ] No `sorry`/`admit` in the moved files.
- [ ] `#print axioms Waring.r2_le_four_mul_card_divisors` is the standard trio.
- [ ] Docstrings and copyright headers are present.
- [ ] The final theorem is imported by `Mathlib.lean`.
- [ ] `GaussianTests.lean` is kept out of Mathlib (it uses `native_decide`).
