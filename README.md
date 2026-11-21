# Waring's theorem in Lean 4

A complete, machine-checked proof of **Waring's theorem** in Lean 4, following Linnik's
elementary density route (via Tim Jameson's notes on the Waring–Hilbert theorem).
29 modules, 10 460 lines of Lean, **no `sorry`**, and `#print axioms` reports only the
three standard axioms.

```lean
theorem waringTheorem : WaringTheorem
-- WaringTheorem := ∀ k : ℕ, 0 < k → ∃ g : ℕ, ∀ n : ℕ, ∃ s ≤ g, IsSumOfKthPowers k n s
-- IsSumOfKthPowers k n s := ∃ f : Fin s → ℕ, n = ∑ i, (f i) ^ k
-- #print axioms waringTheorem = [propext, Classical.choice, Quot.sound]
```

## Status: independent implementation, **no priority claimed**

**This is not the first formalization of Waring's theorem, and not the first in Lean 4.**
Prior work:

| Date | Work | System | Route |
|---|---|---|---|
| 2026-05-28 | [Atlas](https://arxiv.org/abs/2605.29955) — `MathlibExt/NumberTheory/HilbertWaring.lean` (3480 lines) | Lean 4 | Linnik density + Schnirelmann |
| 2026-11-06 | [HOL Light](https://github.com/jrh13/hol-light/blob/master/Sieve/waring.ml) — `Sieve/waring.ml` (1784 lines) | HOL Light | Hardy–Littlewood circle method |
| 2026-11-20 | this repository | Lean 4 | Linnik density + Schnirelmann |

Atlas uses the same route from the same notes (its `Schnirelmann.lean` cites
`warlin.pdf`), six months earlier. This repository depends on **no code** from Atlas or
HOL Light, so it is offered as an independent artifact and a possible cross-check —
not as a first.

## What is different from Atlas

Both follow Linnik's route. They differ in how the Weyl-differencing step handles the fact
that the summed terms `b_h` have summation length `N-h` while their coefficients live at
scale `N`:

- **Atlas** keeps a single scale `N` in the moment bound and uses *moment lifting*
  (`hwMomentLift r A B (hAB : A ≤ B)`) to embed `(N-h)`-scale moments into a larger
  `N`-scale moment.
- **Here** the induction hypothesis is strengthened to `MeanValueBoundS`, which admits an
  arbitrary summation length `M ≤ N` while keeping the coefficient scale at `N`; the
  bound itself is stated at scale `N`. This makes the hypothesis directly applicable to
  every `b_h` with the constant unchanged. See `paper/waring-formalization.pdf` §7.2 for
  why the bound must be stated at `N` rather than at `M`, and what breaks otherwise.

Constant tightness is a mixed bag (normalized to `|a₂| ≤ c`, `|a₁| ≤ cN`):

| Stage | Atlas | Here |
|---|---|---|
| Four-term count (Lemma 7) | `144 + 16384·ζ(2)³ ≈ 73 051` | **5250** (≈14× tighter) |
| Quadratic base case (`c=1`) | **≈ 2.01×10⁶** | `10⁶·4⁴ = 2.56×10⁸` (≈127× looser) |

## Bonus: `g(3) ≥ 9` (the easy half of Wieferich–Kempner)

`WaringG3Lower.lean` (113 lines, no `sorry`) proves the lower bound:

```lean
def IsSumOfCubesAtMost (k n : ℕ) : Prop :=
  ∃ f : ℕ → ℕ, (∀ i, k ≤ i → f i = 0) ∧ ∑ i ∈ Finset.range k, (f i) ^ 3 = n

theorem not_atMost_eight_23 : ¬ IsSumOfCubesAtMost 8 23
theorem g3_lower (k : ℕ) (h : IsSumOfCubesAtMost k 23) : 9 ≤ k
```

Since `23 = 2·2³ + 7·1³` needs nine cubes and no representation by eight or fewer exists
(the only cubes below `23` are `0, 1, 8`, so a representation would require `8a + b = 23`
with `a + b ≤ 8`, which has no solution), we get `g(3) ≥ 9`.

The **upper bound `g(3) ≤ 9` is not included**: the Wieferich–Kempner argument requires
results Mathlib does not have (in particular Legendre's three-square theorem, and the
`G(3) ≤ 8` input of Linnik/Watson for the large-`n` range). Check with
`CheckG3Lower.lean`; axioms are the usual three.

## Verification

```text
$ lean CheckFinal.lean
WaringTheorem : Prop
waringTheorem : WaringTheorem
'Waring.waringTheorem' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The verification protocol applied to every module was: recompile from source with
`lean -o Module.olean Module.lean`; scan for `sorry` / `admit` / `axiom` /
`native_decide`; audit `#print axioms`; and re-read each headline *statement* against its
mathematical content (compilation cannot detect a weakened hypothesis).

## Building

Requires Lean `v4.36.0-rc2` and Mathlib.

With Lake:

```bash
lake exe cache get
lake build
```

Or with an already-built Mathlib (this is how it was developed):

```powershell
$lean = '<toolchain>/bin/lean.exe'
$env:LEAN_PATH = '<repo>;<mathlib>/.lake/build/lib/lean'
# plus one entry per <mathlib>/.lake/packages/*/.lake/build/lib/lean
& $lean -o WaringStatement.olean WaringStatement.lean
# then build the remaining modules in dependency order; the DAG is in paper/fig/fig1_dag.png
```

## Module map

29 modules in 8 dependency layers (figure: `paper/fig/fig1_dag.png`).

| Layer | Modules |
|---|---|
| foundation | `WaringStatement`, `WaringCircle`, `WaringFiniteDifference` |
| arithmetic | `WaringCount`, `WaringLemma3`, `WaringLemma6`, `WaringSymm`, `WaringCoeffBound` |
| analysis | `WaringExpSum`, `WaringWeylDiff`, `WaringWeylInq`, `WaringHolder`, `WaringBPow` |
| mean value | `WaringTheorem1`, `WaringLemma7`, `WaringQuadratic`, `WaringLemma8Form`, `WaringQuadSum` |
| induction | `WaringIndStep`, `WaringIndStep2`, `WaringInduction` |
| density | `WaringBound`, `WaringDensity`, `WaringSchnirelmann`, `WaringLinnik` |
| final | `WaringTheorem2` |

The single-line assembly is

```lean
theorem waringTheorem : WaringTheorem :=
  waringTheorem_of_positive_density positiveDensity
```

## Paper

- English: `paper/waring-formalization.pdf`, `paper/waring-formalization.html`
- Chinese: `paper/waring-formalization-zh.pdf`, `paper/waring-formalization-zh.html`

Both describe the architecture, the proof of Theorems 1 and 2, the formalization design
(including the `M`/`N` separation discussed above), and the verification protocol.

## Provenance

Produced in November 2026 by a DeepSeek Harness agent team (a lead agent plus six
delegated sub-agents) working under a human owner, in several sessions. The human owner
set the direction and accepted the deliverables; the Lean code and the paper were written
by the agents and re-verified from source at each step. Every claim of priority in the
paper is hedged accordingly — and the paper also documents three successive wrong priority
claims made during the project.

## License

Apache 2.0, the same license as Mathlib.
