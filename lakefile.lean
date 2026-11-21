import Lake
open Lake DSL

package «waring» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.36.0-rc2"

/-- The main entry points: the final theorem and the three verification scripts. -/
@[default_target]
lean_lib «Waring» where
  roots := #[
    `WaringTheorem2,
    `CheckFinal,
    `CheckTheorem1,
    `CheckWaringAll
  ]
