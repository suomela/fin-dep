import Lake
open Lake DSL

package finiteDependence where
  -- Keep build output readable; these do not affect kernel checking.
  moreLeanArgs := #[
    "-Dweak.linter.unnecessarySimpa=false",
    "-Dweak.linter.unusedSimpArgs=false",
    "-Dweak.linter.unnecessarySeqFocus=false"
  ]
  -- Some modules benefit from a larger kernel stack in editor/server mode.
  moreServerArgs := #["-K", "65536"]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "c3cf7cbc7d8787edab1c190e3b1cf48941d4854c"

@[default_target]
lean_lib FiniteDependence
