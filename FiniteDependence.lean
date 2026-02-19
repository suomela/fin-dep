import FiniteDependence.Coloring
import FiniteDependence.MIS
import FiniteDependence.Core.Binary
import FiniteDependence.API.Definitions
import FiniteDependence.API.MainTheorems
import FiniteDependence.WeakTwo.Threshold

/-!
# `FiniteDependence`

This is the unified entrypoint for the refactored development combining:

* Holroyd–Liggett finitely dependent colorings (and the induced `6`-dependent MIS), and
* the `k = 5` impossibility result for finitely dependent MIS on `ℤ`,
* the weak-2-coloring threshold (`k=3` exists, `k=2` impossible),
* the greedy proper 3-coloring threshold (`k=6` exists, `k=5` impossible).

For a concise “human-facing interface”, see:

* `FiniteDependence/API/Definitions.lean`
* `FiniteDependence/API/MainTheorems.lean`
  (this also re-exports the weak-2 threshold theorems from
  `FiniteDependence/WeakTwo/Threshold.lean`).
-/
