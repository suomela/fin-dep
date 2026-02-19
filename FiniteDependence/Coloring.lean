import FiniteDependence.Coloring.Existence
import FiniteDependence.Coloring.LowerBounds
import FiniteDependence.Coloring.Distributions
import FiniteDependence.Coloring.GreedyThree
import FiniteDependence.Coloring.MIS

/-!
# `FiniteDependence.Coloring`

This is the main entrypoint for the project formalizing Holroyd–Liggett,
*Finitely dependent coloring* (arXiv:1403.2448v4).

It exports:

* `FiniteDependence.Coloring.exists_stationary_oneDependent_fourColoring`
* `FiniteDependence.Coloring.not_exists_stationary_zeroDependent_fourColoring`
* `FiniteDependence.Coloring.exists_stationary_twoDependent_threeColoring`
* `FiniteDependence.Coloring.exists_stationary_oneDependent_fourColoring_noncontig`
* `FiniteDependence.Coloring.exists_stationary_twoDependent_threeColoring_noncontig`
* `FiniteDependence.Coloring.exists_stationary_sixDependent_greedyThreeColoring`
* `FiniteDependence.Coloring.not_exists_stationary_fiveDependent_greedyThreeColoring`
* `FiniteDependence.Coloring.exists_stationary_sixDependent_MIS`
* `FiniteDependence.Coloring.DependenceEquivalence.isKDependent_iff_isKDependentNoncontig`

as well as the explicit finite-dimensional cylinder weights `FiniteDependence.Coloring.Word.P4`
and `FiniteDependence.Coloring.Word.P3`.
-/
