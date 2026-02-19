import FiniteDependence.MIS.K3Kernel
import FiniteDependence.MIS.K4Kernel

namespace FiniteDependence.MIS

/-!
# Algebraic kernel theorems

This module exposes the pure-algebra contradictions used by the model-level
`k=3` and `k=4` impossibility proofs.
-/

theorem no_k3_kernel (p : ℝ)
    (hp : 3 * p ^ 2 - 6 * p + 2 = 0)
    (hstar : (1 - 2 * p) * (3 * p - 1) = (1 - p) * (p ^ 2 - 5 * p + 2)) :
    False := by
  exact no_k3_algebra p hp hstar

theorem no_k4_kernel (p : ℝ) (hp_ne : p ≠ 0) (hg : g p = 0) (hh : p * h1 p = 0) : False := by
  exact no_k4_algebra p hp_ne hg hh

end FiniteDependence.MIS
