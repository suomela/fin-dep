import FiniteDependence.MIS.K5Bridge.StepLemmas

namespace FiniteDependence.MIS

namespace K5Bridge

namespace Model

noncomputable section

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace Step4Sparse

theorem filter19_anchor_eq :
    (allowedWordsFinset (2 + 5 + 12)).filter
        (fun w => prefixOf w 2 = ("00" : String) ∧ suffixFrom w (2 + 5) = ("001010010100" : String)) =
      ({("0010101001010010100" : String)} : Finset String) := by
  with_unfolding_all decide

end Step4Sparse

end

end Model

end K5Bridge

end FiniteDependence.MIS
