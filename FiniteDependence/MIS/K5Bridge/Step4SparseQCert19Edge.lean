import FiniteDependence.MIS.K5Bridge.StepLemmas

namespace FiniteDependence.MIS

namespace K5Bridge

namespace Model

noncomputable section

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace Step4Sparse

theorem filter19_edge_eq :
    (allowedWordsFinset (7 + 5 + 7)).filter
        (fun w => prefixOf w 7 = ("0010101" : String) ∧ suffixFrom w (7 + 5) = ("0010100" : String)) =
      ({("0010101001010010100" : String), "0010101010010010100"} : Finset String) := by
  with_unfolding_all decide

end Step4Sparse

end

end Model

end K5Bridge

end FiniteDependence.MIS
