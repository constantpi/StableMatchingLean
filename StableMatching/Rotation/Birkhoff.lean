import Mathlib.Order.Birkhoff
import StableMatching.Rotation.Order

namespace StableMatching
namespace SMP
namespace Rotation

/-- 安定マッチングと回転の下方閉集合の間の順序同型。 -/
noncomputable def stableMatchingOrderIsoLowerSet {smp : SMP n} :
    StableMatching smp ≃o LowerSet (Rotation smp) := by
  classical
  exact (OrderIso.lowerSetSupIrred (α := StableMatching smp)).trans
    (LowerSet.map (orderIsoSupIrred (smp := smp)).symm)

end Rotation
end SMP
end StableMatching
