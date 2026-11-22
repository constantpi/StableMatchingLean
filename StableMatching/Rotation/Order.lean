import StableMatching.Rotation.Equiv

namespace StableMatching
namespace SMP
namespace Rotation

/-- `SupIrred` 元の順序を回転に移した半順序。 -/
noncomputable instance rotationPartialOrder {smp : SMP n} :
    PartialOrder (Rotation smp) :=
  PartialOrder.lift (equivSupIrred (smp := smp))
    (equivSupIrred (smp := smp)).injective

/-- 回転と安定マッチングの `SupIrred` 元の間の順序同型。 -/
noncomputable def orderIsoSupIrred {smp : SMP n} :
    Rotation smp ≃o {j : StableMatching smp // SupIrred j} where
  toEquiv := equivSupIrred (smp := smp)
  map_rel_iff' := Iff.rfl

end Rotation
end SMP
end StableMatching
