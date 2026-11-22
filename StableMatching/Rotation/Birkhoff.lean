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

namespace StableMatching

variable {smp : SMP n}

/-- 安定マッチングに対応する回転の下方閉集合。 -/
noncomputable def toRotationLowerSet (M : StableMatching smp) : LowerSet (Rotation smp) :=
  Rotation.stableMatchingOrderIsoLowerSet M

/-- 回転の下方閉集合に対応する安定マッチング。 -/
noncomputable def ofRotationLowerSet (D : LowerSet (Rotation smp)) : StableMatching smp :=
  (Rotation.stableMatchingOrderIsoLowerSet (smp := smp)).symm D

/-- 安定マッチングを下方閉集合に写して戻すと、元の安定マッチングになる。 -/
@[simp]
theorem ofRotationLowerSet_toRotationLowerSet (M : StableMatching smp) :
    ofRotationLowerSet M.toRotationLowerSet = M :=
  Rotation.stableMatchingOrderIsoLowerSet.symm_apply_apply M

/-- 下方閉集合を安定マッチングに写して戻すと、元の下方閉集合になる。 -/
@[simp]
theorem toRotationLowerSet_ofRotationLowerSet (D : LowerSet (Rotation smp)) :
    (ofRotationLowerSet D).toRotationLowerSet = D :=
  Rotation.stableMatchingOrderIsoLowerSet.apply_symm_apply D

/-- 回転が下方閉集合に属するのは、対応する `SupIrred` 元が安定マッチング以下のとき。 -/
theorem mem_toRotationLowerSet_iff (M : StableMatching smp) (ρ : Rotation smp) :
    ρ ∈ M.toRotationLowerSet ↔ (Rotation.toSupIrred ρ).1 ≤ M := by
  classical
  change ρ ∈ LowerSet.map (Rotation.orderIsoSupIrred (smp := smp)).symm
    (OrderIso.lowerSetSupIrred M) ↔ (Rotation.toSupIrred ρ).1 ≤ M
  exact LowerSet.mem_map

end StableMatching

namespace Rotation

/-- 被覆辺の終点と始点に対応する下方閉集合の差は、その辺の回転のみからなる。 -/
theorem SMEdge.toRotationLowerSet_target_diff_source {smp : SMP n} (e : SMEdge smp) :
    (e.target.toRotationLowerSet : Set (Rotation smp)) \
      (e.source.toRotationLowerSet : Set (Rotation smp)) = {e.toRotation} := by
  apply Set.ext
  intro ρ
  change (ρ ∈ e.target.toRotationLowerSet ∧ ρ ∉ e.source.toRotationLowerSet) ↔
    ρ = e.toRotation
  simp only [StableMatching.mem_toRotationLowerSet_iff]
  constructor
  · rintro ⟨hTarget, hSource⟩
    apply toSupIrred_injective
    apply Subtype.ext
    exact e.existsUnique_supIrred.unique ⟨(toSupIrred ρ).2, hTarget, hSource⟩ e.supIrred_spec
  · rintro rfl
    exact e.supIrred_spec.2

end Rotation
end SMP
end StableMatching
