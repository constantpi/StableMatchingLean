import StableMatching.Rotation.Birkhoff
import StableMatching.Rotation.DefEquality

namespace StableMatching
namespace SMP
namespace Rotation

/-- 下方閉集合への回転の1要素追加は、対応する露出回転の除去として実現できる。 -/
theorem ExposedRotation.exists_of_lowerSet_insert {smp : SMP n}
    (D D' : LowerSet (Rotation smp)) (ρ : Rotation smp)
    (hρ : ρ ∉ D)
    (hInsert : (D' : Set (Rotation smp)) = insert ρ (D : Set (Rotation smp))) :
    ∃ τ : ExposedRotation smp,
      τ.M = StableMatching.ofRotationLowerSet D ∧
      τ.eliminate = StableMatching.ofRotationLowerSet D' ∧
      τ.toRotation = ρ := by
  obtain ⟨e, hSource, hTarget, hLabel⟩ := SMEdge.exists_of_lowerSet_insert D D' ρ hρ hInsert
  obtain ⟨τ, hM, hEliminate⟩ := ExposedRotation.exists_exposedRotation e
  refine ⟨τ, hM.trans hSource, hEliminate.trans hTarget, ?_⟩
  have hEquivalent : τ.toSMEdge.Equivalent e := by
    intro m w
    simp only [SMEdge.IsChangedPair, ExposedRotation.toSMEdge, hM, hEliminate]
  exact ((SMEdge.toRotation_eq_iff τ.toSMEdge e).mpr hEquivalent).trans hLabel

end Rotation
end SMP
end StableMatching
