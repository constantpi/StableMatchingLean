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

/-- 線形拡張の接頭部分を基準の下方閉集合に加えても、下方閉集合になる。 -/
theorem isLowerSet_union_take_of_linearExtension {smp : SMP n}
    (D D' : LowerSet (Rotation smp)) (rs : List (Rotation smp))
    (hMem : ∀ ρ : Rotation smp, ρ ∈ rs ↔ ρ ∈ D' ∧ ρ ∉ D)
    (hOrder : rs.Pairwise (fun ρ σ => ¬ σ ≤ ρ)) (k : ℕ) :
    IsLowerSet ((D : Set (Rotation smp)) ∪ {ρ | ρ ∈ rs.take k}) := by
  intro ρ σ hσρ hρ
  change ρ ∈ D ∨ ρ ∈ rs.take k at hρ
  change σ ∈ D ∨ σ ∈ rs.take k
  rcases hρ with hρInD | hρTake
  · exact Or.inl (D.lower hσρ hρInD)
  · have hρD' := ((hMem ρ).mp ((List.take_sublist k rs).subset hρTake)).1
    have hσD' := D'.lower hσρ hρD'
    by_cases hσD : σ ∈ D
    · exact Or.inl hσD
    · have hσList := (hMem σ).mpr ⟨hσD', hσD⟩
      rw [← List.take_append_drop k rs, List.mem_append] at hσList
      rcases hσList with hσTake | hσDrop
      · exact Or.inr hσTake
      · have hSplitOrder := hOrder
        rw [← List.take_append_drop k rs] at hSplitOrder
        exact False.elim ((List.pairwise_append.mp hSplitOrder).2.2 ρ hρTake σ hσDrop hσρ)

end Rotation
end SMP
end StableMatching
