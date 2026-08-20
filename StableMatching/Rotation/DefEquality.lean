import StableMatching.Rotation.ConstructExpose

namespace StableMatching
namespace SMP
namespace Rotation
namespace ExposedRotation

/-- ExposedRotationからSMEdgeへの写像 -/
noncomputable def toSMEdge
    (ρ : ExposedRotation smp) : SMEdge smp where
  source := ρ.M
  target := ρ.eliminate
  covBy := ρ.covBy_eliminate

/-- ExposedRotationからRotationへの写像 -/
noncomputable def toRotation
    (ρ : ExposedRotation smp) : Rotation smp :=
  ρ.toSMEdge.toRotation

/-- IsChangedPairとIsRotationPairの関係 -/
@[simp]
theorem toSMEdge_isChangedPair_iff
    (ρ : ExposedRotation smp)
    (m : smp.Man)
    (w : smp.Woman) :
    ρ.toSMEdge.IsChangedPair m w ↔ IsRotationPair ρ m w := by
  constructor
  · rintro ⟨h₁, h₂⟩
    unfold IsRotationPair
    simp [toSMEdge] at h₁ h₂
    by_cases hm : ρ.ContainsMan m
    · obtain ⟨i, rfl⟩ := hm
      exists i
      simp
      simp [ρ.matched] at h₁
      exact h₁.symm
    .
      simp [ρ.eliminatedPartner_of_not_contains m hm] at h₂
      contradiction
  . rintro ⟨i, ⟨hm, hw⟩⟩
    simp [toSMEdge, SMEdge.IsChangedPair]
    simp [hm, hw, ρ.matched]
    intro h
    apply ρ.woman_injective at h
    exact cycleNext_ne_self ρ i h

/-- ExposedRotationの同値性がRotationの同値性を保つ -/
theorem equivalent_implies_toRotation_eq
    {ρ₁ ρ₂ : ExposedRotation smp}
    (h : ρ₁.Equivalent ρ₂) :
    ρ₁.toRotation = ρ₂.toRotation := by
  apply (SMEdge.toRotation_eq_iff (ρ₁.toSMEdge) (ρ₂.toSMEdge)).mpr
  intro m w
  simp
  exact h m w

/-- Rotationの同値性がExposedRotationの同値性を保つ -/
theorem toRotation_eq_implies_equivalent
    {ρ₁ ρ₂ : ExposedRotation smp}
    (h : ρ₁.toRotation = ρ₂.toRotation) :
    ρ₁.Equivalent ρ₂ := by
  intro m w
  have := (SMEdge.toRotation_eq_iff ρ₁.toSMEdge ρ₂.toSMEdge).mp h m w
  simpa using this

/-- Rotationの同値性とExposedRotationの同値性は同じ-/
theorem toRotation_eq_iff
    (ρ₁ ρ₂ : ExposedRotation smp) :
    ρ₁.toRotation = ρ₂.toRotation ↔ ρ₁.Equivalent ρ₂ :=
  ⟨toRotation_eq_implies_equivalent, equivalent_implies_toRotation_eq⟩

/-- ExposedRotationの商空間からRotationへの写像 -/
noncomputable def ExposedRotationQuotient.toRotation :
    ExposedRotationQuotient smp → Rotation smp :=
  Quotient.lift
    ExposedRotation.toRotation
    (by
      intro ρ₁ ρ₂ h
      exact equivalent_implies_toRotation_eq h)

end ExposedRotation
end Rotation
end SMP
end StableMatching
