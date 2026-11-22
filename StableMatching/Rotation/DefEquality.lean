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

/-- SMEdgeからExposedRotationの存在 -/
theorem exists_exposedRotation
    (e : SMEdge smp) :
    ∃ ρ : ExposedRotation smp,
      ρ.M = e.source ∧
      ρ.eliminate = e.target := by
  obtain ⟨ρ, ⟨h_eq, h_le⟩ ⟩ := exists_exposedRotation_between e.source e.target e.lt
  exists ρ
  constructor
  · exact h_eq
  .
    apply le_antisymm h_le
    have elim_gt : e.source < ρ.eliminate := by
      rw [← h_eq]
      exact ρ.lt_eliminate
    have := e.covBy.2 elim_gt
    cases lt_or_eq_of_le h_le with
    | inl h_lt =>
      exfalso
      exact this h_lt
    | inr h_eq' => rw [h_eq']

end ExposedRotation

namespace ExposedRotationQuotient

/-- ExposedRotationの商空間からRotationへの写像 -/
noncomputable def toRotation :
    ExposedRotationQuotient smp → Rotation smp :=
  Quotient.lift
    ExposedRotation.toRotation
    (by
      intro ρ₁ ρ₂ h
      exact ExposedRotation.equivalent_implies_toRotation_eq h)

/-- ExposedRotationQuotientからRotationへの写像は単射 -/
theorem toRotation_injective :
    Function.Injective (ExposedRotationQuotient.toRotation (smp:=smp)) := by
  intro q₁ q₂
  apply (fun t => Quotient.inductionOn₂ q₁ q₂ t)
  intro ρ₁ ρ₂ h
  simp [ExposedRotationQuotient.toRotation] at h
  apply Quotient.sound
  exact ExposedRotation.toRotation_eq_implies_equivalent h

/-- ExposedRotationQuotientからRotationへの写像は全射 -/
theorem toRotation_surjective :
    Function.Surjective
      (ExposedRotationQuotient.toRotation (smp := smp)) := by
  intro r
  refine Quotient.inductionOn r ?_
  -- apply (fun t :  (∀ (a : SMEdge smp), ∃ a_1, toRotation a_1 = ⟦a⟧)=> Quotient.inductionOn r t)
  intro e

  obtain ⟨ρ, hM, hE⟩ := ExposedRotation.exists_exposedRotation e

  exists Quotient.mk (ExposedRotation.setoid smp) ρ
  simp [ExposedRotationQuotient.toRotation, ExposedRotation.toRotation, ExposedRotation.toSMEdge, hM, hE]
  apply Quotient.sound
  intro m w
  simp

/-- ExposedRotationQuotientからRotationへの写像は同型 -/
noncomputable def equivRotation :
    ExposedRotationQuotient smp ≃ Rotation smp :=
  Equiv.ofBijective
    (ExposedRotationQuotient.toRotation (smp := smp))
    ⟨
      ExposedRotationQuotient.toRotation_injective,
      ExposedRotationQuotient.toRotation_surjective
    ⟩

end ExposedRotationQuotient
end Rotation
end SMP
end StableMatching
