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

/-- 同じ男性が参加する二つの回転は比較可能である。 -/
theorem le_total_of_containsMan {smp : SMP n}
    {ρ₁ ρ₂ : Rotation smp} (m : smp.Man)
    (h₁ : ρ₁.ContainsMan m) (h₂ : ρ₂.ContainsMan m) :
    ρ₁ ≤ ρ₂ ∨ ρ₂ ≤ ρ₁ := by
  obtain ⟨w₁, hw₁⟩ := h₁
  obtain ⟨w₂, hw₂⟩ := h₂
  have threshold_le_of_prefersOrEqual {w w' : smp.Woman} (hPref : w ≼[m] w') :
      Lattice.partnerThreshold m w ≤ Lattice.partnerThreshold m w' := by
    unfold Lattice.partnerThreshold
    apply Finset.inf_mono
    intro P hP
    rw [Finset.mem_filter] at hP ⊢
    exact ⟨hP.1, lt_of_le_of_lt hPref hP.2⟩
  change (toSupIrred ρ₁).1 ≤ (toSupIrred ρ₂).1 ∨ (toSupIrred ρ₂).1 ≤ (toSupIrred ρ₁).1
  rw [toSupIrred_val_eq_partnerThreshold hw₁, toSupIrred_val_eq_partnerThreshold hw₂]
  by_cases hPref : w₁ ≼[m] w₂
  · exact Or.inl (threshold_le_of_prefersOrEqual hPref)
  · have hReverse : w₂ ≺[m] w₁ :=
      (m.prefers_iff_not_prefersOrEqual w₂ w₁).mpr hPref
    exact Or.inr (threshold_le_of_prefersOrEqual (le_of_lt hReverse))

/-- 男性 `m` が参加する回転の集合。 -/
def manChain {smp : SMP n} (m : smp.Man) : Set (Rotation smp) :=
  {ρ | ρ.ContainsMan m}

/-- 回転が `m`-chain に属することと、男性 `m` がその回転に参加することは同値。 -/
@[simp]
theorem mem_manChain_iff {smp : SMP n} {ρ : Rotation smp} (m : smp.Man) :
    ρ ∈ manChain m ↔ ρ.ContainsMan m :=
  Iff.rfl

/-- 男性 `m` が参加する回転の集合は、回転の半順序における鎖である。 -/
theorem isChain_manChain {smp : SMP n} (m : smp.Man) :
    IsChain (· ≤ ·) (manChain m) := by
  intro ρ₁ h₁ ρ₂ h₂ _
  simp
  exact le_total_of_containsMan m h₁ h₂

end Rotation
end SMP
end StableMatching
