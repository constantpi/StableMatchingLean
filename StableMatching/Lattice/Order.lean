import StableMatching.Lattice.Operations


namespace StableMatching
namespace SMP
namespace Lattice

/-- 男性側から見た安定マッチングの比較関係。 -/
def MenAtLeastAsGood
    {smp : SMP n}
    (S₁ S₂ : StableMatching smp) : Prop :=
  ∀ m : smp.Man, S₁.matching.partnerOfMan m ≼[m] S₂.matching.partnerOfMan m

instance : LE (StableMatching smp) where
  le := MenAtLeastAsGood

/-- le_reflの証明 -/
theorem le_refl_smp
    {smp : SMP n}
    (S : StableMatching smp) :
    S ≤ S := by
  intro m
  simp

/-- le_transの証明 -/
theorem le_trans_smp
    {smp : SMP n}
    (S₁ S₂ S₃ : StableMatching smp)
    (h₁₂ : S₁ ≤ S₂)
    (h₂₃ : S₂ ≤ S₃) :
    S₁ ≤ S₃ := by
  intro m
  have h₁₂m := h₁₂ m
  have h₂₃m := h₂₃ m
  exact Man.prefersOrEqual_trans m h₁₂m h₂₃m

/-- le_antisymmの証明 -/
theorem le_antisymm_smp
    {smp : SMP n}
    (S₁ S₂ : StableMatching smp)
    (h₁₂ : S₁ ≤ S₂)
    (h₂₁ : S₂ ≤ S₁) :
    S₁ = S₂ := by
  let ⟨M₁, h₁⟩ := S₁
  let ⟨M₂, h₂⟩ := S₂
  have hM : M₁ = M₂ := by
    ext m
    have h₁m := h₁₂ m
    have h₂m := h₂₁ m
    simp_all
    exact Man.prefersOrEqual_antisymm m h₁m h₂m
  simp [hM]

/-- SMPに半順序関係を定義-/
instance : PartialOrder (StableMatching smp) where
  le := MenAtLeastAsGood
  le_refl := le_refl_smp
  le_trans := le_trans_smp
  le_antisymm := le_antisymm_smp

end Lattice
end SMP
end StableMatching
