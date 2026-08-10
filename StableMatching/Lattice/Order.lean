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

theorem le_iff_women_reverse
    (M₁ M₂ : StableMatching smp) :
    M₁ ≤ M₂ ↔
      ∀ w,
        M₂.matching.partnerOfWoman w ≼[w]
        M₁.matching.partnerOfWoman w := by
  constructor
  case mp =>
    intro h w
    by_contra h'
    have better1 : M₁.matching.partnerOfWoman w ≺[w] M₂.matching.partnerOfWoman w := by
      rw [← Woman.prefers_iff_not_prefersOrEqual] at h'
      exact h'
    set m := M₁.matching.partnerOfWoman w with hm
    have hw : M₁.matching.partnerOfMan m = w := by simp [hm]
    have better2 : w ≼[m] M₂.matching.partnerOfMan m := by
      rw [← hw]
      exact h m
    have better3 : w ≺[m] M₂.matching.partnerOfMan m := by
      by_contra h''
      rw [← Man.prefersOrEqual_iff_not_prefers] at h''
      have : M₂.matching.partnerOfMan m = w := Man.prefersOrEqual_antisymm m h'' better2
      have : M₂.matching.partnerOfWoman w = m := by simp [←this]
      simp [this] at better1
    --better1とbetter3から安定性に反することを導く
    have h_stable := M₂.isStable
    exact h_stable m w ⟨better3, better1⟩
  case mpr =>
    intro h m
    by_contra h'
    have better1 : M₂.matching.partnerOfMan m ≺[m] M₁.matching.partnerOfMan m := by
      rw [← Man.prefers_iff_not_prefersOrEqual] at h'
      exact h'
    set w := M₂.matching.partnerOfMan m with hw
    have hw' : M₂.matching.partnerOfWoman w = m := by simp [hw]
    have better2 : m ≼[w] M₁.matching.partnerOfWoman w := by
      rw [← hw']
      exact h w
    have better3 : m ≺[w] M₁.matching.partnerOfWoman w := by
      by_contra h''
      rw [← Woman.prefersOrEqual_iff_not_prefers] at h''
      have : M₁.matching.partnerOfWoman w = m := Woman.prefersOrEqual_antisymm w h'' better2
      have : M₁.matching.partnerOfMan m = w := by simp [←this]
      simp [this] at better1
    --better1とbetter3から安定性に反することを導く
    have h_stable := M₁.isStable
    exact h_stable m w ⟨better1, better3⟩

end Lattice
end SMP
end StableMatching
