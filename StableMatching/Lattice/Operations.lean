import StableMatching.Basic.Stability

namespace StableMatching
namespace SMP

/-- Of the partners assigned to `m` by two stable matchings, choose the one that
`m` prefers.  This is deliberately only a function until injectivity has been
proved. -/
def menBetterPartner
    {sm : SMP n}
    (M₁ M₂ : StableMatching sm)
    (m : sm.Man) : sm.Woman :=
  if M₁.matching.partnerOfMan m ≺[m] M₂.matching.partnerOfMan m then
    M₁.matching.partnerOfMan m
  else
    M₂.matching.partnerOfMan m

theorem menBetterPartner_eq_first_of_prefers
    {sm : SMP n}
    (M₁ M₂ : StableMatching sm) (m : sm.Man)
    (h : M₁.matching.partnerOfMan m ≺[m] M₂.matching.partnerOfMan m) :
    menBetterPartner M₁ M₂ m = M₁.matching.partnerOfMan m := by
  simp [menBetterPartner, h]

theorem menBetterPartner_eq_second_of_not_prefers
    {sm : SMP n}
    (M₁ M₂ : StableMatching sm) (m : sm.Man)
    (h : ¬ M₁.matching.partnerOfMan m ≺[m] M₂.matching.partnerOfMan m) :
    menBetterPartner M₁ M₂ m = M₂.matching.partnerOfMan m := by
  simp [menBetterPartner, h]

theorem menBetterPartner_eq_first_or_second
    {sm : SMP n}
    (M₁ M₂ : StableMatching sm) (m : sm.Man) :
    menBetterPartner M₁ M₂ m = M₁.matching.partnerOfMan m ∨
      menBetterPartner M₁ M₂ m = M₂.matching.partnerOfMan m := by
  by_cases h : M₁.matching.partnerOfMan m ≺[m] M₂.matching.partnerOfMan m
  · exact Or.inl (menBetterPartner_eq_first_of_prefers M₁ M₂ m h)
  · exact Or.inr (menBetterPartner_eq_second_of_not_prefers M₁ M₂ m h)

theorem menBetterPartner_is_better_or_equal_first
    {sm : SMP n}
    (M₁ M₂ : StableMatching sm) (m : sm.Man) :
    menBetterPartner M₁ M₂ m = M₁.matching.partnerOfMan m ∨
      menBetterPartner M₁ M₂ m ≺[m] M₁.matching.partnerOfMan m := by
  by_cases h : M₁.matching.partnerOfMan m ≺[m] M₂.matching.partnerOfMan m
  · exact Or.inl (menBetterPartner_eq_first_of_prefers M₁ M₂ m h)
  · rw [menBetterPartner_eq_second_of_not_prefers M₁ M₂ m h]
    by_cases heq : M₂.matching.partnerOfMan m = M₁.matching.partnerOfMan m
    · exact Or.inl heq
    · exact Or.inr ((m.prefers_total heq).resolve_right h)

namespace Matching

/-- In a stable matching, if a man prefers another woman to his current
partner, that woman prefers her current partner to him. -/
theorem woman_prefers_current_of_man_prefers_other
    {sm : SMP n}
    (M : sm.Matching)
    (hstable : M.IsStable)
    (m : sm.Man)
    (w : sm.Woman)
    (hm : w ≺[m] M.partnerOfMan m) :
    M.partnerOfWoman w ≺[w] m := by
  have hne : M.partnerOfWoman w ≠ m := by
    intro h
    have : M.partnerOfMan m = w := by
      rw [← h]
      exact M.partnerOfMan_partnerOfWoman w
    rw [this] at hm
    exact m.prefers_irrefl w hm
  rcases w.prefers_total hne with hcurrent | hmcurrent
  · exact hcurrent
  · exact False.elim (hstable m w ⟨hm, hmcurrent⟩)

end Matching

/-- The pointwise choice of the men's better partners is injective.  The two
cross cases are ruled out by the stability of the original matchings. -/
theorem menBetterPartner_injective
    {sm : SMP n}
    (M₁ M₂ : StableMatching sm) :
    Function.Injective (menBetterPartner M₁ M₂) := by
  intro m₁ m₂ hchosen
  by_cases h₁ : M₁.matching.partnerOfMan m₁ ≺[m₁] M₂.matching.partnerOfMan m₁
  · by_cases h₂ : M₁.matching.partnerOfMan m₂ ≺[m₂] M₂.matching.partnerOfMan m₂
    · simp [menBetterPartner, h₁, h₂] at hchosen
      exact M₁.matching.equiv.injective hchosen
    · simp [menBetterPartner, h₁, h₂] at hchosen
      by_cases heq : M₁.matching.partnerOfMan m₂ = M₂.matching.partnerOfMan m₂
      · apply M₁.matching.equiv.injective
        rw [heq]
        exact hchosen
      · have hm₂ : M₂.matching.partnerOfMan m₂ ≺[m₂]
            M₁.matching.partnerOfMan m₂ :=
          (m₂.prefers_total heq.symm).resolve_right h₂
        have hw₁ := M₂.matching.woman_prefers_current_of_man_prefers_other
          M₂.isStable m₁ (M₁.matching.partnerOfMan m₁) h₁
        have hw₂ := M₁.matching.woman_prefers_current_of_man_prefers_other
          M₁.isStable m₂ (M₂.matching.partnerOfMan m₂) hm₂
        rw [hchosen, M₂.matching.partnerOfWoman_partnerOfMan] at hw₁
        rw [← hchosen, M₁.matching.partnerOfWoman_partnerOfMan] at hw₂
        exact False.elim (Woman.prefers_asymm _ hw₁ hw₂)
  · by_cases h₂ : M₁.matching.partnerOfMan m₂ ≺[m₂] M₂.matching.partnerOfMan m₂
    · simp [menBetterPartner, h₁, h₂] at hchosen
      by_cases heq : M₁.matching.partnerOfMan m₁ = M₂.matching.partnerOfMan m₁
      · apply M₂.matching.equiv.injective
        rw [← heq]
        exact hchosen
      · have hm₁ : M₂.matching.partnerOfMan m₁ ≺[m₁]
            M₁.matching.partnerOfMan m₁ :=
          (m₁.prefers_total heq.symm).resolve_right h₁
        have hw₁ := M₁.matching.woman_prefers_current_of_man_prefers_other
          M₁.isStable m₁ (M₂.matching.partnerOfMan m₁) hm₁
        have hw₂ := M₂.matching.woman_prefers_current_of_man_prefers_other
          M₂.isStable m₂ (M₁.matching.partnerOfMan m₂) h₂
        rw [hchosen, M₁.matching.partnerOfWoman_partnerOfMan] at hw₁
        rw [← hchosen, M₂.matching.partnerOfWoman_partnerOfMan] at hw₂
        exact False.elim (Woman.prefers_asymm _ hw₁ hw₂)
    · simp [menBetterPartner, h₁, h₂] at hchosen
      exact M₂.matching.equiv.injective hchosen

theorem menBetterPartner_bijective
    {sm : SMP n}
    (M₁ M₂ : StableMatching sm) :
    Function.Bijective (menBetterPartner M₁ M₂) := by
  apply (Fintype.bijective_iff_injective_and_card (menBetterPartner M₁ M₂)).mpr
  exact ⟨menBetterPartner_injective M₁ M₂, by rw [sm.card_man, sm.card_woman]⟩

/-- The complete matching induced by the pointwise better-partner function. -/
def menBetterMatching
    {sm : SMP n}
    (M₁ M₂ : StableMatching sm) : Matching sm :=
  let f := menBetterPartner M₁ M₂
  let hbij := menBetterPartner_bijective M₁ M₂
  { equiv :=
      { toFun := f
        invFun := Fintype.bijInv hbij
        left_inv := Fintype.leftInverse_bijInv hbij
        right_inv := Fintype.rightInverse_bijInv hbij } }

@[simp]
theorem menBetterMatching_partnerOfMan
    {sm : SMP n}
    (M₁ M₂ : StableMatching sm) (m : sm.Man) :
    (menBetterMatching M₁ M₂).partnerOfMan m = menBetterPartner M₁ M₂ m :=
  rfl

theorem prefers_both_of_prefers_menBetterPartner
    {sm : SMP n}
    (M₁ M₂ : StableMatching sm) (m : sm.Man) (w : sm.Woman)
    (h : w ≺[m] menBetterPartner M₁ M₂ m) :
    w ≺[m] M₁.matching.partnerOfMan m ∧
      w ≺[m] M₂.matching.partnerOfMan m := by
  by_cases hpref : M₁.matching.partnerOfMan m ≺[m] M₂.matching.partnerOfMan m
  · rw [menBetterPartner_eq_first_of_prefers M₁ M₂ m hpref] at h
    exact ⟨h, m.prefers_trans h hpref⟩
  · rw [menBetterPartner_eq_second_of_not_prefers M₁ M₂ m hpref] at h
    by_cases heq : M₂.matching.partnerOfMan m = M₁.matching.partnerOfMan m
    · exact ⟨heq ▸ h, h⟩
    · have hsecond : M₂.matching.partnerOfMan m ≺[m]
          M₁.matching.partnerOfMan m :=
        (m.prefers_total heq).resolve_right hpref
      exact ⟨m.prefers_trans h hsecond, h⟩

/-- Choosing every man's better partner preserves stability. -/
theorem menBetterMatching_isStable
    {sm : SMP n}
    (M₁ M₂ : StableMatching sm) :
    (menBetterMatching M₁ M₂).IsStable := by
  intro m w hblocking
  rcases hblocking with ⟨hm, hw⟩
  rw [menBetterMatching_partnerOfMan] at hm
  obtain ⟨hm₁, hm₂⟩ := prefers_both_of_prefers_menBetterPartner M₁ M₂ m w hm
  have hw₁ := M₁.matching.woman_prefers_current_of_man_prefers_other
    M₁.isStable m w hm₁
  have hw₂ := M₂.matching.woman_prefers_current_of_man_prefers_other
    M₂.isStable m w hm₂
  let m' := (menBetterMatching M₁ M₂).partnerOfWoman w
  change m ≺[w] m' at hw
  have hm'w : menBetterPartner M₁ M₂ m' = w := by
    rw [← menBetterMatching_partnerOfMan]
    exact (menBetterMatching M₁ M₂).partnerOfMan_partnerOfWoman w
  rcases menBetterPartner_eq_first_or_second M₁ M₂ m' with hm'₁ | hm'₂
  · have : M₁.matching.partnerOfMan m' = w := hm'₁.symm.trans hm'w
    have hpartner : M₁.matching.partnerOfWoman w = m' := by
      rw [← this]
      exact M₁.matching.partnerOfWoman_partnerOfMan m'
    rw [hpartner] at hw₁
    exact w.prefers_asymm hw₁ hw
  · have : M₂.matching.partnerOfMan m' = w := hm'₂.symm.trans hm'w
    have hpartner : M₂.matching.partnerOfWoman w = m' := by
      rw [← this]
      exact M₂.matching.partnerOfWoman_partnerOfMan m'
    rw [hpartner] at hw₂
    exact w.prefers_asymm hw₂ hw

/-- The stable matching obtained by assigning every man his preferred partner
from two stable matchings. -/
def menBetter
    {sm : SMP n}
    (M₁ M₂ : StableMatching sm) : StableMatching sm :=
  { matching := menBetterMatching M₁ M₂
    isStable := menBetterMatching_isStable M₁ M₂ }

end SMP
end StableMatching
