import StableMatching.Basic.Preference

namespace StableMatching
namespace SMP

/--
問題 `sm` に対する完全マッチング。
-/
structure Matching (sm : SMP n) where
  equiv : sm.Man ≃ sm.Woman

namespace Matching

/--
男性 `m` のパートナー。
-/
def partnerOfMan
    {sm : SMP n}
    (M : sm.Matching)
    (m : sm.Man) : sm.Woman :=
  M.equiv m

/--
女性 `w` のパートナー。
-/
def partnerOfWoman
    {sm : SMP n}
    (M : sm.Matching)
    (w : sm.Woman) : sm.Man :=
  M.equiv.symm w

@[simp]
theorem partnerOfWoman_partnerOfMan
    {sm : SMP n}
    (M : sm.Matching) (m : sm.Man) :
    M.partnerOfWoman (M.partnerOfMan m) = m := by
  simp [partnerOfWoman, partnerOfMan]

@[simp]
theorem partnerOfMan_partnerOfWoman
    {sm : SMP n}
    (M : sm.Matching) (w : sm.Woman) :
    M.partnerOfMan (M.partnerOfWoman w) = w := by
  simp [partnerOfWoman, partnerOfMan]

/-- partnerOfManの単射性 -/
theorem partnerOfMan_injective
    {sm : SMP n}
    (M : sm.Matching)
    (m₁ m₂ : sm.Man) :
    (M.partnerOfMan m₁ = M.partnerOfMan m₂) → m₁ = m₂ := by
  intro h
  rw [partnerOfMan] at h
  exact M.equiv.injective h

/-- partnerOfWomanの単射性 -/
theorem partnerOfWoman_injective
    {sm : SMP n}
    (M : sm.Matching)
    (w₁ w₂ : sm.Woman) :
    (M.partnerOfWoman w₁ = M.partnerOfWoman w₂) → w₁ = w₂ := by
  intro h
  rw [partnerOfWoman] at h
  exact M.equiv.symm.injective h

end Matching

end SMP
end StableMatching
