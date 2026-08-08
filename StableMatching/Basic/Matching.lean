import StableMatching.Basic.Preference

namespace StableMatching
namespace SMP

/--
問題 `smp` に対する完全マッチング。
-/
structure Matching (smp : SMP n) where
  equiv : smp.Man ≃ smp.Woman

namespace Matching

/--
男性 `m` のパートナー。
-/
def partnerOfMan
    {smp : SMP n}
    (M : smp.Matching)
    (m : smp.Man) : smp.Woman :=
  M.equiv m

/--
女性 `w` のパートナー。
-/
def partnerOfWoman
    {smp : SMP n}
    (M : smp.Matching)
    (w : smp.Woman) : smp.Man :=
  M.equiv.symm w

@[simp]
theorem partnerOfWoman_partnerOfMan
    {smp : SMP n}
    (M : smp.Matching) (m : smp.Man) :
    M.partnerOfWoman (M.partnerOfMan m) = m := by
  simp [partnerOfWoman, partnerOfMan]

@[simp]
theorem partnerOfMan_partnerOfWoman
    {smp : SMP n}
    (M : smp.Matching) (w : smp.Woman) :
    M.partnerOfMan (M.partnerOfWoman w) = w := by
  simp [partnerOfWoman, partnerOfMan]

/-- partnerOfManの単射性 -/
theorem partnerOfMan_injective
    {smp : SMP n}
    (M : smp.Matching)
    (m₁ m₂ : smp.Man) :
    (M.partnerOfMan m₁ = M.partnerOfMan m₂) → m₁ = m₂ := by
  intro h
  rw [partnerOfMan] at h
  exact M.equiv.injective h

/-- partnerOfWomanの単射性 -/
theorem partnerOfWoman_injective
    {smp : SMP n}
    (M : smp.Matching)
    (w₁ w₂ : smp.Woman) :
    (M.partnerOfWoman w₁ = M.partnerOfWoman w₂) → w₁ = w₂ := by
  intro h
  rw [partnerOfWoman] at h
  exact M.equiv.symm.injective h

end Matching

end SMP
end StableMatching
