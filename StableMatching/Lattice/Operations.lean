import StableMatching.Basic.Stability

namespace StableMatching
namespace SMP
namespace Lattice

/-- 2つの安定マッチングで `m` に割り当てられたパートナーのうち、`m` が好む方を選ぶ。単射性が証明されるまでは、意図的に関数としてのみ定義する。 -/
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
    menBetterPartner M₁ M₂ m ≼[m] M₁.matching.partnerOfMan m := by
  by_cases h : M₁.matching.partnerOfMan m ≺[m] M₂.matching.partnerOfMan m
  . simp [menBetterPartner, h]
  . simp [menBetterPartner, h]
    rw [Man.prefersOrEqual_iff_not_prefers]
    exact h


/-- 安定マッチングにおいて、ある男性が現在のパートナーよりも別の女性を好むなら、その女性は現在のパートナーをその男性よりも好む。 -/
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
    have : M.partnerOfMan m = w := by simp [← h]
    simp [this] at hm
  rcases w.prefers_total hne with hcurrent | hmcurrent
  · exact hcurrent
  · exfalso
    have blocking : M.IsBlockingPair m w := ⟨hm, hmcurrent⟩
    exact hstable m w blocking
