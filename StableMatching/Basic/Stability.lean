import StableMatching.Basic.Matching

namespace StableMatching
namespace SMP

namespace Matching

/--
`(m, w)` が matching `M` の blocking pair であること。
-/
def IsBlockingPair
    {smp : SMP n}
    (M : smp.Matching)
    (m : smp.Man)
    (w : smp.Woman) : Prop :=
  (w ≺[m] M.partnerOfMan m) ∧ (m ≺[w] M.partnerOfWoman w)

/--
matching `M` が安定であること。
-/
def IsStable
    {smp : SMP n}
    (M : smp.Matching) : Prop :=
  ∀ m w, ¬ M.IsBlockingPair m w

/-- 安定なマッチングを男女交換しても安定性は保たれる。-/
theorem isStable_swap
    {smp : SMP n}
    {M : smp.Matching}
    (hM : M.IsStable) :
    (M.swap).IsStable := by
  intro m w blocking
  let oldW : smp.Woman := (smp.swapManEquiv).symm m
  let oldM : smp.Man := (smp.swapWomanEquiv).symm w
  apply hM oldM oldW
  constructor
  · simpa [oldW, oldM] using blocking.2
  · simpa [oldW, oldM] using blocking.1

end Matching

/--
問題 `smp` の stable matching。
-/
structure StableMatching (smp : SMP n) where
  matching : smp.Matching
  isStable : matching.IsStable

/- 男性ごとのパートナーが一致する安定マッチングの外延性 -/
theorem StableMatching.ext_partnerOfMan
    {smp : SMP n}
    {S₁ S₂ : smp.StableMatching}
    (h : ∀ m, S₁.matching.partnerOfMan m = S₂.matching.partnerOfMan m) :
    S₁ = S₂ := by
  let ⟨M₁, h₁⟩ := S₁
  let ⟨M₂, h₂⟩ := S₂
  have hM : M₁ = M₂ := Matching.ext_partnerOfMan h
  simp [hM]

/-- 安定マッチングを男女交換後の問題へ移す。-/
def StableMatching.swap
    {smp : SMP n}
    (S : smp.StableMatching) : (smp.swap).StableMatching :=
  {
    matching := S.matching.swap
    isStable := Matching.isStable_swap S.isStable
  }

/- 男女を二回交換すると元の安定マッチングに戻る。 -/
@[simp]
theorem StableMatching.swap_swap
    {smp : SMP n}
    (S : smp.StableMatching) : S.swap.swap = S := by
  rfl


end SMP
end StableMatching
