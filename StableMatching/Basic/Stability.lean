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
@[ext]
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

def StableMatching.toMatching {smp : SMP n} :
    StableMatching smp → Matching smp :=
  fun S => S.matching

theorem StableMatching.toMatching_injective {smp: SMP n} :
    Function.Injective (StableMatching.toMatching (smp := smp)) := by
  intro S₁ S₂ h
  let ⟨M₁, h₁⟩ := S₁
  let ⟨M₂, h₂⟩ := S₂
  simp [toMatching] at h
  ext m
  simp [h]

instance stableMatchingFinite
    {smp : SMP n} :
    Finite (StableMatching smp) :=
  Finite.of_injective (StableMatching.toMatching (smp := smp))
    (StableMatching.toMatching_injective (smp := smp))

noncomputable instance stableMatchingFintype
    {smp : SMP n} :
    Fintype (StableMatching smp) :=
  Fintype.ofFinite (StableMatching smp)

theorem card_stableMatching_le_factorial
    (smp : SMP n) :
    Fintype.card (StableMatching smp) ≤ n.factorial := by
  calc
    Fintype.card (StableMatching smp)
        ≤ Fintype.card (Matching smp) :=
      Fintype.card_le_of_injective
        (StableMatching.toMatching (smp := smp))
        (StableMatching.toMatching_injective (smp := smp))
    _ = n.factorial := Matching.card_matching smp

end SMP
end StableMatching
