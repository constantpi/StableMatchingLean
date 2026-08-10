import StableMatching.Basic.Preference

namespace StableMatching
namespace SMP

/--
問題 `smp` に対する完全マッチング。
-/
structure Matching (smp : SMP n) where
  equiv : smp.Man ≃ smp.Woman

namespace Matching

/-- 男女を交換した問題上の対応する完全マッチング。-/
def swap
    (smp : SMP n)
    (M : smp.Matching) : (smp.swap).Matching :=
  {
    equiv := {
      toFun := fun m =>
        smp.swapWomanEquiv
          (M.equiv.symm (smp.swapManEquiv.symm m))
      invFun := fun w =>
        smp.swapManEquiv
          (M.equiv (smp.swapWomanEquiv.symm w))
      left_inv := by
        intro m
        simp
      right_inv := by
        intro w
        simp
    }
  }

/- 男女を二回交換すると元のマッチングに戻る。 -/
@[simp]
theorem swap_swap
    {smp : SMP n}
    (M : smp.Matching) : M.swap.swap = M := by
  rfl

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
theorem partnerOfMan_swap
    {smp : SMP n}
    (M : smp.Matching) (w : smp.Woman) :
    (M.swap).partnerOfMan (smp.swapMan w) =
      smp.swapWoman (M.partnerOfWoman w) := by
  simp [swap, partnerOfMan, partnerOfWoman, swapManEquiv, swapWomanEquiv,
    swapMan, swapWoman]

@[simp]
theorem partnerOfWoman_swap
    {smp : SMP n}
    (M : smp.Matching) (m : smp.Man) :
    (M.swap).partnerOfWoman (smp.swapWoman m) =
      smp.swapMan (M.partnerOfMan m) := by
  simp [swap, partnerOfMan, partnerOfWoman, swapManEquiv, swapWomanEquiv,
    swapMan, swapWoman]

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

/- 男性ごとのパートナーが一致するマッチングの外延性 -/
@[ext]
theorem ext_partnerOfMan
    {smp : SMP n}
    {M₁ M₂ : smp.Matching}
    (h : ∀ m, M₁.partnerOfMan m = M₂.partnerOfMan m) :
    M₁ = M₂ := by
  let ⟨e1⟩ := M₁
  let ⟨e2⟩ := M₂
  have he : e1 = e2 := by
    apply Equiv.ext
    intro m
    have := h m
    simp [partnerOfMan] at this
    exact this
  rw [he]

def matchingEquiv :
    Matching smp ≃ (smp.Man ≃ smp.Woman) :=
{
  toFun := Matching.equiv
  invFun := fun e => ⟨e⟩
  left_inv := by intro M; cases M; rfl
  right_inv := by intro e; rfl
}

instance matchingFintype
    {smp : SMP n} :
    Fintype (Matching smp) :=
  Fintype.ofEquiv (smp.Man ≃ smp.Woman) (matchingEquiv (smp := smp)).symm

theorem card_matching
    (smp : SMP n) :
    Fintype.card (Matching smp) = n.factorial := by
  let manWomanEquiv : smp.Man ≃ smp.Woman :=
    { toFun := fun m => ⟨m.val⟩
      invFun := fun w => ⟨w.val⟩
      left_inv := by intro m; rfl
      right_inv := by intro w; rfl }
  rw [Fintype.card_congr (matchingEquiv (smp := smp))]
  rw [Fintype.card_equiv manWomanEquiv]
  rw [smp.card_man]

end Matching
end SMP
end StableMatching
