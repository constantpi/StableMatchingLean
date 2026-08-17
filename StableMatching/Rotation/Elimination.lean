import StableMatching.Rotation.Exposed

namespace StableMatching
namespace SMP
namespace Rotation

/-- 回転に男性mが含まれるかどうか -/
def ExposedRotation.ContainsMan
    {smp : SMP n}
    (M : StableMatching smp)
    (ρ : ExposedRotation M)
    (m : smp.Man) : Prop :=
  ∃ i, ρ.man i = m

/-- 回転に女性wが含まれるかどうか -/
def ExposedRotation.ContainsWoman
    {smp : SMP n}
    (M : StableMatching smp)
    (ρ : ExposedRotation M)
    (w : smp.Woman) : Prop :=
  ∃ i, ρ.woman i = w

namespace ExposedRotation

variable {smp : SMP n} {M : StableMatching smp}

/-- PrevのあとにNextを適用すると元の要素に戻ることを示す定理 -/
@[simp]
theorem cycleNext_cyclePrev
    (ρ : ExposedRotation M) (i : Fin ρ.k) :
    cycleNext ρ.hk (cyclePrev ρ.hk i) = i := by
  apply Fin.ext
  unfold cycleNext cyclePrev
  simp
  have : i.val + ρ.k - 1 + 1 = i.val + ρ.k := by omega
  simp [this]
  apply Nat.mod_eq_of_lt
  exact i.isLt

/-- NextのあとにPrevを適用すると元の要素に戻ることを示す定理 -/
@[simp]
theorem cyclePrev_cycleNext
    (ρ : ExposedRotation M) (i : Fin ρ.k) :
    cyclePrev ρ.hk (cycleNext ρ.hk i) = i := by
  apply Fin.ext
  unfold cycleNext cyclePrev
  simp

  have hi : (i : Nat) < ρ.k := i.isLt
  have hk : 1 < ρ.k := by exact ρ.hk

  calc
    ((↑i + 1) % ρ.k + ρ.k - 1) % ρ.k = ((↑i + 1) % ρ.k + (ρ.k - 1)) % ρ.k := by
        congr 1
        omega
    _ = ((↑i + 1) + (ρ.k - 1)) % ρ.k := by rw [Nat.mod_add_mod]
    _ = (↑i + ρ.k) % ρ.k := by
        congr 1
        omega
    _ = ↑i % ρ.k := by simp
    _ = ↑i := Nat.mod_eq_of_lt i.isLt

/-- Nextが単射であることを示す定理 -/
theorem cycleNext_injective
    (ρ : ExposedRotation M) :
    Function.Injective (cycleNext ρ.hk) := by
  intro i j h
  rw [← ρ.cyclePrev_cycleNext i, ← ρ.cyclePrev_cycleNext j]
  rw [h]

/-- 回転に同じ女性がダブって現れることはない-/
theorem woman_injective
    (ρ : ExposedRotation M) :
    Function.Injective ρ.woman := by
  intro i j h
  apply ρ.man_injective
  apply M.matching.partnerOfMan_injective
  simp [ρ.matched]
  exact h

/-- woman iのpartnerはman iである -/
@[simp]
theorem matching_partnerOfWoman_woman
    (ρ : ExposedRotation M) (i : Fin ρ.k) :
    M.matching.partnerOfWoman (ρ.woman i) = ρ.man i := by
  rw [← ρ.matched i]
  simp

/-- 回転に含まれる男性の添字を返す -/
noncomputable def indexOf
    (ρ : ExposedRotation M) (m : smp.Man)
    (hm : ρ.ContainsMan M m) : Fin ρ.k :=
  Classical.choose hm

/-- indexOfが男性mの添字を返す -/
theorem man_indexOf
    (ρ : ExposedRotation M) (m : smp.Man)
    (hm : ρ.ContainsMan M m) :
    ρ.man (ρ.indexOf m hm) = m :=
  Classical.choose_spec hm

/-- indexOfが男性mの添字を返す -/
theorem indexOf_man
    (ρ : ExposedRotation M) (i : Fin ρ.k) :
    ρ.indexOf (ρ.man i) ⟨i, rfl⟩ = i := by
  apply ρ.man_injective
  exact ρ.man_indexOf (ρ.man i) ⟨i, rfl⟩

/-- indexOfが指定された男性の添字を返す -/
theorem indexOf_eq
    (ρ : ExposedRotation M) (m : smp.Man)
    (hm : ρ.ContainsMan M m) (i : Fin ρ.k)
    (hi : ρ.man i = m) :
    ρ.indexOf m hm = i := by
  apply ρ.man_injective
  rw [ρ.man_indexOf m hm]
  exact hi.symm

/-- indexOfが単射であることを示す定理 -/
theorem indexOf_injective
    (ρ : ExposedRotation M)
    (m₁ m₂ : smp.Man) (hm₁ : ρ.ContainsMan M m₁) (hm₂ : ρ.ContainsMan M m₂)
    (h : ρ.indexOf m₁ hm₁ = ρ.indexOf m₂ hm₂) :
    m₁ = m₂ := by
  have := ρ.man_indexOf m₁ hm₁
  rw [h] at this
  rw [man_indexOf] at this
  exact this.symm

/-- eliminatedPartnerは回転の除去後の男性mのパートナーを返す -/
noncomputable def eliminatedPartner
    (ρ : ExposedRotation M) (m : smp.Man) : smp.Woman :=
  by
    classical
    exact if hm : ρ.ContainsMan M m then
      ρ.woman (cycleNext ρ.hk (ρ.indexOf m hm))
    else
      M.matching.partnerOfMan m

/-- man iのパートーはwoman i+1 である-/
@[simp]
theorem eliminatedPartner_man
    (ρ : ExposedRotation M) (i : Fin ρ.k) :
    ρ.eliminatedPartner (ρ.man i) =
      ρ.woman (cycleNext ρ.hk i) := by
  unfold eliminatedPartner
  have hm: ρ.ContainsMan M (ρ.man i) := ⟨i, rfl⟩
  simp [hm]
  congr
  exact ρ.indexOf_eq (ρ.man i) hm i rfl

/-- 回転に含まれない男性mのeliminatedPartnerは、mの元のパートナーである -/
theorem eliminatedPartner_of_not_contains
    (ρ : ExposedRotation M) (m : smp.Man)
    (hm : ¬ ρ.ContainsMan M m) :
    ρ.eliminatedPartner m = M.matching.partnerOfMan m := by
  simp [eliminatedPartner, hm]

/-- eliminatedPartnerは単射である -/
theorem eliminatedPartner_injective
    (ρ : ExposedRotation M) :
    Function.Injective ρ.eliminatedPartner := by
  intro m₁ m₂ h
  -- ¬ ρ.containsman mであって、w=M.matching.partnerofman mのとき、w=rho.woman iとなるiは存在しないことを先に示しておく
  have not_exists (m : smp.Man) (hm : ¬ ρ.ContainsMan M m) :
      ¬ ∃ i, ρ.woman i = M.matching.partnerOfMan m := by
    intro h
    obtain ⟨i, hi⟩ := h
    unfold ContainsMan at hm
    push_neg at hm
    have hmi := hm i
    have : M.matching.partnerOfWoman (ρ.woman i) = M.matching.partnerOfWoman (M.matching.partnerOfMan m) := by rw [hi]
    simp at this
    contradiction

  by_cases h₁ : ρ.ContainsMan M m₁ <;> simp [eliminatedPartner, h₁] at h
  .
    by_cases h₂ : ρ.ContainsMan M m₂ <;> simp [h₂] at h
    .
      apply ρ.woman_injective at h
      apply ρ.cycleNext_injective at h
      exact ρ.indexOf_injective m₁ m₂ h₁ h₂ h
    .
      have := not_exists m₂ h₂
      exfalso
      apply this
      exists cycleNext ρ.hk (ρ.indexOf m₁ h₁)
  .
    by_cases h₂ : ρ.ContainsMan M m₂ <;> simp [h₂] at h
    .
      have := not_exists m₁ h₁
      exfalso
      apply this
      exists cycleNext ρ.hk (ρ.indexOf m₂ h₂)
      exact h.symm
    .
      exact M.matching.partnerOfMan_injective m₁ m₂ h

/-- eliminatedMatchingは回転の除去後のマッチングを返す -/
noncomputable def eliminatedMatching (ρ : ExposedRotation M) : Matching smp :=
  {
    equiv := Equiv.ofBijective ρ.eliminatedPartner
      ⟨ρ.eliminatedPartner_injective,
        (Finite.injective_iff_surjective_of_equiv M.matching.equiv).mp
          ρ.eliminatedPartner_injective⟩
  }

/-- eliminatedMatchingは回転の除去後のマッチングを返す -/
@[simp]
theorem eliminatedMatching_partnerOfMan
    (ρ : ExposedRotation M) (m : smp.Man) :
    ρ.eliminatedMatching.partnerOfMan m = ρ.eliminatedPartner m := by
  simp [eliminatedMatching, Matching.partnerOfMan]


/-- woman iの回転除去後のpartnerはman i-1である -/
@[simp]
theorem eliminatedMatching_partnerOfWoman_woman
    (ρ : ExposedRotation M) (i : Fin ρ.k) :
    ρ.eliminatedMatching.partnerOfWoman (ρ.woman i) =
      ρ.man (cyclePrev ρ.hk i) := by
  have h := ρ.eliminatedMatching.partnerOfWoman_partnerOfMan
    (ρ.man (cyclePrev ρ.hk i))
  simp at h
  exact h

/-- womanが回転に含まれない場合のpartnerOfWoman は元のマッチングのpartnerである -/
theorem eliminatedMatching_partnerOfWoman_of_not_contains
    (ρ : ExposedRotation M) (w : smp.Woman)
    (hw : ¬ ρ.ContainsWoman M w) :
    ρ.eliminatedMatching.partnerOfWoman w = M.matching.partnerOfWoman w := by
  set m := M.matching.partnerOfWoman w with hm
  have hm' : ¬ ρ.ContainsMan M m := by
    intro h
    unfold ContainsMan at h
    obtain ⟨i, hi⟩ := h
    apply hw
    exists i
    rw [← ρ.matched i]
    rw [hi, hm]
    simp
  have eliminated_partner : ρ.eliminatedMatching.partnerOfMan m = w := by
    simp
    rw [ρ.eliminatedPartner_of_not_contains m hm']
    simp [hm]
  set eliminated_matching := ρ.eliminatedMatching with hρ
  rw [←eliminated_partner]
  simp

/-- 除去後にwomanからみたpreferanceは改善 -/
theorem woman_prefersOrEqual_eliminatedPartner
    (ρ : ExposedRotation M) (w : smp.Woman) :
    ρ.eliminatedMatching.partnerOfWoman w ≼[w]
      M.matching.partnerOfWoman w := by
  by_cases hw : ρ.ContainsWoman M w
  ·
    obtain ⟨i, woman_i⟩ := hw
    rw [← woman_i]
    rw [ρ.eliminatedMatching_partnerOfWoman_woman,
      ρ.matching_partnerOfWoman_woman]
    exact le_of_lt (ρ.nextAccepts i)
  ·
    rw [ρ.eliminatedMatching_partnerOfWoman_of_not_contains w hw]
    simp

/-- eliminatedMatchingは安定である -/
theorem eliminatedMatching_isStable
    (ρ : ExposedRotation M) :
    ρ.eliminatedMatching.IsStable := by
  intro m w hblocking
  unfold Matching.IsBlockingPair at hblocking
  have hwoman : m ≺[w] M.matching.partnerOfWoman w := lt_of_lt_of_le hblocking.right (ρ.woman_prefersOrEqual_eliminatedPartner w)
  by_cases hm : ρ.ContainsMan M m
  ·
    -- ρに男性mが含まれる場合
    -- obtain ⟨i, rfl⟩ := hm
    obtain ⟨i, him⟩ := hm
    rw [← him] at hblocking hwoman
    rw [ρ.eliminatedMatching_partnerOfMan,
      ρ.eliminatedPartner_man] at hblocking
    have hne : w ≠ ρ.woman i := by
      intro h
      rw [h] at hwoman
      rw [ρ.matching_partnerOfWoman_woman] at hwoman
      exact (Woman.prefers_irrefl (ρ.woman i) (ρ.man i)) hwoman
    cases  Man.prefers_total (ρ.man i) hne with
    | inl hbetter =>
      -- ρ.man iとwがblocking pairであることを示す
      have : Matching.IsBlockingPair M.matching (ρ.man i) w := by
        constructor
        .
          simp [ρ.matched]
          exact hbetter
        .
          exact hwoman
      exact M.isStable (ρ.man i) w this
    | inr hworse =>
      have hnext := ρ.nextIsBest i w hworse hwoman
      exact not_lt_of_ge hnext hblocking.left
  ·
    -- ρに男性mが含まれない場合
    apply M.isStable m w
    constructor
    ·
      rw [ρ.eliminatedMatching_partnerOfMan,
        ρ.eliminatedPartner_of_not_contains m hm] at hblocking
      exact hblocking.1
    · exact hwoman

/-- 安定マッチングから回転を除去したものを得る -/
noncomputable def eliminate
    (ρ : ExposedRotation M) : StableMatching smp where
  matching := ρ.eliminatedMatching
  isStable := ρ.eliminatedMatching_isStable

/-- 除去後の男性の相手-/
@[simp]
theorem eliminate_partnerOfMan
    (ρ : ExposedRotation M) (m : smp.Man) :
    ρ.eliminate.matching.partnerOfMan m = ρ.eliminatedPartner m := by
  exact ρ.eliminatedMatching_partnerOfMan m

/-- man iの相手がwoman i+1になる -/
@[simp]
theorem eliminate_partnerOfMan_man
    (ρ : ExposedRotation M) (i : Fin ρ.k) :
    ρ.eliminate.matching.partnerOfMan (ρ.man i) =
      ρ.woman (cycleNext ρ.hk i) := by
  rw [ρ.eliminate_partnerOfMan, ρ.eliminatedPartner_man]

/-- 回転に含まれない相手は除去後も変わらない-/
theorem eliminate_partnerOfMan_of_not_contains
    (ρ : ExposedRotation M) (m : smp.Man)
    (hm : ¬ ρ.ContainsMan M m) :
    ρ.eliminate.matching.partnerOfMan m =
      M.matching.partnerOfMan m := by
  rw [ρ.eliminate_partnerOfMan,
    ρ.eliminatedPartner_of_not_contains m hm]

end ExposedRotation

end Rotation
end SMP
end StableMatching
