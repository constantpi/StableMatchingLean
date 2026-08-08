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

theorem memBetterPartner_eq_first_and_second
    {sm : SMP n}
    (M₁ M₂ : StableMatching sm) (m : sm.Man)
    (h : M₁.matching.partnerOfMan m = M₂.matching.partnerOfMan m) :
    menBetterPartner M₁ M₂ m = M₁.matching.partnerOfMan m ∧
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

/-- menBetterPartnerは可換-/
theorem menBetterPartner_comm
    {sm : SMP n}
    (M₁ M₂ : StableMatching sm) (m : sm.Man) :
    menBetterPartner M₁ M₂ m = menBetterPartner M₂ M₁ m := by
  unfold menBetterPartner
  set w₁ := M₁.matching.partnerOfMan m
  set w₂ := M₂.matching.partnerOfMan m
  by_cases h : w₁ ≺[m] w₂
  ·
    have h' : ¬ w₂ ≺[m] w₁ := by
      -- rw [Man.prefersOrEqual_iff_not_prefers] at h
      sorry
    simp [h, h']
  .
    have h' : w₂ ≺[m] w₁ := by
      -- rw [Man.prefersOrEqual_iff_not_prefers] at h
      sorry
    simp [h, h']



/-- 安定マッチングにおいて、ある男性が現在のパートナーよりも別の女性を好むなら、その女性は現在のパートナーをその男性よりも好む。 -/
theorem woman_prefers_current_of_man_prefers_other
    {sm : SMP n}
    (M : StableMatching sm)
    (m : sm.Man)
    (w : sm.Woman)
    (hm : w ≺[m] M.matching.partnerOfMan m) :
    M.matching.partnerOfWoman w ≺[w] m := by
  have hne : M.matching.partnerOfWoman w ≠ m := by
    intro h
    have : M.matching.partnerOfMan m = w := by simp [← h]
    simp [this] at hm
  rcases w.prefers_total hne with hcurrent | hmcurrent
  · exact hcurrent
  · exfalso
    have blocking : M.matching.IsBlockingPair m w := ⟨hm, hmcurrent⟩
    exact M.isStable m w blocking

/-- 安定マッチングにおいて、ある女性が現在のパートナーよりも別の男性を好むなら、その男性は現在のパートナーをその女性よりも好む。 -/
theorem man_prefers_current_of_woman_prefers_other
    {sm : SMP n}
    (M : StableMatching sm)
    (m : sm.Man)
    (w : sm.Woman)
    (hw : m ≺[w] M.matching.partnerOfWoman w) :
    M.matching.partnerOfMan m ≺[m] w := by
  have hne : M.matching.partnerOfMan m ≠ w := by
    intro h
    have : M.matching.partnerOfWoman w = m := by simp [← h]
    simp [this] at hw
  rcases m.prefers_total hne with hcurrent | hwcurrent
  · exact hcurrent
  · exfalso
    have blocking : M.matching.IsBlockingPair m w := ⟨hwcurrent, hw⟩
    exact M.isStable m w blocking

/-- 男性ごとにより好ましいパートナーを選ぶ関数は単射である。
2つの元のマッチングの安定性により、2つの交差する場合は排除される。 -/
theorem menBetterPartner_injective
    {sm : SMP n}
    (M₁ M₂ : StableMatching sm) :
    Function.Injective (menBetterPartner M₁ M₂) := by
  intro m₁ m₂ hchosen
  -- 補題: m1, m2が異なりm1はM1を選び、m2はM2を選んだことで衝突したことは矛盾
  have contra
      (Ma Mb : StableMatching sm)
      (h₁ : Ma.matching.partnerOfMan m₁ ≺[m₁] Mb.matching.partnerOfMan m₁)
      (h₂ : Mb.matching.partnerOfMan m₂ ≺[m₂] Ma.matching.partnerOfMan m₂)
      (hchosen : menBetterPartner Ma Mb m₁ = menBetterPartner Ma Mb m₂)
      : False := by
    -- h1によって menBetterPartner Ma Mb m₁ = Ma.matching.partnerOfMan m₁
    rw [menBetterPartner_eq_first_of_prefers Ma Mb m₁ h₁] at hchosen
    -- h2によって menBetterPartner Ma Mb m₂ = Mb.matching.partnerOf
    have : menBetterPartner Ma Mb m₂ = Mb.matching.partnerOfMan m₂ := by
      rw [menBetterPartner_comm]
      exact menBetterPartner_eq_first_of_prefers Mb Ma m₂ h₂
    rw [this] at hchosen
    set w := Ma.matching.partnerOfMan m₁ with hw
    rw [← hchosen] at h₂
    -- Maにおいてm2 wがblockingでないことをつかう
    have ma_blocking := woman_prefers_current_of_man_prefers_other Ma m₂ w h₂
    have : Ma.matching.partnerOfWoman w = m₁ := by simp [hw]
    rw [this] at ma_blocking
    have mb_blocking := woman_prefers_current_of_man_prefers_other Mb m₁ w h₁
    have : Mb.matching.partnerOfWoman w = m₂ := by simp [hchosen]
    rw [this] at mb_blocking
    apply Woman.prefers_asymm w ma_blocking
    exact mb_blocking

  -- 補題: m1とm2がともにMaを選んだことで衝突したならm1=m2
  have eq_chosen
      (Ma Mb : StableMatching sm)
      (h₁ : Ma.matching.partnerOfMan m₁ ≺[m₁] Mb.matching.partnerOfMan m₁)
      (h₂ : Ma.matching.partnerOfMan m₂ ≺[m₂] Mb.matching.partnerOfMan m₂)
      (hchosen : menBetterPartner Ma Mb m₁ = menBetterPartner Ma Mb m₂)
      : m₁ = m₂ := by
    rw [menBetterPartner_eq_first_of_prefers Ma Mb m₁ h₁] at hchosen
    rw [menBetterPartner_eq_first_of_prefers Ma Mb m₂ h₂] at hchosen
    -- exact M₁.matching.equiv.injective hchosen
    exact Ma.matching.partnerOfMan_injective m₁ m₂ hchosen

  -- 補題: m1がMa,Mbで同じパートナを選んでいて、衝突したならm1=m2
  have eq_chosen_same
      (Ma Mb : StableMatching sm)
      (ma mb : sm.Man)
      (h : Ma.matching.partnerOfMan ma = Mb.matching.partnerOfMan ma)
      (hchosen : menBetterPartner Ma Mb ma = menBetterPartner Ma Mb mb)
      : ma = mb := by
    if compare : Ma.matching.partnerOfMan mb ≺[mb] Mb.matching.partnerOfMan mb then
      have : menBetterPartner Ma Mb mb = Ma.matching.partnerOfMan mb := menBetterPartner_eq_first_of_prefers Ma Mb mb compare
      rw [this] at hchosen
      have : menBetterPartner Ma Mb ma = Ma.matching.partnerOfMan ma := (memBetterPartner_eq_first_and_second Ma Mb ma h).left
      rw [this] at hchosen
      exact Ma.matching.partnerOfMan_injective ma mb hchosen
    else
      have : menBetterPartner Ma Mb mb = Mb.matching.partnerOfMan mb := menBetterPartner_eq_second_of_not_prefers Ma Mb mb compare
      rw [this] at hchosen
      have : menBetterPartner Ma Mb ma = Mb.matching.partnerOfMan ma := (memBetterPartner_eq_first_and_second Ma Mb ma h).right
      rw [this] at hchosen
      exact Mb.matching.partnerOfMan_injective ma mb hchosen


  if eq_1: M₁.matching.partnerOfMan m₁ = M₂.matching.partnerOfMan m₁ then
    exact eq_chosen_same M₁ M₂ m₁ m₂ eq_1 hchosen
  else
    have m_compare := Man.prefers_total (sm:=sm) m₁ eq_1
    cases m_compare with
    | inl pref1 =>
      if eq_2: M₁.matching.partnerOfMan m₂ = M₂.matching.partnerOfMan m₂ then
        exact (eq_chosen_same M₁ M₂ m₂ m₁ eq_2 hchosen.symm).symm
      else
        have m_compare2 := Man.prefers_total (sm:=sm) m₂ eq_2
        cases m_compare2 with
        | inl pref2 =>
          exact eq_chosen M₁ M₂ pref1 pref2 hchosen
        | inr pref2 =>
          exfalso
          exact contra M₁ M₂ pref1 pref2 hchosen
    | inr pref2 =>
      if eq_2: M₁.matching.partnerOfMan m₂ = M₂.matching.partnerOfMan m₂ then
        exact (eq_chosen_same M₁ M₂ m₂ m₁ eq_2 hchosen.symm).symm
      else
        have m_compare2 := Man.prefers_total (sm:=sm) m₂ eq_2
        have : menBetterPartner M₂ M₁ m₁ = menBetterPartner M₂ M₁ m₂ := by
          rw [menBetterPartner_comm, menBetterPartner_comm M₂ M₁]
          exact hchosen


        cases m_compare2 with
        | inl pref1 =>
          exfalso
          exact contra M₂ M₁ pref2 pref1 this
        | inr pref1 =>
          exact eq_chosen M₂ M₁ pref2 pref1 this

theorem menBetterPartner_bijective
    {sm : SMP n}
    (M₁ M₂ : StableMatching sm) :
    Function.Bijective (menBetterPartner M₁ M₂) := by
  apply (Fintype.bijective_iff_injective_and_card (menBetterPartner M₁ M₂)).mpr
  exact ⟨menBetterPartner_injective M₁ M₂, by rw [sm.card_man, sm.card_woman]⟩

/-- 男性ごとにより好ましいパートナーを選ぶ関数から誘導される完全マッチング。 -/
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

end Lattice
end SMP
end StableMatching
