import StableMatching.Basic.Stability

namespace StableMatching
namespace SMP
namespace Lattice

/-- 2つの安定マッチングで `m` に割り当てられたパートナーのうち、`m` が好む方を選ぶ。単射性が証明されるまでは、意図的に関数としてのみ定義する。 -/
def menBetterPartner
    {smp : SMP n}
    (M₁ M₂ : StableMatching smp)
    (m : smp.Man) : smp.Woman :=
  if M₁.matching.partnerOfMan m ≺[m] M₂.matching.partnerOfMan m then
    M₁.matching.partnerOfMan m
  else
    M₂.matching.partnerOfMan m

theorem menBetterPartner_eq_first_of_prefers
    {smp : SMP n}
    (M₁ M₂ : StableMatching smp) (m : smp.Man)
    (h : M₁.matching.partnerOfMan m ≺[m] M₂.matching.partnerOfMan m) :
    menBetterPartner M₁ M₂ m = M₁.matching.partnerOfMan m := by
  simp [menBetterPartner, h]

theorem menBetterPartner_eq_second_of_not_prefers
    {smp : SMP n}
    (M₁ M₂ : StableMatching smp) (m : smp.Man)
    (h : ¬ M₁.matching.partnerOfMan m ≺[m] M₂.matching.partnerOfMan m) :
    menBetterPartner M₁ M₂ m = M₂.matching.partnerOfMan m := by
  simp [menBetterPartner, h]

theorem memBetterPartner_eq_first_and_second
    {smp : SMP n}
    (M₁ M₂ : StableMatching smp) (m : smp.Man)
    (h : M₁.matching.partnerOfMan m = M₂.matching.partnerOfMan m) :
    menBetterPartner M₁ M₂ m = M₁.matching.partnerOfMan m ∧
      menBetterPartner M₁ M₂ m = M₂.matching.partnerOfMan m := by
  simp [menBetterPartner, h]

theorem menBetterPartner_eq_first_or_second
    {smp : SMP n}
    (M₁ M₂ : StableMatching smp) (m : smp.Man) :
    menBetterPartner M₁ M₂ m = M₁.matching.partnerOfMan m ∨
      menBetterPartner M₁ M₂ m = M₂.matching.partnerOfMan m := by
  by_cases h : M₁.matching.partnerOfMan m ≺[m] M₂.matching.partnerOfMan m
  · exact Or.inl (menBetterPartner_eq_first_of_prefers M₁ M₂ m h)
  · exact Or.inr (menBetterPartner_eq_second_of_not_prefers M₁ M₂ m h)

theorem menBetterPartner_is_better_or_equal_first
    {smp : SMP n}
    (M₁ M₂ : StableMatching smp) (m : smp.Man) :
    menBetterPartner M₁ M₂ m ≼[m] M₁.matching.partnerOfMan m := by
  by_cases h : M₁.matching.partnerOfMan m ≺[m] M₂.matching.partnerOfMan m
  . simp [menBetterPartner, h]
  . simp [menBetterPartner, h]
    rw [Man.prefersOrEqual_iff_not_prefers]
    exact h

/-- menBetterPartnerは可換-/
theorem menBetterPartner_comm
    {smp : SMP n}
    (M₁ M₂ : StableMatching smp) (m : smp.Man) :
    menBetterPartner M₁ M₂ m = menBetterPartner M₂ M₁ m := by
  unfold menBetterPartner
  set w₁ := M₁.matching.partnerOfMan m
  set w₂ := M₂.matching.partnerOfMan m
  by_cases eq : w₁ = w₂
  · simp [eq]
  .
    have compare := Man.prefers_total (smp:=smp) m eq
    cases compare with
    | inl h =>
      have h' : ¬ w₂ ≺[m] w₁ := Man.prefers_asymm m h
      simp [h, h']
    | inr h =>
      have h' : ¬ w₁ ≺[m] w₂ := Man.prefers_asymm m h
      simp [h, h']


/-- 安定マッチングにおいて、ある男性が現在のパートナーよりも別の女性を好むなら、その女性は現在のパートナーをその男性よりも好む。 -/
theorem woman_prefers_current_of_man_prefers_other
    {smp : SMP n}
    (M : StableMatching smp)
    (m : smp.Man)
    (w : smp.Woman)
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
    {smp : SMP n}
    (M : StableMatching smp)
    (m : smp.Man)
    (w : smp.Woman)
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
    {smp : SMP n}
    (M₁ M₂ : StableMatching smp) :
    Function.Injective (menBetterPartner M₁ M₂) := by
  intro m₁ m₂ hchosen
  -- 補題: m1, m2が異なりm1はM1を選び、m2はM2を選んだことで衝突したことは矛盾
  have contra
      (Ma Mb : StableMatching smp)
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
      (Ma Mb : StableMatching smp)
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
      (Ma Mb : StableMatching smp)
      (ma mb : smp.Man)
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
    have m_compare := Man.prefers_total (smp:=smp) m₁ eq_1
    cases m_compare with
    | inl pref1 =>
      if eq_2: M₁.matching.partnerOfMan m₂ = M₂.matching.partnerOfMan m₂ then
        exact (eq_chosen_same M₁ M₂ m₂ m₁ eq_2 hchosen.symm).symm
      else
        have m_compare2 := Man.prefers_total (smp:=smp) m₂ eq_2
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
        have m_compare2 := Man.prefers_total (smp:=smp) m₂ eq_2
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
    {smp : SMP n}
    (M₁ M₂ : StableMatching smp) :
    Function.Bijective (menBetterPartner M₁ M₂) := by
  apply (Fintype.bijective_iff_injective_and_card (menBetterPartner M₁ M₂)).mpr
  exact ⟨menBetterPartner_injective M₁ M₂, by rw [smp.card_man, smp.card_woman]⟩

/-- 男性ごとにより好ましいパートナーを選ぶ関数から誘導される完全マッチング。 -/
def menBetterMatching
    {smp : SMP n}
    (M₁ M₂ : StableMatching smp) : Matching smp :=
  let f := menBetterPartner M₁ M₂
  let hbij := menBetterPartner_bijective M₁ M₂
  { equiv :=
      { toFun := f
        invFun := Fintype.bijInv hbij
        left_inv := Fintype.leftInverse_bijInv hbij
        right_inv := Fintype.rightInverse_bijInv hbij } }

@[simp]
theorem menBetterMatching_partnerOfMan
    {smp : SMP n}
    (M₁ M₂ : StableMatching smp) (m : smp.Man) :
    (menBetterMatching M₁ M₂).partnerOfMan m = menBetterPartner M₁ M₂ m :=
  rfl

theorem prefers_both_of_prefers_menBetterPartner
    {smp : SMP n}
    (M₁ M₂ : StableMatching smp) (m : smp.Man) (w : smp.Woman)
    (h : w ≺[m] menBetterPartner M₁ M₂ m) :
    (w ≺[m] M₁.matching.partnerOfMan m) ∧
      (w ≺[m] M₂.matching.partnerOfMan m) := by
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

/-- すべての男性にとってより好ましいパートナーを選んでも、安定性は保たれる。 -/
theorem menBetterMatching_isStable
    {smp : SMP n}
    (M₁ M₂ : StableMatching smp) :
    (menBetterMatching M₁ M₂).IsStable := by
  intro m w hblocking
  rcases hblocking with ⟨hm, hw⟩
  rw [menBetterMatching_partnerOfMan] at hm
  obtain ⟨hm₁, hm₂⟩ := prefers_both_of_prefers_menBetterPartner M₁ M₂ m w hm
  -- mはM₁とM₂の両方で現在のパートナーよりもwを好む
  have hw₁ := woman_prefers_current_of_man_prefers_other M₁ m w hm₁
  have hw₂ := woman_prefers_current_of_man_prefers_other M₂ m w hm₂
  let m' := (menBetterMatching M₁ M₂).partnerOfWoman w
  change m ≺[w] m' at hw
  have hm'w : menBetterPartner M₁ M₂ m' = w := by
    rw [← menBetterMatching_partnerOfMan]
    exact (menBetterMatching M₁ M₂).partnerOfMan_partnerOfWoman w
  rcases menBetterPartner_eq_first_or_second M₁ M₂ m' with hm'₁ | hm'₂
  · have : M₁.matching.partnerOfMan m' = w := hm'₁.symm.trans hm'w
    have hpartner : M₁.matching.partnerOfWoman w = m' := by simp [← this]
    rw [hpartner] at hw₁
    exact w.prefers_asymm hw₁ hw
  · have : M₂.matching.partnerOfMan m' = w := hm'₂.symm.trans hm'w
    have hpartner : M₂.matching.partnerOfWoman w = m' := by simp [← this]
    rw [hpartner] at hw₂
    exact w.prefers_asymm hw₂ hw

/-- 2つの安定マッチングから、すべての男性にとって好ましいパートナーを
割り当てることで得られる安定マッチング。 -/
def menBetter
    {smp : SMP n}
    (M₁ M₂ : StableMatching smp) : StableMatching smp :=
  { matching := menBetterMatching M₁ M₂
    isStable := menBetterMatching_isStable M₁ M₂ }

/-- 男女を交換した問題で `menBetter` を適用し、元の問題に戻して得られる安定マッチング。 -/
def womenBetter
    {smp : SMP n}
    (M₁ M₂ : StableMatching smp) : StableMatching smp :=
  (menBetter M₁.swap M₂.swap).swap

/-- womenBetterで女性はM₁とM₂の両方で好ましいパートナーを選ぶ。-/
theorem womenBetter_partnerOfWoman
    {smp : SMP n}
    (M₁ M₂ : StableMatching smp) (w : smp.Woman) :
    (womenBetter M₁ M₂).matching.partnerOfWoman w =
      if M₁.matching.partnerOfWoman w ≺[w] M₂.matching.partnerOfWoman w then
        M₁.matching.partnerOfWoman w
      else
        M₂.matching.partnerOfWoman w := by
  -- これはほとんど定義から明らかなのでひたすら展開して簡約する
  unfold womenBetter menBetter menBetterMatching
  simp [StableMatching.swap, Matching.swap, Matching.partnerOfWoman, Matching.partnerOfMan, swapManEquiv, swapWomanEquiv, swapMan, swapWoman, menBetterPartner]
  split
  · rename_i h'
    have h : M₁.matching.partnerOfWoman w ≺[w] M₂.matching.partnerOfWoman w := by
      simp [SMP.swap, Man.Prefers, manRank] at h'
      exact h'
    have h'' : M₁.matching.equiv.symm w ≺[w] M₂.matching.equiv.symm w := by
      simp [Matching.partnerOfWoman] at h
      exact h
    simp [h'']
    rfl
  · rename_i h'
    have h : ¬ M₁.matching.partnerOfWoman w ≺[w] M₂.matching.partnerOfWoman w := by
      simp [SMP.swap, Man.Prefers, Woman.Prefers, manRank, womanRank] at *
      exact h'
    have h'' : ¬ M₁.matching.equiv.symm w ≺[w] M₂.matching.equiv.symm w := by
      simp [Matching.partnerOfWoman] at h
      exact h
    simp [h'']
    rfl

/-- womenBetterで男性はM₁とM₂のいずれかのパートナーを選ぶ。-/
theorem womenBetter_partnerOfMan_either
    {smp : SMP n}
    (M₁ M₂ : StableMatching smp) (m : smp.Man) :
    (womenBetter M₁ M₂).matching.partnerOfMan m = M₁.matching.partnerOfMan m ∨
      (womenBetter M₁ M₂).matching.partnerOfMan m = M₂.matching.partnerOfMan m := by
  -- womenBetter_partnerOfWomanから女性側がM₁とM₂のいずれかを選ぶことがわかるので、男性側も同様にM₁とM₂のいずれかを選ぶことがわかる
  -- 背理法をつかってmのパートナーがM₁とM₂のいずれでもないと仮定する
  by_contra h
  push_neg at h
  obtain ⟨h1, h2⟩ := h
  set w := (womenBetter M₁ M₂).matching.partnerOfMan m with hw
  have h1' : M₁.matching.partnerOfWoman w ≠ m := by
    intro h
    have : M₁.matching.partnerOfMan m = w := by simp [← h]
    rw [this] at h1
    contradiction
  have h2' : M₂.matching.partnerOfWoman w ≠ m := by
    intro h
    have : M₂.matching.partnerOfMan m = w := by simp [← h]
    rw [this] at h2
    contradiction
  have hw' : (womenBetter M₁ M₂).matching.partnerOfWoman w = m := by simp [hw]
  have h_better := womenBetter_partnerOfWoman M₁ M₂ w
  rw [hw'] at h_better
  have h1'' : ¬ M₁.matching.partnerOfWoman w ≺[w] M₂.matching.partnerOfWoman w := by
    intro h
    simp [h] at h_better
    exact h1' h_better.symm
  simp [h1''] at h_better
  exact h2' h_better.symm

def menWorsePartner
    {smp : SMP n}
    (M₁ M₂ : StableMatching smp)
    (m : smp.Man) : smp.Woman :=
  if M₁.matching.partnerOfMan m ≺[m] M₂.matching.partnerOfMan m then
    M₂.matching.partnerOfMan m
  else
    M₁.matching.partnerOfMan m

/-- womenBetterで男性はM₁とM₂のうち望ましくないパートナーを選ぶ。-/
theorem womenBetterMatching_partnerOfMan
    {smp : SMP n}
    (M₁ M₂ : StableMatching smp) (m : smp.Man) :
    (womenBetter M₁ M₂).matching.partnerOfMan m = menWorsePartner M₁ M₂ m := by
  unfold menWorsePartner

  have either := womenBetter_partnerOfMan_either M₁ M₂ m
  if eq : M₁.matching.partnerOfMan m = M₂.matching.partnerOfMan m then
    simp [eq] at *
    simp [either]
  else
    cases either with
    | inl h =>
      simp [h]
      intro m1_better
      exfalso
      set w := M₁.matching.partnerOfMan m with hw
      have inv_h : (womenBetter M₁ M₂).matching.partnerOfWoman w = m := by simp [← h]
      have h1 : M₁.matching.partnerOfWoman w = m := by simp [hw]
      have h2 : M₂.matching.partnerOfWoman w ≠ m := by
        intro h
        have : M₂.matching.partnerOfMan m = w := by simp [← h]
        rw [this] at eq
        contradiction
      have h3 : m ≺[w] M₂.matching.partnerOfWoman w := by
        -- これはwがM₁のパートナーを選んだことから、M₁のパートナーをM₂のパートナーよりも好むことを意味する
        have := womenBetter_partnerOfWoman M₁ M₂ w
        simp [inv_h, h1] at this
        by_contra contra
        exact h2.symm (this contra)
      -- m1_betterとh3から、M₂においてmとwがblocking pairになることがわかる
      have blocking : M₂.matching.IsBlockingPair m w := ⟨m1_better, h3⟩
      exact M₂.isStable m w blocking
    | inr h =>
      simp [h]
      intro m2_better
      have m2_better' : M₂.matching.partnerOfMan m ≺[m] M₁.matching.partnerOfMan m := by
        have := Man.prefers_total (smp:=smp) m eq
        cases this with
        | inl h' =>
          exfalso
          exact m2_better h'
        | inr h' => exact h'
      exfalso
      set w := M₂.matching.partnerOfMan m with hw
      have inv_h : (womenBetter M₁ M₂).matching.partnerOfWoman w = m := by simp [← h]
      have h1 : M₂.matching.partnerOfWoman w = m := by simp [hw]
      have h2 : M₁.matching.partnerOfWoman w ≠ m := by
        intro h
        have : M₁.matching.partnerOfMan m = w := by simp [← h]
        rw [this] at eq
        contradiction
      have h3 : m ≺[w] M₁.matching.partnerOfWoman w := by
        -- これはwがM₂のパートナーを選んだことから、M₂のパートナーをM₁のパートナーよりも好むことを意味する
        have := womenBetter_partnerOfWoman M₁ M₂ w
        simp [inv_h, h1] at this
        by_contra contra
        have compare : M₁.matching.partnerOfWoman w ≺[w] m := by
          have := Woman.prefers_total (smp:=smp) w h2
          cases this with
          | inl h' => exact h'
          | inr h' =>
            exfalso
            exact contra h'
        exact h2.symm (this compare)
      have blocking : M₁.matching.IsBlockingPair m w := ⟨m2_better', h3⟩
      exact M₁.isStable m w blocking

end Lattice
end SMP
end StableMatching
