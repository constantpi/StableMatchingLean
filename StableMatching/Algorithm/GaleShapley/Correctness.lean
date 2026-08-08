import StableMatching.Algorithm.GaleShapley.Termination

namespace StableMatching
namespace SMP
namespace GSState

/-- 提案男性がいなくかつ未婚の男性がいれば彼のnextRank=n-/
theorem nextRank_eq_n_of_noProposingMan_and_unengaged
    {smp : SMP n}
    (s : ValidGSState smp)
    (hno : noProposingMan s)
    (m : smp.Man)
    (hunengaged : ¬ s.state.isEngaged m) :
    s.state.nextRank m = n := by
  -- nextRank mの値とnの大小関係で場合分けをする
  if hnext : s.state.nextRank m < n then
    -- nextRank m < n の場合、mはまだ提案していない女性がいるので、提案男性がいることになる
    unfold noProposingMan at hno
    have hfind : ∃m', s.state.findProposingMan = some m' := by
      -- mが条件を満たしていることを示す
      unfold findProposingMan
      have hmem : m ∈ Man.iterator := by
        cases m with
        | mk i => simp [Man.iterator]
      match hone : List.find? (fun m' => ¬ s.state.isEngaged m' ∧ s.state.nextRank m' < n) Man.iterator with
      | none =>
        rw [List.find?_eq_none] at hone
        have := hone m hmem
        simp [hunengaged, hnext] at this
      | some m' => exists m'
    rw [hno] at hfind
    simp at hfind
  else
    if hnext_eq : s.state.nextRank m = n then
      exact hnext_eq
    else
      omega

/-- 提案男性がいなくかつ未婚の男性がいれば女性は全員既婚-/
theorem allWomenEngaged_of_noProposingMan_and_unengaged
    {smp : SMP n}
    (s : ValidGSState smp)
    (hno : noProposingMan s)
    -- : (∃m : smp.Man, ¬ s.state.isEngaged m) → ∀ w : smp.Woman, ¬ (s.state.engaged w = none) := by
    : (∃m : smp.Man, ¬ s.state.isEngaged m) → ∀ w : smp.Woman, ∃m : smp.Man, s.state.engaged w = some m := by
  intro hunengaged w
  have ⟨m, hm⟩ := hunengaged
  have hasProposed : s.state.hasProposed m w := by
    unfold hasProposed
    have hnext := nextRank_eq_n_of_noProposingMan_and_unengaged s hno m hm
    simp [hnext]
  have hengaged := s.bestProposal m w hasProposed
  match some_m':s.state.engaged w with
  | none =>
    simp [some_m'] at hengaged
  | some m' =>
    exists m'

/-- 提案男性がいないなら男性は全員既婚-/
theorem allMenEngaged_of_noProposingMan
    {smp : SMP n}
    (s : ValidGSState smp)
    (hno : noProposingMan s) :
    ∀ m : smp.Man, s.state.isEngaged m := by
  by_contra h
  push_neg at h
  have allWomenEngaged := allWomenEngaged_of_noProposingMan_and_unengaged s hno h
  -- 女性から男性への写像が作れる
  -- 全女性が婚約しているので、その婚約相手を男性として取り出す
  let partner : smp.Woman → smp.Man := fun w => Classical.choose (allWomenEngaged w)



  -- この写像が単射であることを示す
  have partner_injective : Function.Injective partner := by
    intro w₁ w₂ h
    have := allWomenEngaged w₁
    have ⟨m1, hm1⟩ := this
    have := allWomenEngaged w₂
    have ⟨m2, hm2⟩ := this
    simp [partner, hm1, hm2] at h
    rw [←h] at hm2
    exact s.validEngagement w₁ w₂ m1 hm1 hm2

  -- 濃度が同じであることを使って、単射が全射であることを示す
  have same_card : Finset.card (Finset.univ : Finset smp.Woman) = Finset.card (Finset.univ : Finset smp.Man) := by
    simp [Finset.card_univ]
    rw [smp.card_woman, smp.card_man]

  have partner_bijective : Function.Bijective partner := by
    apply (Fintype.bijective_iff_injective_and_card partner).mpr
    constructor
    · exact partner_injective
    · exact same_card

  have partner_surjective := partner_bijective.right

  -- しかし、未婚の男性がいるので、全射であることに矛盾する
  have ⟨m, hm⟩ := h
  simp [isEngaged] at hm
  have hsurj := partner_surjective m
  unfold partner at hsurj
  have ⟨w, hw⟩ := hsurj
  have m_engaged : s.state.engaged w = some m := by
    have hw_spec := Classical.choose_spec (allWomenEngaged w)
    rw [hw] at hw_spec
    exact hw_spec
  have hmw := hm w
  contradiction

/-- 提案男性がいないなら女性は全員既婚-/
theorem allWomenEngaged_of_noProposingMan
    {smp : SMP n}
    (s : ValidGSState smp)
    (hno : noProposingMan s) :
    ∀ w : smp.Woman, ∃ m : smp.Man, s.state.engaged w = some m := by
  -- まず男性は全員既婚であることを示す
  have allMenEngaged := allMenEngaged_of_noProposingMan s hno
  unfold isEngaged at allMenEngaged
  let m_to_w : smp.Man → smp.Woman := fun m => Classical.choose (allMenEngaged m)
  have m_to_w_injective : Function.Injective m_to_w := by
    intro m₁ m₂ h
    unfold m_to_w at h
    have hspec1 := Classical.choose_spec (allMenEngaged m₁)
    have hspec2 := Classical.choose_spec (allMenEngaged m₂)
    rw [←h] at hspec2
    simp [hspec1] at hspec2
    exact hspec2

  have same_card : Finset.card (Finset.univ : Finset smp.Man) = Finset.card (Finset.univ : Finset smp.Woman) := by
    simp [Finset.card_univ]
    rw [smp.card_man, smp.card_woman]

  have m_to_w_bijective : Function.Bijective m_to_w := by
    apply (Fintype.bijective_iff_injective_and_card m_to_w).mpr
    constructor
    · exact m_to_w_injective
    · exact same_card

  have m_to_w_surjective := m_to_w_bijective.right

  intro w
  have hsurj := m_to_w_surjective w
  have ⟨m, hm⟩ := hsurj
  exists m
  unfold m_to_w at hm
  have hspec := Classical.choose_spec (allMenEngaged m)
  rw [hm] at hspec
  exact hspec


end GSState
end SMP
end StableMatching
