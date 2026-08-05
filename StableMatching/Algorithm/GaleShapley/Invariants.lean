import StableMatching.Algorithm.GaleShapley.Step

namespace StableMatching
namespace SMP
namespace GSState

/-- 有効なエンゲージメントを表す述語。-/
def ValidEngagement
    {sm : SMP n}
    (s : GSState sm) : Prop :=
  ∀ w₁ w₂ m,
    s.engaged w₁ = some m →
    s.engaged w₂ = some m →
    w₁ = w₂


/-- 提案ステップは有効なエンゲージメントを保持する -/
theorem proposeStep_preserves_validEngagement
    {sm : SMP n}
    (s : GSState sm)
    (m : sm.Man)
    (hm : ¬ s.isEngaged m)
    (hnext : s.nextRank m < n)
    (hvalid : s.ValidEngagement) :
    (proposeStep s m hnext).ValidEngagement := by
  simp [proposeStep, GSState.ValidEngagement]

  set w := s.proposedWoman m hnext with hw
  set changed_engaged := fun w' => if w' = w then some m else s.engaged w' with hchanged
  have changed_is_valid: ∀ w₁ w₂ m',
      changed_engaged w₁ = some m' →
      changed_engaged w₂ = some m' →
      w₁ = w₂ := by
    intro w₁ w₂ m' h₁ h₂
    by_cases hw₁ : w₁ = w
    ·
      simp [hw₁, hchanged] at h₁
      by_cases hw₂ : w₂ = w
      · simp_all
      .
        simp [hw₂, hchanged] at h₂
        exfalso
        apply hm
        simp [GSState.isEngaged, h₁]
        exists w₂
    .
      simp [hw₁, hchanged] at h₁
      by_cases hw₂ : w₂ = w
      · simp [hw₂, hchanged] at h₂
        exfalso
        apply hm
        simp [GSState.isEngaged, h₂]
        exists w₁
      .
        simp [hw₂, hchanged] at h₂
        exact hvalid w₁ w₂ m' h₁ h₂
  match s.engaged w with
  | none =>
    simp [receivesProposal]
    exact changed_is_valid
  | some cur_m =>
    simp [receivesProposal]
    by_cases hpref : m ≺[w] cur_m
    ·
      simp [hpref] at *
      exact changed_is_valid
    .
      simp [hpref] at *
      exact hvalid

/-- 初期状態において有効なエンゲージメントが成立することを示す -/
theorem initial_validEngagement
    {sm : SMP n} :
    (GSState.initial sm).ValidEngagement := by simp [initial, ValidEngagement]

/-- 提案の回数を計算する。Σ_m  (s.nextRank m).val) -/
def totalProposals
    {sm : SMP n}
    (s : GSState sm) : Nat :=
  ∑ m : sm.Man, (s.nextRank m).val


/-- (m, w)が今回の提案ペアでないなら、wに提案したことがある男性集合は変わらない -/
theorem proposeStep_hasProposed_of_ne
    {sm : SMP n}
    (s : GSState sm)
    (m : sm.Man)
    (hnext : s.nextRank m < n)
    (w : sm.Woman)
    (hne : w ≠ s.proposedWoman m hnext)
    : ∀ m': sm.Man, (proposeStep s m hnext).hasProposed m' w ↔ s.hasProposed m' w := by
  intro m'
  unfold proposeStep hasProposed
  if hm : m' = m then
    simp [hm]
    -- #check manRank_injective -- StableMatching.SMP.manRank_injective {n : ℕ} {sm : SMP n} (m : sm.Man) : Function.Injective (manRank m)
    -- #check manRank_womanAtRank -- StableMatching.SMP.manRank_womanAtRank {n : ℕ} {sm : SMP n} (m : sm.Man) (r : Fin n) : manRank m (womanAtRank m r) = r

    have woman_to_rank_inj := manRank_injective m
    -- manRank m w ≠ manRank m (s.proposedWoman m hnext) であることを示す必要がある
    set next_rank_m : Fin n := ⟨s.nextRank m, hnext⟩ with hnext_rank
    have h_proposed_rank : sm.manRank m (s.proposedWoman m hnext) = next_rank_m := by
      simp [proposedWoman]
      exact manRank_womanAtRank m next_rank_m
    have h_ne : sm.manRank m w ≠ next_rank_m := by
      intro h_eq
      rw [← h_proposed_rank] at h_eq
      have h_eq' : w = s.proposedWoman m hnext := woman_to_rank_inj h_eq
      contradiction
    have h_ne_val: (sm.manRank m w).val ≠ next_rank_m.val := by
      intro h_eq
      have h_eq' : sm.manRank m w = next_rank_m := Fin.val_inj.mp h_eq
      contradiction
    set next_rank_m_val := (next_rank_m).val
    set man_rank_m_w_val := (sm.manRank m w).val
    omega
  else
    simp [hm]



/-- 女性が過去に提案してきた男性の中で最良の人と仮の婚約をしている -/
def allWomenEngagedToBestProposal
    {sm : SMP n}
    (s : GSState sm)
    : Prop :=
  -- 各ペア(m, w)について、男性mが女性wに提案したことがある場合、女性wは男性mと仮の婚約をしているか、または女性wは男性mよりも好ましい男性と仮の婚約をしていることを保証する。
  ∀ m: sm.Man, ∀ w: sm.Woman, s.hasProposed m w → match s.engaged w with
    | none => False
    | some cur_m => (m = cur_m ∨ cur_m ≺[w] m)

/-- allWomenEngagedToBestProposalがアルゴリズム中で保持される -/
theorem proposeStep_preserves_allWomenEngagedToBestProposal
    {sm : SMP n}
    (s : GSState sm)
    (m : sm.Man)
    (hnext : s.nextRank m < n)
    (hvalid : s.allWomenEngagedToBestProposal) :
    (proposeStep s m hnext).allWomenEngagedToBestProposal := by
  unfold allWomenEngagedToBestProposal at *
  intro m_1 w new_proposed
  have hvalid_mw := hvalid m_1 w
  set next_rank_m : Fin n := ⟨s.nextRank m, hnext⟩ with hnext_rank
  -- set new_s := proposeStep s m hm hnext with hnew_s
  -- wが提案相手かどうかで場合分けをする
  -- if h_w_is_proposed : w = sm.womanAtRank m next_rank_m then
  if h_w_is_proposed : w = s.proposedWoman m hnext then
    -- wが提案相手の場合、m_1が現在の提案男性mと同じかどうかで場合分けをする
    if h_m_eq : m_1 = m then
      simp [h_m_eq]
      -- m_1が現在の提案男性mと同じ場合
      -- 提案が受け入れられたかどうかで場合分けをする
      if h_accept : receivesProposal w m (s.engaged w) then
        -- 提案が受け入れられた場合
        -- simp [proposeStep, ← h_w_is_proposed, h_accept]
        simp [proposeStep, ← h_w_is_proposed]
        simp [h_accept]
      else
        -- 提案が拒否された場合
        simp [proposeStep, ← h_w_is_proposed]
        simp [h_accept]
        unfold receivesProposal at h_accept
        match engaged:s.engaged w with
        | none =>
          simp [engaged] at h_accept
        | some cur_m =>
          simp [engaged] at h_accept
          simp
          unfold Woman.Prefers at *
          -- womanRank関数がinjectiveであることを用いて m = cur_m ↔ womanRank w m = womanRank w cur_m を示す
          have : m = cur_m ↔ womanRank w m = womanRank w cur_m := by
            constructor
            · intro h_eq
              rw [h_eq]
            · intro h_eq
              exact womanRank_injective w h_eq
          rw [this]
          omega
    else
      -- m_1が現在の提案男性mと異なる場合
      -- まず、sの時点でwがm_1に提案されたことがあることを示す。
      have : s.hasProposed m_1 w := by
        simp [hasProposed]
        simp [hasProposed, proposeStep, h_m_eq] at new_proposed
        exact new_proposed
      have hprev_mw := hvalid_mw this
      match pre_engage:s.engaged w with
      | none =>
        simp [pre_engage] at hprev_mw
      | some prev_m =>
        simp [pre_engage] at hprev_mw
        if h_accept : receivesProposal w m (s.engaged w) then
          -- 提案が受け入れられた場合
          simp [proposeStep, ← h_w_is_proposed]
          simp [h_accept]
          -- unfold receivesProposal at h_accept
          simp [receivesProposal, pre_engage] at h_accept
          right
          -- hprev_mwのorの分解をする
          match hprev_mw with
          | Or.inl h_eq =>
            rw [h_eq]
            exact h_accept
          | Or.inr h_pref =>
            -- Transを使う
            exact Woman.prefers_trans w h_accept h_pref
        else
          -- 提案が拒否された場合
          simp [proposeStep, ← h_w_is_proposed]
          simp [h_accept]
          simp [pre_engage]
          exact hprev_mw
  else
    -- wが提案相手でない場合、wに提案したことがある男性集合は変わらない。
    -- そして現在の相手も変わらない。
    have invariant_engage:= proposeStep_engaged_of_ne s m hnext w h_w_is_proposed
    -- rw [← hnew_s] at invariant_engage
    simp [invariant_engage]
    have hprev_mw := proposeStep_hasProposed_of_ne s m hnext w h_w_is_proposed m_1
    -- rw [← hnew_s] at hprev_mw
    simp [hprev_mw] at new_proposed
    exact hvalid_mw new_proposed

/-- 初期状態において、すべての女性は過去に提案してきた男性の中で最良の人と仮の婚約をしていることを示す -/
theorem initial_allWomenEngagedToBestProposal
    {sm : SMP n} :
    (GSState.initial sm).allWomenEngagedToBestProposal := by simp [initial, allWomenEngagedToBestProposal, hasProposed]

end GSState
end SMP
end StableMatching
