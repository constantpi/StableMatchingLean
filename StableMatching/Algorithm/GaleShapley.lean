import StableMatching.Basic.Stability

namespace StableMatching
namespace SMP

structure GSState (sm : SMP n) where
  /-- 女性の仮の相手-/
  engaged : sm.Woman → Option sm.Man
  /-- 0 から n までの整数を表す Fin (n + 1) 型を使用して、男性が次に提案する女性の順位を追跡する。-/
  nextRank : sm.Man → Fin (n + 1) --

namespace GSState

def initial (sm : SMP n) : GSState sm :=
  {
    engaged := fun _ => none
    nextRank := fun _ => 0
  }

/-- 有効なエンゲージメントを表す述語。-/
def ValidEngagement
    {sm : SMP n}
    (s : GSState sm) : Prop :=
  ∀ w₁ w₂ m,
    s.engaged w₁ = some m →
    s.engaged w₂ = some m →
    w₁ = w₂

/-- 現在の状態において男性が仮の相手と結婚しているかどうかを判定する。-/
def isEngaged
    {sm : SMP n}
    (s : GSState sm)
    (m : sm.Man) : Prop :=
  ∃ w, s.engaged w = some m

/-- isEngagedは決定可能 -/
instance
    {sm : SMP n}
    (s : GSState sm)
    (m : sm.Man) :
    Decidable (s.isEngaged m) := by
  unfold isEngaged
  infer_instance

/-- 女性が提案を受け取るかどうかを判定する。-/
def receivesProposal
    {sm : SMP n}
    (w : sm.Woman)
    (m : sm.Man)
    (cur_m : Option sm.Man)
    : Prop :=
  match cur_m with
  | none => true -- 女性がまだ誰とも婚約していない場合、提案を受け入れる
  | some cur_m' => m ≺[w] cur_m' -- 女性がすでに婚約している場合、彼女の選好を比較する

instance
    {sm : SMP n}
    (w : sm.Woman)
    (m : sm.Man)
    (cur_m : Option sm.Man) :
    Decidable (receivesProposal w m cur_m) := by
  unfold receivesProposal
  match cur_m with
  | none => infer_instance
  | some cur_m' => infer_instance

/-- 今回の提案相手の女性 -/
def proposedWoman
    {sm : SMP n}
    (s : sm.GSState)
    (m : sm.Man)
    (hnext : s.nextRank m < n)
    :sm.Woman :=
  -- これはn未満なので、Fin n の値として安全に使用できる
  let rank : Fin n := ⟨s.nextRank m, hnext⟩
  sm.womanAtRank m rank

/-- GSアルゴリズムの提案の1ステップ-/
def proposeStep
    {sm : SMP n}
    (s : sm.GSState)
    (m : sm.Man)
    (_hm : ¬ s.isEngaged m) -- この引数は内部では使用されないが、提案する男性がまだ婚約していないことを保証するために必要
    (hnext : s.nextRank m < n) :
    GSState sm :=
  -- 次に提案する女性を取得
  let w := s.proposedWoman m hnext
  let currentEngagement := s.engaged w
  let next : Fin (n + 1) := ⟨(s.nextRank m).val + 1, by omega⟩
  let nextRank := fun m' => if m' = m then next else s.nextRank m'
  let changed_engaged := fun w' => if w' = w then some m else s.engaged w'
  let new_engaged := if receivesProposal w m currentEngagement then changed_engaged else s.engaged
  {
    engaged := new_engaged
    nextRank
  }

/-- 提案をした時にその男性のrankは1増加する-/
theorem proposeStep_nextRank
    {sm : SMP n}
    (s : GSState sm)
    (m : sm.Man)
    (hm : ¬ s.isEngaged m)
    (hnext : s.nextRank m < n) :
    (proposeStep s m hm hnext).nextRank = fun m' => if m' = m then ⟨(s.nextRank m).val + 1, by omega⟩ else s.nextRank m' := by
  simp only [proposeStep]

/-- 提案した男性の nextRank は 1 増える。 -/
theorem proposeStep_nextRank_self
    {sm : SMP n}
    (s : GSState sm)
    (m : sm.Man)
    (hm : ¬ s.isEngaged m)
    (hnext : s.nextRank m < n) :
    ((proposeStep s m hm hnext).nextRank m).val
      = (s.nextRank m).val + 1 := by
  -- proposeStep_nextRank を使用して、次のように書き換える
  have h := proposeStep_nextRank s m hm hnext
  simp [h] -- nextRank の定義を展開

theorem proposeStep_nextRank_of_ne
    {sm : SMP n}
    (s : GSState sm)
    (m : sm.Man)
    (m' : sm.Man)
    (hm : ¬ s.isEngaged m)
    (hnext : s.nextRank m < n)
    (hne : m' ≠ m) :
    ((proposeStep s m hm hnext).nextRank m').val = (s.nextRank m').val := by
  -- proposeStep_nextRank を使用して、次のように書き換える
  have h := proposeStep_nextRank s m hm hnext
  simp [h, hne] -- nextRank の定義を展開

/-- 提案ステップによってengagedは提案対象の女性のみ変更されうる-/
theorem proposeStep_engaged_of_ne
    {sm : SMP n}
    (s : GSState sm)
    (m : sm.Man)
    (hm : ¬ s.isEngaged m)
    (hnext : s.nextRank m < n)
    (w' : sm.Woman)
    : w' ≠ s.proposedWoman m hnext →
    (proposeStep s m hm hnext).engaged w' = s.engaged w' := by
  unfold proposeStep
  simp
  intro hw
  set proposed_w := s.proposedWoman m hnext with hproposed_w
  set changed_engaged := fun w' => if w' = proposed_w then some m else s.engaged w' with hchanged
  if h : receivesProposal proposed_w m (s.engaged proposed_w) then
    -- w' が提案された女性でない場合、engagedは変更されない

    simp [h, hchanged, hw]
  else
    -- 提案を受け入れなかった場合、engagedは変更されない
    simp [h]

/-- 提案ステップは有効なエンゲージメントを保持する -/
theorem proposeStep_preserves_validEngagement
    {sm : SMP n}
    (s : GSState sm)
    (m : sm.Man)
    (hm : ¬ s.isEngaged m)
    (hnext : s.nextRank m < n)
    (hvalid : s.ValidEngagement) :
    (proposeStep s m hm hnext).ValidEngagement := by
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

/-- 提案の回数を計算する。Σ_m  (s.nextRank m).val) -/
def totalProposals
    {sm : SMP n}
    (s : GSState sm) : Nat :=
  ∑ m : sm.Man, (s.nextRank m).val

/-- 提案回数が単調に増加することを示す-/
theorem proposeStep_proposalCount
    {sm : SMP n}
    (s : GSState sm)
    (m : sm.Man)
    (hm : ¬ s.isEngaged m)
    (hnext : s.nextRank m < n) :
    (totalProposals (proposeStep s m hm hnext)) = totalProposals s + 1 := by
  unfold totalProposals
  have next_rank := proposeStep_nextRank s m hm hnext

  have hm_mem : m ∈ (Finset.univ : Finset sm.Man) := by simp only [Finset.mem_univ]
  have hother :
    ∀ x ≠ m,
      ((s.proposeStep m hm hnext).nextRank x).val = (s.nextRank x).val := by
    intro x hne
    simp [next_rank, hne]
  have erase_sum :  ∑ x ∈ Finset.univ.erase m, ↑((s.proposeStep m hm hnext).nextRank x).val = ∑ x ∈ Finset.univ.erase m, ↑(s.nextRank x).val := by
    apply Finset.sum_congr rfl
    intro x hx
    have xne : x ≠ m := by
      simp [Finset.mem_erase] at hx
      exact hx
    simp [next_rank, xne]
  rw [← Finset.sum_erase_add _ _ hm_mem]
  rw [erase_sum]
  simp [next_rank]
  rw [← Finset.sum_erase_add _ _ hm_mem]
  ac_rfl

theorem totalProposals_le
    {sm : SMP n}
    (s : GSState sm) :
    totalProposals s ≤ n * n := by
  unfold totalProposals
  have : ∑ m : sm.Man, (s.nextRank m).val ≤ ∑ m : sm.Man, n := by
    apply Finset.sum_le_sum
    intro m _
    omega
  have sum_n : ∑ m : sm.Man, n = n * n := by
    simp [Finset.sum_const, Finset.card_univ]
    left
    exact sm.card_man
  rw [← sum_n]
  exact this

/-- 現在の状態において(m, w)のペアを受け取って男性mが女性wに提案をしたことがあるかどうかを判定する -/
def hasProposed
    {sm : SMP n}
    (s : GSState sm)
    (m : sm.Man)
    (w : sm.Woman) : Prop :=
  -- 男性mが女性wに提案をしたことがあるかどうかを判定する。ランクを使用して、男性mが次に提案する女性のランクがwのランクよりも大きいかどうかを確認する。
  (s.nextRank m).val > (sm.manRank m w).val

/-- (m, w)が今回の提案ペアでないなら、wに提案したことがある男性集合は変わらない -/
theorem proposeStep_hasProposed_of_ne
    {sm : SMP n}
    (s : GSState sm)
    (m : sm.Man)
    (hm : ¬ s.isEngaged m)
    (hnext : s.nextRank m < n)
    (w : sm.Woman)
    (hne : w ≠ s.proposedWoman m hnext)
    : ∀ m': sm.Man, (proposeStep s m hm hnext).hasProposed m' w ↔ s.hasProposed m' w := by
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
    (hm : ¬ s.isEngaged m)
    (hnext : s.nextRank m < n)
    (hvalid : s.allWomenEngagedToBestProposal) :
    (proposeStep s m hm hnext).allWomenEngagedToBestProposal := by
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
    have invariant_engage:= proposeStep_engaged_of_ne s m hm hnext w h_w_is_proposed
    -- rw [← hnew_s] at invariant_engage
    simp [invariant_engage]
    have hprev_mw := proposeStep_hasProposed_of_ne s m hm hnext w h_w_is_proposed m_1
    -- rw [← hnew_s] at hprev_mw
    simp [hprev_mw] at new_proposed
    exact hvalid_mw new_proposed



/-- 提案する男性を見つける関数。いなければ none を返す。-/
def findProposingMan
    {sm : SMP n}
    (s : GSState sm) :
    -- Option {m : sm.Man // ¬ s.isEngaged m ∧ s.nextRank m < n} :=
    Option sm.Man :=
  Man.iterator.find? (fun m => (¬ s.isEngaged m ∧ s.nextRank m < n))

/-- 提案する男性が見つかる場合、彼はまだ婚約しておらず、次の提案の順位は n 未満であることを保証する。-/
theorem findProposingMan_spec
    {sm : SMP n}
    (s : GSState sm)
    (m : sm.Man)
    (h : s.findProposingMan = some m) :
    ¬ s.isEngaged m ∧ s.nextRank m < n := by
  unfold findProposingMan at h
  have hp := List.find?_some h
  exact of_decide_eq_true hp

end GSState
end SMP
end StableMatching
