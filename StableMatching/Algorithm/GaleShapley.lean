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
