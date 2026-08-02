import StableMatching.Basic.Stability

namespace StableMatching
namespace SMP

structure GSState (sm : SMP n) where
  /-- 女性の仮の相手-/
  engaged : sm.Woman → Option sm.Man
  /-- 0 から n までの整数を表す Fin (n + 1) 型を使用して、男性が次に提案する女性の順位を追跡する。-/
  nextRank : sm.Man → Fin (n + 1) --

def GSState.initial (sm : SMP n) : GSState sm :=
  {
    engaged := fun _ => none
    nextRank := fun _ => 0
  }

/-- 有効なエンゲージメントを表す述語。-/
def GSState.ValidEngagement
    {sm : SMP n}
    (s : GSState sm) : Prop :=
  ∀ w₁ w₂ m,
    s.engaged w₁ = some m →
    s.engaged w₂ = some m →
    w₁ = w₂

/-- 現在の状態において男性が仮の相手と結婚しているかどうかを判定する。-/
def GSState.isEngaged
    {sm : SMP n}
    (s : GSState sm)
    (m : sm.Man) : Prop :=
  ∃ w, s.engaged w = some m

/-- GSアルゴリズムの提案の1ステップ-/
def proposeStep
    {sm : SMP n}
    (s : sm.GSState)
    (m : sm.Man)
    (_hm : ¬ s.isEngaged m) -- この引数は内部では使用されないが、提案する男性がまだ婚約していないことを保証するために必要
    (hnext : s.nextRank m < n) :
    GSState sm :=
  -- これはn未満なので、Fin n の値として安全に使用できる
  let rank : Fin n := ⟨s.nextRank m, hnext⟩
  -- 次に提案する女性を取得
  let w := sm.womanAtRank m rank
  let currentEngagement := s.engaged w
  let next : Fin (n + 1) := ⟨(s.nextRank m).val + 1, by omega⟩
  let nextRank := fun m' => if m' = m then next else s.nextRank m'
  let changed_engaged := fun w' => if w' = w then some m else s.engaged w'
  match currentEngagement with
  | none =>
    -- 女性がまだ誰とも婚約していない場合、男性 m と女性 wを婚約させる
    {
      engaged := changed_engaged
      nextRank
    }
  | some cur_m =>
    -- 女性がすでに婚約している場合、彼女の選好を比較する
    if m ≺[w] cur_m then
      -- 女性 w は男性 m を好む場合、彼女は m と婚約し、cur_m は解放される
      {
        engaged := changed_engaged
        nextRank
      }
    else
      -- 女性 w は男性 m' を好む場合、状態は変わらない
      {
        engaged := s.engaged
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
  let w := sm.womanAtRank m ⟨s.nextRank m, hnext⟩
  match s.engaged w with
  | none =>
      simp
  | some cur_m =>
      by_cases hpref : m ≺[w] cur_m
      · simp [w, hpref]
      · simp [w, hpref]

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

  set w := sm.womanAtRank m ⟨s.nextRank m, hnext⟩ with hw
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
    simp
    exact changed_is_valid
  | some cur_m =>
    simp
    by_cases hpref : m ≺[w] cur_m
    ·
      simp [hpref] at *
      exact changed_is_valid
    .
      simp [hpref] at *
      exact hvalid

end SMP
end StableMatching
