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

def proposeStep
    {sm : SMP n}
    (s : sm.GSState)
    (m : sm.Man)
    (hm : ¬ s.isEngaged m)
    (hnext : s.nextRank m < n) :
    GSState sm :=
  -- これはn未満なので、Fin n の値として安全に使用できる
  let rank : Fin n := ⟨s.nextRank m, hnext⟩
  -- 次に提案する女性を取得
  let w := sm.womanAtRank m rank
  let currentEngagement := s.engaged w
  match currentEngagement with
  | none =>
    -- 女性がまだ誰とも婚約していない場合、男性 m と女性 wを婚約させる
    {
      engaged := fun w' => if w' = w then some m else s.engaged w'
      nextRank := fun m' => if m' = m then s.nextRank m + 1 else s.nextRank m'
    }
  | some m' =>
    -- 女性がすでに婚約している場合、彼女の選好を比較する
    if m ≺[w] m' then
      -- 女性 w は男性 m を好む場合、彼女は m と婚約し、m' は解放される
      {
        engaged := fun w' => if w' = w then some m else s.engaged w'
        nextRank := fun m'' => if m'' = m then s.nextRank m + 1 else s.nextRank m''
      }
    else
      -- 女性 w は男性 m' を好む場合、状態は変わらない
      {
        engaged := s.engaged
        nextRank := fun m'' => if m'' = m then s.nextRank m + 1 else s.nextRank m''
      }

end SMP
end StableMatching
