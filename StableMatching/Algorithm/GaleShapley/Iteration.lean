import StableMatching.Algorithm.GaleShapley.Invariants

namespace StableMatching
namespace SMP
namespace GSState

/-- 提案する男性を見つける関数。いなければ none を返す。-/
def findProposingMan
    {smp : SMP n}
    (s : GSState smp) :
    -- Option {m : smp.Man // ¬ s.isEngaged m ∧ s.nextRank m < n} :=
    Option smp.Man :=
  Man.iterator.find? (fun m => (¬ s.isEngaged m ∧ s.nextRank m < n))

/-- 提案する男性が見つかる場合、彼はまだ婚約しておらず、次の提案の順位は n 未満であることを保証する。-/
theorem findProposingMan_spec
    {smp : SMP n}
    (s : GSState smp)
    (m : smp.Man)
    (h : s.findProposingMan = some m) :
    ¬ s.isEngaged m ∧ s.nextRank m < n := by
  unfold findProposingMan at h
  have hp := List.find?_some h
  exact of_decide_eq_true hp

structure ValidGSState (smp : SMP n) where
  state : GSState smp
  /-- 同じ男性が二人以上と婚約していない -/
  validEngagement : state.ValidEngagement
  /-- 女性は過去に提案してきた男性の中で最良の相手と婚約している-/
  bestProposal : state.allWomenEngagedToBestProposal
  /-- 現在の相手はnextRankよりも低い順位にある -/
  nextRank_gt_engagedRank : state.nextRank_gt_engagedRank

/-- GSアルゴリズムの1ステップ -/
def Step {smp : SMP n} (vs : ValidGSState smp) : ValidGSState smp :=
  let s := vs.state
  match hfind: s.findProposingMan with
  | none =>
    -- もう提案する男性がいない場合、状態は変化しない
    vs
  | some m =>
    -- m が提案をする
    let spec := s.findProposingMan_spec m hfind
    have hm := spec.left -- mは誰とも婚約していない
    have hnext := spec.right -- mはすべての人に申し出をしたわけではない
    have newValidEngagement := proposeStep_preserves_validEngagement (smp:=smp) s m hm hnext vs.validEngagement
    have newbestProposal := proposeStep_preserves_allWomenEngagedToBestProposal (smp:=smp) s m hnext vs.bestProposal
    have newNextRank_gt_engagedRank := proposeStep_preserves_nextRank_gt_engagedRank (smp:=smp) s m hm hnext vs.nextRank_gt_engagedRank
    let newState := s.proposeStep m hnext
    {
      state := newState
      validEngagement := newValidEngagement
      bestProposal := newbestProposal
      nextRank_gt_engagedRank := newNextRank_gt_engagedRank
    }

def GSiteration {smp : SMP n} (vs : ValidGSState smp) (k : ℕ) : ValidGSState smp :=
  -- if k = 0 then
  --   vs
  -- else
  --   let newVS := Step vs
  --   GSiteration newVS (k - 1)
  match k with
  | 0 => vs
  | k + 1 => Step (GSiteration vs k)

/-- GSアルゴリズム本体-/
def GSloop {smp : SMP n} (k : ℕ) : ValidGSState smp :=
  let initial_state := GSState.initial smp
  let initial_validEngagement := initial_validEngagement
  let initial_bestProposal := initial_allWomenEngagedToBestProposal
  let initialvalidState : ValidGSState smp := {
    state := initial_state,
    validEngagement := initial_validEngagement,
    bestProposal := initial_bestProposal,
    nextRank_gt_engagedRank := initial_nextRank_gt_engagedRank
  }
  GSiteration initialvalidState k

end GSState
end SMP
end StableMatching
