import StableMatching.Algorithm.GaleShapley.State

namespace StableMatching
namespace SMP
namespace GSState

def proposedWoman {sm : SMP n} (s : sm.GSState) (m : sm.Man)
    (hnext : s.nextRank m < n) : sm.Woman :=
  let rank : Fin n := ⟨s.nextRank m, hnext⟩
  sm.womanAtRank m rank

def proposeStep {sm : SMP n} (s : sm.GSState) (m : sm.Man)
    (hnext : s.nextRank m < n) : GSState sm :=
  let w := s.proposedWoman m hnext
  let currentEngagement := s.engaged w
  let next : Fin (n + 1) := ⟨(s.nextRank m).val + 1, by omega⟩
  let nextRank := fun m' => if m' = m then next else s.nextRank m'
  let changed_engaged := fun w' => if w' = w then some m else s.engaged w'
  let new_engaged := if receivesProposal w m currentEngagement then changed_engaged else s.engaged
  { engaged := new_engaged, nextRank }

theorem proposeStep_nextRank {sm : SMP n} (s : GSState sm) (m : sm.Man)
    (hnext : s.nextRank m < n) :
    (proposeStep s m hnext).nextRank =
      fun m' => if m' = m then ⟨(s.nextRank m).val + 1, by omega⟩ else s.nextRank m' := by
  simp only [proposeStep]

theorem proposeStep_engaged_of_ne {sm : SMP n} (s : GSState sm) (m : sm.Man)
    (hnext : s.nextRank m < n) (w' : sm.Woman) :
    w' ≠ s.proposedWoman m hnext →
    (proposeStep s m hnext).engaged w' = s.engaged w' := by
  unfold proposeStep
  simp
  intro hw
  set proposed_w := s.proposedWoman m hnext with hproposed_w
  set changed_engaged := fun w' => if w' = proposed_w then some m else s.engaged w' with hchanged
  if h : receivesProposal proposed_w m (s.engaged proposed_w) then
    simp [h, hchanged, hw]
  else
    simp [h]

end GSState
end SMP
end StableMatching
