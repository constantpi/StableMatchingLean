import StableMatching.Algorithm.GaleShapley.MatchingOutput

namespace StableMatching
namespace SMP
namespace GSState

/-- 提案男性がいないならマッチングは安定である-/
theorem stable_of_noProposingMan
    {sm : SMP n}
    (s : ValidGSState sm)
    (hno : noProposingMan s) :
    (matching_of_noProposingMan s hno).IsStable := by
  set matching := matching_of_noProposingMan s hno with hmatching
  unfold Matching.IsStable
  intro m w blocking
  unfold Matching.IsBlockingPair at blocking
  set m_partner := matching.partnerOfMan m with hm_partner
  set w_partner := matching.partnerOfWoman w with hw_partner
  have hm_engaged : s.state.engaged m_partner = some m := engaged_of_matched_partner_of_man s hno m m_partner rfl
  have hw_engaged : s.state.engaged w = some w_partner := engaged_of_matched_partner_of_woman s hno w_partner w rfl
  have w_nextRank := s.nextRank_gt_engagedRank m m_partner hm_engaged
  -- ここまでからmはwに対して提案をしていることがわかる
  have mProposed_w : s.state.hasProposed m w := by
    unfold hasProposed
    have := blocking.left
    unfold Man.Prefers at this
    omega
  have w_bestproposal := s.bestProposal m w mProposed_w
  simp [hw_engaged] at w_bestproposal
  unfold Woman.Prefers Woman.PrefersOrEqual at *
  omega

/-- GaleShapleyアルゴリズム-/
def GaleShapley (sm : SMP n) : StableMatching sm :=
  let s : ValidGSState sm := GSloop (n * n + 1)
  have hno : noProposingMan s := GSloop_terminates_at_n2_plus_1
  let matching := matching_of_noProposingMan s hno
  have hstable : matching.IsStable := stable_of_noProposingMan s hno
  { matching := matching, isStable := hstable }

/-- 安定マッチングの存在性-/
theorem exists_stable_matching (sm : SMP n) : Nonempty (StableMatching sm) :=
  ⟨GaleShapley sm⟩

end GSState
end SMP
end StableMatching
