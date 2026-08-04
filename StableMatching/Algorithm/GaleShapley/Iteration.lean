import StableMatching.Algorithm.GaleShapley.Invariants

namespace StableMatching
namespace SMP
namespace GSState

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
