import StableMatching.Basic.Stability

namespace StableMatching
namespace SMP

structure GSState (sm : SMP n) where
  /-- 女性の仮の相手-/
  engaged : sm.Woman → Option sm.Man
  /-- 男性が次に提案する女性の順位-/
  nextRank : sm.Man → Fin (n + 1)

namespace GSState

def initial (sm : SMP n) : GSState sm :=
  { engaged := fun _ => none, nextRank := fun _ => 0 }

def isEngaged {sm : SMP n} (s : GSState sm) (m : sm.Man) : Prop :=
  ∃ w, s.engaged w = some m

instance {sm : SMP n} (s : GSState sm) (m : sm.Man) : Decidable (s.isEngaged m) := by
  unfold isEngaged
  infer_instance

def receivesProposal {sm : SMP n} (w : sm.Woman) (m : sm.Man)
    (cur_m : Option sm.Man) : Prop :=
  match cur_m with
  | none => true
  | some cur_m' => m ≺[w] cur_m'

instance {sm : SMP n} (w : sm.Woman) (m : sm.Man) (cur_m : Option sm.Man) :
    Decidable (receivesProposal w m cur_m) := by
  unfold receivesProposal
  match cur_m with
  | none => infer_instance
  | some cur_m' => infer_instance

def hasProposed {sm : SMP n} (s : GSState sm) (m : sm.Man) (w : sm.Woman) : Prop :=
  (s.nextRank m).val > (sm.manRank m w).val

end GSState
end SMP
end StableMatching
