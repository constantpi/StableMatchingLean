import StableMatching.Basic.Stability

namespace StableMatching
namespace SMP

structure GSState (smp : SMP n) where
  /-- 女性の仮の相手-/
  engaged : smp.Woman → Option smp.Man
  /-- 男性が次に提案する女性の順位-/
  nextRank : smp.Man → Fin (n + 1)

namespace GSState

def initial (smp : SMP n) : GSState smp :=
  { engaged := fun _ => none, nextRank := fun _ => 0 }

def isEngaged {smp : SMP n} (s : GSState smp) (m : smp.Man) : Prop :=
  ∃ w, s.engaged w = some m

instance {smp : SMP n} (s : GSState smp) (m : smp.Man) : Decidable (s.isEngaged m) := by
  unfold isEngaged
  infer_instance

def receivesProposal {smp : SMP n} (w : smp.Woman) (m : smp.Man)
    (cur_m : Option smp.Man) : Prop :=
  match cur_m with
  | none => true
  | some cur_m' => m ≺[w] cur_m'

instance {smp : SMP n} (w : smp.Woman) (m : smp.Man) (cur_m : Option smp.Man) :
    Decidable (receivesProposal w m cur_m) := by
  unfold receivesProposal
  match cur_m with
  | none => infer_instance
  | some cur_m' => infer_instance

def hasProposed {smp : SMP n} (s : GSState smp) (m : smp.Man) (w : smp.Woman) : Prop :=
  (s.nextRank m).val > (smp.manRank m w).val

end GSState
end SMP
end StableMatching
