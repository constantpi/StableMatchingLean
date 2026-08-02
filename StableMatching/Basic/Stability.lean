import StableMatching.Basic.Matching

namespace StableMatching
namespace SMP

namespace Matching

/--
`(m, w)` が matching `M` の blocking pair であること。
-/
def IsBlockingPair
    {sm : SMP n}
    (M : sm.Matching)
    (m : sm.Man)
    (w : sm.Woman) : Prop :=
  (w ≺[m] M.partnerOfMan m) ∧ (m ≺[w] M.partnerOfWoman w)

/--
matching `M` が安定であること。
-/
def IsStable
    {sm : SMP n}
    (M : sm.Matching) : Prop :=
  ∀ m w, ¬ M.IsBlockingPair m w

end Matching

/--
問題 `sm` の stable matching。
-/
def StableMatching (sm : SMP n) :=
  {M : sm.Matching // M.IsStable}

end SMP
end StableMatching
