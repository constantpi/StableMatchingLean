import StableMatching.Basic.Matching

namespace StableMatching
namespace SMP

namespace Matching

/--
`(m, w)` が matching `M` の blocking pair であること。
-/
def IsBlockingPair
    {smp : SMP n}
    (M : smp.Matching)
    (m : smp.Man)
    (w : smp.Woman) : Prop :=
  (w ≺[m] M.partnerOfMan m) ∧ (m ≺[w] M.partnerOfWoman w)

/--
matching `M` が安定であること。
-/
def IsStable
    {smp : SMP n}
    (M : smp.Matching) : Prop :=
  ∀ m w, ¬ M.IsBlockingPair m w

end Matching

/--
問題 `smp` の stable matching。
-/
structure StableMatching (smp : SMP n) where
  matching : smp.Matching
  isStable : matching.IsStable


end SMP
end StableMatching
