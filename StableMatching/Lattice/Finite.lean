import StableMatching.Lattice.Distributive
import StableMatching.Algorithm.GaleShapley.StableOutput

namespace StableMatching
namespace SMP
namespace Lattice

noncomputable instance stableMatchingNonempty
    {smp : SMP n} :
    Nonempty (StableMatching smp) :=
  GSState.exists_stable_matching smp

noncomputable instance stableMatchingBoundedOrder
    {smp : SMP n} :
    BoundedOrder (StableMatching smp) :=
  Fintype.toBoundedOrder (StableMatching smp)

theorem bot_is_men_optimal
    (M : StableMatching smp) :
    (⊥ : StableMatching smp) ≤ M :=
  bot_le

theorem top_is_women_optimal
    (M : StableMatching smp) :
    M ≤ (⊤ : StableMatching smp) :=
  le_top

end Lattice
end SMP
end StableMatching
