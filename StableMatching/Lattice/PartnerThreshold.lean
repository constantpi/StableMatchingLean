import Mathlib.Order.Irreducible
import StableMatching.Lattice.Finite

namespace StableMatching
namespace SMP
namespace Lattice

variable {smp : SMP n}

/-- `m` の相手が `w` より悪い安定マッチング全体の meet。 -/
noncomputable def partnerThreshold (m : smp.Man) (w : smp.Woman) : StableMatching smp :=
  ((Finset.univ: Finset (StableMatching smp)).filter fun P => w ≺[m] (P.matching.partnerOfMan m)).inf id

/-- `m` の相手が `w` より悪い安定マッチングが存在するなら、境界元はそれらの最小元。 -/
theorem isLeast_partnerThreshold
    (m : smp.Man) (w : smp.Woman)
    (hWorse : ∃ P : StableMatching smp, w ≺[m] P.matching.partnerOfMan m) :
    IsLeast {P : StableMatching smp | w ≺[m] P.matching.partnerOfMan m}
      (partnerThreshold m w) := by
  unfold partnerThreshold
  constructor
  · refine Finset.inf_mem {P : StableMatching smp | w ≺[m] P.matching.partnerOfMan m}
      ?_ ?_ _ id ?_
    · obtain ⟨P, hP⟩ := hWorse
      exact lt_of_lt_of_le hP ((top_is_women_optimal P) m)
    · intro P hP Q hQ
      change w ≺[m] (P ⊓ Q).matching.partnerOfMan m
      rw [inf_partnerOfMan, menBetterPartner]
      split
      · exact hP
      · exact hQ
    · intro P hP
      exact (Finset.mem_filter.mp hP).2
  · intro P hP
    apply Finset.inf_le
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hP⟩

/-- より悪い安定相手が存在するなら、境界元以上であることと `m` の相手が `w` より悪いことは同値。 -/
theorem partnerThreshold_le_iff
    (m : smp.Man) (w : smp.Woman)
    (hWorse : ∃ P : StableMatching smp, w ≺[m] P.matching.partnerOfMan m)
    (P : StableMatching smp) :
    partnerThreshold m w ≤ P ↔ w ≺[m] P.matching.partnerOfMan m := by
  have hLeast := isLeast_partnerThreshold m w hWorse
  constructor
  · intro h
    exact lt_of_lt_of_le hLeast.1 (h m)
  · intro h
    exact hLeast.2 h

/-- `w` が `m` の安定相手で、さらに悪い安定相手も存在するなら、境界元は `SupIrred`。 -/
theorem supIrred_partnerThreshold
    (m : smp.Man) (w : smp.Woman)
    (hStable : ∃ P : StableMatching smp, P.matching.partnerOfMan m = w)
    (hWorse : ∃ P : StableMatching smp, w ≺[m] P.matching.partnerOfMan m) :
    SupIrred (partnerThreshold m w) := by
  have hLeast := isLeast_partnerThreshold m w hWorse
  constructor
  · rw [isMin_iff_eq_bot]
    intro hBot
    obtain ⟨R, hR⟩ := hStable
    have h := (bot_is_men_optimal R) m
    rw [hR, ← hBot] at h
    exact (m.prefersOrEqual_iff_not_prefers _ _).mp h hLeast.1
  · intro P Q hSup
    have h : w ≺[m] (P ⊔ Q).matching.partnerOfMan m := by
      rw [hSup]
      exact hLeast.1
    rw [sup_partnerOfMan, menWorsePartner] at h
    split at h
    · exact Or.inr (le_antisymm (le_sup_right.trans_eq hSup) (hLeast.2 h))
    · exact Or.inl (le_antisymm (le_sup_left.trans_eq hSup) (hLeast.2 h))

end Lattice
end SMP
end StableMatching
