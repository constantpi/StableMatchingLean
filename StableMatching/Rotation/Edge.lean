import StableMatching.Lattice.Lattice

namespace StableMatching
namespace SMP
namespace Rotation

structure SMEdge (smp : SMP n) where
  source : StableMatching smp
  target : StableMatching smp
  covBy : CovBy source target

theorem SMEdge.lt (e : SMEdge smp) : e.source < e.target :=
  e.covBy.lt

theorem SMEdge.le (e : SMEdge smp) : e.source ≤ e.target :=
  e.covBy.le

theorem SMEdge.ne (e : SMEdge smp) : e.source ≠ e.target :=
  e.covBy.ne

theorem SMEdge.not_exists_between (e : SMEdge smp) :
    ¬ ∃ M : StableMatching smp, e.source < M ∧ M < e.target := by
  intro h
  obtain ⟨M, h1, h2⟩ := h
  cases e.covBy.eq_or_eq h1.le h2.le with
  | inl h3 => exact h1.ne h3.symm
  | inr h4 => exact h2.ne h4

/-- 被覆辺の両端での相手の間には、その男性の安定相手は存在しない。 -/
theorem SMEdge.not_exists_intermediate_stable_partner
    (e : SMEdge smp) (m : smp.Man) (w : smp.Woman)
    (hsource : e.source.matching.partnerOfMan m ≺[m] w)
    (htarget : w ≺[m] e.target.matching.partnerOfMan m) :
    ¬ ∃ P : StableMatching smp, P.matching.partnerOfMan m = w := by
  rintro ⟨P, hP⟩
  let Q := (e.source ⊔ P) ⊓ e.target
  have hsourceQ : e.source ≤ Q := le_inf le_sup_left e.le
  have hQtarget : Q ≤ e.target := inf_le_right
  have hsup : (e.source ⊔ P).matching.partnerOfMan m = w := by
    rw [Lattice.sup_partnerOfMan, Lattice.menWorsePartner, hP, if_pos hsource]
  have hQ : Q.matching.partnerOfMan m = w := by
    change ((e.source ⊔ P) ⊓ e.target).matching.partnerOfMan m = w
    rw [Lattice.inf_partnerOfMan, Lattice.menBetterPartner, hsup, if_pos htarget]
  apply e.not_exists_between
  refine ⟨Q, lt_of_le_of_ne hsourceQ ?_, lt_of_le_of_ne hQtarget ?_⟩
  · intro h
    rw [h, hQ] at hsource
    exact m.prefers_irrefl w hsource
  · intro h
    rw [← h, hQ] at htarget
    exact m.prefers_irrefl w htarget

end Rotation
end SMP
end StableMatching
