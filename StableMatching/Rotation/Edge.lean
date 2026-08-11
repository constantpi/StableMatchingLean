import StableMatching.Lattice.Order

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

end Rotation
end SMP
end StableMatching
