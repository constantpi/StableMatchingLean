import StableMatching.Lattice.PartnerThreshold

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

/-- 被覆辺の終点以下で始点以下でない `SupIrred` 元は一意に存在する。 -/
theorem SMEdge.existsUnique_supIrred (e : SMEdge smp) :
    ∃! j : StableMatching smp, SupIrred j ∧ j ≤ e.target ∧ ¬ j ≤ e.source := by

  -- まず、被覆関係からMとNを取り出す
  set M := e.source
  set N := e.target
  have hmn : M < N := e.lt
  -- M < Nより、ある男性mが存在してM(m) < N(m)となる。lt_iff_le_and_not_eq_manを使う
  obtain ⟨m, h_m⟩ := ((Lattice.lt_iff_le_and_not_eq_man M N).mp hmn).2
  -- その男性mに対して、partnerThresholdを使う
  set w := M.matching.partnerOfMan m with hw
  have hWorse : ∃ P : StableMatching smp, w ≺[m] P.matching.partnerOfMan m := by
    exists N
  set j := Lattice.partnerThreshold m w with hj
  have hjProps : SupIrred j ∧ j ≤ N ∧ ¬ j ≤ M := by
    -- ここに、今書いている j の性質の証明を置く
    constructor
    . exact Lattice.supIrred_partnerThreshold m w (by exists M) (by exists N)
    . constructor
      . exact (Lattice.partnerThreshold_le_iff m w hWorse N).mpr h_m
      .
        rw [hj]
        intro h
        have := (Lattice.partnerThreshold_le_iff m w hWorse M).mp h
        rw [hw] at this
        exact m.prefers_irrefl w this
  refine ⟨j, hjProps, ?_⟩

  intro k kProps
  have le_of_props (a b : StableMatching smp)
      (ha : SupIrred a ∧ a ≤ N ∧ ¬ a ≤ M)
      (hb : SupIrred b ∧ b ≤ N ∧ ¬ b ≤ M) : a ≤ b := by
    have hLt : M < M ⊔ b := by
      apply lt_of_le_of_ne le_sup_left
      intro h
      exact hb.2.2 (sup_eq_left.mp h.symm)
    -- 被覆関係から M ⊔ b = N が従う。
    have hSup : M ⊔ b = N := by
      have hLe : M ⊔ b ≤ N := sup_le e.le hb.2.1
      exact (lt_or_eq_of_le hLe).resolve_left (e.covBy.2 hLt)
    have hDecomp : (a ⊓ M) ⊔ (a ⊓ b) = a := by
      rw [← inf_sup_left, hSup]
      exact inf_eq_left.mpr ha.2.1
    have hInfNe : a ⊓ M ≠ a := by
      intro h
      exact ha.2.2 (inf_eq_left.mp h)
    exact inf_eq_left.mp ((ha.1.2 hDecomp).resolve_left hInfNe)
  exact le_antisymm (le_of_props k j kProps hjProps) (le_of_props j k hjProps kProps)

/-- 被覆辺の終点以下で始点以下でない唯一の `SupIrred` 元。 -/
noncomputable def SMEdge.supIrred (e : SMEdge smp) : StableMatching smp :=
  Classical.choose e.existsUnique_supIrred.exists

/-- 被覆辺に対応する元は `SupIrred` で、終点以下かつ始点以下ではない。 -/
theorem SMEdge.supIrred_spec (e : SMEdge smp) :
    SupIrred e.supIrred ∧ e.supIrred ≤ e.target ∧ ¬ e.supIrred ≤ e.source :=
  Classical.choose_spec e.existsUnique_supIrred.exists

end Rotation
end SMP
end StableMatching
