import StableMatching.Rotation.Equiv
import StableMatching.Rotation.Elimination


namespace StableMatching
namespace SMP
namespace Rotation

/-- 2つの安定マッチング間で男性mのパートナーが変更されたかどうか -/
def is_changed_partner (M N : StableMatching smp) (m : Man smp) : Prop :=
  M.matching.partnerOfMan m ≠ N.matching.partnerOfMan m

/-- 男性は今のままがよくて女性は変更してほしいと思う片思いペア-/
def is_one_sided_preferred (M : StableMatching smp) (m : Man smp) (w : Woman smp) : Prop :=
  (M.matching.partnerOfMan m ≺[m] w) ∧ (m ≺[w] M.matching.partnerOfWoman w)

/-- 今の安定マッチングにおいて(m, w)が回転の候補となるかどうか -/
def is_exposed_rotation_candidate
    {smp : SMP n}
    (M : StableMatching smp)
    (m : Man smp)
    (w : Woman smp)
    : Prop :=
  is_one_sided_preferred M m w ∧
  -- 上記を満たすwの中で最良
  (∀ w' : Woman smp, is_one_sided_preferred M m w' → (w ≼[m] w'))

/-- 回転の候補のペアを返す-/
theorem exposed_rotation_candidate
    {smp : SMP n}
    (M N : StableMatching smp)
    (horder : M ≤ N)
    (m : Man smp)
    (is_changed : is_changed_partner M N m)
    : ∃ w : Woman smp, (is_exposed_rotation_candidate M m w) ∧ is_changed_partner M N (M.matching.partnerOfWoman w) := by
  set w1 := M.matching.partnerOfMan m with hw1
  set w2 := N.matching.partnerOfMan m with hw2
  have one_sided : is_one_sided_preferred M m w2 := by
    have h1 : w1 ≺[m] w2 := by
      have := horder m
      rw [← hw1, ← hw2] at this
      exact (Man.prefers_iff_prefersOrEqual_and_ne m w1 w2).mpr ⟨this, is_changed⟩
    constructor
    . exact h1
    .
      have := (Lattice.le_iff_women_reverse M N).mp horder w2
      nth_rw 2 [hw2] at this
      simp at this
      apply (Woman.prefers_iff_prefersOrEqual_and_ne w2 m (M.matching.partnerOfWoman w2)).mpr
      constructor
      . exact this
      . intro h_eq
        have : M.matching.partnerOfMan m = N.matching.partnerOfMan m := by
          nth_rw 1 [h_eq]
          simp
          exact hw2
        contradiction

  set candidates := { w : Woman smp | is_one_sided_preferred M m w } with hcandidates
  have w2_in_candidates : w2 ∈ candidates := by simp [hcandidates, one_sided]
  have candidates_nonempty : candidates.Nonempty := by exists w2

  -- 上記を満たすwの中で最良のものを選ぶ
  set w := Function.argminOn (fun w => SMP.manRank m w) candidates candidates_nonempty with hmin
  --wはcandidatesの中に入っている
  have w_in_candidates : w ∈ candidates := Function.argminOn_mem (fun w => SMP.manRank m w) candidates candidates_nonempty
  have one_sided_w : is_one_sided_preferred M m w := by
    simp [hcandidates] at w_in_candidates
    exact w_in_candidates
  have w_is_best : ∀ (w' : smp.Woman), is_one_sided_preferred M m w' → w ≼[m] w' := by
    intro w' h_w'
    have w'_in_candidates : w' ∈ candidates := by
      simp [hcandidates]
      exact h_w'
    -- 最小性をつかう
    have := Function.argminOn_le (fun w => SMP.manRank m w) candidates w'_in_candidates candidates_nonempty
    rw [← hmin] at this
    exact this
  exists w
  constructor
  .
    exact ⟨one_sided_w, w_is_best⟩
  .
    unfold is_changed_partner
    by_contra h_eq
    simp at h_eq
    have w_is_better_than_w2 : w ≼[m] w2 := w_is_best w2 one_sided
    by_cases h_case : w = w2
    .
      nth_rw 1 [h_case] at h_eq
      rw [hw2] at h_eq
      have hmw := N.matching.partnerOfMan_injective m (M.matching.partnerOfWoman w) h_eq
      have h_eq' : w = w1 := by
        simp [hmw] at hw1
        exact hw1.symm
      have := one_sided_w.1
      nth_rw 2 [hmw] at this
      simp at this
    .
      match m.prefers_total h_case with
      | Or.inl h_w_better =>
        apply N.isStable m w
        constructor
        .
          rw [hw2] at h_w_better
          exact h_w_better
        .
          nth_rw 2 [h_eq]
          simp
          exact one_sided_w.2
      | Or.inr h_w2_better =>
        exact (m.prefers_iff_not_prefersOrEqual w2 w).mp h_w2_better w_is_better_than_w2


theorem exists_exposedRotation_between
    {smp : SMP n}
    (M N : StableMatching smp)
    (hMN : M < N) :
    ∃ ρ : ExposedRotation M, ρ.eliminate ≤ N := by
  sorry


end Rotation
end SMP
end StableMatching
