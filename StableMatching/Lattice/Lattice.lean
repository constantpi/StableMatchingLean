import StableMatching.Lattice.Order

namespace StableMatching
namespace SMP
namespace Lattice

theorem menBetter_isGLB
    {smp : SMP n}
    (M₁ M₂ : StableMatching smp) :
    IsGLB {M₁, M₂} (menBetter M₁ M₂) := by
  have h_better1 := menBetterPartner_is_better_or_equal_first M₁ M₂
  have h_better2 := menBetterPartner_is_better_or_equal_second M₁ M₂
  constructor
  .
    intro M hM m
    cases hM with
    | inl hM₁ =>
      rw [hM₁]
      exact h_better1 m
    | inr hM₂ =>
      rw [hM₂]
      exact h_better2 m
  .
    intro M hM m
    simp at hM
    -- menBetterのeigherを使う
    have eigher := menBetterPartner_eq_first_or_second M₁ M₂ m
    cases eigher with
    | inl h_eq =>
      have left := hM.left m
      change M.matching.partnerOfMan m ≼[m] menBetterPartner M₁ M₂ m
      rw [h_eq]
      exact left
    | inr h_eq =>
      have right := hM.right m
      change M.matching.partnerOfMan m ≼[m] menBetterPartner M₁ M₂ m
      rw [h_eq]
      exact right

theorem menWorse_isLUB
    {smp : SMP n}
    (M₁ M₂ : StableMatching smp) :
    IsLUB {M₁, M₂} (womenBetter M₁ M₂) := by
  constructor
  · intro M hM m
    cases hM with
    | inl hM₁ =>
      rw [hM₁, womenBetterMatching_partnerOfMan]
      exact menWorsePartner_is_worse_or_equal_first M₁ M₂ m
    | inr hM₂ =>
      rw [hM₂, womenBetterMatching_partnerOfMan]
      exact menWorsePartner_is_worse_or_equal_second M₁ M₂ m
  · intro M hM m
    simp at hM
    rw [womenBetterMatching_partnerOfMan]
    unfold menWorsePartner
    by_cases h : M₁.matching.partnerOfMan m ≺[m] M₂.matching.partnerOfMan m
    · simp [h]
      exact hM.right m
    · simp [h]
      exact hM.left m

end Lattice
end SMP
end StableMatching
