import StableMatching.Lattice.Order

namespace StableMatching
namespace SMP
namespace Rotation

def cycleNext {k : Nat} (hk : 1 < k) (i : Fin k) : Fin k :=
  have h1 : 0 < k := by omega
  ⟨(i.val + 1) % k, Nat.mod_lt (i.val + 1) h1⟩

def cyclePrev {k : Nat} (hk : 1 < k) (i : Fin k) : Fin k :=
  have h1 : 0 < k := by omega
  ⟨(i.val + k - 1) % k, Nat.mod_lt (i.val + k - 1) h1⟩

structure ExposedRotation (smp : SMP n) where
  M : StableMatching smp
  k : Nat
  hk : 1 < k
  man : Fin k → smp.Man
  woman : Fin k → smp.Woman
  man_injective : Function.Injective man
  matched : ∀ i, M.matching.partnerOfMan (man i) = woman i
  movesDown :∀ i, woman i ≺[man i] woman (cycleNext hk i)
  nextAccepts : ∀ i, man (cyclePrev hk i) ≺[woman i] man i
  nextIsBest : ∀ i w,
    (woman i ≺[man i] w) → (man i ≺[w] M.matching.partnerOfWoman w) → woman (cycleNext hk i) ≼[man i] w

def ExposedRotation.Equivalent
    (ρ₁ ρ₂ : ExposedRotation smp) : Prop :=
  ∀ m w,
    (∃ i, m = ρ₁.man i ∧ w = ρ₁.woman i) ↔ (∃ i, m = ρ₂.man i ∧ w = ρ₂.woman i)

theorem ExposedRotation.Equivalent.refl
    (ρ : ExposedRotation smp) :
    ρ.Equivalent ρ := by
  intro m w
  rfl

theorem ExposedRotation.Equivalent.symm
    {ρ₁ ρ₂ : ExposedRotation smp}
    (h : ρ₁.Equivalent ρ₂) :
    ρ₂.Equivalent ρ₁ := by
  intro m w
  rw [h]

theorem ExposedRotation.Equivalent.trans
    {ρ₁ ρ₂ ρ₃ : ExposedRotation smp}
    (h₁₂ : ρ₁.Equivalent ρ₂)
    (h₂₃ : ρ₂.Equivalent ρ₃) :
    ρ₁.Equivalent ρ₃ := by
  intro m w
  rw [h₁₂, h₂₃]

def ExposedRotation.setoid (smp : SMP n) : Setoid (ExposedRotation smp) where
  r := ExposedRotation.Equivalent
  iseqv := ⟨ExposedRotation.Equivalent.refl, ExposedRotation.Equivalent.symm, ExposedRotation.Equivalent.trans⟩

/-- ExposedRotationを変更するペアのみに着目する同値関係で割ったもの -/
def ExposedRotationQuotient (smp : SMP n) : Type :=
  Quotient (ExposedRotation.setoid smp)

end Rotation
end SMP
end StableMatching
