import StableMatching.Rotation.Edge


namespace StableMatching
namespace SMP
namespace Rotation

def SMEdge.IsChangedPair
    (e : SMEdge smp)
    (m : smp.Man)
    (w : smp.Woman) : Prop :=
  e.source.matching.partnerOfMan m = w ∧
  e.target.matching.partnerOfMan m ≠ w

def SMEdge.Equivalent
    (e₁ e₂ : SMEdge smp) : Prop :=
  ∀ m w,
    e₁.IsChangedPair m w ↔
    e₂.IsChangedPair m w

theorem SMEdge.equivalent_refl
    (e : SMEdge smp) :
    e.Equivalent e := by
  intro m w₁
  rfl

theorem SMEdge.equivalent_symm
    {e₁ e₂ : SMEdge smp}
    (h : e₁.Equivalent e₂) :
    e₂.Equivalent e₁ := by
  intro m w₁
  exact Iff.symm (h m w₁)

theorem SMEdge.equivalent_trans
    {e₁ e₂ e₃ : SMEdge smp}
    (h₁₂ : e₁.Equivalent e₂)
    (h₂₃ : e₂.Equivalent e₃) :
    e₁.Equivalent e₃ := by
  intro m w₁
  exact Iff.trans (h₁₂ m w₁) (h₂₃ m w₁)

def SMEdge.setoid (smp : SMP n) : Setoid (SMEdge smp) where
  r := SMEdge.Equivalent
  iseqv := {
    refl := equivalent_refl
    symm := equivalent_symm
    trans := equivalent_trans
  }
end Rotation

def Rotation (smp : SMP n) :=
  Quotient (Rotation.SMEdge.setoid smp)

namespace Rotation

def SMEdge.toRotation
    (e : SMEdge smp) :
    Rotation smp :=
  Quotient.mk (Rotation.SMEdge.setoid smp) e

theorem SMEdge.toRotation_eq_iff
    (e₁ e₂ : SMEdge smp) :
    e₁.toRotation = e₂.toRotation ↔ e₁.Equivalent e₂ := by
  apply Quotient.eq

end Rotation

end SMP
end StableMatching
