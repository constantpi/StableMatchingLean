import StableMatching.Rotation.Edge


namespace StableMatching
namespace SMP
namespace Rotation

def SMEdge.IsChange
    (e : SMEdge smp)
    (m : smp.Man)
    (w₁ w₂ : smp.Woman) : Prop :=
  e.source.matching.partnerOfMan m = w₁ ∧
  e.target.matching.partnerOfMan m = w₂ ∧
  w₁ ≠ w₂

def SMEdge.Equivalent
    (e₁ e₂ : SMEdge smp) : Prop :=
  ∀ m w₁ w₂,
    e₁.IsChange m w₁ w₂ ↔
    e₂.IsChange m w₁ w₂

theorem SMEdge.equivalent_refl
    (e : SMEdge smp) :
    e.Equivalent e := by
  intro m w₁ w₂
  rfl

theorem SMEdge.equivalent_symm
    {e₁ e₂ : SMEdge smp}
    (h : e₁.Equivalent e₂) :
    e₂.Equivalent e₁ := by
  intro m w₁ w₂
  exact Iff.symm (h m w₁ w₂)

theorem SMEdge.equivalent_trans
    {e₁ e₂ e₃ : SMEdge smp}
    (h₁₂ : e₁.Equivalent e₂)
    (h₂₃ : e₂.Equivalent e₃) :
    e₁.Equivalent e₃ := by
  intro m w₁ w₂
  exact Iff.trans (h₁₂ m w₁ w₂) (h₂₃ m w₁ w₂)

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
