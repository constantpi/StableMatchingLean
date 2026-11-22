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

/-- 被覆辺に対応する元は、その変更前ペアの境界元に等しい。 -/
theorem SMEdge.supIrred_eq_partnerThreshold
    (e : SMEdge smp) {m : smp.Man} {w : smp.Woman}
    (h : e.IsChangedPair m w) :
    e.supIrred = Lattice.partnerThreshold m w := by
  obtain ⟨hSource, hTarget⟩ := h
  have hLe := e.le m
  rw [hSource] at hLe
  have hPref : w ≺[m] e.target.matching.partnerOfMan m :=
    (m.prefers_iff_prefersOrEqual_and_ne _ _).mpr ⟨hLe, hTarget.symm⟩
  have hWorse : ∃ P : StableMatching smp, w ≺[m] P.matching.partnerOfMan m := by
    exists e.target

  refine e.existsUnique_supIrred.unique e.supIrred_spec ⟨?_, ?_, ?_⟩
  · exact Lattice.supIrred_partnerThreshold m w ⟨e.source, hSource⟩ hWorse
  · exact (Lattice.partnerThreshold_le_iff m w hWorse e.target).mpr hPref
  · intro hLeSource
    have hPrefSource := (Lattice.partnerThreshold_le_iff m w hWorse e.source).mp hLeSource
    rw [hSource] at hPrefSource
    exact m.prefers_irrefl w hPrefSource

/-- 安定相手の境界元が被覆辺に対応する元と等しければ、そのペアは変更前ペアである。 -/
theorem SMEdge.isChangedPair_of_supIrred_eq_partnerThreshold
    (e : SMEdge smp) {m : smp.Man} {w : smp.Woman}
    (hStable : ∃ P : StableMatching smp, P.matching.partnerOfMan m = w)
    (hWorse : ∃ P : StableMatching smp, w ≺[m] P.matching.partnerOfMan m)
    (h : e.supIrred = Lattice.partnerThreshold m w) : e.IsChangedPair m w := by
  obtain ⟨hLeTarget, hNotLeSource⟩ := (e.supIrred_spec).2
  rw [h] at hLeTarget hNotLeSource
  have htarget := (Lattice.partnerThreshold_le_iff m w hWorse e.target).mp hLeTarget
  have hsource : e.source.matching.partnerOfMan m ≼[m] w := by
    apply (m.prefersOrEqual_iff_not_prefers _ _).mpr
    intro hlt
    exact hNotLeSource ((Lattice.partnerThreshold_le_iff m w hWorse e.source).mpr hlt)
  constructor
  · by_contra hne
    have hlt := (m.prefers_iff_prefersOrEqual_and_ne _ _).mpr ⟨hsource, hne⟩
    exact e.not_exists_intermediate_stable_partner m w hlt htarget hStable
  · intro heq
    rw [heq] at htarget
    exact m.prefers_irrefl w htarget

/-- 変更前ペアの集合が一致する被覆辺には、同じ `SupIrred` 元が対応する。 -/
theorem SMEdge.supIrred_eq_of_equivalent
    {e₁ e₂ : SMEdge smp} (h : e₁.Equivalent e₂) : e₁.supIrred = e₂.supIrred := by
  obtain ⟨m, hm⟩ := ((Lattice.lt_iff_le_and_not_eq_man e₁.source e₁.target).mp e₁.lt).2
  let w := e₁.source.matching.partnerOfMan m
  have hChanged : e₁.IsChangedPair m w :=
    ⟨rfl, ((m.prefers_iff_prefersOrEqual_and_ne _ _).mp hm).2.symm⟩
  have he1 := e₁.supIrred_eq_partnerThreshold hChanged
  have := (h m w).mp hChanged
  have he2 := e₂.supIrred_eq_partnerThreshold this
  rw [he1, he2]

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

/-- 回転を、代表する被覆辺に対応する `SupIrred` 元に写す。 -/
noncomputable def toSupIrred : Rotation smp → {j : StableMatching smp // SupIrred j} :=
  Quotient.lift
    (fun e : SMEdge smp => ⟨e.supIrred, e.supIrred_spec.1⟩)
    (fun _ _ h => Subtype.ext (SMEdge.supIrred_eq_of_equivalent h))

/-- 回転から `SupIrred` 元への写像は単射である。 -/
theorem toSupIrred_injective {smp : SMP n} :
    Function.Injective (toSupIrred (smp := smp)) := by
  intro r₁ r₂
  refine Quotient.inductionOn₂ r₁ r₂ ?_
  intro e₁ e₂ h
  simp [toSupIrred] at h
  change e₁.toRotation = e₂.toRotation
  apply (SMEdge.toRotation_eq_iff e₁ e₂).mpr
  unfold SMEdge.Equivalent
  intro m w
  constructor
  . intro hchange
    have := SMEdge.supIrred_eq_partnerThreshold e₁ hchange
    rw [h] at this
    have hstable : ∃ P : StableMatching smp, P.matching.partnerOfMan m = w := by
      exists e₁.source
      exact hchange.1
    have hWorse : ∃ P : StableMatching smp, w ≺[m] P.matching.partnerOfMan m := by
      exists e₁.target
      have hstneq := hchange.2
      rw [← hchange.1] at *
      have hstle:= e₁.le m
      exact (m.prefers_iff_prefersOrEqual_and_ne _ _).mpr ⟨hstle, hstneq.symm⟩
    exact SMEdge.isChangedPair_of_supIrred_eq_partnerThreshold e₂ hstable hWorse this
  .
    intro hchange
    have := SMEdge.supIrred_eq_partnerThreshold e₂ hchange
    rw [← h] at this
    have hstable : ∃ P : StableMatching smp, P.matching.partnerOfMan m = w := by
      exists e₂.source
      exact hchange.1
    have hWorse : ∃ P : StableMatching smp, w ≺[m] P.matching.partnerOfMan m := by
      exists e₂.target
      have hstneq := hchange.2
      rw [← hchange.1] at *
      have hstle:= e₂.le m
      exact (m.prefers_iff_prefersOrEqual_and_ne _ _).mpr ⟨hstle, hstneq.symm⟩
    exact SMEdge.isChangedPair_of_supIrred_eq_partnerThreshold e₁ hstable hWorse this

/-- 回転から `SupIrred` 元への写像は全射である。 -/
theorem toSupIrred_surjective {smp : SMP n} :
    Function.Surjective (toSupIrred (smp := smp)) := by
  intro j'
  set j := j'.val
  have hSupIrred : SupIrred j := j'.property
  have h_not_bot := hSupIrred.1
  -- jより小さい要素を集めて、その中で極大元を取ると、jに対応する被覆辺が得られる。
  let S := {P : StableMatching smp | P < j}
  have hS_nonempty : S.Nonempty := by
    change ∃ P : StableMatching smp, P < j
    exact not_isMin_iff.mp h_not_bot
  -- 非空であり、有限集合であるため、極大元が存在する。
  have hS_finite : S.Finite := S.toFinite
  obtain ⟨M, hM_in_S, hM_max⟩ := hS_finite.exists_maximal hS_nonempty
  simp at hM_max
  -- Mとjが被覆関係にあることを示す。
  have hM_lt_j : M ⋖ j := by
    refine ⟨ hM_in_S, ?_ ⟩
    intro c hMc hcj
    have hc_in_S : c ∈ S := hcj
    have := hM_max hc_in_S hMc.le
    -- M < c と C ≤ M から矛盾が生じる。
    exact not_le_of_gt hMc this
  let e := SMEdge.mk M j hM_lt_j
  exists e.toRotation
  apply Subtype.ext
  change e.supIrred = j
  have he_uniq := e.existsUnique_supIrred
  have he_sqec := e.supIrred_spec
  -- SupIrred jはすでに証明されているので、残りの2つの条件を示す
  have : SupIrred j ∧ j ≤ e.target ∧ ¬(j ≤ e.source) := by
    refine ⟨hSupIrred, ?_, ?_⟩
    . rfl
    .
      simp [e]
      exact not_le_of_gt hM_lt_j.lt
  exact he_uniq.unique he_sqec this

/-- 回転と安定マッチングの `SupIrred` 元の間の全単射。 -/
noncomputable def equivSupIrred {smp : SMP n} :
    Rotation smp ≃ {j : StableMatching smp // SupIrred j} :=
  Equiv.ofBijective (toSupIrred (smp := smp))
    ⟨toSupIrred_injective, toSupIrred_surjective⟩

end Rotation
end SMP
end StableMatching
