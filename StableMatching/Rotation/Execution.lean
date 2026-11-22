import StableMatching.Rotation.Birkhoff
import StableMatching.Rotation.DefEquality

namespace StableMatching
namespace SMP
namespace Rotation

/-- `rs` が安定マッチング `M` から `N` への合法な回転除去列であること。 -/
inductive IsEliminationSequence {smp : SMP n} :
    StableMatching smp → List (Rotation smp) → StableMatching smp → Prop where
  | nil (M : StableMatching smp) :
      IsEliminationSequence M [] M
  | cons {rs : List (Rotation smp)} {N : StableMatching smp}
      (τ : ExposedRotation smp)
      (hTail : IsEliminationSequence τ.eliminate rs N) :
      IsEliminationSequence τ.M (τ.toRotation :: rs) N

/-- `rs` が `M` から `N` への合法な回転除去の取り消し列であること。 -/
inductive IsUndoSequence {smp : SMP n} :
    StableMatching smp → List (Rotation smp) → StableMatching smp → Prop where
  | nil (M : StableMatching smp) :
      IsUndoSequence M [] M
  | cons {rs : List (Rotation smp)} {N : StableMatching smp}
      (τ : ExposedRotation smp)
      (hTail : IsUndoSequence τ.M rs N) :
      IsUndoSequence τ.eliminate (τ.toRotation :: rs) N

/-- 合法な回転除去列を逆順に取り消すと、元の安定マッチングに戻る。 -/
theorem IsEliminationSequence.reverse_isUndoSequence {smp : SMP n}
    {M N : StableMatching smp} {rs : List (Rotation smp)}
    (h : IsEliminationSequence M rs N) :
    IsUndoSequence N rs.reverse M := by
  have appendUndo {A B C : StableMatching smp} {xs ys : List (Rotation smp)}
      (hPrefix : IsUndoSequence A xs B) (hSuffix : IsUndoSequence B ys C) :
      IsUndoSequence A (xs ++ ys) C := by
    revert hSuffix
    induction hPrefix with
    | nil _ =>
        intro hSuffix
        exact hSuffix
    | cons τ _ ih =>
        intro hSuffix
        exact IsUndoSequence.cons τ (ih hSuffix)
  induction h with
  | nil M =>
      exact IsUndoSequence.nil M
  | cons τ _ ih =>
      rw [List.reverse_cons]
      exact appendUndo ih (IsUndoSequence.cons τ (IsUndoSequence.nil τ.M))

/-- 下方閉集合への回転の1要素追加は、対応する露出回転の除去として実現できる。 -/
theorem ExposedRotation.exists_of_lowerSet_insert {smp : SMP n}
    (D D' : LowerSet (Rotation smp)) (ρ : Rotation smp)
    (hρ : ρ ∉ D)
    (hInsert : (D' : Set (Rotation smp)) = insert ρ (D : Set (Rotation smp))) :
    ∃ τ : ExposedRotation smp,
      τ.M = StableMatching.ofRotationLowerSet D ∧
      τ.eliminate = StableMatching.ofRotationLowerSet D' ∧
      τ.toRotation = ρ := by
  obtain ⟨e, hSource, hTarget, hLabel⟩ := SMEdge.exists_of_lowerSet_insert D D' ρ hρ hInsert
  obtain ⟨τ, hM, hEliminate⟩ := ExposedRotation.exists_exposedRotation e
  refine ⟨τ, hM.trans hSource, hEliminate.trans hTarget, ?_⟩
  have hEquivalent : τ.toSMEdge.Equivalent e := by
    intro m w
    simp only [SMEdge.IsChangedPair, ExposedRotation.toSMEdge, hM, hEliminate]
  exact ((SMEdge.toRotation_eq_iff τ.toSMEdge e).mpr hEquivalent).trans hLabel

/-- 線形拡張の接頭部分を基準の下方閉集合に加えても、下方閉集合になる。 -/
theorem isLowerSet_union_take_of_linearExtension {smp : SMP n}
    (D D' : LowerSet (Rotation smp)) (rs : List (Rotation smp))
    (hMem : ∀ ρ : Rotation smp, ρ ∈ rs ↔ ρ ∈ D' ∧ ρ ∉ D)
    (hOrder : rs.Pairwise (fun ρ σ => ¬ σ ≤ ρ)) (k : ℕ) :
    IsLowerSet ((D : Set (Rotation smp)) ∪ {ρ | ρ ∈ rs.take k}) := by
  intro ρ σ hσρ hρ
  change ρ ∈ D ∨ ρ ∈ rs.take k at hρ
  change σ ∈ D ∨ σ ∈ rs.take k
  rcases hρ with hρInD | hρTake
  · exact Or.inl (D.lower hσρ hρInD)
  · have hρD' := ((hMem ρ).mp ((List.take_sublist k rs).subset hρTake)).1
    have hσD' := D'.lower hσρ hρD'
    by_cases hσD : σ ∈ D
    · exact Or.inl hσD
    · have hσList := (hMem σ).mpr ⟨hσD', hσD⟩
      rw [← List.take_append_drop k rs, List.mem_append] at hσList
      rcases hσList with hσTake | hσDrop
      · exact Or.inr hσTake
      · have hSplitOrder := hOrder
        rw [← List.take_append_drop k rs] at hSplitOrder
        exact False.elim ((List.pairwise_append.mp hSplitOrder).2.2 ρ hρTake σ hσDrop hσρ)

/-- 下方閉集合の差の線形拡張は、対応する安定マッチング間の合法な回転除去列である。 -/
theorem isEliminationSequence_of_linearExtension {smp : SMP n}
    (D D' : LowerSet (Rotation smp)) (rs : List (Rotation smp))
    (hSubset : D ≤ D')
    (hMem : ∀ ρ : Rotation smp, ρ ∈ rs ↔ ρ ∈ D' ∧ ρ ∉ D)
    (hOrder : rs.Pairwise (fun ρ σ => ¬ σ ≤ ρ)) :
    IsEliminationSequence
      (StableMatching.ofRotationLowerSet D) rs
      (StableMatching.ofRotationLowerSet D') := by
  induction rs generalizing D with
  | nil =>
      have hEq : D = D' := by
        apply le_antisymm hSubset
        intro ρ hρD'
        by_contra hρNotInD
        exact List.not_mem_nil ((hMem ρ).mpr ⟨hρD', hρNotInD⟩)
      rw [hEq]
      exact IsEliminationSequence.nil _
  | cons ρ rs ih =>
      have hρ := (hMem ρ).mp List.mem_cons_self
      have hLower : IsLowerSet (insert ρ (D : Set (Rotation smp))) := by
        have hPrefix := isLowerSet_union_take_of_linearExtension D D' (ρ :: rs) hMem hOrder 1
        change IsLowerSet ((D : Set (Rotation smp)) ∪ {σ | σ ∈ [ρ]}) at hPrefix
        simpa only [List.mem_singleton, Set.setOf_eq_eq_singleton, Set.union_singleton] using hPrefix
      let E : LowerSet (Rotation smp) := ⟨insert ρ (D : Set (Rotation smp)), hLower⟩
      have hESubset : E ≤ D' := by
        intro σ hσ
        change σ ∈ insert ρ (D : Set (Rotation smp)) at hσ
        rcases Set.mem_insert_iff.mp hσ with rfl | hσD
        · exact hρ.1
        · exact hSubset hσD
      have hConsOrder := List.pairwise_cons.mp hOrder
      have hTailMem : ∀ σ : Rotation smp, σ ∈ rs ↔ σ ∈ D' ∧ σ ∉ E := by
        intro σ
        change σ ∈ rs ↔ σ ∈ D' ∧ σ ∉ insert ρ (D : Set (Rotation smp))
        rw [Set.mem_insert_iff, not_or]
        constructor
        · intro hσ
          have hσDiff := (hMem σ).mp (List.mem_cons_of_mem ρ hσ)
          exact ⟨hσDiff.1, fun hEq => hConsOrder.1 σ hσ (le_of_eq hEq), hσDiff.2⟩
        · rintro ⟨hσD', hNe, hσNotInD⟩
          exact (List.mem_cons.mp ((hMem σ).mpr ⟨hσD', hσNotInD⟩)).resolve_left hNe
      obtain ⟨τ, hSource, hEliminate, hLabel⟩ :=
        ExposedRotation.exists_of_lowerSet_insert D E ρ hρ.2 rfl
      have hTail := ih E hESubset hTailMem hConsOrder.2
      rw [← hEliminate] at hTail
      rw [← hSource, ← hLabel]
      exact IsEliminationSequence.cons τ hTail

/-- 合法な回転除去列は、両端の下方閉集合の差の線形拡張である。 -/
theorem IsEliminationSequence.linearExtension {smp : SMP n}
    {M N : StableMatching smp} {rs : List (Rotation smp)}
    (h : IsEliminationSequence M rs N) :
    M.toRotationLowerSet ≤ N.toRotationLowerSet ∧
      (∀ ρ : Rotation smp, ρ ∈ rs ↔
        ρ ∈ N.toRotationLowerSet ∧ ρ ∉ M.toRotationLowerSet) ∧
      rs.Pairwise (fun ρ σ => ¬ σ ≤ ρ) := by
  induction h with
  | nil M =>
      refine ⟨le_rfl, ?_, List.Pairwise.nil⟩
      intro ρ
      simp
  | cons τ _ ih =>
      obtain ⟨hTailSubset, hTailMem, hTailOrder⟩ := ih
      have hStepSubset : τ.M.toRotationLowerSet ≤ τ.eliminate.toRotationLowerSet :=
        stableMatchingOrderIsoLowerSet.monotone τ.covBy_eliminate.le
      have hStepMem (ρ : Rotation smp) :
          (ρ ∈ τ.eliminate.toRotationLowerSet ∧ ρ ∉ τ.M.toRotationLowerSet) ↔
            ρ = τ.toRotation := by
        change ρ ∈ (τ.toSMEdge.target.toRotationLowerSet : Set (Rotation smp)) \
          (τ.toSMEdge.source.toRotationLowerSet : Set (Rotation smp)) ↔
            ρ = τ.toSMEdge.toRotation
        rw [τ.toSMEdge.toRotationLowerSet_target_diff_source, Set.mem_singleton_iff]
      have hHead := (hStepMem τ.toRotation).mpr rfl
      refine ⟨hStepSubset.trans hTailSubset, ?_, ?_⟩
      · intro ρ
        rw [List.mem_cons]
        constructor
        · rintro (rfl | hInTail)
          · exact ⟨hTailSubset hHead.1, hHead.2⟩
          · obtain ⟨hInN, hNotInStep⟩ := (hTailMem ρ).mp hInTail
            exact ⟨hInN, fun hInM => hNotInStep (hStepSubset hInM)⟩
        · rintro ⟨hInN, hNotInM⟩
          by_cases hInStep : ρ ∈ τ.eliminate.toRotationLowerSet
          · exact Or.inl ((hStepMem ρ).mp ⟨hInStep, hNotInM⟩)
          · exact Or.inr ((hTailMem ρ).mpr ⟨hInN, hInStep⟩)
      · rw [List.pairwise_cons]
        refine ⟨?_, hTailOrder⟩
        intro ρ hInTail hLe
        exact ((hTailMem ρ).mp hInTail).2 (τ.eliminate.toRotationLowerSet.lower hLe hHead.1)

/-- 合法な回転除去列の始点は終点以下である。 -/
theorem IsEliminationSequence.le {smp : SMP n}
    {M N : StableMatching smp} {rs : List (Rotation smp)}
    (h : IsEliminationSequence M rs N) :
    M ≤ N :=
  (stableMatchingOrderIsoLowerSet (smp := smp)).le_iff_le.mp h.linearExtension.1

/-- 合法な回転除去の取り消し列の終点は始点以下である。 -/
theorem IsUndoSequence.le {smp : SMP n}
    {M N : StableMatching smp} {rs : List (Rotation smp)}
    (h : IsUndoSequence M rs N) :
    N ≤ M := by
  induction h with
  | nil _ => exact le_rfl
  | cons τ _ ih => exact ih.trans τ.covBy_eliminate.le

/-- 回転除去で相手が変わった男性は、その後の除去で元の相手に戻らない。 -/
theorem IsEliminationSequence.partnerOfMan_ne_of_changed {smp : SMP n}
    {M N P : StableMatching smp} {rs ts : List (Rotation smp)}
    (h₁ : IsEliminationSequence M rs N)
    (h₂ : IsEliminationSequence N ts P) (m : smp.Man)
    (hChanged : M.matching.partnerOfMan m ≠ N.matching.partnerOfMan m) :
    M.matching.partnerOfMan m ≠ P.matching.partnerOfMan m := by
  intro hReturn
  apply hChanged
  apply m.prefersOrEqual_antisymm
  · exact h₁.le m
  · simpa only [← hReturn] using h₂.le m

/-- 合法な除去列の始点と終点で男性の相手が異なることと、その男性が参加する回転が列にあることは同値。 -/
theorem IsEliminationSequence.partnerOfMan_ne_iff_exists_containsMan
    {smp : SMP n} {M N : StableMatching smp} {rs : List (Rotation smp)}
    (h : IsEliminationSequence M rs N) (m : smp.Man) :
    M.matching.partnerOfMan m ≠ N.matching.partnerOfMan m ↔
      ∃ ρ ∈ rs, ρ.ContainsMan m := by
  classical
  induction h with
  | nil M => simp
  | cons τ hTail ih =>
    have hStep : τ.toRotation.ContainsMan m ↔
        τ.M.matching.partnerOfMan m ≠ τ.eliminate.matching.partnerOfMan m :=
      τ.toSMEdge.toRotation_containsMan_iff m
    by_cases hContains : τ.toRotation.ContainsMan m
    · have hHead := IsEliminationSequence.cons τ (IsEliminationSequence.nil τ.eliminate)
      exact ⟨fun _ => ⟨τ.toRotation, List.mem_cons_self, hContains⟩,
        fun _ => hHead.partnerOfMan_ne_of_changed hTail m (hStep.mp hContains)⟩
    · have hSame : τ.M.matching.partnerOfMan m = τ.eliminate.matching.partnerOfMan m :=
        not_ne_iff.mp (mt hStep.mpr hContains)
      rw [hSame, ih]
      simp only [List.mem_cons]
      constructor
      · rintro ⟨ρ, hρ, hMan⟩
        exact ⟨ρ, Or.inr hρ, hMan⟩
      · rintro ⟨ρ, rfl | hρ, hMan⟩
        · exact (hContains hMan).elim
        · exact ⟨ρ, hρ, hMan⟩

/-- 回転除去の取り消しで相手が変わった男性は、その後の取り消しで元の相手に戻らない。 -/
theorem IsUndoSequence.partnerOfMan_ne_of_changed {smp : SMP n}
    {M N P : StableMatching smp} {rs ts : List (Rotation smp)}
    (h₁ : IsUndoSequence M rs N)
    (h₂ : IsUndoSequence N ts P) (m : smp.Man)
    (hChanged : M.matching.partnerOfMan m ≠ N.matching.partnerOfMan m) :
    M.matching.partnerOfMan m ≠ P.matching.partnerOfMan m := by
  intro hReturn
  apply hChanged
  apply m.prefersOrEqual_antisymm
  · simpa only [← hReturn] using h₂.le m
  · exact h₁.le m

/-- 男性集合の内部だけで回転を除去すると、その集合の相手全体は保存される。 -/
theorem IsEliminationSequence.image_partnerOfMan_eq {smp : SMP n}
    {M N : StableMatching smp} {rs : List (Rotation smp)}
    (h : IsEliminationSequence M rs N) (S : Set smp.Man)
    (hS : ∀ ρ ∈ rs, ∀ m : smp.Man, ρ.ContainsMan m → m ∈ S) :
    M.matching.partnerOfMan '' S = N.matching.partnerOfMan '' S := by
  apply Matching.image_partnerOfMan_eq_of_eqOn_compl S
  intro m hm
  change m ∉ S at hm
  revert hS
  induction h with
  | nil _ =>
      intro _
      rfl
  | cons τ _ ih =>
      intro hS
      have hStep : τ.M.matching.partnerOfMan m = τ.eliminate.matching.partnerOfMan m := by
        by_contra hChanged
        exact hm (hS τ.toRotation List.mem_cons_self m
          ((τ.toSMEdge.toRotation_containsMan_iff m).mpr hChanged))
      exact hStep.trans (ih (fun ρ hMem => hS ρ (List.mem_cons_of_mem _ hMem)))

/-- 男性集合の内部だけで回転除去を取り消すと、その集合の相手全体は保存される。 -/
theorem IsUndoSequence.image_partnerOfMan_eq {smp : SMP n}
    {M N : StableMatching smp} {rs : List (Rotation smp)}
    (h : IsUndoSequence M rs N) (S : Set smp.Man)
    (hS : ∀ ρ ∈ rs, ∀ m : smp.Man, ρ.ContainsMan m → m ∈ S) :
    M.matching.partnerOfMan '' S = N.matching.partnerOfMan '' S := by
  revert hS
  induction h with
  | nil _ =>
      intro _
      rfl
  | cons τ _ ih =>
      intro hS
      have hOne : IsEliminationSequence τ.M [τ.toRotation] τ.eliminate :=
        IsEliminationSequence.cons τ (IsEliminationSequence.nil τ.eliminate)
      have hStep := hOne.image_partnerOfMan_eq S (by
        intro ρ hρ
        rw [List.mem_singleton] at hρ
        subst ρ
        exact hS τ.toRotation List.mem_cons_self)
      exact hStep.symm.trans (ih (fun ρ hMem => hS ρ (List.mem_cons_of_mem _ hMem)))

/-- 二つの下方閉集合の差を列挙する回転の線形拡張が存在する。 -/
theorem exists_linearExtension {smp : SMP n}
    (D D' : LowerSet (Rotation smp)) :
    ∃ rs : List (Rotation smp),
      (∀ ρ : Rotation smp, ρ ∈ rs ↔ ρ ∈ D' ∧ ρ ∉ D) ∧
      rs.Pairwise (fun ρ σ => ¬ σ ≤ ρ) := by
  classical
  let Remaining := {ρ : Rotation smp // ρ ∈ D' ∧ ρ ∉ D}
  letI : Fintype (LinearExtension Remaining) := Fintype.ofFinite Remaining
  let sorted : List (LinearExtension Remaining) :=
    (Finset.univ : Finset (LinearExtension Remaining)).sort (· ≤ ·)
  let rotationOf (a : LinearExtension Remaining) : Rotation smp :=
    (show Remaining from a).1
  refine ⟨sorted.map rotationOf, ?_, ?_⟩
  · intro ρ
    constructor
    · intro hρ
      obtain ⟨a, _, rfl⟩ := List.mem_map.mp hρ
      exact (show Remaining from a).2
    · intro hρ
      let a : LinearExtension Remaining := (⟨ρ, hρ⟩ : Remaining)
      have ha : a ∈ sorted := by simp [sorted]
      exact List.mem_map.mpr ⟨a, ha, rfl⟩
  · have hSorted : sorted.Pairwise (· < ·) := Finset.sort_sorted_lt _
    apply List.pairwise_map.mpr
    apply hSorted.imp
    intro a b hab hba
    have hba' : (show Remaining from b) ≤ (show Remaining from a) := hba
    exact (not_le_of_gt hab) ((toLinearExtension (α := Remaining)).monotone hba')

/-- 回転 `ρ` がリスト `rs` の中で `σ` より前に現れること。 -/
def PrecedesIn {smp : SMP n} (ρ σ : Rotation smp)
    (rs : List (Rotation smp)) : Prop :=
  List.Sublist [ρ, σ] rs

/-- 回転の狭義順序は、合法な除去列における先行関係と一致する。 -/
theorem lt_iff_forall_eliminationSequence_precedes {smp : SMP n}
    (ρ σ : Rotation smp) :
    ρ < σ ↔
      ∀ {M N : StableMatching smp} {rs : List (Rotation smp)},
        IsEliminationSequence M rs N →
        ρ ∈ rs → σ ∈ rs → PrecedesIn ρ σ rs := by
  constructor
  · intro hLt M N rs hRun hρ hσ
    have precedes (xs : List (Rotation smp)) :
        ρ ∈ xs → σ ∈ xs → xs.Pairwise (fun a b => ¬ b ≤ a) →
          List.Sublist [ρ, σ] xs := by
      induction xs with
      | nil =>
          intro hρMem
          exact (List.not_mem_nil hρMem).elim
      | cons a xs ih =>
          intro hρMem hσMem hOrder
          obtain ⟨hHeadOrder, hTailOrder⟩ := List.pairwise_cons.mp hOrder
          rcases List.mem_cons.mp hρMem with hρHead | hρTail
          · subst a
            have hσTail := (List.mem_cons.mp hσMem).resolve_left hLt.ne.symm
            exact (List.singleton_sublist.mpr hσTail).cons_cons ρ
          · rcases List.mem_cons.mp hσMem with hσHead | hσTail
            · subst a
              exact (hHeadOrder ρ hρTail hLt.le).elim
            · exact (ih hρTail hσTail hTailOrder).cons a
    exact precedes rs hρ hσ hRun.linearExtension.2.2
  · intro hPrecedes
    by_contra hNotLt
    have hInsert : (LowerSet.Iic σ : Set (Rotation smp)) =
        insert σ (LowerSet.Iio σ : Set (Rotation smp)) := by
      apply Set.ext
      intro a
      rw [Set.mem_insert_iff]
      change a ≤ σ ↔ a = σ ∨ a < σ
      exact le_iff_eq_or_lt
    obtain ⟨τ, hM, hEliminate, hLabel⟩ :=
      ExposedRotation.exists_of_lowerSet_insert (LowerSet.Iio σ) (LowerSet.Iic σ) σ
        (lt_irrefl σ) hInsert
    obtain ⟨rs, hMem, hOrder⟩ := exists_linearExtension (LowerSet.Iic σ) ⊤
    have hTail := isEliminationSequence_of_linearExtension (LowerSet.Iic σ) ⊤ rs le_top hMem hOrder
    rw [← hEliminate] at hTail
    have hRun : IsEliminationSequence τ.M (σ :: rs)
        (StableMatching.ofRotationLowerSet (⊤ : LowerSet (Rotation smp))) := by
      rw [← hLabel]
      exact IsEliminationSequence.cons τ hTail
    have hρMem : ρ ∈ σ :: rs := by
      apply (hRun.linearExtension.2.1 ρ).mpr
      refine ⟨?_, ?_⟩
      · simpa only [StableMatching.toRotationLowerSet_ofRotationLowerSet] using
          (LowerSet.mem_top : ρ ∈ (⊤ : LowerSet (Rotation smp)))
      · simpa only [hM, StableMatching.toRotationLowerSet_ofRotationLowerSet] using hNotLt
    have hBefore : List.Sublist [ρ, σ] (σ :: rs) :=
      hPrecedes hRun hρMem List.mem_cons_self
    have hSingleton : List.Sublist [σ] rs := hBefore.tail
    have hσTail := List.singleton_sublist.mp hSingleton
    exact ((hMem σ).mp hσTail).2 (LowerSet.mem_Iic_iff.mpr le_rfl)

end Rotation
end SMP
end StableMatching
