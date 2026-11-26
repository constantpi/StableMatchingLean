import StableMatching.Basic.LabeledRanks

namespace StableMatching
namespace SMP

variable {k l : ℕ}

/-- 市場の男性と内部番号の間の全単射。 -/
private def manLabels (I : SMP k) : I.Man ≃ Fin k :=
  ⟨SMP.Man.val, SMP.Man.mk, fun _ => rfl, fun _ => rfl⟩

/-- 市場の女性と内部番号の間の全単射。 -/
private def womanLabels (I : SMP k) : I.Woman ≃ Fin k :=
  ⟨SMP.Woman.val, SMP.Woman.mk, fun _ => rfl, fun _ => rfl⟩

/-- 男性から見た女性の順位を全単射として取り出す。 -/
private noncomputable def manRanks (I : SMP k) (m : I.Man) : I.Woman ≃ Fin k :=
  Equiv.ofBijective (manRank m) ⟨manRank_injective m,
    fun r => ⟨womanAtRank m r, manRank_womanAtRank m r⟩⟩

/-- 女性から見た男性の順位を全単射として取り出す。 -/
private noncomputable def womanRanks (I : SMP k) (w : I.Woman) : I.Man ≃ Fin k :=
  Equiv.ofBijective (womanRank w) ⟨womanRank_injective w,
    fun r => ⟨manAtRank w r, womanRank_manAtRank w r⟩⟩

/-- 左側の候補を先に並べた順位表を作る。 -/
private def preferFirst {A B : Type*} (e : A ≃ Fin k) (f : B ≃ Fin l) :
    A ⊕ B ≃ Fin (k + l) :=
  (Equiv.sumCongr e f).trans finSumFinEquiv

/-- 右側の候補を先に並べた順位表を作る。 -/
private def preferSecond {A B : Type*} (e : A ≃ Fin k) (f : B ≃ Fin l) :
    A ⊕ B ≃ Fin (k + l) :=
  ((Equiv.sumComm A B).trans (preferFirst f e)).trans (finCongr (Nat.add_comm l k))

/-- 左側を優先する順位表では、右側の候補は左側の候補より下位にある。 -/
private theorem preferFirst_cross {A B : Type*} (e : A ≃ Fin k) (f : B ≃ Fin l)
    (a : A) (b : B) :
    ¬ preferFirst e f (Sum.inr b) < preferFirst e f (Sum.inl a) := by
  change ¬ k + (f b).val < (e a).val
  have := (e a).isLt
  omega

/-- 右側を優先する順位表では、左側の候補は右側の候補より下位にある。 -/
private theorem preferSecond_cross {A B : Type*} (e : A ≃ Fin k) (f : B ≃ Fin l)
    (a : A) (b : B) :
    ¬ preferSecond e f (Sum.inl a) < preferSecond e f (Sum.inr b) := by
  change ¬ l + (e a).val < (f b).val
  have := (f b).isLt
  omega

/-- 市場の所属を区別するラベルを使い、併合市場の順位表を作る。 -/
private noncomputable def combinedRanks (I : SMP k) (J : SMP l) :
    LabeledRanks (I.Man ⊕ J.Man) (I.Woman ⊕ J.Woman) (k + l) where
  men := preferFirst (manLabels I) (manLabels J)
  women := preferFirst (womanLabels I) (womanLabels J)
  manRanking := Sum.elim
    (fun m => preferFirst (manRanks I m) (womanLabels J))
    (fun m => preferSecond (womanLabels I) (manRanks J m))
  womanRanking := Sum.elim
    (fun w => preferFirst (womanRanks I w) (manLabels J))
    (fun w => preferSecond (manLabels I) (womanRanks J w))

/-- 各人が自市場の全員を他市場の全員より好むように併合した市場。 -/
noncomputable def disjointMarket (I : SMP k) (J : SMP l) : SMP (k + l) :=
  (combinedRanks I J).toSMP

/-- 二市場の相手関係をラベル上の全単射として並べる。 -/
private noncomputable def matchingEquiv {I : SMP k} {J : SMP l}
    (μ : I.StableMatching) (ν : J.StableMatching) :
    (I.Man ⊕ J.Man) ≃ (I.Woman ⊕ J.Woman) :=
  Equiv.sumCongr μ.matching.equiv ν.matching.equiv

/-- 二つの市場の安定マッチングを並べたマッチングは、併合後も安定である。 -/
noncomputable def StableMatching.combineStable {I : SMP k} {J : SMP l}
    (μ : I.StableMatching) (ν : J.StableMatching) :
    (I.disjointMarket J).StableMatching := by
  let d := combinedRanks I J
  let p := matchingEquiv μ ν
  refine ⟨d.mkMatching p, d.isStable_mkMatching p ?_⟩
  intro a b
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      exact μ.2 a b
    | inr b =>
      exact fun h => preferFirst_cross (manRanks I a) (womanLabels J) _ _ h.1
  | inr a =>
    cases b with
    | inl b =>
      exact fun h => preferSecond_cross (womanLabels I) (manRanks J a) _ _ h.1
    | inr b =>
      exact ν.2 a b

/-- 両側のマッチングは、併合後のマッチングから一意に復元される。 -/
theorem StableMatching.combineStable_injective (I : SMP k) (J : SMP l) :
    Function.Injective (fun x : I.StableMatching × J.StableMatching =>
      x.1.combineStable x.2) := by
  intro x y h
  let d := combinedRanks I J
  have hm (a : I.Man ⊕ J.Man) :
      matchingEquiv x.1 x.2 a = matchingEquiv y.1 y.2 a := by
    have he := congrArg (fun M : (I.disjointMarket J).StableMatching =>
      M.matching.partnerOfMan (d.manEquiv a)) h
    exact d.womanEquiv.injective (by simpa only [d, StableMatching.combineStable,
      LabeledRanks.partnerOfMan_mkMatching] using he)
  apply Prod.ext
  · exact StableMatching.ext_partnerOfMan fun a => Sum.inl.inj (hm (Sum.inl a))
  · exact StableMatching.ext_partnerOfMan fun a => Sum.inr.inj (hm (Sum.inr a))

/-- 市場を併合すると、二つの市場の安定マッチング数の積以上を得られる。 -/
theorem card_stableMatching_mul_le_disjointMarket (I : SMP k) (J : SMP l) :
    Fintype.card I.StableMatching * Fintype.card J.StableMatching ≤
      Fintype.card (I.disjointMarket J).StableMatching := by
  rw [← Fintype.card_prod]
  exact Fintype.card_le_of_injective _ (StableMatching.combineStable_injective I J)

end SMP
end StableMatching
