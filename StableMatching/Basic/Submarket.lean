import StableMatching.Basic.LabeledRanks

namespace StableMatching
namespace SMP
namespace StableMatching

variable {n : ℕ}

/-- 元の順位の相対順序に従い、残った相手に連続した順位を割り当てる。 -/
private noncomputable def compressedRanks {A : Type*} [Fintype A] (f : A ↪ Fin n)
    (k : ℕ) (hk : Fintype.card A = k) : A ≃ Fin k :=
  letI : LinearOrder A := LinearOrder.lift' f f.injective
  (Fintype.orderIsoFinOfCardEq A hk).symm.toEquiv

/-- 順位を詰め直しても、相手の優先順は変わらない。 -/
private theorem compressedRanks_lt_iff {A : Type*} [Fintype A] (f : A ↪ Fin n)
    (k : ℕ) (hk : Fintype.card A = k) (a b : A) :
    compressedRanks f k hk a < compressedRanks f k hk b ↔ f a < f b := by
  letI : LinearOrder A := LinearOrder.lift' f f.injective
  change (Fintype.orderIsoFinOfCardEq A hk).symm a <
    (Fintype.orderIsoFinOfCardEq A hk).symm b ↔ a < b
  exact (Fintype.orderIsoFinOfCardEq A hk).symm.lt_iff_lt

variable {smp : SMP n}

/-- 部分市場に残る女性に対する男性の元の順位。 -/
private def maleRanking (a : smp.Man) (μ : smp.StableMatching) (Y : Finset smp.Man) :
    ↥Y ↪ Fin n :=
  ⟨fun b => manRank a (μ.matching.partnerOfMan b.val), fun _ _ h =>
    Subtype.ext (μ.matching.partnerOfMan_injective _ _ (manRank_injective a h))⟩

/-- 部分市場に残る男性に対する女性の元の順位。 -/
private def femaleRanking (b : smp.Woman) (Y : Finset smp.Man) : ↥Y ↪ Fin n :=
  ⟨fun a => womanRank b a.val, fun _ _ h => Subtype.ext (womanRank_injective b h)⟩

/-- 部分市場では女性にも基準マッチングにおける相手の男性ラベルを使う。 -/
private noncomputable def submarketRanks (μ : smp.StableMatching) (Y : Finset smp.Man) :
    LabeledRanks ↥Y ↥Y Y.card where
  men := Fintype.equivFinOfCardEq (Fintype.card_coe Y)
  women := Fintype.equivFinOfCardEq (Fintype.card_coe Y)
  manRanking a := compressedRanks (maleRanking a.val μ Y) _ (Fintype.card_coe Y)
  womanRanking b := compressedRanks (femaleRanking (μ.matching.partnerOfMan b.val) Y)
    _ (Fintype.card_coe Y)

/-- 男性 Y と、基準マッチングでその相手となる女性への制限市場。 -/
noncomputable def submarket (μ : smp.StableMatching) (Y : Finset smp.Man) : SMP Y.card :=
  (submarketRanks μ Y).toSMP

/-- 基準マッチングと Y の外で相手が一致する安定マッチング。 -/
abbrev FixedOutside (μ : smp.StableMatching) (Y : Finset smp.Man) :=
  {N : smp.StableMatching //
    Set.EqOn N.matching.partnerOfMan μ.matching.partnerOfMan (Y : Set smp.Man)ᶜ}

/-- 制限するマッチングにおける男性の相手を、基準マッチングでの男性ラベルで表す。 -/
private def restrictedLabel (μ : smp.StableMatching) (Y : Finset smp.Man)
    (N : μ.FixedOutside Y) (a : ↥Y) : ↥Y :=
  ⟨μ.matching.partnerOfWoman (N.val.matching.partnerOfMan a.val), by
    have hImage := Matching.image_partnerOfMan_eq_of_eqOn_compl (Y : Set smp.Man) N.property
    have hb : N.val.matching.partnerOfMan a.val ∈ μ.matching.partnerOfMan '' (Y : Set smp.Man) := by
      rw [← hImage]
      exact ⟨a.val, a.property, rfl⟩
    obtain ⟨b, hb, he⟩ := hb
    rw [← he, Matching.partnerOfWoman_partnerOfMan]
    exact hb⟩

/-- 制限するマッチングの相手関係を、部分市場のラベル間の全単射として表す。 -/
private noncomputable def restrictedEquiv (μ : smp.StableMatching) (Y : Finset smp.Man)
    (N : μ.FixedOutside Y) : ↥Y ≃ ↥Y :=
  let f := restrictedLabel μ Y N
  have hf : Function.Injective f := fun a b h =>
    Subtype.ext (N.val.matching.partnerOfMan_injective a.val b.val
      (μ.matching.partnerOfWoman_injective _ _ (congrArg Subtype.val h)))
  Equiv.ofBijective f ⟨hf, Finite.surjective_of_injective hf⟩

/-- 女性ラベルを元の女性に戻すと、制限した男性の相手が得られる。 -/
private theorem submarket_partner (μ : smp.StableMatching) {Y : Finset smp.Man}
    (N : μ.FixedOutside Y) (a : ↥Y) :
    μ.matching.partnerOfMan (restrictedEquiv μ Y N a).val =
      N.val.matching.partnerOfMan a.val := by
  change μ.matching.partnerOfMan
    (μ.matching.partnerOfWoman (N.val.matching.partnerOfMan a.val)) = _
  exact Matching.partnerOfMan_partnerOfWoman _ _

/-- 女性ラベルに逆写像を適用すると、制限した女性の相手が得られる。 -/
private theorem submarket_inverse_partner (μ : smp.StableMatching) {Y : Finset smp.Man}
    (N : μ.FixedOutside Y) (b : ↥Y) :
    ((restrictedEquiv μ Y N).symm b).val =
      N.val.matching.partnerOfWoman (μ.matching.partnerOfMan b.val) := by
  apply N.val.matching.partnerOfMan_injective
  rw [Matching.partnerOfMan_partnerOfWoman, ← submarket_partner μ N, Equiv.apply_symm_apply]

/-- 部分市場への制限は安定性を保存する。 -/
noncomputable def restrictStable (μ : smp.StableMatching) (Y : Finset smp.Man)
    (N : μ.FixedOutside Y) : (μ.submarket Y).StableMatching where
  matching := (submarketRanks μ Y).mkMatching (restrictedEquiv μ Y N)
  isStable := by
    apply (submarketRanks μ Y).isStable_mkMatching
    intro a b h
    have hm := (compressedRanks_lt_iff _ _ _ _ _).mp h.1
    have hw := (compressedRanks_lt_iff _ _ _ _ _).mp h.2
    apply N.val.isStable a.val (μ.matching.partnerOfMan b.val)
    constructor
    · change manRank a.val (μ.matching.partnerOfMan b.val) <
        manRank a.val (N.val.matching.partnerOfMan a.val)
      simpa only [maleRanking, Function.Embedding.coeFn_mk, submarket_partner μ N] using hm
    · change womanRank (μ.matching.partnerOfMan b.val) a.val <
        womanRank (μ.matching.partnerOfMan b.val)
          (N.val.matching.partnerOfWoman (μ.matching.partnerOfMan b.val))
      simpa only [femaleRanking, Function.Embedding.coeFn_mk, submarket_inverse_partner μ N] using hw

/-- Y の外の相手を固定すると、部分市場への制限は単射になる。 -/
theorem restrictStable_injective (μ : smp.StableMatching) (Y : Finset smp.Man) :
    Function.Injective (μ.restrictStable Y) := by
  intro N P he
  apply Subtype.ext
  apply StableMatching.ext_partnerOfMan
  intro a
  by_cases ha : a ∈ Y
  · let m : ↥Y := ⟨a, ha⟩
    let d := submarketRanks μ Y
    have h := congrArg (fun S : (μ.submarket Y).StableMatching =>
      S.matching.partnerOfMan (d.manEquiv m)) he
    change (d.mkMatching (restrictedEquiv μ Y N)).partnerOfMan (d.manEquiv m) =
      (d.mkMatching (restrictedEquiv μ Y P)).partnerOfMan (d.manEquiv m) at h
    simp only [LabeledRanks.partnerOfMan_mkMatching, Equiv.apply_eq_iff_eq] at h
    change N.val.matching.partnerOfMan m.val = P.val.matching.partnerOfMan m.val
    rw [← submarket_partner μ N, ← submarket_partner μ P, h]
  · exact (N.property ha).trans (P.property ha).symm

end StableMatching
end SMP
end StableMatching
