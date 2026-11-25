import StableMatching.Basic.Stability

namespace StableMatching
namespace SMP

/-- 有限な型付きエージェント集合で順位表を記述し、SMP に移すためのデータ。 -/
structure LabeledRanks (A B : Type*) (k : ℕ) where
  men : A ≃ Fin k
  women : B ≃ Fin k
  manRanking : A → B ≃ Fin k
  womanRanking : B → A ≃ Fin k

namespace LabeledRanks

variable {A B : Type*}

/-- ラベル付きの順位表から同じ選好を持つ市場を作る。 -/
def toSMP {k : ℕ} (d : LabeledRanks A B k) : SMP k :=
  SMP.ofRanks (fun i => d.women.symm.trans (d.manRanking (d.men.symm i)))
    (fun j => d.men.symm.trans (d.womanRanking (d.women.symm j)))

/-- 元の男性ラベルと構成後の市場の男性との同値。 -/
def manEquiv {k : ℕ} (d : LabeledRanks A B k) : A ≃ d.toSMP.Man where
  toFun a := ⟨d.men a⟩
  invFun a := d.men.symm a.val
  left_inv a := d.men.symm_apply_apply a
  right_inv a := by cases a; simp

/-- 元の女性ラベルと構成後の市場の女性との同値。 -/
def womanEquiv {k : ℕ} (d : LabeledRanks A B k) : B ≃ d.toSMP.Woman where
  toFun b := ⟨d.women b⟩
  invFun b := d.women.symm b.val
  left_inv b := d.women.symm_apply_apply b
  right_inv b := by cases b; simp

/-- 元のラベル上での男性の順位は、構成後の市場でも保存される。 -/
@[simp]
theorem manRank_equiv {k : ℕ} (d : LabeledRanks A B k) (a : A) (b : B) :
    manRank (smp := d.toSMP) (d.manEquiv a) (d.womanEquiv b) = d.manRanking a b := by
  change (d.women.symm.trans (d.manRanking (d.men.symm (d.men a)))) (d.women b) = _
  simp

/-- 元のラベル上での女性の順位は、構成後の市場でも保存される。 -/
@[simp]
theorem womanRank_equiv {k : ℕ} (d : LabeledRanks A B k) (a : A) (b : B) :
    womanRank (smp := d.toSMP) (d.womanEquiv b) (d.manEquiv a) = d.womanRanking b a := by
  change (d.men.symm.trans (d.womanRanking (d.women.symm (d.women b)))) (d.men a) = _
  simp

/-- ラベル間の全単射から、構成後の市場のマッチングを作る。 -/
def mkMatching {k : ℕ} (d : LabeledRanks A B k) (p : A ≃ B) : d.toSMP.Matching :=
  ⟨d.manEquiv.symm.trans (p.trans d.womanEquiv)⟩

/-- ラベル間の全単射で指定した男性の相手は、構成後のマッチングでも保存される。 -/
@[simp]
theorem partnerOfMan_mkMatching {k : ℕ} (d : LabeledRanks A B k) (p : A ≃ B) (a : A) :
    (d.mkMatching p).partnerOfMan (d.manEquiv a) = d.womanEquiv (p a) := by
  change d.womanEquiv (p (d.manEquiv.symm (d.manEquiv a))) = _
  simp

/-- ラベル間の全単射で指定した女性の相手は、構成後のマッチングでも保存される。 -/
@[simp]
theorem partnerOfWoman_mkMatching {k : ℕ} (d : LabeledRanks A B k) (p : A ≃ B) (b : B) :
    (d.mkMatching p).partnerOfWoman (d.womanEquiv b) = d.manEquiv (p.symm b) := by
  change d.manEquiv (p.symm (d.womanEquiv.symm (d.womanEquiv b))) = _
  simp

/-- ラベル上の順位比較でブロッキングペアがないなら、構成後のマッチングも安定である。 -/
theorem isStable_mkMatching {k : ℕ} (d : LabeledRanks A B k) (p : A ≃ B)
    (h : ∀ a b, ¬ (d.manRanking a b < d.manRanking a (p a) ∧
      d.womanRanking b a < d.womanRanking b (p.symm b))) :
    (d.mkMatching p).IsStable := by
  intro m w
  obtain ⟨a, rfl⟩ := d.manEquiv.surjective m
  obtain ⟨b, rfl⟩ := d.womanEquiv.surjective w
  simpa only [Matching.IsBlockingPair, Man.Prefers, Woman.Prefers,
    partnerOfMan_mkMatching, partnerOfWoman_mkMatching, manRank_equiv, womanRank_equiv] using h a b

end LabeledRanks

end SMP
end StableMatching
