import Mathlib

namespace StableMatching

/--
`n` 人対 `n` 人の stable marriage problem。

内部的には男性・女性とも `Fin n` で番号付けする。
各選好は相手から順位への全単射として保持する。

順位は小さいほど好ましいものとする。
-/
structure SMP (n : ℕ) where
  private menRankImpl   : Fin n → Fin n ≃ Fin n
  private womenRankImpl : Fin n → Fin n ≃ Fin n

namespace SMP

/--
内部表現から stable marriage problem を構築する。

通常の数学的操作では `Fin n` を直接使用せず、
構築時のみ使用することを想定している。
-/
def ofRanks
    (menRank : Fin n → Fin n ≃ Fin n)
    (womenRank : Fin n → Fin n ≃ Fin n) :
    SMP n :=
  {
    menRankImpl := menRank
    womenRankImpl := womenRank
  }

/--
男性と女性を入れ替えた stable marriage problem。

交換後の男性の選好は元の女性の選好であり、交換後の女性の選好は
元の男性の選好である。
-/
def swap (smp : SMP n) : SMP n :=
  {
    menRankImpl := smp.womenRankImpl
    womenRankImpl := smp.menRankImpl
  }

/--
stable marriage problem `smp` に属する男性。

異なる問題 `sm₁`, `sm₂` に対して
`sm₁.Man` と `sm₂.Man` は異なる型になる。
-/
structure Man (smp : SMP n) where
  val : Fin n
deriving DecidableEq, Fintype

/- 男性を内部番号の順に列挙する iterator。-/
def Man.iterator
    {smp : SMP n} : List smp.Man :=
  List.ofFn (fun i : Fin n => ⟨i⟩)

/--
stable marriage problem `smp` に属する女性。

異なる問題 `sm₁`, `sm₂` に対して
`sm₁.Woman` と `sm₂.Woman` は異なる型になる。
-/
structure Woman (smp : SMP n) where
  val : Fin n
deriving DecidableEq, Fintype

/-- 元の女性を、男女交換後の問題の男性として見る。-/
def swapMan (smp : SMP n) (w : smp.Woman) : (swap smp).Man :=
  ⟨w.val⟩

/-- 元の男性を、男女交換後の問題の女性として見る。-/
def swapWoman (smp : SMP n) (m : smp.Man) : (swap smp).Woman :=
  ⟨m.val⟩

/-- 元の女性と交換後の男性との間の自然な同値。-/
def swapManEquiv (smp : SMP n) : smp.Woman ≃ (swap smp).Man :=
  {
    toFun := swapMan smp
    invFun := fun m => ⟨m.val⟩
    left_inv := by intro w; rfl
    right_inv := by intro m; rfl
  }

/-- 元の男性と交換後の女性との間の自然な同値。-/
def swapWomanEquiv (smp : SMP n) : smp.Man ≃ (swap smp).Woman :=
  {
    toFun := swapWoman smp
    invFun := fun w => ⟨w.val⟩
    left_inv := by intro m; rfl
    right_inv := by intro w; rfl
  }

/--
男性 `m` から見た女性 `w` の順位。

値が小さいほど好ましい。
-/
def manRank
    {smp : SMP n}
    (m : smp.Man)
    (w : smp.Woman) : Fin n :=
  smp.menRankImpl m.val w.val

/--
女性 `w` から見た男性 `m` の順位。

値が小さいほど好ましい。
-/
def womanRank
    {smp : SMP n}
    (w : smp.Woman)
    (m : smp.Man) : Fin n :=
  smp.womenRankImpl w.val m.val

@[simp]
theorem manRank_swap
    (smp : SMP n) (w : smp.Woman) (m : smp.Man) :
    manRank (smp.swapMan w) (smp.swapWoman m) = womanRank w m := by
  rfl

@[simp]
theorem womanRank_swap
    (smp : SMP n) (m : smp.Man) (w : smp.Woman) :
    womanRank (smp.swapWoman m) (smp.swapMan w) = manRank m w := by
  rfl

theorem manRank_injective
    {smp : SMP n}
    (m : smp.Man) : Function.Injective (manRank m) := by
  intro w₁ w₂ h
  cases w₁ with
  | mk v₁ =>
    cases w₂ with
    | mk v₂ =>
      simp only [manRank] at h
      congr
      exact (smp.menRankImpl m.val).injective h

theorem womanRank_injective
    {smp : SMP n}
    (w : smp.Woman) : Function.Injective (womanRank w) := by
  intro m₁ m₂ h
  cases m₁ with
  | mk v₁ =>
    cases m₂ with
    | mk v₂ =>
      simp only [womanRank] at h
      congr
      exact (smp.womenRankImpl w.val).injective h

def womanAtRank
    {smp : SMP n}
    (m : smp.Man)
    (r : Fin n) : smp.Woman :=
  ⟨(smp.menRankImpl m.val).symm r⟩

def manAtRank
    {smp : SMP n}
    (w : smp.Woman)
    (r : Fin n) : smp.Man :=
  ⟨(smp.womenRankImpl w.val).symm r⟩

/-- manRank m (womanAtRank m r) = r -/
@[simp]
theorem manRank_womanAtRank
    {smp : SMP n}
    (m : smp.Man) (r : Fin n) :
    manRank m (womanAtRank m r) = r := by
  simp [manRank, womanAtRank]

/-- womanRank w (manAtRank w r) = r -/
@[simp]
theorem womanRank_manAtRank
    {smp : SMP n}
    (w : smp.Woman) (r : Fin n) :
    womanRank w (manAtRank w r) = r := by
  simp [womanRank, manAtRank]

theorem card_man (smp : SMP n) : Fintype.card smp.Man = n := by
  calc
    _ = Fintype.card (Fin n) := by
      apply Fintype.card_congr
      exact {
        toFun := fun m => m.val
        invFun := fun i => ⟨i⟩
        left_inv := by
          intro m
          rfl
        right_inv := by
          intro i
          rfl
      }
    _ = n := Fintype.card_fin n
theorem card_woman (smp : SMP n) : Fintype.card smp.Woman = n := by
  calc
    _ = Fintype.card (Fin n) := by
      apply Fintype.card_congr
      exact {
        toFun := fun w => w.val
        invFun := fun i => ⟨i⟩
        left_inv := by
          intro w
          rfl
        right_inv := by
          intro i
          rfl
      }
    _ = n := Fintype.card_fin n

end SMP

end StableMatching
