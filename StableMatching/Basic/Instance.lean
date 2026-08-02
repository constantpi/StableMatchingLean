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
stable marriage problem `sm` に属する男性。

異なる問題 `sm₁`, `sm₂` に対して
`sm₁.Man` と `sm₂.Man` は異なる型になる。
-/
structure Man (sm : SMP n) where
  val : Fin n
deriving DecidableEq, Fintype

/--
stable marriage problem `sm` に属する女性。

異なる問題 `sm₁`, `sm₂` に対して
`sm₁.Woman` と `sm₂.Woman` は異なる型になる。
-/
structure Woman (sm : SMP n) where
  val : Fin n
deriving DecidableEq, Fintype

/--
男性 `m` から見た女性 `w` の順位。

値が小さいほど好ましい。
-/
def manRank
    {sm : SMP n}
    (m : sm.Man)
    (w : sm.Woman) : Fin n :=
  sm.menRankImpl m.val w.val

/--
女性 `w` から見た男性 `m` の順位。

値が小さいほど好ましい。
-/
def womanRank
    {sm : SMP n}
    (w : sm.Woman)
    (m : sm.Man) : Fin n :=
  sm.womenRankImpl w.val m.val

theorem manRank_injective
    {sm : SMP n}
    (m : sm.Man) : Function.Injective (manRank m) := by
  intro w₁ w₂ h
  cases w₁ with
  | mk v₁ =>
    cases w₂ with
    | mk v₂ =>
      simp only [manRank] at h
      congr
      exact (sm.menRankImpl m.val).injective h

theorem womanRank_injective
    {sm : SMP n}
    (w : sm.Woman) : Function.Injective (womanRank w) := by
  intro m₁ m₂ h
  cases m₁ with
  | mk v₁ =>
    cases m₂ with
    | mk v₂ =>
      simp only [womanRank] at h
      congr
      exact (sm.womenRankImpl w.val).injective h

def womanAtRank
    {sm : SMP n}
    (m : sm.Man)
    (r : Fin n) : sm.Woman :=
  ⟨(sm.menRankImpl m.val).symm r⟩

def manAtRank
    {sm : SMP n}
    (w : sm.Woman)
    (r : Fin n) : sm.Man :=
  ⟨(sm.womenRankImpl w.val).symm r⟩

/-- manRank m (womanAtRank m r) = r -/
theorem manRank_womanAtRank
    {sm : SMP n}
    (m : sm.Man) (r : Fin n) :
    manRank m (womanAtRank m r) = r := by
  simp [manRank, womanAtRank]

/-- womanRank w (manAtRank w r) = r -/
theorem womanRank_manAtRank
    {sm : SMP n}
    (w : sm.Woman) (r : Fin n) :
    womanRank w (manAtRank w r) = r := by
  simp [womanRank, manAtRank]

end SMP

end StableMatching
