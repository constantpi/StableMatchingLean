import StableMatching.Basic.Instance

namespace StableMatching
namespace SMP

/--
男性 `m` が `w₂` より `w₁` を好む。
-/
def Man.Prefers
    {sm : SMP n}
    (m : sm.Man)
    (w₁ w₂ : sm.Woman) : Prop :=
  manRank m w₁ < manRank m w₂

/--
女性 `w` が `m₂` より `m₁` を好む。
-/
def Woman.Prefers
    {sm : SMP n}
    (w : sm.Woman)
    (m₁ m₂ : sm.Man) : Prop :=
  womanRank w m₁ < womanRank w m₂

end SMP
end StableMatching
