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

notation:50 w₁ " ≺[" m "] " w₂ => Man.Prefers m w₁ w₂
notation:50 m₁ " ≺[" w "] " m₂ => Woman.Prefers w m₁ m₂


end SMP
end StableMatching
