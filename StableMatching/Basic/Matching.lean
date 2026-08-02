import StableMatching.Basic.Preference

namespace StableMatching
namespace SMP

/--
問題 `sm` に対する完全マッチング。
-/
structure Matching (sm : SMP n) where
  equiv : sm.Man ≃ sm.Woman

namespace Matching

/--
男性 `m` のパートナー。
-/
def partnerOfMan
    {sm : SMP n}
    (M : sm.Matching)
    (m : sm.Man) : sm.Woman :=
  M.equiv m

/--
女性 `w` のパートナー。
-/
def partnerOfWoman
    {sm : SMP n}
    (M : sm.Matching)
    (w : sm.Woman) : sm.Man :=
  M.equiv.symm w

end Matching

end SMP
end StableMatching
