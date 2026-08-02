import StableMatching.Basic.Stability

namespace StableMatching.Examples

open StableMatching

def sm3 : SMP 3 :=
  SMP.ofRanks
    (fun _ => Equiv.refl (Fin 3))
    (fun _ => Equiv.refl (Fin 3))

-- #check sm3.menRankImpl -- これはprivateなのでアクセスできない

def m0 : sm3.Man := ⟨0⟩
def m1 : sm3.Man := ⟨1⟩
def m2 : sm3.Man := ⟨2⟩

def w0 : sm3.Woman := ⟨0⟩
def w1 : sm3.Woman := ⟨1⟩
def w2 : sm3.Woman := ⟨2⟩

#eval SMP.manRank m0 w0
#eval SMP.manRank m0 w2

example : w0 ≺[m0] w1 := by
  simp [SMP.Man.Prefers, SMP.manRank]
  decide

end StableMatching.Examples
