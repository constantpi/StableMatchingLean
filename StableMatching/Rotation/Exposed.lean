import StableMatching.Lattice.Order

namespace StableMatching
namespace SMP
namespace Rotation

def cycleNext {k : Nat} (hk : 1 < k) (i : Fin k) : Fin k :=
  have h1 : 0 < k := by omega
  ⟨(i.val + 1) % k, Nat.mod_lt (i.val + 1) h1⟩

def cyclePrev {k : Nat} (hk : 1 < k) (i : Fin k) : Fin k :=
  have h1 : 0 < k := by omega
  ⟨(i.val + k - 1) % k, Nat.mod_lt (i.val + k - 1) h1⟩

structure ExposedRotation
    (M : StableMatching smp) where
  k : Nat
  hk : 1 < k
  man : Fin k → smp.Man
  woman : Fin k → smp.Woman
  man_injective : Function.Injective man
  matched : ∀ i, M.matching.partnerOfMan (man i) = woman i
  movesDown :∀ i, woman i ≺[man i] woman (cycleNext hk i)
  nextAccepts : ∀ i, man (cyclePrev hk i) ≺[woman i] man i
  nextIsBest : ∀ i w,
    (woman i ≺[man i] w) → (man i ≺[w] M.matching.partnerOfWoman w) → woman (cycleNext hk i) ≼[man i] w

end Rotation
end SMP
end StableMatching
