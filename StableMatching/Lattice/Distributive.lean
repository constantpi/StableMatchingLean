import StableMatching.Lattice.Lattice

namespace StableMatching
namespace SMP
namespace Lattice

theorem inf_sup_distrib
    {smp : SMP n}
    (M₁ M₂ M₃ : StableMatching smp) :
    M₁ ⊓ (M₂ ⊔ M₃) = (M₁ ⊓ M₂) ⊔ (M₁ ⊓ M₃) := by
  apply StableMatching.ext_partnerOfMan
  intro m
  simp [menBetterPartner, menWorsePartner]
  simp [Man.Prefers]
  apply manRank_injective m
  repeat' first | split
  all_goals omega

theorem sup_inf_distrib
    {smp : SMP n}
    (M₁ M₂ M₃ : StableMatching smp) :
    M₁ ⊔ (M₂ ⊓ M₃) = (M₁ ⊔ M₂) ⊓ (M₁ ⊔ M₃) := by
  apply StableMatching.ext_partnerOfMan
  intro m
  simp [menBetterPartner, menWorsePartner]
  simp [Man.Prefers]
  apply manRank_injective m
  repeat' first | split
  all_goals omega

instance stableMatchingDistribLattice :
    DistribLattice (StableMatching smp) :=
  DistribLattice.ofInfSupLe (fun M₁ M₂ M₃ => (inf_sup_distrib M₁ M₂ M₃).le)


end Lattice
end SMP
end StableMatching
