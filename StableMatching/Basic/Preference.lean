import StableMatching.Basic.Instance

namespace StableMatching
namespace SMP

/--
男性 `m` が `w₂` より `w₁` を好む。
-/
def Man.Prefers
    {smp : SMP n}
    (m : smp.Man)
    (w₁ w₂ : smp.Woman) : Prop :=
  manRank m w₁ < manRank m w₂

/--
男性 `m` が `w₂` より `w₁` を少なくとも同程度に好む。
-/
def Man.PrefersOrEqual
    {smp : SMP n}
    (m : smp.Man)
    (w₁ w₂ : smp.Woman) : Prop :=
  manRank m w₁ ≤ manRank m w₂

/--
女性 `w` が `m₂` より `m₁` を好む。
-/
def Woman.Prefers
    {smp : SMP n}
    (w : smp.Woman)
    (m₁ m₂ : smp.Man) : Prop :=
  womanRank w m₁ < womanRank w m₂

/--
女性 `w` が `m₂` より `m₁` を少なくとも同程度に好む。
-/
def Woman.PrefersOrEqual
    {smp : SMP n}
    (w : smp.Woman)
    (m₁ m₂ : smp.Man) : Prop :=
  womanRank w m₁ ≤ womanRank w m₂

notation:50 w₁ " ≺[" m "] " w₂ => Man.Prefers m w₁ w₂
notation:50 m₁ " ≺[" w "] " m₂ => Woman.Prefers w m₁ m₂
notation:50 w₁ " ≼[" m "] " w₂ => Man.PrefersOrEqual m w₁ w₂
notation:50 m₁ " ≼[" w "] " m₂ => Woman.PrefersOrEqual w m₁ m₂

instance manPrefersDecidable
    {smp : SMP n} (m : smp.Man) (w₁ w₂ : smp.Woman) :
    Decidable (w₁ ≺[m] w₂) := by
  unfold Man.Prefers
  infer_instance

instance womanPrefersDecidable
    {smp : SMP n} (w : smp.Woman) (m₁ m₂ : smp.Man) :
    Decidable (m₁ ≺[w] m₂) := by
  unfold Woman.Prefers
  infer_instance

instance manPrefersOrEqualDecidable
    {smp : SMP n} (m : smp.Man) (w₁ w₂ : smp.Woman) :
    Decidable (w₁ ≼[m] w₂) := by
  unfold Man.PrefersOrEqual
  infer_instance

instance womanPrefersOrEqualDecidable
    {smp : SMP n} (w : smp.Woman) (m₁ m₂ : smp.Man) :
    Decidable (m₁ ≼[w] m₂) := by
  unfold Woman.PrefersOrEqual
  infer_instance

@[simp]
theorem Man.prefersOrEqual_refl
    {smp : SMP n}
    (m : smp.Man) : ∀ w, w ≼[m] w := by
  intro w
  exact le_refl _

theorem Man.prefersOrEqual_trans
    {smp : SMP n}
    (m : smp.Man) : ∀ ⦃w₁ w₂ w₃⦄, (w₁ ≼[m] w₂) → (w₂ ≼[m] w₃) → (w₁ ≼[m] w₃) := by
  intro w₁ w₂ w₃ h₁ h₂
  exact le_trans h₁ h₂

@[simp]
theorem Woman.prefersOrEqual_refl
    {smp : SMP n}
    (w : smp.Woman) : ∀ m, m ≼[w] m := by
  intro m
  exact le_refl _

theorem Woman.prefersOrEqual_trans
    {smp : SMP n}
    (w : smp.Woman) : ∀ ⦃m₁ m₂ m₃⦄, (m₁ ≼[w] m₂) → (m₂ ≼[w] m₃) → (m₁ ≼[w] m₃) := by
  intro m₁ m₂ m₃ h₁ h₂
  exact le_trans h₁ h₂

theorem Man.prefers_iff_not_prefersOrEqual
    {smp : SMP n}
    (m : smp.Man) (w₁ w₂ : smp.Woman) :
    (w₁ ≺[m] w₂) ↔ ¬ (w₂ ≼[m] w₁) := by
  unfold Man.Prefers Man.PrefersOrEqual
  exact lt_iff_not_ge

theorem Man.prefersOrEqual_iff_not_prefers
    {smp : SMP n}
    (m : smp.Man) (w₁ w₂ : smp.Woman) :
    (w₁ ≼[m] w₂) ↔ ¬ (w₂ ≺[m] w₁) := by
  unfold Man.Prefers Man.PrefersOrEqual
  exact not_lt.symm

theorem Woman.prefers_iff_not_prefersOrEqual
    {smp : SMP n}
    (w : smp.Woman) (m₁ m₂ : smp.Man) :
    (m₁ ≺[w] m₂) ↔ ¬ (m₂ ≼[w] m₁) := by
  unfold Woman.Prefers Woman.PrefersOrEqual
  exact lt_iff_not_ge

theorem Woman.prefersOrEqual_iff_not_prefers
    {smp : SMP n}
    (w : smp.Woman) (m₁ m₂ : smp.Man) :
    (m₁ ≼[w] m₂) ↔ ¬ (m₂ ≺[w] m₁) := by
  unfold Woman.Prefers Woman.PrefersOrEqual
  exact not_lt.symm

@[simp]
theorem Man.prefers_irrefl
    {smp : SMP n}
    (m : smp.Man) : ∀ w, ¬ (w ≺[m] w) := by
  intro w
  simp [Man.Prefers]

theorem Man.prefers_trans
    {smp : SMP n}
    (m : smp.Man) : ∀ ⦃w₁ w₂ w₃⦄, (w₁ ≺[m] w₂) → (w₂ ≺[m] w₃) → (w₁ ≺[m] w₃) := by
  intro w₁ w₂ w₃ h₁ h₂
  exact lt_trans h₁ h₂

theorem Man.prefers_asymm
    {smp : SMP n}
    (m : smp.Man) : ∀ ⦃w₁ w₂⦄, (w₁ ≺[m] w₂) → ¬ (w₂ ≺[m] w₁) := by
  intro w₁ w₂ h₁ h₂
  exact lt_asymm h₁ h₂

theorem Man.prefers_total
    {smp : SMP n}
    (m : smp.Man) {w₁ w₂ : smp.Woman} (h : w₁ ≠ w₂) :
    (w₁ ≺[m] w₂) ∨ (w₂ ≺[m] w₁) := by
  -- rcases lt_or_gt_of_ne (fun h' => h (manRank_injective m h')) with h' | h'
  -- · exact Or.inl h'
  -- · exact Or.inr h'
  have : manRank m w₁ ≠ manRank m w₂ := by
    intro h'
    exact h (manRank_injective m h')
  have : manRank m w₁ < manRank m w₂ ∨ manRank m w₂ < manRank m w₁ := by
    exact lt_or_gt_of_ne this
  simp_all [Man.Prefers]

@[simp]
theorem Woman.prefers_irrefl
    {smp : SMP n}
    (w : smp.Woman) : ∀ m, ¬ (m ≺[w] m) := by
  intro m
  simp [Woman.Prefers]

theorem Woman.prefers_trans
    {smp : SMP n}
    (w : smp.Woman) : ∀ ⦃m₁ m₂ m₃⦄, (m₁ ≺[w] m₂) → (m₂ ≺[w] m₃) → (m₁ ≺[w] m₃) := by
  intro m₁ m₂ m₃ h₁ h₂
  exact lt_trans h₁ h₂

theorem Woman.prefers_asymm
    {smp : SMP n}
    (w : smp.Woman) : ∀ ⦃m₁ m₂⦄, (m₁ ≺[w] m₂) → ¬ (m₂ ≺[w] m₁) := by
  intro m₁ m₂ h₁ h₂
  exact lt_asymm h₁ h₂

theorem Woman.prefers_total
    {smp : SMP n}
    (w : smp.Woman) {m₁ m₂ : smp.Man} (h : m₁ ≠ m₂) :
    (m₁ ≺[w] m₂) ∨ (m₂ ≺[w] m₁) := by
  -- rcases lt_or_gt_of_ne (fun h' => h (womanRank_injective w h')) with h' | h'
  -- · exact Or.inl h'
  -- · exact Or.inr h'
  have : womanRank w m₁ ≠ womanRank w m₂ := by
    intro h'
    exact h (womanRank_injective w h')
  have : womanRank w m₁ < womanRank w m₂ ∨ womanRank w m₂ < womanRank w m₁ := by
    exact lt_or_gt_of_ne this
  simp_all [Woman.Prefers]


end SMP
end StableMatching
