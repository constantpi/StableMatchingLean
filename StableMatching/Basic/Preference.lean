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
男性 `m` が `w₂` より `w₁` を少なくとも同程度に好む。
-/
def Man.PrefersOrEqual
    {sm : SMP n}
    (m : sm.Man)
    (w₁ w₂ : sm.Woman) : Prop :=
  manRank m w₁ ≤ manRank m w₂

/--
女性 `w` が `m₂` より `m₁` を好む。
-/
def Woman.Prefers
    {sm : SMP n}
    (w : sm.Woman)
    (m₁ m₂ : sm.Man) : Prop :=
  womanRank w m₁ < womanRank w m₂

/--
女性 `w` が `m₂` より `m₁` を少なくとも同程度に好む。
-/
def Woman.PrefersOrEqual
    {sm : SMP n}
    (w : sm.Woman)
    (m₁ m₂ : sm.Man) : Prop :=
  womanRank w m₁ ≤ womanRank w m₂

notation:50 w₁ " ≺[" m "] " w₂ => Man.Prefers m w₁ w₂
notation:50 m₁ " ≺[" w "] " m₂ => Woman.Prefers w m₁ m₂
notation:50 w₁ " ≼[" m "] " w₂ => Man.PrefersOrEqual m w₁ w₂
notation:50 m₁ " ≼[" w "] " m₂ => Woman.PrefersOrEqual w m₁ m₂

instance manPrefersDecidable
    {sm : SMP n} (m : sm.Man) (w₁ w₂ : sm.Woman) :
    Decidable (w₁ ≺[m] w₂) := by
  unfold Man.Prefers
  infer_instance

instance womanPrefersDecidable
    {sm : SMP n} (w : sm.Woman) (m₁ m₂ : sm.Man) :
    Decidable (m₁ ≺[w] m₂) := by
  unfold Woman.Prefers
  infer_instance

instance manPrefersOrEqualDecidable
    {sm : SMP n} (m : sm.Man) (w₁ w₂ : sm.Woman) :
    Decidable (w₁ ≼[m] w₂) := by
  unfold Man.PrefersOrEqual
  infer_instance

instance womanPrefersOrEqualDecidable
    {sm : SMP n} (w : sm.Woman) (m₁ m₂ : sm.Man) :
    Decidable (m₁ ≼[w] m₂) := by
  unfold Woman.PrefersOrEqual
  infer_instance

@[simp]
theorem Man.prefersOrEqual_refl
    {sm : SMP n}
    (m : sm.Man) : ∀ w, w ≼[m] w := by
  intro w
  exact le_refl _

theorem Man.prefersOrEqual_trans
    {sm : SMP n}
    (m : sm.Man) : ∀ ⦃w₁ w₂ w₃⦄, (w₁ ≼[m] w₂) → (w₂ ≼[m] w₃) → (w₁ ≼[m] w₃) := by
  intro w₁ w₂ w₃ h₁ h₂
  exact le_trans h₁ h₂

@[simp]
theorem Woman.prefersOrEqual_refl
    {sm : SMP n}
    (w : sm.Woman) : ∀ m, m ≼[w] m := by
  intro m
  exact le_refl _

theorem Woman.prefersOrEqual_trans
    {sm : SMP n}
    (w : sm.Woman) : ∀ ⦃m₁ m₂ m₃⦄, (m₁ ≼[w] m₂) → (m₂ ≼[w] m₃) → (m₁ ≼[w] m₃) := by
  intro m₁ m₂ m₃ h₁ h₂
  exact le_trans h₁ h₂

@[simp]
theorem Man.prefers_irrefl
    {sm : SMP n}
    (m : sm.Man) : ∀ w, ¬ (w ≺[m] w) := by
  intro w
  simp [Man.Prefers]

theorem Man.prefers_trans
    {sm : SMP n}
    (m : sm.Man) : ∀ ⦃w₁ w₂ w₃⦄, (w₁ ≺[m] w₂) → (w₂ ≺[m] w₃) → (w₁ ≺[m] w₃) := by
  intro w₁ w₂ w₃ h₁ h₂
  exact lt_trans h₁ h₂

theorem Man.prefers_asymm
    {sm : SMP n}
    (m : sm.Man) : ∀ ⦃w₁ w₂⦄, (w₁ ≺[m] w₂) → ¬ (w₂ ≺[m] w₁) := by
  intro w₁ w₂ h₁ h₂
  exact lt_asymm h₁ h₂

theorem Man.prefers_total
    {sm : SMP n}
    (m : sm.Man) {w₁ w₂ : sm.Woman} (h : w₁ ≠ w₂) :
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
    {sm : SMP n}
    (w : sm.Woman) : ∀ m, ¬ (m ≺[w] m) := by
  intro m
  simp [Woman.Prefers]

theorem Woman.prefers_trans
    {sm : SMP n}
    (w : sm.Woman) : ∀ ⦃m₁ m₂ m₃⦄, (m₁ ≺[w] m₂) → (m₂ ≺[w] m₃) → (m₁ ≺[w] m₃) := by
  intro m₁ m₂ m₃ h₁ h₂
  exact lt_trans h₁ h₂

theorem Woman.prefers_asymm
    {sm : SMP n}
    (w : sm.Woman) : ∀ ⦃m₁ m₂⦄, (m₁ ≺[w] m₂) → ¬ (m₂ ≺[w] m₁) := by
  intro m₁ m₂ h₁ h₂
  exact lt_asymm h₁ h₂

theorem Woman.prefers_total
    {sm : SMP n}
    (w : sm.Woman) {m₁ m₂ : sm.Man} (h : m₁ ≠ m₂) :
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
