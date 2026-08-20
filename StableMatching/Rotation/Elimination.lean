import StableMatching.Rotation.Exposed

namespace StableMatching
namespace SMP
namespace Rotation

/-- 回転に男性mが含まれるかどうか -/
def ExposedRotation.ContainsMan
    {smp : SMP n}
    (ρ : ExposedRotation smp)
    (m : smp.Man) : Prop :=
  ∃ i, ρ.man i = m

/-- 回転に女性wが含まれるかどうか -/
def ExposedRotation.ContainsWoman
    {smp : SMP n}
    (ρ : ExposedRotation smp)
    (w : smp.Woman) : Prop :=
  ∃ i, ρ.woman i = w

namespace ExposedRotation

variable {smp : SMP n} {M : StableMatching smp}

/-- cycleNextは固定点を持たない-/
@[simp]
theorem cycleNext_ne_self
    (ρ : ExposedRotation smp) (i : Fin ρ.k) (h : cycleNext ρ.hk i = i) : False := by
  simp [cycleNext] at h
  by_cases hi : i.val + 1 < ρ.k
  .
    have hval := congrArg Fin.val h
    simp [Nat.mod_eq_of_lt hi] at hval
  .
    have : i.val + 1 = ρ.k := by omega
    simp [this] at h
    simp [← h] at this
    have hk := ρ.hk
    omega

/-- PrevのあとにNextを適用すると元の要素に戻ることを示す定理 -/
@[simp]
theorem cycleNext_cyclePrev
    (ρ : ExposedRotation smp) (i : Fin ρ.k) :
    cycleNext ρ.hk (cyclePrev ρ.hk i) = i := by
  apply Fin.ext
  unfold cycleNext cyclePrev
  simp
  have : i.val + ρ.k - 1 + 1 = i.val + ρ.k := by omega
  simp [this]
  apply Nat.mod_eq_of_lt
  exact i.isLt

/-- NextのあとにPrevを適用すると元の要素に戻ることを示す定理 -/
@[simp]
theorem cyclePrev_cycleNext
    (ρ : ExposedRotation smp) (i : Fin ρ.k) :
    cyclePrev ρ.hk (cycleNext ρ.hk i) = i := by
  apply Fin.ext
  unfold cycleNext cyclePrev
  simp

  have hi : (i : Nat) < ρ.k := i.isLt
  have hk : 1 < ρ.k := by exact ρ.hk

  calc
    ((↑i + 1) % ρ.k + ρ.k - 1) % ρ.k = ((↑i + 1) % ρ.k + (ρ.k - 1)) % ρ.k := by
        congr 1
        omega
    _ = ((↑i + 1) + (ρ.k - 1)) % ρ.k := by rw [Nat.mod_add_mod]
    _ = (↑i + ρ.k) % ρ.k := by
        congr 1
        omega
    _ = ↑i % ρ.k := by simp
    _ = ↑i := Nat.mod_eq_of_lt i.isLt

/-- Nextが単射であることを示す定理 -/
theorem cycleNext_injective
    (ρ : ExposedRotation smp) :
    Function.Injective (cycleNext ρ.hk) := by
  intro i j h
  rw [← ρ.cyclePrev_cycleNext i, ← ρ.cyclePrev_cycleNext j]
  rw [h]

/-- 回転に同じ女性がダブって現れることはない-/
theorem woman_injective
    (ρ : ExposedRotation smp) :
    Function.Injective ρ.woman := by
  intro i j h
  apply ρ.man_injective
  apply ρ.M.matching.partnerOfMan_injective
  simp [ρ.matched]
  exact h

/-- woman iのpartnerはman iである -/
@[simp]
theorem matching_partnerOfWoman_woman
    (ρ : ExposedRotation smp) (i : Fin ρ.k) :
    ρ.M.matching.partnerOfWoman (ρ.woman i) = ρ.man i := by
  rw [← ρ.matched i]
  simp

/-- 回転に含まれる男性の添字を返す -/
noncomputable def indexOf
    (ρ : ExposedRotation smp) (m : smp.Man)
    (hm : ρ.ContainsMan m) : Fin ρ.k :=
  Classical.choose hm

/-- indexOfが男性mの添字を返す -/
theorem man_indexOf
    (ρ : ExposedRotation smp) (m : smp.Man)
    (hm : ρ.ContainsMan m) :
    ρ.man (ρ.indexOf m hm) = m :=
  Classical.choose_spec hm

/-- indexOfが男性mの添字を返す -/
theorem indexOf_man
    (ρ : ExposedRotation smp) (i : Fin ρ.k) :
    ρ.indexOf (ρ.man i) ⟨i, rfl⟩ = i := by
  apply ρ.man_injective
  exact ρ.man_indexOf (ρ.man i) ⟨i, rfl⟩

/-- indexOfが指定された男性の添字を返す -/
theorem indexOf_eq
    (ρ : ExposedRotation smp) (m : smp.Man)
    (hm : ρ.ContainsMan m) (i : Fin ρ.k)
    (hi : ρ.man i = m) :
    ρ.indexOf m hm = i := by
  apply ρ.man_injective
  rw [ρ.man_indexOf m hm]
  exact hi.symm

/-- indexOfが単射であることを示す定理 -/
theorem indexOf_injective
    (ρ : ExposedRotation smp)
    (m₁ m₂ : smp.Man) (hm₁ : ρ.ContainsMan m₁) (hm₂ : ρ.ContainsMan m₂)
    (h : ρ.indexOf m₁ hm₁ = ρ.indexOf m₂ hm₂) :
    m₁ = m₂ := by
  have := ρ.man_indexOf m₁ hm₁
  rw [h] at this
  rw [man_indexOf] at this
  exact this.symm

/-- eliminatedPartnerは回転の除去後の男性mのパートナーを返す -/
noncomputable def eliminatedPartner
    (ρ : ExposedRotation smp) (m : smp.Man) : smp.Woman :=
  by
    classical
    exact if hm : ρ.ContainsMan m then
      ρ.woman (cycleNext ρ.hk (ρ.indexOf m hm))
    else
      ρ.M.matching.partnerOfMan m

/-- man iのパートーはwoman i+1 である-/
@[simp]
theorem eliminatedPartner_man
    (ρ : ExposedRotation smp) (i : Fin ρ.k) :
    ρ.eliminatedPartner (ρ.man i) =
      ρ.woman (cycleNext ρ.hk i) := by
  unfold eliminatedPartner
  have hm: ρ.ContainsMan (ρ.man i) := ⟨i, rfl⟩
  simp [hm]
  congr
  exact ρ.indexOf_eq (ρ.man i) hm i rfl

/-- 回転に含まれない男性mのeliminatedPartnerは、mの元のパートナーである -/
theorem eliminatedPartner_of_not_contains
    (ρ : ExposedRotation smp) (m : smp.Man)
    (hm : ¬ ρ.ContainsMan m) :
    ρ.eliminatedPartner m = ρ.M.matching.partnerOfMan m := by
  simp [eliminatedPartner, hm]

/-- eliminatedPartnerは単射である -/
theorem eliminatedPartner_injective
    (ρ : ExposedRotation smp) :
    Function.Injective ρ.eliminatedPartner := by
  intro m₁ m₂ h
  -- ¬ ρ.containsman mであって、w=M.matching.partnerofman mのとき、w=rho.woman iとなるiは存在しないことを先に示しておく
  have not_exists (m : smp.Man) (hm : ¬ ρ.ContainsMan m) :
      ¬ ∃ i, ρ.woman i = ρ.M.matching.partnerOfMan m := by
    intro h
    obtain ⟨i, hi⟩ := h
    unfold ContainsMan at hm
    push_neg at hm
    have hmi := hm i
    have : ρ.M.matching.partnerOfWoman (ρ.woman i) = ρ.M.matching.partnerOfWoman (ρ.M.matching.partnerOfMan m) := by rw [hi]
    simp at this
    contradiction

  by_cases h₁ : ρ.ContainsMan m₁ <;> simp [eliminatedPartner, h₁] at h
  .
    by_cases h₂ : ρ.ContainsMan m₂ <;> simp [h₂] at h
    .
      apply ρ.woman_injective at h
      apply ρ.cycleNext_injective at h
      exact ρ.indexOf_injective m₁ m₂ h₁ h₂ h
    .
      have := not_exists m₂ h₂
      exfalso
      apply this
      exists cycleNext ρ.hk (ρ.indexOf m₁ h₁)
  .
    by_cases h₂ : ρ.ContainsMan m₂ <;> simp [h₂] at h
    .
      have := not_exists m₁ h₁
      exfalso
      apply this
      exists cycleNext ρ.hk (ρ.indexOf m₂ h₂)
      exact h.symm
    .
      exact ρ.M.matching.partnerOfMan_injective m₁ m₂ h

/-- eliminatedMatchingは回転の除去後のマッチングを返す -/
noncomputable def eliminatedMatching (ρ : ExposedRotation smp) : Matching smp :=
  {
    equiv := Equiv.ofBijective ρ.eliminatedPartner
      ⟨ρ.eliminatedPartner_injective,
        (Finite.injective_iff_surjective_of_equiv ρ.M.matching.equiv).mp
          ρ.eliminatedPartner_injective⟩
  }

/-- eliminatedMatchingは回転の除去後のマッチングを返す -/
@[simp]
theorem eliminatedMatching_partnerOfMan
    (ρ : ExposedRotation smp) (m : smp.Man) :
    ρ.eliminatedMatching.partnerOfMan m = ρ.eliminatedPartner m := by
  simp [eliminatedMatching, Matching.partnerOfMan]


/-- woman iの回転除去後のpartnerはman i-1である -/
@[simp]
theorem eliminatedMatching_partnerOfWoman_woman
    (ρ : ExposedRotation smp) (i : Fin ρ.k) :
    ρ.eliminatedMatching.partnerOfWoman (ρ.woman i) =
      ρ.man (cyclePrev ρ.hk i) := by
  have h := ρ.eliminatedMatching.partnerOfWoman_partnerOfMan
    (ρ.man (cyclePrev ρ.hk i))
  simp at h
  exact h

/-- womanが回転に含まれない場合のpartnerOfWoman は元のマッチングのpartnerである -/
theorem eliminatedMatching_partnerOfWoman_of_not_contains
    (ρ : ExposedRotation smp) (w : smp.Woman)
    (hw : ¬ ρ.ContainsWoman w) :
    ρ.eliminatedMatching.partnerOfWoman w = ρ.M.matching.partnerOfWoman w := by
  set m := ρ.M.matching.partnerOfWoman w with hm
  have hm' : ¬ ρ.ContainsMan m := by
    intro h
    unfold ContainsMan at h
    obtain ⟨i, hi⟩ := h
    apply hw
    exists i
    rw [← ρ.matched i]
    rw [hi, hm]
    simp
  have eliminated_partner : ρ.eliminatedMatching.partnerOfMan m = w := by
    simp
    rw [ρ.eliminatedPartner_of_not_contains m hm']
    simp [hm]
  set eliminated_matching := ρ.eliminatedMatching with hρ
  rw [←eliminated_partner]
  simp

/-- 除去後にwomanからみたpreferanceは改善 -/
theorem woman_prefersOrEqual_eliminatedPartner
    (ρ : ExposedRotation smp) (w : smp.Woman) :
    ρ.eliminatedMatching.partnerOfWoman w ≼[w]
      ρ.M.matching.partnerOfWoman w := by
  by_cases hw : ρ.ContainsWoman w
  ·
    obtain ⟨i, woman_i⟩ := hw
    rw [← woman_i]
    rw [ρ.eliminatedMatching_partnerOfWoman_woman,
      ρ.matching_partnerOfWoman_woman]
    exact le_of_lt (ρ.nextAccepts i)
  ·
    rw [ρ.eliminatedMatching_partnerOfWoman_of_not_contains w hw]
    simp

/-- eliminatedMatchingは安定である -/
theorem eliminatedMatching_isStable
    (ρ : ExposedRotation smp) :
    ρ.eliminatedMatching.IsStable := by
  intro m w hblocking
  unfold Matching.IsBlockingPair at hblocking
  have hwoman : m ≺[w] ρ.M.matching.partnerOfWoman w := lt_of_lt_of_le hblocking.right (ρ.woman_prefersOrEqual_eliminatedPartner w)
  by_cases hm : ρ.ContainsMan m
  ·
    -- ρに男性mが含まれる場合
    -- obtain ⟨i, rfl⟩ := hm
    obtain ⟨i, him⟩ := hm
    rw [← him] at hblocking hwoman
    rw [ρ.eliminatedMatching_partnerOfMan,
      ρ.eliminatedPartner_man] at hblocking
    have hne : w ≠ ρ.woman i := by
      intro h
      rw [h] at hwoman
      rw [ρ.matching_partnerOfWoman_woman] at hwoman
      exact (Woman.prefers_irrefl (ρ.woman i) (ρ.man i)) hwoman
    cases Man.prefers_total (ρ.man i) hne with
    | inl hbetter =>
      -- ρ.man iとwがblocking pairであることを示す
      have : Matching.IsBlockingPair ρ.M.matching (ρ.man i) w := by
        constructor
        .
          simp [ρ.matched]
          exact hbetter
        .
          exact hwoman
      exact ρ.M.isStable (ρ.man i) w this
    | inr hworse =>
      have hnext := ρ.nextIsBest i w hworse hwoman
      exact not_lt_of_ge hnext hblocking.left
  ·
    -- ρに男性mが含まれない場合
    apply ρ.M.isStable m w
    constructor
    ·
      rw [ρ.eliminatedMatching_partnerOfMan,
        ρ.eliminatedPartner_of_not_contains m hm] at hblocking
      exact hblocking.1
    · exact hwoman

/-- 安定マッチングから回転を除去したものを得る -/
noncomputable def eliminate
    (ρ : ExposedRotation smp) : StableMatching smp where
  matching := ρ.eliminatedMatching
  isStable := ρ.eliminatedMatching_isStable

/-- 除去後の男性の相手-/
@[simp]
theorem eliminate_partnerOfMan
    (ρ : ExposedRotation smp) (m : smp.Man) :
    ρ.eliminate.matching.partnerOfMan m = ρ.eliminatedPartner m := by
  exact ρ.eliminatedMatching_partnerOfMan m

/-- man iの相手がwoman i+1になる -/
@[simp]
theorem eliminate_partnerOfMan_man
    (ρ : ExposedRotation smp) (i : Fin ρ.k) :
    ρ.eliminate.matching.partnerOfMan (ρ.man i) =
      ρ.woman (cycleNext ρ.hk i) := by
  rw [ρ.eliminate_partnerOfMan, ρ.eliminatedPartner_man]

/-- 回転に含まれない相手は除去後も変わらない-/
theorem eliminate_partnerOfMan_of_not_contains
    (ρ : ExposedRotation smp) (m : smp.Man)
    (hm : ¬ ρ.ContainsMan m) :
    ρ.eliminate.matching.partnerOfMan m =
      ρ.M.matching.partnerOfMan m := by
  rw [ρ.eliminate_partnerOfMan,
    ρ.eliminatedPartner_of_not_contains m hm]

/-- ρ.M < ρ.eliminateを示す-/
theorem lt_eliminate
    (ρ : ExposedRotation smp) : ρ.M < ρ.eliminate := by
  apply lt_of_le_of_ne
  ·
    -- 男性にとって回転の除去は改善しないことを示す
    intro m
    by_cases hm : ρ.ContainsMan m
    ·
      obtain ⟨i, him⟩ := hm
      rw [← him]
      rw [ρ.matched, ρ.eliminate_partnerOfMan_man]
      apply Nat.le_of_lt
      exact ρ.movesDown i
    · rw [ρ.eliminate_partnerOfMan_of_not_contains m hm]
      simp
  ·
    -- man 0について相手が変わることを示す
    intro h
    let i0 : Fin ρ.k := ⟨0, by
      have hk := ρ.hk
      omega⟩
    let i1 : Fin ρ.k := ⟨1, ρ.hk⟩
    have hequal : ρ.M.matching.partnerOfMan (ρ.man i0) = ρ.eliminate.matching.partnerOfMan (ρ.man i0) := by simp [h]
    have h0 : ρ.M.matching.partnerOfMan (ρ.man i0) = ρ.woman i0 := by rw [ρ.matched]
    have h1 : ρ.eliminate.matching.partnerOfMan (ρ.man i0) = ρ.woman i1 := by
      simp [ρ.eliminate_partnerOfMan]
      congr
      simp [cycleNext, i0 ,i1]
      have hk := ρ.hk
      exact Nat.mod_eq_of_lt hk
    simp [h0, h1] at hequal
    apply ρ.woman_injective at hequal
    simp [i0, i1] at hequal

/-- 回転に含まれない男性についてはMとNでペアは同じ -/
theorem intermediate_partnerOfMan_of_not_contains
    (ρ : ExposedRotation smp)
    (N : StableMatching smp)
    (hMN : ρ.M ≤ N)
    (hNE : N ≤ ρ.eliminate)
    (m : smp.Man)
    (hm : ¬ ρ.ContainsMan m) :
    N.matching.partnerOfMan m = ρ.M.matching.partnerOfMan m := by
  have h₁ := hMN m
  have h₂ := hNE m
  rw [ρ.eliminate_partnerOfMan_of_not_contains m hm] at h₂
  exact Man.prefersOrEqual_antisymm m h₂ h₁

/-- Mとρ.eliminateの間のNはMまたはρ.eliminateのどちらかのパートナーと組むことになる。 -/
theorem intermediate_changed_eq_next
    (ρ : ExposedRotation smp)
    (N : StableMatching smp)
    (hMN : ρ.M ≤ N)
    (hNE : N ≤ ρ.eliminate)
    (i : Fin ρ.k)
    (hchange : N.matching.partnerOfMan (ρ.man i) ≠ ρ.M.matching.partnerOfMan (ρ.man i)) :
    N.matching.partnerOfMan (ρ.man i) = ρ.woman (cycleNext ρ.hk i) := by
  set w := N.matching.partnerOfMan (ρ.man i) with hw
  -- w は現在の woman i とは異なる
  have hw_ne : ρ.woman i ≠ w := by
    rw [ρ.matched] at hchange
    exact hchange.symm
  -- ρ.M ≤ N なので、wはwoman iよりも望ましい
  have hcur_lt : ρ.woman i ≺[ρ.man i] w := by
    apply (Man.prefers_iff_prefersOrEqual_and_ne (ρ.man i) (ρ.woman i) w).mpr
    constructor
    .
      rw [← ρ.matched, hw]
      exact hMN (ρ.man i)
    .
      exact hw_ne
  -- 女性側では N の方を好む
  have hwoman_lt : ρ.man i ≺[w] ρ.M.matching.partnerOfWoman w := by
    have hwoman_le : ρ.man i ≼[w] ρ.M.matching.partnerOfWoman w:= by
      have := (Lattice.le_iff_women_reverse ρ.M N).mp hMN w
      simp [hw] at this
      rw [hw]
      exact this
    have hwoman_ne : ρ.man i ≠ ρ.M.matching.partnerOfWoman w := by
      intro h
      rw [← matching_partnerOfWoman_woman ρ i] at h
      -- ρ.M.mathingの単射性を使う
      have := ρ.M.matching.partnerOfWoman_injective (ρ.woman i) w h
      contradiction
    exact (Woman.prefers_iff_prefersOrEqual_and_ne w (ρ.man i) (ρ.M.matching.partnerOfWoman w)).mpr ⟨hwoman_le, hwoman_ne⟩
  -- exposed rotation の nextIsBest
  have hbest := ρ.nextIsBest i w hcur_lt hwoman_lt

  -- 一方 N ≤ eliminate なので w ≼ next
  have hw_le_next : w ≼[ρ.man i] ρ.woman (cycleNext ρ.hk i) := by
    have h := hNE (ρ.man i)
    simp at h
    rw [hw]
    exact h

  exact Man.prefersOrEqual_antisymm (ρ.man i) hw_le_next hbest

/-- 中間変化は回転中の次の変化に伝播する -/
theorem intermediate_change_propagates
    (ρ : ExposedRotation smp)
    (N : StableMatching smp)
    (hMN : ρ.M ≤ N)
    (hNE : N ≤ ρ.eliminate)
    (i : Fin ρ.k)
    (hchange : N.matching.partnerOfMan (ρ.man i) ≠ ρ.M.matching.partnerOfMan (ρ.man i)) :
    N.matching.partnerOfMan (ρ.man (cycleNext ρ.hk i)) ≠ ρ.M.matching.partnerOfMan (ρ.man (cycleNext ρ.hk i)) := by
  have hi := ρ.intermediate_changed_eq_next N hMN hNE i hchange
  intro hnext
  set j := cycleNext ρ.hk i with hj
  rw [ρ.matched] at hnext
  rw [← hnext] at hi
  have hm_eq := N.matching.partnerOfMan_injective (ρ.man i) (ρ.man j) hi
  -- man i = man j となることが示された
  have ij_eq := ρ.man_injective hm_eq
  rw [hj] at ij_eq
  have hmoves := ρ.movesDown i
  rw [← ij_eq] at hmoves
  exact Man.prefers_irrefl (ρ.man i) (ρ.woman i) hmoves

/-- 中間変化は回転中の次の変化に伝播する -/
theorem intermediate_go_next_propagates
    (ρ : ExposedRotation smp)
    (N : StableMatching smp)
    (hMN : ρ.M ≤ N)
    (hNE : N ≤ ρ.eliminate)
    (i : Fin ρ.k)
    (hchange : N.matching.partnerOfMan (ρ.man i) = ρ.woman (cycleNext ρ.hk i)) :
    N.matching.partnerOfMan (ρ.man (cycleNext ρ.hk i)) = ρ.woman (cycleNext ρ.hk (cycleNext ρ.hk i)) := by
  have hneq : N.matching.partnerOfMan (ρ.man i) ≠ ρ.M.matching.partnerOfMan (ρ.man i) := by
    rw [ρ.matched]
    intro h
    rw [h] at hchange
    have hnext := ρ.movesDown i
    rw [hchange] at hnext
    exact Man.prefers_irrefl (ρ.man i) (ρ.woman (cycleNext ρ.hk i)) hnext
  have hnext := ρ.intermediate_change_propagates N hMN hNE i hneq
  have hnext_eq := ρ.intermediate_changed_eq_next N hMN hNE (cycleNext ρ.hk i) hnext
  exact hnext_eq

/-- cycleNextの反復値 -/
theorem cycleNext_iterate_val
    (ρ : ExposedRotation smp)
    (i : Fin ρ.k)
    (t : Nat) :
    (((cycleNext ρ.hk)^[t]) i).val =
      (i.val + t) % ρ.k := by
  induction t with
  | zero => simp [Nat.mod_eq_of_lt i.isLt]
  | succ t ih =>
    -- t+1回目の適用は、t回目の適用の結果にcycleNextを適用することと同じ
    -- rw [Function.iterate_succ_apply' (cycleNext i ρ.hk) t i]
    rw [Function.iterate_succ_apply' (cycleNext ρ.hk) t i]
    have hmod : (i.val + (t + 1)) % ρ.k = ((i.val + t) % ρ.k + 1) % ρ.k := by rw [← Nat.add_assoc, Nat.mod_add_mod]
    -- t回目の適用の結果をihで書き換える
    rw [hmod, ← ih]
    simp [cycleNext]

/-- 有限回の適用で到達可能 -/
theorem cycleNext_reachable
    (ρ : ExposedRotation smp)
    (i j : Fin ρ.k) :
    ∃ t : Nat, ((cycleNext ρ.hk)^[t]) i = j := by
  -- iからjまでの距離を計算する
  set t := (j.val + ρ.k - i.val) % ρ.k with ht
  exists t
  apply Fin.ext
  rw [ρ.cycleNext_iterate_val i t, ht]
  simp
  have h : ↑i + (↑j + ρ.k - ↑i) = ↑j + ρ.k := by omega
  simp [h, Nat.mod_eq_of_lt j.isLt]

theorem cycleNext_closed
    (ρ : ExposedRotation smp)
    (P : Fin ρ.k → Prop)
    (hstep : ∀ i, P i → P (cycleNext ρ.hk i))
    (i : Fin ρ.k)
    (hi : P i) :
    ∀ j, P j := by
  intro j
  obtain ⟨t, ht⟩ := ρ.cycleNext_reachable i j
  rw [← ht]
  have : ∀ t, P ((cycleNext ρ.hk)^[t] i) := by
    intro t
    induction t with
    | zero => exact hi
    | succ t ih =>
      rw [Function.iterate_succ_apply' (cycleNext ρ.hk) t i]
      exact hstep ((cycleNext ρ.hk)^[t] i) ih
  exact this t

/-- 回転の除去前後の間に別の安定マッチングは存在しない。 -/
theorem covBy_eliminate
    (ρ : ExposedRotation smp) :
    CovBy ρ.M ρ.eliminate := by
  apply covBy_of_eq_or_eq ρ.lt_eliminate
  intro N hMN hNE
  by_cases hNM : N = ρ.M
  · exact Or.inl hNM
  .
    right
    -- このときNとMでペアが変わる男性が存在することを示す
    have hexists : ∃ i, N.matching.partnerOfMan (ρ.man i) ≠ ρ.M.matching.partnerOfMan (ρ.man i) := by
      -- 対偶を示す
      by_contra h
      push_neg at h
      apply hNM
      ext m
      by_cases hm : ρ.ContainsMan m
      · obtain ⟨i, rfl⟩ := hm
        exact h i
      · exact ρ.intermediate_partnerOfMan_of_not_contains N hMN hNE m hm
    obtain ⟨i, hi⟩ := hexists
    have hfirst := ρ.intermediate_changed_eq_next N hMN hNE i hi
    have hpropagate := ρ.intermediate_go_next_propagates N hMN hNE
    have := ρ.cycleNext_closed (fun i => N.matching.partnerOfMan (ρ.man i) = ρ.woman (cycleNext ρ.hk i)) hpropagate i hfirst

    ext m
    by_cases hm : ρ.ContainsMan m
    ·
      obtain ⟨i, rfl⟩ := hm
      have h := this i
      simp [h]
    .
      rw [ρ.eliminate_partnerOfMan_of_not_contains m hm]
      exact ρ.intermediate_partnerOfMan_of_not_contains N hMN hNE m hm

end ExposedRotation

end Rotation
end SMP
end StableMatching
