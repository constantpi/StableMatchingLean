import StableMatching.Rotation.Equiv
import StableMatching.Rotation.Elimination


namespace StableMatching
namespace SMP
namespace Rotation

/-- 2つの安定マッチング間で男性mのパートナーが変更されたかどうか -/
def is_changed_partner (M N : StableMatching smp) (m : Man smp) : Prop :=
  M.matching.partnerOfMan m ≠ N.matching.partnerOfMan m

/-- 男性は今のままがよくて女性は変更してほしいと思う片思いペア-/
def is_one_sided_preferred (M : StableMatching smp) (m : Man smp) (w : Woman smp) : Prop :=
  (M.matching.partnerOfMan m ≺[m] w) ∧ (m ≺[w] M.matching.partnerOfWoman w)

/-- 今の安定マッチングにおいて(m, w)が回転の候補となるかどうか -/
def is_exposed_rotation_candidate
    {smp : SMP n}
    (M : StableMatching smp)
    (m : Man smp)
    (w : Woman smp)
    : Prop :=
  is_one_sided_preferred M m w ∧
  -- 上記を満たすwの中で最良
  (∀ w' : Woman smp, is_one_sided_preferred M m w' → (w ≼[m] w'))

/-- 回転の候補の存在証明-/
theorem exposed_rotation_candidate
    {smp : SMP n}
    (M N : StableMatching smp)
    (horder : M ≤ N)
    (m : Man smp)
    (is_changed : is_changed_partner M N m)
    : ∃ w : Woman smp, (is_exposed_rotation_candidate M m w)
      ∧ is_changed_partner M N (M.matching.partnerOfWoman w)
      ∧ w ≼[m] N.matching.partnerOfMan m
      := by
  set w1 := M.matching.partnerOfMan m with hw1
  set w2 := N.matching.partnerOfMan m with hw2
  have one_sided : is_one_sided_preferred M m w2 := by
    have h1 : w1 ≺[m] w2 := by
      have := horder m
      rw [← hw1, ← hw2] at this
      exact (Man.prefers_iff_prefersOrEqual_and_ne m w1 w2).mpr ⟨this, is_changed⟩
    constructor
    . exact h1
    .
      have := (Lattice.le_iff_women_reverse M N).mp horder w2
      nth_rw 2 [hw2] at this
      simp at this
      apply (Woman.prefers_iff_prefersOrEqual_and_ne w2 m (M.matching.partnerOfWoman w2)).mpr
      constructor
      . exact this
      . intro h_eq
        have : M.matching.partnerOfMan m = N.matching.partnerOfMan m := by
          nth_rw 1 [h_eq]
          simp
          exact hw2
        contradiction

  set candidates := { w : Woman smp | is_one_sided_preferred M m w } with hcandidates
  have w2_in_candidates : w2 ∈ candidates := by simp [hcandidates, one_sided]
  have candidates_nonempty : candidates.Nonempty := by exists w2

  -- 上記を満たすwの中で最良のものを選ぶ
  set w := Function.argminOn (fun w => SMP.manRank m w) candidates candidates_nonempty with hmin
  --wはcandidatesの中に入っている
  have w_in_candidates : w ∈ candidates := Function.argminOn_mem (fun w => SMP.manRank m w) candidates candidates_nonempty
  have one_sided_w : is_one_sided_preferred M m w := by
    simp [hcandidates] at w_in_candidates
    exact w_in_candidates
  have w_is_best : ∀ (w' : smp.Woman), is_one_sided_preferred M m w' → w ≼[m] w' := by
    intro w' h_w'
    have w'_in_candidates : w' ∈ candidates := by
      simp [hcandidates]
      exact h_w'
    -- 最小性をつかう
    have := Function.argminOn_le (fun w => SMP.manRank m w) candidates w'_in_candidates candidates_nonempty
    rw [← hmin] at this
    exact this
  exists w
  constructor
  .
    exact ⟨one_sided_w, w_is_best⟩
  .
    constructor
    .
      unfold is_changed_partner
      by_contra h_eq
      simp at h_eq
      have w_is_better_than_w2 : w ≼[m] w2 := w_is_best w2 one_sided
      by_cases h_case : w = w2
      .
        nth_rw 1 [h_case] at h_eq
        rw [hw2] at h_eq
        have hmw := N.matching.partnerOfMan_injective m (M.matching.partnerOfWoman w) h_eq
        have h_eq' : w = w1 := by
          simp [hmw] at hw1
          exact hw1.symm
        have := one_sided_w.1
        nth_rw 2 [hmw] at this
        simp at this
      .
        match m.prefers_total h_case with
        | Or.inl h_w_better =>
          apply N.isStable m w
          constructor
          .
            rw [hw2] at h_w_better
            exact h_w_better
          .
            nth_rw 2 [h_eq]
            simp
            exact one_sided_w.2
        | Or.inr h_w2_better =>
          exact (m.prefers_iff_not_prefersOrEqual w2 w).mp h_w2_better w_is_better_than_w2
    .
      exact w_is_best w2 one_sided

/-- 回転の候補の相手を返す -/
noncomputable def get_exposed_rotation_candidate_partner
    {smp : SMP n}
    (M N : StableMatching smp)
    (horder : M ≤ N)
    (m : Man smp)
    (is_changed : is_changed_partner M N m)
    : { w : Woman smp // is_exposed_rotation_candidate M m w ∧ is_changed_partner M N (M.matching.partnerOfWoman w) ∧ w ≼[m] N.matching.partnerOfMan m } := by
  have := exposed_rotation_candidate M N horder m is_changed
  -- 選択公理でwを選ぶ
  exact ⟨Classical.choose this, Classical.choose_spec this⟩

/-- MからNへの変化でパートナーが変わった男性 -/
def ChangedMan {smp : SMP n} (M N : StableMatching smp) :=
  {m : Man smp // is_changed_partner M N m}

/-- changed man から、候補女性の現在の相手である changed man へ進む自己写像 -/
noncomputable def next_changed_man
    {smp : SMP n}
    (M N : StableMatching smp)
    (horder : M ≤ N) :
    ChangedMan M N → ChangedMan M N :=
  fun m =>
    let := get_exposed_rotation_candidate_partner M N horder m.1 m.2
    let w := this.1
    let m' := M.matching.partnerOfWoman w
    have is_changed : is_changed_partner M N m' := this.2.2.1
    ⟨m', is_changed⟩

/-- next_changed_manは固定点を持たない-/
theorem next_changed_man_no_fixed_point
    {smp : SMP n}
    (M N : StableMatching smp)
    (horder : M ≤ N) :
    ∀ m : ChangedMan M N, next_changed_man M N horder m ≠ m := by
  intro m h_eq
  -- simp [next_changed_man] at h_eq
  unfold next_changed_man at h_eq
  simp at h_eq
  have h_eq' :M.matching.partnerOfWoman (get_exposed_rotation_candidate_partner M N horder m.1 m.2).1 = m.1 := by simp [← h_eq]
  set w := get_exposed_rotation_candidate_partner M N horder m.1 m.2 with hget
  have := w.2.1.1.1
  nth_rw 2 [← h_eq'] at this
  simp at this

/-- changed man が空でない -/
theorem changed_man_nonempty
    {smp : SMP n}
    (M N : StableMatching smp)
    (hMN : M < N) :
    Nonempty (ChangedMan M N) := by
  obtain ⟨_, ⟨m, h⟩⟩ := (SMP.Lattice.lt_iff_le_and_not_eq_man M N).mp hMN
  exists m
  unfold is_changed_partner
  intro h_eq
  simp [h_eq] at h

/-- 有限 nonempty 型上の自己写像には周期点が存在する -/
theorem exists_periodic_point_of_finite
    {α : Type*}
    [Finite α]
    [Nonempty α]
    (f : α → α) :
    ∃ x : α, x ∈ Function.periodicPts f := by
  let x0 := Classical.choice (by infer_instance : Nonempty α)
  -- 鳩ノ巣原理
  -- have := Finite.exists_ne_map_eq_of_infinite (fun t => (f^[t]) x0)
  obtain ⟨i, j, h_ij, h_eq⟩ := Finite.exists_ne_map_eq_of_infinite (fun t => (f^[t]) x0)
  -- i≠j より iとjの間の大小関係を考える
  cases h_ij.lt_or_gt with
  | inl h_lt =>
    set x := (f^[i]) x0 with hx
    set k := j - i with hk
    have hk_pos : 0 < k := by omega
    have hk_eq : j = k + i := by omega
    have hx' : (f^[k]) x = x := by rw [hx, ← Function.iterate_add_apply, ← hk_eq, ← h_eq]
    exists x, k
  | inr h_gt =>
    set x := (f^[j]) x0 with hx
    set k := i - j with hk
    have hk_pos : 0 < k := by omega
    have hk_eq : i = k + j := by omega
    have hx' : (f^[k]) x = x := by rw [hx, ← Function.iterate_add_apply, ← hk_eq, h_eq]
    exists x, k

/--
changed man の自己写像には長さ2以上の巡回部分が存在する。
その巡回部分を Fin k で添字付けする。
-/
theorem exists_changed_cycle
    {smp : SMP n}
    (M N : StableMatching smp)
    (hMN : M < N) :
    ∃ (k : Nat) (hk : 1 < k) (man : Fin k → ChangedMan M N),
      Function.Injective man ∧
      ∀ i, man (cycleNext hk i) = next_changed_man M N hMN.le (man i) := by
  let : Nonempty (ChangedMan M N) := changed_man_nonempty M N hMN
  let : Finite (ChangedMan M N) := by
    unfold ChangedMan
    infer_instance
  set f := next_changed_man M N hMN.le
  -- 周期点を得る
  obtain ⟨x, hx⟩ := exists_periodic_point_of_finite f
  -- その最小周期を k とする
  set k := Function.minimalPeriod f x with hk
  have h_fk : (f^[k]) x = x := Function.iterate_minimalPeriod
  exists k
  have hk_pos : 1 < k := by
    have : k ≠ 0 := by -- 最小の周期は0ではない
      intro k_zero
      rw [k_zero] at hk
      have := Function.minimalPeriod_eq_zero_iff_notMem_periodicPts.mp hk.symm
      contradiction
    have : k ≠ 1 := by -- 最小の周期が1なら固定点が存在することになる
      intro h_eq
      have : f x = x := by
        simp [h_eq] at h_fk
        exact h_fk
      exact next_changed_man_no_fixed_point M N hMN.le x this
    omega
  exists hk_pos
  -- fの周期点の列を作る
  set man := fun i : Fin k => (f^[i]) x with hman
  exists man
  constructor
  .
    intro i j h_eq
    have : (f^[i]) x = (f^[j]) x := by
      simp [hman] at h_eq
      exact h_eq
    have hi : i.val < Function.minimalPeriod f x := by simp [k]
    have hj : j.val < Function.minimalPeriod f x := by simp [k]
    ext
    exact (Function.iterate_eq_iterate_iff_of_lt_minimalPeriod
        hi hj).mp this
  .
    intro i
    simp [hman]
    have h_lt : i.val < Function.minimalPeriod f x := by simp [k]
    simp [cycleNext]
    by_cases i_small : i.val + 1 < k
    .
      have : (↑i + 1) % k = i.val + 1 := Nat.mod_eq_of_lt i_small
      simp [this, Function.iterate_succ_apply']
    .
      have : i.val + 1 = k := by omega
      simp [← Function.iterate_succ_apply' f, Nat.succ_eq_add_one, this, h_fk]

/-- M < N ならばMの露出回転が存在して、N以下となる。-/
theorem exists_exposedRotation_between
    {smp : SMP n}
    (M N : StableMatching smp)
    (hMN : M < N) :
    -- ∃ ρ : ExposedRotation smp, ρ.eliminate ≤ N := by
    ∃ ρ : ExposedRotation smp,
      ρ.M = M ∧
      ρ.eliminate ≤ N := by
  obtain ⟨k, hk, man, h_inj, h_next⟩ := exists_changed_cycle M N hMN

  set man' := fun i : Fin k => (man i).1 with hman
  set woman := fun i : Fin k => M.matching.partnerOfMan (man i).1 with hwoman

  have hman_injective : Function.Injective man' := by
    intro i j h_eq
    have : man i = man j := by
      simp [hman] at h_eq
      exact Subtype.ext h_eq
    exact h_inj this

  have h_matched : ∀ i, M.matching.partnerOfMan (man' i) = woman i := by simp [hman, hwoman]

  have movesDown : ∀ (i : Fin k), woman i ≺[man' i] woman (cycleNext hk i) := by
    intro i
    simp [hman, hwoman, h_next i, next_changed_man]
    set m := man i
    set w := get_exposed_rotation_candidate_partner M N hMN.le m.1 m.2
    exact w.2.1.1.1

  have nextAccepts : ∀ (i : Fin k), man' i ≺[woman (cycleNext hk i)] man' (cycleNext hk i) := by
    intro i
    simp [hman, hwoman, h_next i, next_changed_man]
    set m := man i
    set w := get_exposed_rotation_candidate_partner M N hMN.le m.1 m.2
    exact w.2.1.1.2

  have nextAccepts' : ∀ (i : Fin k), man' (cyclePrev hk i) ≺[woman i] man' i := by
    intro i
    have := nextAccepts (cyclePrev hk i)
    have next_prev : cycleNext hk (cyclePrev hk i) = i := by
      simp [cycleNext, cyclePrev]
      have : i.val + k - 1 + 1 = i.val + k := by omega
      simp [this]
      exact Fin.ext (Nat.mod_eq_of_lt i.isLt)
    rw [next_prev] at this
    exact this

  have nextIsBest : ∀ (i : Fin k) (w : smp.Woman),
      (woman i ≺[man' i] w) → (man' i ≺[w] M.matching.partnerOfWoman w) → woman (cycleNext hk i) ≼[man' i] w := by
    intro i w h_w_better h_m_better
    simp [man', woman, h_next i, next_changed_man]
    set w' := get_exposed_rotation_candidate_partner M N hMN.le (man i).1 (man i).2
    have := w'.2.1.2 w
    simp [is_one_sided_preferred] at this
    apply this
    .
      rw [show M.matching.partnerOfMan (man' i) = woman i by simp [hman,hwoman]]
      exact h_w_better
    .
      simp [man'] at h_m_better
      exact h_m_better

  let ρ : ExposedRotation smp := {
    M := M,
    k := k,
    hk := hk,
    man := man',
    woman := woman,
    man_injective := hman_injective,
    matched := h_matched,
    movesDown := movesDown,
    nextAccepts := nextAccepts',
    nextIsBest := nextIsBest
  }

  exists ρ

  constructor
  . rfl
  .
    intro m
    simp
    by_cases h_m : ∃ i, man' i = m
    .
      obtain ⟨i, h_eq⟩ := h_m
      simp [← h_eq]
      simp [show man' i = ρ.man i by simp [ρ]]
      simp [ρ, woman, h_next i, next_changed_man]
      set w := get_exposed_rotation_candidate_partner M N hMN.le (man i).1 (man i).2
      exact w.2.2.2
    .
      simp [ρ.eliminatedPartner_of_not_contains m h_m]
      exact hMN.le m


end Rotation
end SMP
end StableMatching
