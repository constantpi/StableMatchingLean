import StableMatching.Algorithm.GaleShapley.Iteration

namespace StableMatching
namespace SMP
namespace GSState

/-- 現在の状態で提案男性がいないという命題-/
def noProposingMan {smp : SMP n} (s : ValidGSState smp) : Prop :=
  s.state.findProposingMan = none

/-- 提案回数が単調に増加することを示す-/
theorem proposeStep_proposalCount
    {smp : SMP n}
    (s : GSState smp)
    (m : smp.Man)
    (hnext : s.nextRank m < n) :
    (totalProposals (proposeStep s m hnext)) = totalProposals s + 1 := by
  unfold totalProposals
  have next_rank := proposeStep_nextRank s m hnext

  have hm_mem : m ∈ (Finset.univ : Finset smp.Man) := by simp only [Finset.mem_univ]
  have hother :
    ∀ x ≠ m,
      ((s.proposeStep m hnext).nextRank x).val = (s.nextRank x).val := by
    intro x hne
    simp [next_rank, hne]
  have erase_sum :  ∑ x ∈ Finset.univ.erase m, ↑((s.proposeStep m hnext).nextRank x).val = ∑ x ∈ Finset.univ.erase m, ↑(s.nextRank x).val := by
    apply Finset.sum_congr rfl
    intro x hx
    have xne : x ≠ m := by
      simp [Finset.mem_erase] at hx
      exact hx
    simp [next_rank, xne]
  rw [← Finset.sum_erase_add _ _ hm_mem]
  rw [erase_sum]
  simp [next_rank]
  rw [← Finset.sum_erase_add _ _ hm_mem]
  ac_rfl

theorem totalProposals_le
    {smp : SMP n}
    (s : GSState smp) :
    totalProposals s ≤ n * n := by
  unfold totalProposals
  have : ∑ m : smp.Man, (s.nextRank m).val ≤ ∑ m : smp.Man, n := by
    apply Finset.sum_le_sum
    intro m _
    omega
  have sum_n : ∑ m : smp.Man, n = n * n := by
    simp [Finset.sum_const, Finset.card_univ]
    left
    exact smp.card_man
  rw [← sum_n]
  exact this


/-- GSアルゴリズムの出力において、一定の回数で提案男性がいない状態に到達する -/
theorem GSloop_terminates {smp : SMP n} : ∃k, (k ≤ n * n + 1 ∧ noProposingMan (GSloop (smp:=smp) k)) := by
  have exists_proposingMan_iff (s : ValidGSState smp) :
      ¬ noProposingMan s ↔ ∃ m, s.state.findProposingMan = some m := by
    unfold noProposingMan
    constructor
    · intro h
      match hfind : s.state.findProposingMan with
      | none => contradiction
      | some m => exact ⟨m, by rfl⟩
    · rintro ⟨m, hm⟩ hnone
      simp [hm] at hnone

  have step_totalProposals (s : ValidGSState smp) (m : smp.Man)
      (hm : s.state.findProposingMan = some m) :
      totalProposals (Step s).state = totalProposals s.state + 1 := by
    unfold Step
    dsimp
    split
    · rename_i is_none
      rw [hm] at is_none
      contradiction
    . rename_i m' hfind
      simp
      apply proposeStep_proposalCount


  -- 背理法を使う
  by_contra h
  push_neg at h -- すべての k ≤ n * n + 1 に対して、提案男性が存在する
  -- このときtotalProposalsは単調に増加するので、∀k ≤ n * n + 1, totalProposals (GSloop k) = k となる
  have total_proposals_increasing : ∀ k ≤ n * n + 1, totalProposals (smp:=smp) (GSloop k).state = k := by
    intro k
    induction k with
    | zero => simp [GSloop, initial, totalProposals, GSiteration]
    | succ k ih =>
      intro hk
      have hk_le : k ≤ n * n + 1 := by omega
      have : GSloop (smp:=smp) (k + 1) = Step (GSloop (smp:=smp) k) := by rfl
      rw [this]
      set k_state := GSloop (smp:=smp) k with hk_state
      have k_state_total := ih hk_le
      obtain ⟨m, hm⟩ := (exists_proposingMan_iff k_state).mp (h k hk_le)
      rw [step_totalProposals k_state m hm, k_state_total]

  have htotal := total_proposals_increasing (n * n + 1) (le_refl _)
  have hbound := totalProposals_le (GSloop (smp := smp) (n * n + 1)).state
  omega

/-- n^2 + 1回の反復後に提案男性がいない状態に到達する -/
theorem GSloop_terminates_at_n2_plus_1 {smp : SMP n} : noProposingMan (GSloop (smp:=smp) (n * n + 1)) := by
  obtain ⟨k, hk⟩ := GSloop_terminates (smp:=smp)
  -- k回以上繰り返して呼ぶと、提案男性がいない状態に到達する
  have : ∀t, noProposingMan (GSloop (smp:=smp) (k + t)) := by
    intro t
    induction t with
    | zero => exact hk.right
    | succ t ih =>
      have : GSloop (smp:=smp) (k + (t + 1)) = Step (GSloop (smp:=smp) (k + t)) := by rfl
      rw [this]
      unfold Step
      simp [noProposingMan] at *
      split
      . exact ih
      . rename_i m hfind
        rw [hfind] at ih
        contradiction
  have hkn : k ≤ n * n + 1 := hk.left
  let t := n * n + 1 - k
  have hkn_plus : k + t = n * n + 1 := by omega
  have : noProposingMan (GSloop (smp:=smp) (k + t)) := this t
  rw [hkn_plus] at this
  exact this

end GSState
end SMP
end StableMatching
