import StableMatching.Algorithm.GaleShapley.Iteration

namespace StableMatching
namespace SMP
namespace GSState

/-- 現在の状態で提案男性がいないという命題-/
def noProposingMan {sm : SMP n} (s : ValidGSState sm) : Prop :=
  s.state.findProposingMan = none

/-- 提案回数が単調に増加することを示す-/
theorem proposeStep_proposalCount
    {sm : SMP n}
    (s : GSState sm)
    (m : sm.Man)
    (hnext : s.nextRank m < n) :
    (totalProposals (proposeStep s m hnext)) = totalProposals s + 1 := by
  unfold totalProposals
  have next_rank := proposeStep_nextRank s m hnext

  have hm_mem : m ∈ (Finset.univ : Finset sm.Man) := by simp only [Finset.mem_univ]
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
    {sm : SMP n}
    (s : GSState sm) :
    totalProposals s ≤ n * n := by
  unfold totalProposals
  have : ∑ m : sm.Man, (s.nextRank m).val ≤ ∑ m : sm.Man, n := by
    apply Finset.sum_le_sum
    intro m _
    omega
  have sum_n : ∑ m : sm.Man, n = n * n := by
    simp [Finset.sum_const, Finset.card_univ]
    left
    exact sm.card_man
  rw [← sum_n]
  exact this


/-- GSアルゴリズムの出力において、提案男性がいない状態に到達する-/
theorem GSloop_terminates {sm : SMP n} : ∃k, (k ≤ n * n + 1 ∧ noProposingMan (GSloop (sm:=sm) k)) := by
  -- 背理法を使う
  by_contra h
  push_neg at h -- すべての k ≤ n * n + 1 に対して、提案男性が存在する
  -- このときtotalProposalsは単調に増加するので、∀k ≤ n * n + 1, totalProposals (GSloop k) = k となる
  have total_proposals_increasing : ∀ k ≤ n * n + 1, totalProposals (sm:=sm) (GSloop k).state = k := by
    intro k
    induction k with
    | zero => simp [GSloop, initial, totalProposals, GSiteration]
    | succ k ih =>
      intro hk
      have hk_le : k ≤ n * n + 1 := by omega
      have k_proposing_man := h k hk_le
      have : GSloop (sm:=sm) (k + 1) = Step (GSloop (sm:=sm) k) := by rfl
      rw [this]
      set k_state := GSloop (sm:=sm) k with hk_state
      have k_state_total := ih hk_le
      have k_state_proposing_man : ∃ m, k_state.state.findProposingMan = some m := by
        unfold noProposingMan at k_proposing_man
        generalize hfind : k_state.state.findProposingMan = f
        cases f with
        | none => contradiction
        | some m => exact ⟨m, by rfl⟩
      have hstep : totalProposals (Step k_state).state = totalProposals k_state.state + 1 := by
        unfold Step
        dsimp only
        split
        · contradiction
        · rename_i m' hfind
          simp only
          apply proposeStep_proposalCount
      rw [hstep, k_state_total]




  have htotal := total_proposals_increasing (n * n + 1) (le_refl _)
  have hbound := totalProposals_le (GSloop (sm := sm) (n * n + 1)).state
  omega



end GSState
end SMP
end StableMatching
