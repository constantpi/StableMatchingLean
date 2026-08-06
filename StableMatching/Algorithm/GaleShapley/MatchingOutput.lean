import StableMatching.Algorithm.GaleShapley.Correctness

namespace StableMatching
namespace SMP
namespace GSState

/-- 提案男性がいないなら女性から男性への関数が存在する -/
def engaged_function_of_noProposingMan
    {sm : SMP n}
    (s : ValidGSState sm)
    (hno : noProposingMan s) :
    sm.Woman → sm.Man :=
  fun w => (s.state.engaged w).get (by
    obtain ⟨m, hm⟩ := allWomenEngaged_of_noProposingMan s hno w
    simp [hm]
  )

/-- 提案男性がいないなら女性から男性への関数は単射である -/
theorem injective_engaged_function_of_noProposingMan
    {sm : SMP n}
    (s : ValidGSState sm)
    (hno : noProposingMan s) :
    Function.Injective (engaged_function_of_noProposingMan s hno) := by
  intro w₁ w₂ h
  obtain ⟨m₁, hm₁⟩ := allWomenEngaged_of_noProposingMan s hno w₁
  obtain ⟨m₂, hm₂⟩ := allWomenEngaged_of_noProposingMan s hno w₂
  unfold engaged_function_of_noProposingMan at h
  simp [hm₁, hm₂] at h
  rw [← h] at hm₂
  exact s.validEngagement w₁ w₂ m₁ hm₁ hm₂

/-- 提案男性がいないなら女性から男性への関数は全単射である -/
theorem surjective_engaged_function_of_noProposingMan
    {sm : SMP n}
    (s : ValidGSState sm)
    (hno : noProposingMan s) :
    Function.Bijective (engaged_function_of_noProposingMan s hno) := by
  have inj := injective_engaged_function_of_noProposingMan s hno

  have same_card : Fintype.card sm.Man = Fintype.card sm.Woman := by rw [sm.card_man, sm.card_woman]

  exact (Fintype.bijective_iff_injective_and_card (engaged_function_of_noProposingMan s hno)).mpr
    ⟨inj, same_card.symm⟩

/-- 提案男性がいないならマッチングを与える -/
def matching_of_noProposingMan
    {sm : SMP n}
    (s : ValidGSState sm)
    (hno : noProposingMan s) :
    Matching sm :=
  let f := engaged_function_of_noProposingMan s hno
  let f_bij := surjective_engaged_function_of_noProposingMan s hno
  -- 逆写像を作る必要がある
  let f_inv := Fintype.bijInv f_bij
  let equiv : sm.Man ≃ sm.Woman := {
    toFun := f_inv
    invFun := f
    left_inv := Fintype.rightInverse_bijInv f_bij
    right_inv := Fintype.leftInverse_bijInv f_bij
  }
  { equiv }



end GSState
end SMP
end StableMatching
