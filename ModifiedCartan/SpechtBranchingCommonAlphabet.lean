import ModifiedCartan.CornerRemainingAlphabet
import ModifiedCartan.SpechtCharacterBranching
import ModifiedCartan.SpechtCharacterLabels

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

theorem youngCornerCharacter_eq_remaining (μ : YoungDiagram) (a : YoungBoxes μ)
    (b : YoungCorner μ) (g : youngLetterStabilizer μ a) :
    youngCornerCharacter μ a b g =
      spechtCharacterOn (removePartitionBox μ b) (youngRemaining_card μ a b)
        (youngRemainingPermutation μ a g) := by
  rw [spechtCharacterOn_eq_young (removePartitionBox μ b) (youngRemaining_card μ a b)
    (youngCornerRemainingEquiv μ a b).symm]
  rw [← youngCornerRemainingEquiv_permCongr μ a b g]
  exact congrArg (youngSpechtRepresentation (removePartitionBox μ b)).character
    ((youngCornerRemainingEquiv μ a b).permCongr.symm_apply_apply
      (youngCornerRemovalHom μ a b g)).symm

/-- The branching sum uses one and the same remaining-letter permutation in every summand. -/
theorem youngSpechtCharacter_branching_remaining (μ : YoungDiagram) (a : YoungBoxes μ)
    (g : youngLetterStabilizer μ a) :
    (youngSpechtRepresentation μ).character g.val =
      ∑ b : YoungCorner μ,
        spechtCharacterOn (removePartitionBox μ b) (youngRemaining_card μ a b)
          (youngRemainingPermutation μ a g) := by
  rw [youngSpechtCharacter_branching μ a g]
  apply Finset.sum_congr rfl
  intro b _
  exact youngCornerCharacter_eq_remaining μ a b g

end
end ModifiedCartan


