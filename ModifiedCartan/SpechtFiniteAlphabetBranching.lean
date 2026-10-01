import ModifiedCartan.SpechtBranchingCommonAlphabet
import ModifiedCartan.FixedPointDeletion

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

theorem card_erase_eq_partition_remove {A : Type*} [Fintype A] [DecidableEq A]
    (μ : YoungDiagram) (h : Fintype.card A = partitionSize μ) (a : A) (b : YoungCorner μ) :
    Fintype.card (↥(Finset.univ.erase a)) = partitionSize (removePartitionBox μ b) := by
  rw [Fintype.card_coe, Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ,
    h, partitionSize_removePartitionBox]

/-- Restriction branching on any actual finite alphabet, with the fixed letter deleted.
This supplies the character input for LaTeX `eq:KP-translation`. -/
theorem spechtCharacterOn_branching {A : Type*} [Fintype A] [DecidableEq A]
    (μ : YoungDiagram) (h : Fintype.card A = partitionSize μ) (a : A)
    (g : Equiv.Perm A) (hg : g a = a) :
    spechtCharacterOn μ h g =
      ∑ b : YoungCorner μ, spechtCharacterOn (removePartitionBox μ b)
        (card_erase_eq_partition_remove μ h a b) (deleteFixedPoint a g hg) := by
  let e : A ≃ YoungBoxes μ := (Fintype.equivFinOfCardEq h).trans (youngBoxNumbering μ).symm
  let G : youngLetterStabilizer μ (e a) :=
    fixedPointStabilizerElement (e a) (e.permCongr g) (permCongr_fixes e a g hg)
  rw [spechtCharacterOn_eq_young μ h e g]
  have hb := youngSpechtCharacter_branching_remaining μ (e a) G
  change (youngSpechtRepresentation μ).character (e.permCongr g) = _ at hb
  refine hb.trans ?_
  apply Finset.sum_congr rfl
  intro b _
  change spechtCharacterOn (removePartitionBox μ b) (youngRemaining_card μ (e a) b)
      (deleteFixedPoint (e a) (e.permCongr g) (permCongr_fixes e a g hg)) = _
  rw [← deleteFixedPoint_relabel e a g hg]
  exact spechtCharacterOn_relabel (removePartitionBox μ b)
    (card_erase_eq_partition_remove μ h a b) (youngRemaining_card μ (e a) b)
    (eraseLetterEquiv e a) (deleteFixedPoint a g hg)

end
end ModifiedCartan


