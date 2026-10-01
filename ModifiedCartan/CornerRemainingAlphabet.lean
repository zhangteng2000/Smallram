import ModifiedCartan.CornerCharacterContributions

open scoped Classical

namespace ModifiedCartan
noncomputable section

/-- The common alphabet left after deleting a chosen fixed letter. -/
def youngRemainingPermutation (μ : YoungDiagram) (a : YoungBoxes μ)
    (g : youngLetterStabilizer μ a) : Equiv.Perm (↥(Finset.univ.erase a)) :=
  (supportedPermutationEquiv (Finset.univ.erase a)).symm g

theorem youngRemainingPermutation_apply (μ : YoungDiagram) (a : YoungBoxes μ)
    (g : youngLetterStabilizer μ a) (x : ↥(Finset.univ.erase a)) :
    (youngRemainingPermutation μ a g x).val = g.val x.val := by
  have he := supportedPermutationEquiv_apply_coe (Finset.univ.erase a)
    (youngRemainingPermutation μ a g) x
  have hi : supportedPermutationEquiv (Finset.univ.erase a)
      (youngRemainingPermutation μ a g) = g :=
    (supportedPermutationEquiv (Finset.univ.erase a)).apply_symm_apply g
  rw [hi] at he
  exact he.symm

/-- Each corner-removal alphabet is relabeled to the same remaining letters. -/
def youngCornerRemainingEquiv (μ : YoungDiagram) (a : YoungBoxes μ) (b : YoungCorner μ) :
    YoungBoxes (removePartitionBox μ b) ≃ ↥(Finset.univ.erase a) :=
  (youngRemovedSetEquiv μ b).trans
    ((Equiv.swap a b.val).symm.subtypeEquiv (by
      intro x
      simp only [Finset.mem_erase, Finset.mem_univ, and_true, ne_eq, Equiv.symm_apply_eq,
        Equiv.swap_apply_left]))

theorem youngCornerRemainingEquiv_apply_val (μ : YoungDiagram) (a : YoungBoxes μ)
    (b : YoungCorner μ) (x : YoungBoxes (removePartitionBox μ b)) :
    (youngCornerRemainingEquiv μ a b x).val =
      (Equiv.swap a b.val).symm (youngBoxBeforeRemoval μ b x) := rfl

theorem youngCornerRemainingEquiv_intertwines (μ : YoungDiagram) (a : YoungBoxes μ)
    (b : YoungCorner μ) (g : youngLetterStabilizer μ a)
    (x : YoungBoxes (removePartitionBox μ b)) :
    youngCornerRemainingEquiv μ a b (youngCornerRemovalHom μ a b g x) =
      youngRemainingPermutation μ a g (youngCornerRemainingEquiv μ a b x) := by
  apply Subtype.ext
  rw [youngCornerRemainingEquiv_apply_val, youngRemainingPermutation_apply,
    youngCornerRemainingEquiv_apply_val, ← youngRemovalPermutation_apply_before]
  have he : youngRemovalPermutationEquiv μ b (youngCornerRemovalHom μ a b g) =
      youngLetterStabilizerConjugate μ a b.val (Equiv.swap a b.val)
        (Equiv.swap_apply_left a b.val) g :=
    (youngRemovalPermutationEquiv μ b).apply_symm_apply _
  rw [he]
  change (Equiv.swap a b.val).symm
      ((Equiv.swap a b.val) (g.val ((Equiv.swap a b.val).symm (youngBoxBeforeRemoval μ b x)))) = _
  exact (Equiv.swap a b.val).symm_apply_apply _

theorem youngCornerRemainingEquiv_permCongr (μ : YoungDiagram) (a : YoungBoxes μ)
    (b : YoungCorner μ) (g : youngLetterStabilizer μ a) :
    (youngCornerRemainingEquiv μ a b).permCongr (youngCornerRemovalHom μ a b g) =
      youngRemainingPermutation μ a g := by
  apply Equiv.ext
  intro y
  obtain ⟨x, rfl⟩ := (youngCornerRemainingEquiv μ a b).surjective y
  rw [Equiv.permCongr_apply, Equiv.symm_apply_apply]
  exact youngCornerRemainingEquiv_intertwines μ a b g x

theorem youngRemaining_card (μ : YoungDiagram) (a : YoungBoxes μ) (b : YoungCorner μ) :
    Fintype.card (↥(Finset.univ.erase a)) = partitionSize (removePartitionBox μ b) :=
  Fintype.card_congr ((youngCornerRemainingEquiv μ a b).symm.trans
    (youngBoxNumbering (removePartitionBox μ b))) |>.trans (Fintype.card_fin _)

end
end ModifiedCartan


