import ModifiedCartan.FixedPointPermutationSums
import ModifiedCartan.ClassWeightedOperator
import ModifiedCartan.SpechtFiniteAlphabetBranching

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

theorem card_erase_of_successor_size {A : Type*} [Fintype A] [DecidableEq A]
    (μ : YoungDiagram) (h : Fintype.card A = partitionSize μ + 1) (a : A) :
    Fintype.card (↥(Finset.univ.erase a)) = partitionSize μ := by
  rw [Fintype.card_coe, Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ, h]
  omega

/-- The actual one-letter induction character formula, as a sum over fixed
letters. Its Specht expansion is proved separately. -/
def inducedSpechtCharacter {A : Type*} [Fintype A] [DecidableEq A]
    (μ : YoungDiagram) (h : Fintype.card A = partitionSize μ + 1) (g : Equiv.Perm A) : ℂ :=
  ∑ a : A, if hg : g a = a then
    spechtCharacterOn μ (card_erase_of_successor_size μ h a) (deleteFixedPoint a g hg) else 0

theorem inducedSpechtCharacter_relabel {A B : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] (μ : YoungDiagram)
    (hA : Fintype.card A = partitionSize μ + 1) (hB : Fintype.card B = partitionSize μ + 1)
    (e : A ≃ B) (g : Equiv.Perm A) :
    inducedSpechtCharacter μ hB (e.permCongr g) = inducedSpechtCharacter μ hA g := by
  unfold inducedSpechtCharacter
  rw [← e.sum_comp]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hg : g a = a
  · rw [dif_pos (permCongr_fixes e a g hg), dif_pos hg, ← deleteFixedPoint_relabel e a g hg]
    exact spechtCharacterOn_relabel μ (card_erase_of_successor_size μ hA a)
      (card_erase_of_successor_size μ hB (e a)) (eraseLetterEquiv e a) (deleteFixedPoint a g hg)
  · have he : e.permCongr g (e a) ≠ e a := by
      intro he
      apply hg
      apply e.injective
      simpa only [Equiv.permCongr_apply, Equiv.symm_apply_apply] using he
    rw [dif_neg he, dif_neg hg]

theorem inducedSpechtCharacter_conjugationInvariant {A : Type*} [Fintype A] [DecidableEq A]
    (μ : YoungDiagram) (h : Fintype.card A = partitionSize μ + 1) :
    IsConjugationInvariant (inducedSpechtCharacter μ h) := by
  intro g u
  have he : u.permCongr g = u * g * u⁻¹ := by
    apply Equiv.ext
    intro a
    rfl
  rw [← he]
  exact inducedSpechtCharacter_relabel μ h h u g

theorem inducedSpechtCharacter_inv {A : Type*} [Fintype A] [DecidableEq A]
    (μ : YoungDiagram) (h : Fintype.card A = partitionSize μ + 1) (g : Equiv.Perm A) :
    inducedSpechtCharacter μ h g⁻¹ = ∑ a : A, if hg : g a = a then
      spechtCharacterOn μ (card_erase_of_successor_size μ h a) (deleteFixedPoint a g hg)⁻¹ else 0 := by
  unfold inducedSpechtCharacter
  apply Finset.sum_congr rfl
  intro a _
  by_cases hg : g a = a
  · rw [dif_pos (inverse_fixes_of_fixes a g hg), dif_pos hg, deleteFixedPoint_inv]
  · have hi : g⁻¹ a ≠ a := by
      intro hi
      apply hg
      simpa only [inv_inv] using inverse_fixes_of_fixes a g⁻¹ hi
    rw [dif_neg hi, dif_neg hg]

end
end ModifiedCartan


