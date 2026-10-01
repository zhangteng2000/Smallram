import ModifiedCartan.SpechtRowCharacters
import ModifiedCartan.RowFiltrationCharacterRelabel

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

/-- Relabel the fixed letter to the corner and delete it, as a group homomorphism. -/
def youngCornerRemovalHom (μ : YoungDiagram) (a : YoungBoxes μ) (b : YoungCorner μ) :
    youngLetterStabilizer μ a →* Equiv.Perm (YoungBoxes (removePartitionBox μ b)) :=
  (youngRemovalPermutationEquiv μ b).symm.toMonoidHom.comp
    (youngLetterStabilizerConjugate μ a b.val (Equiv.swap a b.val) (Equiv.swap_apply_left a b.val))

def youngCornerCharacter (μ : YoungDiagram) (a : YoungBoxes μ) (b : YoungCorner μ)
    (g : youngLetterStabilizer μ a) : ℂ :=
  (youngSpechtRepresentation (removePartitionBox μ b)).character (youngCornerRemovalHom μ a b g)

theorem youngSpechtRowCharacter_corner_at_letter (μ : YoungDiagram) (a : YoungBoxes μ)
    (b : YoungCorner μ) (g : youngLetterStabilizer μ a) :
    youngSpechtRowCharacter μ a (b.val.val.1 + 1) g =
      youngSpechtRowCharacter μ a b.val.val.1 g + youngCornerCharacter μ a b g := by
  have ht := youngSpechtRowCharacter_corner μ b (youngCornerRemovalHom μ a b g)
  have he : youngRemovalPermutationEquiv μ b (youngCornerRemovalHom μ a b g) =
      youngLetterStabilizerConjugate μ a b.val (Equiv.swap a b.val)
        (Equiv.swap_apply_left a b.val) g :=
    (youngRemovalPermutationEquiv μ b).apply_symm_apply _
  rw [he] at ht
  unfold youngSpechtRowCharacter
  rw [youngSpechtRowFiltration_character_relabel μ a b.val (Equiv.swap a b.val)
        (Equiv.swap_apply_left a b.val) (b.val.val.1 + 1) g,
      youngSpechtRowFiltration_character_relabel μ a b.val (Equiv.swap a b.val)
        (Equiv.swap_apply_left a b.val) b.val.val.1 g]
  exact ht

def youngCornerCharacterAtRow (μ : YoungDiagram) (a : YoungBoxes μ) (r : ℕ)
    (g : youngLetterStabilizer μ a) : ℂ :=
  ∑ b : YoungCorner μ, if b.val.val.1 = r then youngCornerCharacter μ a b g else 0

theorem youngCornerCharacterAtRow_corner (μ : YoungDiagram) (a : YoungBoxes μ)
    (b : YoungCorner μ) (g : youngLetterStabilizer μ a) :
    youngCornerCharacterAtRow μ a b.val.val.1 g = youngCornerCharacter μ a b g := by
  unfold youngCornerCharacterAtRow
  rw [Finset.sum_eq_single b]
  · simp
  · intro c _ hcb
    have hrow : c.val.val.1 ≠ b.val.val.1 := fun h => hcb (youngCorner_row_injective μ h)
    simp [hrow]
  · simp

theorem youngCornerCharacterAtRow_zero_of_no_corner (μ : YoungDiagram) (a : YoungBoxes μ)
    (r : ℕ) (hn : ¬ ∃ b : YoungCorner μ, b.val.val.1 = r) (g : youngLetterStabilizer μ a) :
    youngCornerCharacterAtRow μ a r g = 0 := by
  apply Finset.sum_eq_zero
  intro b _
  have hb : b.val.val.1 ≠ r := fun hb => hn ⟨b, hb⟩
  simp [hb]

theorem youngSpechtRowCharacter_step (μ : YoungDiagram) (a : YoungBoxes μ)
    (r : ℕ) (hr : r < μ.colLen 0) (g : youngLetterStabilizer μ a) :
    youngSpechtRowCharacter μ a (r + 1) g =
      youngSpechtRowCharacter μ a r g + youngCornerCharacterAtRow μ a r g := by
  by_cases hn : ∃ b : YoungCorner μ, b.val.val.1 = r
  · obtain ⟨b, rfl⟩ := hn
    rw [youngCornerCharacterAtRow_corner]
    exact youngSpechtRowCharacter_corner_at_letter μ a b g
  · rw [youngCornerCharacterAtRow_zero_of_no_corner μ a r hn g, add_zero]
    exact youngSpechtRowCharacter_eq_of_no_corner μ a r hr hn g

theorem youngCornerCharacterAtRow_sum (μ : YoungDiagram) (a : YoungBoxes μ)
    (g : youngLetterStabilizer μ a) :
    (∑ r ∈ Finset.range (μ.colLen 0), youngCornerCharacterAtRow μ a r g) =
      ∑ b : YoungCorner μ, youngCornerCharacter μ a b g := by
  unfold youngCornerCharacterAtRow
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  have hb : b.val.val.1 < μ.colLen 0 := (youngCornerRowIndex μ b).isLt
  simp [hb]

end
end ModifiedCartan


