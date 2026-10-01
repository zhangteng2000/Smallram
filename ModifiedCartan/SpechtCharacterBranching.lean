import ModifiedCartan.CornerCharacterContributions

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

theorem youngSpechtRowCharacter_zero (μ : YoungDiagram) (a : YoungBoxes μ)
    (g : youngLetterStabilizer μ a) : youngSpechtRowCharacter μ a 0 g = 0 := by
  unfold youngSpechtRowCharacter
  rw [youngSpechtRowFiltration_zero]
  unfold Representation.character
  have hz : (⊥ : Subrepresentation (youngLetterRepresentation μ a)).toRepresentation g = 0 := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    change youngLetterRepresentation μ a g v.val = 0
    rw [show v.val = 0 from v.property, map_zero]
  rw [hz, map_zero]

theorem youngSpechtRowCharacter_height (μ : YoungDiagram) (a : YoungBoxes μ)
    (g : youngLetterStabilizer μ a) :
    youngSpechtRowCharacter μ a (μ.colLen 0) g = (youngSpechtRepresentation μ).character g.val := by
  unfold youngSpechtRowCharacter
  rw [youngSpechtRowFiltration_height]
  rfl

theorem youngSpechtRowCharacter_partial_sum (μ : YoungDiagram) (a : YoungBoxes μ)
    (g : youngLetterStabilizer μ a) (n : ℕ) (hn : n ≤ μ.colLen 0) :
    youngSpechtRowCharacter μ a n g =
      ∑ r ∈ Finset.range n, youngCornerCharacterAtRow μ a r g := by
  induction n with
  | zero => simp [youngSpechtRowCharacter_zero]
  | succ n ih =>
    rw [youngSpechtRowCharacter_step μ a n (by omega) g,
      ih (by omega), Finset.sum_range_succ]

/-- Actual restriction branching for Specht characters, used for
LaTeX `lem:KP-correspondence` and `eq:KP-translation`. -/
theorem youngSpechtCharacter_branching (μ : YoungDiagram) (a : YoungBoxes μ)
    (g : youngLetterStabilizer μ a) :
    (youngSpechtRepresentation μ).character g.val =
      ∑ b : YoungCorner μ,
        (youngSpechtRepresentation (removePartitionBox μ b)).character
          (youngCornerRemovalHom μ a b g) := by
  rw [← youngSpechtRowCharacter_height μ a g,
    youngSpechtRowCharacter_partial_sum μ a g (μ.colLen 0) le_rfl,
    youngCornerCharacterAtRow_sum]
  rfl

end
end ModifiedCartan


