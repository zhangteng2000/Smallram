import ModifiedCartan.CornerDimensionSum

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

/-- All corner lower bounds are equalities, because the actual increments
and the corner dimensions have the same finite sum. -/
theorem youngSpechtRowIncrement_eq_cornerDimension (μ : YoungDiagram) (a : YoungBoxes μ)
    (r : ℕ) (hr : r < μ.colLen 0) :
    youngSpechtRowIncrement μ a r = youngCornerDimensionAtRow μ r := by
  have hpos : 0 < partitionSize μ := Finset.card_pos.mpr ⟨a.val, a.property⟩
  have hs : (∑ i ∈ Finset.range (μ.colLen 0), youngCornerDimensionAtRow μ i) =
      ∑ i ∈ Finset.range (μ.colLen 0), youngSpechtRowIncrement μ a i := by
    rw [youngCornerDimensionAtRow_sum, ← finrank_specht_remove_recurrence μ hpos,
      youngSpechtRowIncrement_sum]
  have he := (Finset.sum_eq_sum_iff_of_le
    (fun i (_ : i ∈ Finset.range (μ.colLen 0)) =>
      youngCornerDimensionAtRow_le_increment μ a i)).mp hs
  exact (he r (Finset.mem_range.mpr hr)).symm

theorem youngSpechtRowIncrement_zero_of_no_corner (μ : YoungDiagram) (a : YoungBoxes μ)
    (r : ℕ) (hr : r < μ.colLen 0) (h : ¬ ∃ b : YoungCorner μ, b.val.val.1 = r) :
    youngSpechtRowIncrement μ a r = 0 := by
  rw [youngSpechtRowIncrement_eq_cornerDimension μ a r hr,
    youngCornerDimensionAtRow_zero_of_no_corner μ r h]

/-- The actual image of the corner deletion map on its Specht row cutoff is
exactly the smaller Specht representation. -/
theorem youngDeletionImage_eq_specht (μ : YoungDiagram) (b : YoungCorner μ) :
    youngDeletionImageSubrepresentation μ b (b.val.val.1 + 1) =
      youngSpechtSubrepresentation (removePartitionBox μ b) := by
  apply Subrepresentation.toSubmodule_injective
  symm
  apply Submodule.eq_of_le_of_finrank_eq (youngSpecht_le_deletionImage μ b)
  rw [youngDeletionImage_finrank_eq_increment,
    youngSpechtRowIncrement_eq_cornerDimension μ b.val b.val.val.1 (youngCornerRowIndex μ b).isLt,
    youngCornerDimensionAtRow_corner]

end
end ModifiedCartan


