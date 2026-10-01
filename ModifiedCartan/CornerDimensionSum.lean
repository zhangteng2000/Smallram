import ModifiedCartan.DeletionImageDimension
import ModifiedCartan.CornerTableauCount

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

def youngCornerRowIndex (μ : YoungDiagram) (b : YoungCorner μ) : Fin (μ.colLen 0) :=
  ⟨b.val.val.1, (YoungDiagram.mem_iff_lt_colLen.mp b.val.property).trans_le
    (μ.colLen_anti 0 b.val.val.2 (Nat.zero_le _))⟩

def youngCornerDimensionAtRow (μ : YoungDiagram) (r : ℕ) : ℕ :=
  ∑ b : YoungCorner μ, if b.val.val.1 = r then
    Module.finrank ℂ (YoungSpechtModule (removePartitionBox μ b)) else 0

theorem youngCornerDimensionAtRow_corner (μ : YoungDiagram) (b : YoungCorner μ) :
    youngCornerDimensionAtRow μ b.val.val.1 =
      Module.finrank ℂ (YoungSpechtModule (removePartitionBox μ b)) := by
  unfold youngCornerDimensionAtRow
  rw [Finset.sum_eq_single b]
  · simp
  · intro c _ hcb
    have hrow : c.val.val.1 ≠ b.val.val.1 := fun h => hcb (youngCorner_row_injective μ h)
    simp [hrow]
  · simp

theorem youngCornerDimensionAtRow_zero_of_no_corner (μ : YoungDiagram) (r : ℕ)
    (h : ¬ ∃ b : YoungCorner μ, b.val.val.1 = r) : youngCornerDimensionAtRow μ r = 0 := by
  apply Finset.sum_eq_zero
  intro b _
  have hb : b.val.val.1 ≠ r := fun hb => h ⟨b, hb⟩
  simp [hb]

theorem youngCornerDimensionAtRow_le_increment (μ : YoungDiagram) (a : YoungBoxes μ) (r : ℕ) :
    youngCornerDimensionAtRow μ r ≤ youngSpechtRowIncrement μ a r := by
  by_cases h : ∃ b : YoungCorner μ, b.val.val.1 = r
  · obtain ⟨b, rfl⟩ := h
    rw [youngCornerDimensionAtRow_corner]
    exact youngSpechtRowIncrement_corner_lower_bound μ a b
  · rw [youngCornerDimensionAtRow_zero_of_no_corner μ r h]
    exact Nat.zero_le _

theorem youngCornerDimensionAtRow_sum (μ : YoungDiagram) :
    (∑ r ∈ Finset.range (μ.colLen 0), youngCornerDimensionAtRow μ r) =
      ∑ b : YoungCorner μ, Module.finrank ℂ (YoungSpechtModule (removePartitionBox μ b)) := by
  unfold youngCornerDimensionAtRow
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  have hb : b.val.val.1 < μ.colLen 0 := (youngCornerRowIndex μ b).isLt
  simp [hb]

end
end ModifiedCartan


