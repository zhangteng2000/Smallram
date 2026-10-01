import ModifiedCartan.PartitionCorners
import ModifiedCartan.YoungFillings

open scoped Classical

namespace ModifiedCartan
noncomputable section

def youngMaxLabel (μ : YoungDiagram) (hpos : 0 < partitionSize μ) : Fin (partitionSize μ) :=
  ⟨partitionSize μ - 1, by omega⟩

/-- In an actual standard tableau, the box with maximal label is an outer corner. -/
def youngTableauLastBox (μ : YoungDiagram) (hpos : 0 < partitionSize μ)
    (T : StandardYoungTableau μ) : YoungCorner μ :=
  ⟨T.val.symm (youngMaxLabel μ hpos), by
    intro c hc hbc
    by_contra hne
    have hne' : T.val.symm (youngMaxLabel μ hpos) ≠ (⟨c, hc⟩ : YoungBoxes μ) := by
      intro he
      exact hne (congrArg Subtype.val he).symm
    have hh := T.property (lt_of_le_of_ne hbc hne')
    rw [T.val.apply_symm_apply] at hh
    have hbound := (T.val ⟨c, hc⟩).isLt
    change partitionSize μ - 1 < (T.val ⟨c, hc⟩).val at hh
    omega⟩

theorem youngTableauLastBox_label (μ : YoungDiagram) (hpos : 0 < partitionSize μ)
    (T : StandardYoungTableau μ) :
    T.val (youngTableauLastBox μ hpos T).val = youngMaxLabel μ hpos :=
  T.val.apply_symm_apply _

theorem youngTableauLastBox_label_val (μ : YoungDiagram) (hpos : 0 < partitionSize μ)
    (T : StandardYoungTableau μ) :
    (T.val (youngTableauLastBox μ hpos T).val).val =
      partitionSize (removePartitionBox μ (youngTableauLastBox μ hpos T)) := by
  rw [youngTableauLastBox_label, partitionSize_removePartitionBox]
  rfl

/-- A column permutation can only move a corner's letter to a row above it. -/
theorem youngCorner_column_row_le (μ : YoungDiagram) (b : YoungCorner μ)
    (c : youngColumnSubgroup μ) : (c.val b.val).val.1 ≤ b.val.val.1 := by
  have hc : (c.val b.val).val.2 = b.val.val.2 := c.property b.val
  have hb : (c.val b.val).val.1 < μ.colLen (c.val b.val).val.2 :=
    YoungDiagram.mem_iff_lt_colLen.mp (c.val b.val).property
  rw [hc, youngCorner_colLen] at hb
  omega

end
end ModifiedCartan


