import ModifiedCartan.YoungPermutationSubgroups

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

/-- A box's column index lies below the length of the top row. -/
def youngColumnIndex (μ : YoungDiagram) (b : YoungBoxes μ) : Fin (μ.rowLen 0) :=
  ⟨b.val.2, (YoungDiagram.mem_iff_lt_rowLen.mp b.property).trans_le
    (μ.rowLen_anti 0 b.val.1 (Nat.zero_le _))⟩

abbrev YoungColumnBoxes (μ : YoungDiagram) (j : Fin (μ.rowLen 0)) :=
  {b : YoungBoxes μ // youngColumnIndex μ b = j}

/-- The rows in a Young column are exactly its initial consecutive row indices. -/
def youngColumnEquiv (μ : YoungDiagram) (j : Fin (μ.rowLen 0)) :
    Fin (μ.colLen j.val) ≃ YoungColumnBoxes μ j where
  toFun r := ⟨⟨(r.val, j.val), YoungDiagram.mem_iff_lt_colLen.mpr r.isLt⟩, by
    apply Fin.ext
    rfl⟩
  invFun b := ⟨b.val.val.1, by
    have hc : b.val.val.2 = j.val := congrArg Fin.val b.property
    rw [← hc]
    exact YoungDiagram.mem_iff_lt_colLen.mp b.val.property⟩
  left_inv r := rfl
  right_inv b := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact (congrArg Fin.val b.property).symm

theorem youngColumnBoxes_card (μ : YoungDiagram) (j : Fin (μ.rowLen 0)) :
    Fintype.card (YoungColumnBoxes μ j) = μ.colLen j.val := by
  rw [← Fintype.card_congr (youngColumnEquiv μ j), Fintype.card_fin]

theorem youngColumnBoxes_row_sum (μ : YoungDiagram) (j : Fin (μ.rowLen 0)) :
    (∑ b : YoungColumnBoxes μ j, b.val.val.1) = ∑ r : Fin (μ.colLen j.val), r.val := by
  exact ((youngColumnEquiv μ j).sum_comp (fun b => b.val.val.1)).symm

theorem young_sum_columns (μ : YoungDiagram) (f : YoungBoxes μ → ℕ) :
    (∑ j : Fin (μ.rowLen 0), ∑ b : YoungColumnBoxes μ j, f b.val) =
      ∑ b : YoungBoxes μ, f b :=
  Fintype.sum_fiberwise (youngColumnIndex μ) f

end
end ModifiedCartan


