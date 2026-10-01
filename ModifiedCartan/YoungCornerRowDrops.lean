import ModifiedCartan.PartitionCorners

open scoped Classical

namespace ModifiedCartan
noncomputable section

theorem youngCorner_row_lt_height (μ : YoungDiagram) (b : YoungCorner μ) :
    b.val.val.1 < μ.colLen 0 :=
  (YoungDiagram.mem_iff_lt_colLen.mp b.val.property).trans_le
    (μ.colLen_anti 0 b.val.val.2 (Nat.zero_le _))

theorem youngCorner_row_drop (μ : YoungDiagram) (b : YoungCorner μ) :
    μ.rowLen (b.val.val.1 + 1) < μ.rowLen b.val.val.1 := by
  have hn : (b.val.val.1 + 1, b.val.val.2) ∉ μ := by
    rw [YoungDiagram.mem_iff_lt_colLen, youngCorner_colLen]
    exact (lt_irrefl _)
  rw [YoungDiagram.mem_iff_lt_rowLen] at hn
  rw [youngCorner_rowLen]
  omega

/-- A strict drop between consecutive row lengths determines its unique removable corner. -/
def youngCornerOfRowDrop (μ : YoungDiagram) (r : ℕ) (h : μ.rowLen (r + 1) < μ.rowLen r) :
    YoungCorner μ :=
  ⟨⟨(r, μ.rowLen r - 1), YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)⟩, by
    intro c hc hrc
    change (r, μ.rowLen r - 1) ≤ c at hrc
    change c = (r, μ.rowLen r - 1)
    have hcmem : c.2 < μ.rowLen c.1 := YoungDiagram.mem_iff_lt_rowLen.mp hc
    have hrow : c.1 = r := by
      by_contra hn
      have hrl : r + 1 ≤ c.1 := by have := hrc.1; omega
      have hanti := μ.rowLen_anti (r + 1) c.1 hrl
      have := hrc.2
      omega
    apply Prod.ext hrow
    rw [hrow] at hcmem
    have := hrc.2
    omega⟩

@[simp] theorem youngCornerOfRowDrop_row (μ : YoungDiagram) (r : ℕ)
    (h : μ.rowLen (r + 1) < μ.rowLen r) : (youngCornerOfRowDrop μ r h).val.val.1 = r := rfl

end
end ModifiedCartan


