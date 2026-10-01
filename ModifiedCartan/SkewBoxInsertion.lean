import ModifiedCartan.SkewTableaux

open scoped BigOperators Classical

namespace ModifiedCartan

noncomputable section

theorem skewCells_addPartitionBox {ν μ : YoungDiagram} {r : ℕ}
    (h : AddablePartitionRow μ r) :
    ν.cells \ (addPartitionBox μ r h).cells =
      (ν.cells \ μ.cells).erase (r, μ.rowLen r) := by
  ext c
  simp only [Finset.mem_sdiff, Finset.mem_erase, addPartitionBox, Finset.mem_insert]
  tauto

theorem addedBox_mem_skew {ν μ : YoungDiagram} {r : ℕ}
    (hc : (r, μ.rowLen r) ∈ ν) : (r, μ.rowLen r) ∈ ν.cells \ μ.cells := by
  apply Finset.mem_sdiff.mpr
  refine ⟨hc, ?_⟩
  rw [YoungDiagram.mem_cells, YoungDiagram.mem_iff_lt_rowLen]
  exact lt_irrefl _

theorem skewCells_card_addPartitionBox {ν μ : YoungDiagram} {r : ℕ}
    (h : AddablePartitionRow μ r) (hc : (r, μ.rowLen r) ∈ ν) :
    (ν.cells \ μ.cells).card = (ν.cells \ (addPartitionBox μ r h).cells).card + 1 := by
  rw [skewCells_addPartitionBox, Finset.card_erase_of_mem (addedBox_mem_skew hc)]
  have hp : 0 < (ν.cells \ μ.cells).card :=
    Finset.card_pos.mpr ⟨_, addedBox_mem_skew hc⟩
  omega

/-- The tail skew diagram is included in the original one. -/
def skewBoxBefore {ν μ : YoungDiagram} {r : ℕ} (h : AddablePartitionRow μ r)
    (c : SkewPartitionBoxes ν (addPartitionBox μ r h)) : SkewPartitionBoxes ν μ :=
  ⟨c.val, Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp c.property).1, by
    intro hc
    exact (Finset.mem_sdiff.mp c.property).2 ((le_addPartitionBox _ _ _) hc)⟩⟩

@[simp] theorem skewBoxBefore_val {ν μ : YoungDiagram} {r : ℕ}
    (h : AddablePartitionRow μ r) (c : SkewPartitionBoxes ν (addPartitionBox μ r h)) :
    (skewBoxBefore h c).val = c.val := rfl

theorem skewBoxBefore_injective {ν μ : YoungDiagram} {r : ℕ}
    (h : AddablePartitionRow μ r) : Function.Injective (@skewBoxBefore ν μ r h) := by
  intro a b hab
  apply Subtype.ext
  exact congrArg (fun c : SkewPartitionBoxes ν μ => c.val) hab

theorem skewBoxBefore_ne_added {ν μ : YoungDiagram} {r : ℕ}
    (h : AddablePartitionRow μ r) (c : SkewPartitionBoxes ν (addPartitionBox μ r h)) :
    c.val ≠ (r, μ.rowLen r) := by
  intro heq
  exact (Finset.mem_sdiff.mp c.property).2
    ((mem_addPartitionBox _ _ _ c.val).mpr (Or.inl heq))

def skewBoxAfter {ν μ : YoungDiagram} {r : ℕ} (h : AddablePartitionRow μ r)
    (c : SkewPartitionBoxes ν μ) (hne : c.val ≠ (r, μ.rowLen r)) :
    SkewPartitionBoxes ν (addPartitionBox μ r h) :=
  ⟨c.val, by rw [skewCells_addPartitionBox]; exact Finset.mem_erase.mpr ⟨hne, c.property⟩⟩

@[simp] theorem skewBoxAfter_val {ν μ : YoungDiagram} {r : ℕ}
    (h : AddablePartitionRow μ r) (c : SkewPartitionBoxes ν μ)
    (hne : c.val ≠ (r, μ.rowLen r)) : (skewBoxAfter h c hne).val = c.val := rfl

@[simp] theorem skewBoxBefore_after {ν μ : YoungDiagram} {r : ℕ}
    (h : AddablePartitionRow μ r) (c : SkewPartitionBoxes ν μ)
    (hne : c.val ≠ (r, μ.rowLen r)) : skewBoxBefore h (skewBoxAfter h c hne) = c := rfl

@[simp] theorem skewBoxAfter_before {ν μ : YoungDiagram} {r : ℕ}
    (h : AddablePartitionRow μ r) (c : SkewPartitionBoxes ν (addPartitionBox μ r h)) :
    skewBoxAfter h (skewBoxBefore h c) (skewBoxBefore_ne_added h c) = c := rfl

end
end ModifiedCartan


