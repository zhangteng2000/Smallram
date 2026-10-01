import ModifiedCartan.SkewBoxInsertion

open scoped BigOperators Classical

namespace ModifiedCartan

noncomputable section

namespace StandardSkewTableau

theorem label_pos_after_first {ν μ : YoungDiagram} (T : StandardSkewTableau ν μ)
    {r : ℕ} (h : AddablePartitionRow μ r) (hc : (r, μ.rowLen r) ∈ ν)
    (hzero : (T.val ⟨(r, μ.rowLen r), addedBox_mem_skew hc⟩ : ℕ) = 0)
    (c : SkewPartitionBoxes ν (addPartitionBox μ r h)) :
    0 < (T.val (skewBoxBefore h c) : ℕ) := by
  by_contra! hnot
  have heq : T.val (skewBoxBefore h c) =
      T.val ⟨(r, μ.rowLen r), addedBox_mem_skew hc⟩ := by
    apply Fin.ext
    omega
  exact skewBoxBefore_ne_added h c (congrArg Subtype.val (T.val.injective heq))

/-- Labels of the tableau after its first box is removed. -/
def tailLabel {ν μ : YoungDiagram} (T : StandardSkewTableau ν μ)
    {r : ℕ} (h : AddablePartitionRow μ r) (hc : (r, μ.rowLen r) ∈ ν)
    (hzero : (T.val ⟨(r, μ.rowLen r), addedBox_mem_skew hc⟩ : ℕ) = 0)
    (c : SkewPartitionBoxes ν (addPartitionBox μ r h)) :
    Fin (ν.cells \ (addPartitionBox μ r h).cells).card :=
  ⟨(T.val (skewBoxBefore h c) : ℕ) - 1, by
    have hp := T.label_pos_after_first h hc hzero c
    have ht := (T.val (skewBoxBefore h c)).isLt
    have hh := skewCells_card_addPartitionBox h hc
    omega⟩

@[simp] theorem tailLabel_val {ν μ : YoungDiagram} (T : StandardSkewTableau ν μ)
    {r : ℕ} (h : AddablePartitionRow μ r) (hc : (r, μ.rowLen r) ∈ ν)
    (hzero : (T.val ⟨(r, μ.rowLen r), addedBox_mem_skew hc⟩ : ℕ) = 0)
    (c : SkewPartitionBoxes ν (addPartitionBox μ r h)) :
    (T.tailLabel h hc hzero c : ℕ) = (T.val (skewBoxBefore h c) : ℕ) - 1 := rfl

theorem tailLabel_injective {ν μ : YoungDiagram} (T : StandardSkewTableau ν μ)
    {r : ℕ} (h : AddablePartitionRow μ r) (hc : (r, μ.rowLen r) ∈ ν)
    (hzero : (T.val ⟨(r, μ.rowLen r), addedBox_mem_skew hc⟩ : ℕ) = 0) :
    Function.Injective (T.tailLabel h hc hzero) := by
  intro a b hab
  apply skewBoxBefore_injective h
  apply T.val.injective
  apply Fin.ext
  have he := congrArg Fin.val hab
  simp only [tailLabel_val] at he
  have ha := T.label_pos_after_first h hc hzero a
  have hb := T.label_pos_after_first h hc hzero b
  omega

theorem tailLabel_strictMono {ν μ : YoungDiagram} (T : StandardSkewTableau ν μ)
    {r : ℕ} (h : AddablePartitionRow μ r) (hc : (r, μ.rowLen r) ∈ ν)
    (hzero : (T.val ⟨(r, μ.rowLen r), addedBox_mem_skew hc⟩ : ℕ) = 0) :
    StrictMono (T.tailLabel h hc hzero) := by
  intro a b hab
  have ht : (T.val (skewBoxBefore h a) : ℕ) <
      (T.val (skewBoxBefore h b) : ℕ) := T.property hab
  have ha := T.label_pos_after_first h hc hzero a
  change (T.val (skewBoxBefore h a) : ℕ) - 1 < (T.val (skewBoxBefore h b) : ℕ) - 1
  omega

/-- Remove the first box and shift all remaining labels down by one. -/
def tailTableau {ν μ : YoungDiagram} (T : StandardSkewTableau ν μ)
    {r : ℕ} (h : AddablePartitionRow μ r) (hc : (r, μ.rowLen r) ∈ ν)
    (hzero : (T.val ⟨(r, μ.rowLen r), addedBox_mem_skew hc⟩ : ℕ) = 0) :
    StandardSkewTableau ν (addPartitionBox μ r h) :=
  ⟨Equiv.ofBijective (T.tailLabel h hc hzero)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨T.tailLabel_injective h hc hzero, by simp⟩),
    T.tailLabel_strictMono h hc hzero⟩

@[simp] theorem tailTableau_label {ν μ : YoungDiagram} (T : StandardSkewTableau ν μ)
    {r : ℕ} (h : AddablePartitionRow μ r) (hc : (r, μ.rowLen r) ∈ ν)
    (hzero : (T.val ⟨(r, μ.rowLen r), addedBox_mem_skew hc⟩ : ℕ) = 0)
    (c : SkewPartitionBoxes ν (addPartitionBox μ r h)) :
    ((T.tailTableau h hc hzero).val c : ℕ) = (T.val (skewBoxBefore h c) : ℕ) - 1 := rfl

end StandardSkewTableau
end
end ModifiedCartan


