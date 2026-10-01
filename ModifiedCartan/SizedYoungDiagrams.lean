import ModifiedCartan.FinitePartitions

open scoped Classical

namespace ModifiedCartan
noncomputable section

def partitionSquare (n : ℕ) : YoungDiagram where
  cells := Finset.range n ×ˢ Finset.range n
  isLowerSet := by
    intro a b hba ha
    rcases Finset.mem_product.mp ha with ⟨ha₁, ha₂⟩
    exact Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (hba.1.trans_lt (Finset.mem_range.mp ha₁)),
        Finset.mem_range.mpr (hba.2.trans_lt (Finset.mem_range.mp ha₂))⟩

theorem partition_rowLen_le_size (μ : YoungDiagram) (r : ℕ) : μ.rowLen r ≤ partitionSize μ := by
  rw [μ.rowLen_eq_card]
  exact Finset.card_le_card (Finset.filter_subset _ _)

theorem partition_colLen_le_size (μ : YoungDiagram) (c : ℕ) : μ.colLen c ≤ partitionSize μ := by
  rw [μ.colLen_eq_card]
  exact Finset.card_le_card (Finset.filter_subset _ _)

theorem partition_le_square (μ : YoungDiagram) : μ ≤ partitionSquare (partitionSize μ) := by
  intro a ha
  exact Finset.mem_product.mpr
    ⟨Finset.mem_range.mpr ((YoungDiagram.mem_iff_lt_colLen.mp ha).trans_le
      (partition_colLen_le_size μ a.2)),
      Finset.mem_range.mpr ((YoungDiagram.mem_iff_lt_rowLen.mp ha).trans_le
        (partition_rowLen_le_size μ a.1))⟩

/-- The finite set of all actual Young diagrams with a specified number of boxes. -/
abbrev SizedYoungDiagram (n : ℕ) := {μ : YoungDiagram // partitionSize μ = n}

def sizedYoungDiagramSubpartition (n : ℕ) (μ : SizedYoungDiagram n) : Subpartition (partitionSquare n) :=
  ⟨μ.val, by simpa only [μ.property] using partition_le_square μ.val⟩

theorem sizedYoungDiagramSubpartition_injective (n : ℕ) :
    Function.Injective (sizedYoungDiagramSubpartition n) := by
  intro μ ν he
  have hv := congrArg (fun τ : Subpartition (partitionSquare n) => τ.val) he
  exact Subtype.ext hv

instance (n : ℕ) : Fintype (SizedYoungDiagram n) :=
  Fintype.ofInjective (sizedYoungDiagramSubpartition n) (sizedYoungDiagramSubpartition_injective n)

instance : Unique (SizedYoungDiagram 0) where
  default := ⟨⊥, rfl⟩
  uniq μ := Subtype.ext (YoungDiagram.ext (Finset.card_eq_zero.mp μ.property))

end
end ModifiedCartan


