import ModifiedCartan.PartitionBoxes

open scoped BigOperators Classical

namespace ModifiedCartan

noncomputable section

abbrev Subpartition (ω : YoungDiagram) := {μ : YoungDiagram // μ ≤ ω}

def subpartitionCells {ω : YoungDiagram} (μ : Subpartition ω) :
    Finset {c : ℕ × ℕ // c ∈ ω.cells} :=
  Finset.univ.filter fun c => c.val ∈ μ.val

theorem subpartitionCells_injective (ω : YoungDiagram) :
    Function.Injective (@subpartitionCells ω) := by
  intro μ ν h
  apply Subtype.ext
  apply YoungDiagram.ext
  ext c
  constructor
  · intro hc
    have hω : c ∈ ω.cells := μ.property hc
    have hm : (⟨c, hω⟩ : {c // c ∈ ω.cells}) ∈ subpartitionCells μ := by
      simpa [subpartitionCells] using hc
    rw [h] at hm
    simpa [subpartitionCells] using hm
  · intro hc
    have hω : c ∈ ω.cells := ν.property hc
    have hm : (⟨c, hω⟩ : {c // c ∈ ω.cells}) ∈ subpartitionCells ν := by
      simpa [subpartitionCells] using hc
    rw [← h] at hm
    simpa [subpartitionCells] using hm

instance (ω : YoungDiagram) : Fintype (Subpartition ω) :=
  Fintype.ofInjective _ (subpartitionCells_injective ω)

theorem partitionSize_mono {μ ν : YoungDiagram} (h : μ ≤ ν) :
    partitionSize μ ≤ partitionSize ν := Finset.card_le_card h

theorem partition_eq_of_le_of_size_le {μ ν : YoungDiagram} (h : μ ≤ ν)
    (hs : partitionSize ν ≤ partitionSize μ) : μ = ν := by
  exact YoungDiagram.ext (Finset.eq_of_subset_of_card_le h hs)

theorem partition_rowLen_mono {μ ν : YoungDiagram} (h : μ ≤ ν) (r : ℕ) :
    μ.rowLen r ≤ ν.rowLen r := by
  by_contra! hlt
  have hm : (r, ν.rowLen r) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr hlt
  have hn := h hm
  rw [YoungDiagram.mem_iff_lt_rowLen] at hn
  exact lt_irrefl _ hn

theorem partition_le_iff_rowLen_le {μ ν : YoungDiagram} :
    μ ≤ ν ↔ ∀ r, μ.rowLen r ≤ ν.rowLen r := by
  refine ⟨fun h r => partition_rowLen_mono h r, ?_⟩
  intro h c hc
  rw [YoungDiagram.mem_iff_lt_rowLen] at hc ⊢
  exact hc.trans_le (h c.1)

theorem partitionSize_eq_sum_rowLen {n : ℕ} {μ : YoungDiagram}
    (h : PartitionFits n μ) : partitionSize μ = ∑ i : Fin (n + 1), μ.rowLen i := by
  let e : {c : ℕ × ℕ // c ∈ μ.cells} ≃
      Σ i : Fin (n + 1), Fin (μ.rowLen i) :=
    { toFun := fun c =>
        ⟨⟨c.val.1, h.row_lt_of_mem c.property⟩,
          ⟨c.val.2, YoungDiagram.mem_iff_lt_rowLen.mp c.property⟩⟩
      invFun := fun c => ⟨(c.1.val, c.2.val),
        YoungDiagram.mem_iff_lt_rowLen.mpr c.2.isLt⟩
      left_inv := fun c => by cases c; rfl
      right_inv := fun c => by cases c; rfl }
  have he := Fintype.card_congr e
  simpa [partitionSize] using he

theorem partitionMinorOrders_injective_on_fits {n : ℕ} {μ ν : YoungDiagram}
    (hμ : PartitionFits n μ) (hν : PartitionFits n ν)
    (h : partitionMinorOrders n μ = partitionMinorOrders n ν) : μ = ν := by
  apply le_antisymm <;> rw [partition_le_iff_rowLen_le]
  · intro r
    by_cases hr : r < n + 1
    · let i : Fin (n + 1) := ⟨n - r, by omega⟩
      have he := congrFun h i
      have hi : n - (n - r) = r := by omega
      dsimp [partitionMinorOrders, i] at he
      rw [hi] at he
      omega
    · rw [hμ.rowLen_eq_zero (by omega)]
      exact Nat.zero_le _
  · intro r
    by_cases hr : r < n + 1
    · let i : Fin (n + 1) := ⟨n - r, by omega⟩
      have he := congrFun h i
      have hi : n - (n - r) = r := by omega
      dsimp [partitionMinorOrders, i] at he
      rw [hi] at he
      omega
    · rw [hν.rowLen_eq_zero (by omega)]
      exact Nat.zero_le _

end
end ModifiedCartan


