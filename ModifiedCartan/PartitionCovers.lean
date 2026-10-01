import ModifiedCartan.CornerPredecessors

open scoped Classical

namespace ModifiedCartan
noncomputable section

/-- An actual one-box cover in Young's lattice. -/
def PartitionCovers (ν μ : YoungDiagram) : Prop := μ ≤ ν ∧ partitionSize ν = partitionSize μ + 1

theorem removePartitionBox_covers (μ : YoungDiagram) (b : YoungCorner μ) :
    PartitionCovers μ (removePartitionBox μ b) :=
  ⟨removePartitionBox_le μ b, (partitionSize_removePartitionBox_add_one μ b).symm⟩

theorem addPartitionBox_covers (μ : YoungDiagram) (r : ℕ) (h : AddablePartitionRow μ r) :
    PartitionCovers (addPartitionBox μ r h) μ :=
  ⟨le_addPartitionBox μ r h, partitionSize_addPartitionBox μ r h⟩

theorem PartitionCovers.exists_difference_box {μ ν : YoungDiagram} (h : PartitionCovers ν μ) :
    ∃ a : ℕ × ℕ, ν.cells \ μ.cells = {a} := by
  apply Finset.card_eq_one.mp
  rw [Finset.card_sdiff_of_subset h.1]
  change partitionSize ν - partitionSize μ = 1
  rw [h.2]
  omega

theorem PartitionCovers.exists_corner_removal {μ ν : YoungDiagram} (h : PartitionCovers ν μ) :
    ∃ b : YoungCorner ν, removePartitionBox ν b = μ := by
  obtain ⟨a, ha⟩ := h.exists_difference_box
  have has : a ∈ ν.cells \ μ.cells := by rw [ha]; simp
  have haν : a ∈ ν := (Finset.mem_sdiff.mp has).1
  have haμ : a ∉ μ := (Finset.mem_sdiff.mp has).2
  have hmax : IsPartitionCorner ν ⟨a, haν⟩ := by
    intro c hc hac
    have hcμ : c ∉ μ := fun hh => haμ (μ.isLowerSet hac hh)
    have hc' : c ∈ ν.cells \ μ.cells := Finset.mem_sdiff.mpr ⟨hc, hcμ⟩
    rw [ha] at hc'
    exact Finset.mem_singleton.mp hc'
  let b : YoungCorner ν := ⟨⟨a, haν⟩, hmax⟩
  refine ⟨b, ?_⟩
  apply YoungDiagram.ext
  ext c
  change c ∈ removePartitionBox ν b ↔ c ∈ μ
  rw [mem_removePartitionBox]
  constructor
  · rintro ⟨hne, hc⟩
    by_contra hn
    have hc' : c ∈ ν.cells \ μ.cells := Finset.mem_sdiff.mpr ⟨hc, hn⟩
    rw [ha] at hc'
    exact hne (Finset.mem_singleton.mp hc')
  · intro hc
    refine ⟨?_, h.1 hc⟩
    intro he
    have he' : c = a := he
    exact haμ (he' ▸ hc)

theorem partitionCovers_iff_corner_removal (μ ν : YoungDiagram) :
    PartitionCovers ν μ ↔ ∃ b : YoungCorner ν, removePartitionBox ν b = μ := by
  refine ⟨PartitionCovers.exists_corner_removal, ?_⟩
  rintro ⟨b, rfl⟩
  exact removePartitionBox_covers ν b

end
end ModifiedCartan


