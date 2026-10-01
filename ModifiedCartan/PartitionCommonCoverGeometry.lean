import ModifiedCartan.PartitionCovers

namespace ModifiedCartan

theorem partitionSize_sup_add_inf (μ ν : YoungDiagram) :
    partitionSize (μ ⊔ ν) + partitionSize (μ ⊓ ν) = partitionSize μ + partitionSize ν :=
  Finset.card_union_add_card_inter μ.cells ν.cells

theorem partitionSize_sup_gt_of_ne (μ ν : YoungDiagram)
    (hs : partitionSize μ = partitionSize ν) (hne : μ ≠ ν) :
    partitionSize μ < partitionSize (μ ⊔ ν) := by
  by_contra hn
  have he : μ = μ ⊔ ν := partition_eq_of_le_of_size_le le_sup_left (by omega)
  have hle : ν ≤ μ := by rw [he]; exact le_sup_right
  exact hne (partition_eq_of_le_of_size_le hle hs.le).symm

theorem partitionSize_inf_lt_of_ne (μ ν : YoungDiagram)
    (hs : partitionSize μ = partitionSize ν) (hne : μ ≠ ν) :
    partitionSize (μ ⊓ ν) < partitionSize μ := by
  have hsup := partitionSize_sup_gt_of_ne μ ν hs hne
  have hadd := partitionSize_sup_add_inf μ ν
  omega

theorem common_upper_eq_sup (μ ν ξ : YoungDiagram)
    (hs : partitionSize μ = partitionSize ν) (hne : μ ≠ ν)
    (hξμ : PartitionCovers ξ μ) (hξν : PartitionCovers ξ ν) : ξ = μ ⊔ ν := by
  symm
  apply partition_eq_of_le_of_size_le (sup_le hξμ.1 hξν.1)
  have hh := partitionSize_sup_gt_of_ne μ ν hs hne
  have hsz := hξμ.2
  omega

theorem common_lower_eq_inf (μ ν δ : YoungDiagram)
    (hs : partitionSize μ = partitionSize ν) (hne : μ ≠ ν)
    (hμδ : PartitionCovers μ δ) (hνδ : PartitionCovers ν δ) : δ = μ ⊓ ν := by
  apply partition_eq_of_le_of_size_le (le_inf hμδ.1 hνδ.1)
  have hh := partitionSize_inf_lt_of_ne μ ν hs hne
  have hsz := hμδ.2
  omega

theorem common_inf_covers_of_upper (μ ν ξ : YoungDiagram)
    (hs : partitionSize μ = partitionSize ν) (hne : μ ≠ ν)
    (hξμ : PartitionCovers ξ μ) (hξν : PartitionCovers ξ ν) :
    PartitionCovers μ (μ ⊓ ν) ∧ PartitionCovers ν (μ ⊓ ν) := by
  have he := common_upper_eq_sup μ ν ξ hs hne hξμ hξν
  have hu := hξμ.2
  rw [he] at hu
  have hadd := partitionSize_sup_add_inf μ ν
  exact ⟨⟨inf_le_left, by omega⟩, ⟨inf_le_right, by omega⟩⟩

theorem common_sup_covers_of_lower (μ ν δ : YoungDiagram)
    (hs : partitionSize μ = partitionSize ν) (hne : μ ≠ ν)
    (hμδ : PartitionCovers μ δ) (hνδ : PartitionCovers ν δ) :
    PartitionCovers (μ ⊔ ν) μ ∧ PartitionCovers (μ ⊔ ν) ν := by
  have he := common_lower_eq_inf μ ν δ hs hne hμδ hνδ
  have hl := hμδ.2
  rw [he] at hl
  have hadd := partitionSize_sup_add_inf μ ν
  exact ⟨⟨le_sup_left, by omega⟩, ⟨le_sup_right, by omega⟩⟩

end ModifiedCartan


