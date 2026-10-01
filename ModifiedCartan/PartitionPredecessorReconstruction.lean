import ModifiedCartan.CornerRemovalGeometry

open scoped Classical

namespace ModifiedCartan
noncomputable section

theorem unique_corner_same_removal_shapes (μ ν : YoungDiagram)
    (b : YoungCorner μ) (c : YoungCorner ν)
    (hb : ∀ d : YoungCorner μ, d = b) (hc : ∀ d : YoungCorner ν, d = c)
    (he : removePartitionBox μ b = removePartitionBox ν c) (hne : μ ≠ ν) :
    (b.val.val = (0, 1) ∧ c.val.val = (1, 0)) ∨
      (b.val.val = (1, 0) ∧ c.val.val = (0, 1)) := by
  have hneq : b.val.val ≠ c.val.val := fun h =>
    hne (partition_eq_of_same_corner_removal μ ν b c h he)
  rcases lt_trichotomy b.val.val.1 c.val.val.1 with hr | hr | hr
  · exact Or.inl (unique_corners_ordered_coordinates μ ν b c hb hc he hr)
  · have hn₁ := corner_not_le_of_same_removal μ ν b c hneq he
    have hn₂ := corner_not_le_of_same_removal ν μ c b hneq.symm he.symm
    rcases le_total b.val.val.2 c.val.val.2 with hs | hs
    · exact False.elim (hn₁ ⟨hr.le, hs⟩)
    · exact False.elim (hn₂ ⟨hr.ge, hs⟩)
  · have hh := unique_corners_ordered_coordinates ν μ c b hc hb he.symm hr
    exact Or.inr ⟨hh.2, hh.1⟩

theorem partitionSize_le_two_of_small_unique_corner (μ : YoungDiagram) (b : YoungCorner μ)
    (hb : ∀ d : YoungCorner μ, d = b) (hc : b.val.val = (0, 1) ∨ b.val.val = (1, 0)) :
    partitionSize μ ≤ 2 := by
  have hsub : μ.cells ⊆ {(0, 0), b.val.val} := by
    intro x hx
    have hle := (mem_iff_le_unique_corner μ b hb x).mp hx
    rcases x with ⟨r, s⟩
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases hc with hc | hc
    · rw [hc] at hle ⊢
      have hr : r ≤ 0 := hle.1
      have hs : s ≤ 1 := hle.2
      simp only [Prod.mk.injEq]
      omega
    · rw [hc] at hle ⊢
      have hr : r ≤ 1 := hle.1
      have hs : s ≤ 0 := hle.2
      simp only [Prod.mk.injEq]
      omega
  have hcard := Finset.card_le_card hsub
  rcases hc with hc | hc
  · simpa [partitionSize, hc] using hcard
  · simpa [partitionSize, hc] using hcard

/-- Equal predecessor sets determine a Young diagram with at least three boxes. -/
theorem partition_eq_of_same_predecessors (μ ν : YoungDiagram)
    (hs : partitionSize μ = partitionSize ν) (hsize : 3 ≤ partitionSize μ)
    (hpred : youngPredecessors μ = youngPredecessors ν) : μ = ν := by
  by_contra hne
  obtain ⟨b⟩ := youngCorner_exists_of_pos μ (by omega)
  have hmem : removePartitionBox μ b ∈ youngPredecessors ν := hpred ▸ Set.mem_range_self b
  obtain ⟨c, he⟩ := hmem
  have hb : ∀ d : YoungCorner μ, d = b := by
    intro d
    by_contra hd
    exact hne (partition_eq_of_same_predecessors_two_corners μ ν hs hpred d b hd)
  have hc : ∀ d : YoungCorner ν, d = c := by
    intro d
    by_contra hd
    exact hne (partition_eq_of_same_predecessors_two_corners ν μ hs.symm hpred.symm d c hd).symm
  have hshape := unique_corner_same_removal_shapes μ ν b c hb hc he.symm hne
  have hsmall := partitionSize_le_two_of_small_unique_corner μ b hb
    (hshape.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1))
  omega

end
end ModifiedCartan


