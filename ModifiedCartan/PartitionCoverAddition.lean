import ModifiedCartan.PartitionCovers
import ModifiedCartan.TableauPrefixSteps

open scoped Classical

namespace ModifiedCartan
noncomputable section

theorem minimal_missing_box_row_le_height {μ : YoungDiagram} {a : ℕ × ℕ}
    (hmin : ∀ d, d ≤ a → d ≠ a → d ∈ μ) : a.1 ≤ μ.colLen 0 := by
  by_contra hn
  have hh := hmin (μ.colLen 0, 0) ⟨by omega, Nat.zero_le _⟩ (by
    intro he
    have hfst := congrArg Prod.fst he
    dsimp at hfst
    omega)
  rw [YoungDiagram.mem_iff_lt_colLen] at hh
  exact (lt_irrefl _ hh)

theorem PartitionCovers.exists_row_addition {μ ν : YoungDiagram} (h : PartitionCovers ν μ) :
    ∃ (r : ℕ) (hr : AddablePartitionRow μ r), r ≤ μ.colLen 0 ∧ addPartitionBox μ r hr = ν := by
  obtain ⟨a, ha⟩ := h.exists_difference_box
  have has : a ∈ ν.cells \ μ.cells := by rw [ha]; simp
  have haν : a ∈ ν := (Finset.mem_sdiff.mp has).1
  have haμ : a ∉ μ := (Finset.mem_sdiff.mp has).2
  have hmin : ∀ d, d ≤ a → d ≠ a → d ∈ μ := by
    intro d hda hne
    by_contra hd
    have hm : d ∈ ν.cells \ μ.cells := Finset.mem_sdiff.mpr ⟨ν.isLowerSet hda haν, hd⟩
    rw [ha] at hm
    exact hne (Finset.mem_singleton.mp hm)
  have hrow := rowLen_eq_of_minimal_missing_box haμ hmin
  let hr := addableRow_of_minimal_missing_box haμ hmin
  refine ⟨a.1, hr, minimal_missing_box_row_le_height hmin, ?_⟩
  apply YoungDiagram.ext
  ext d
  change d ∈ addPartitionBox μ a.1 hr ↔ d ∈ ν
  rw [mem_addPartitionBox, ← hrow]
  change (d = a ∨ d ∈ μ) ↔ d ∈ ν
  constructor
  · rintro (rfl | hd)
    · exact haν
    · exact h.1 hd
  · intro hd
    by_cases hm : d ∈ μ
    · exact Or.inr hm
    · have hh : d ∈ ν.cells \ μ.cells := Finset.mem_sdiff.mpr ⟨hd, hm⟩
      rw [ha] at hh
      exact Or.inl (Finset.mem_singleton.mp hh)

theorem addPartitionBox_row_injective (μ : YoungDiagram) (r s : ℕ)
    (hr : AddablePartitionRow μ r) (hs : AddablePartitionRow μ s)
    (he : addPartitionBox μ r hr = addPartitionBox μ s hs) : r = s := by
  have hm : (r, μ.rowLen r) ∈ addPartitionBox μ r hr := by simp
  rw [he, mem_addPartitionBox] at hm
  rcases hm with hm | hm
  · exact congrArg Prod.fst hm
  · rw [YoungDiagram.mem_iff_lt_rowLen] at hm
    exact False.elim (lt_irrefl _ hm)

end
end ModifiedCartan


