import ModifiedCartan.PartitionCorners
import ModifiedCartan.FinitePartitions
import Mathlib.Data.Finset.Max

open scoped Classical

namespace ModifiedCartan
noncomputable section

theorem youngBox_le_corner (μ : YoungDiagram) (a : YoungBoxes μ) :
    ∃ b : YoungCorner μ, a.val ≤ b.val.val := by
  let S := μ.cells.filter (fun c => a.val ≤ c)
  have ha : a.val ∈ S := Finset.mem_filter.mpr ⟨a.property, le_rfl⟩
  obtain ⟨c, hc, hmax⟩ := S.exists_max_image (fun c => c.1 + c.2) ⟨a.val, ha⟩
  have hcμ : c ∈ μ := (Finset.mem_filter.mp hc).1
  have hac : a.val ≤ c := (Finset.mem_filter.mp hc).2
  refine ⟨⟨⟨c, hcμ⟩, ?_⟩, hac⟩
  intro d hd hcd
  change c ≤ d at hcd
  change d = c
  have hdc : d ∈ S := Finset.mem_filter.mpr ⟨hd, hac.trans hcd⟩
  have hsum := hmax d hdc
  exact Prod.ext (by have := hcd.1; have := hcd.2; omega)
    (by have := hcd.1; have := hcd.2; omega)

theorem youngCorner_exists_of_pos (μ : YoungDiagram) (h : 0 < partitionSize μ) :
    Nonempty (YoungCorner μ) := by
  obtain ⟨a, ha⟩ := Finset.card_pos.mp h
  obtain ⟨b, _⟩ := youngBox_le_corner μ ⟨a, ha⟩
  exact ⟨b⟩

theorem mem_iff_le_unique_corner (μ : YoungDiagram) (b : YoungCorner μ)
    (hb : ∀ c : YoungCorner μ, c = b) (a : ℕ × ℕ) : a ∈ μ ↔ a ≤ b.val.val := by
  constructor
  · intro ha
    obtain ⟨c, hc⟩ := youngBox_le_corner μ ⟨a, ha⟩
    rw [hb c] at hc
    exact hc
  · intro ha
    exact μ.isLowerSet ha b.val.property

theorem removePartitionBox_injective (μ : YoungDiagram) :
    Function.Injective (removePartitionBox μ) := by
  intro b c he
  by_contra hbc
  have hval : b.val.val ≠ c.val.val := by
    intro hh
    exact hbc (Subtype.ext (Subtype.ext hh))
  have hb : b.val.val ∈ removePartitionBox μ c :=
    (mem_removePartitionBox μ c b.val.val).mpr ⟨hval, b.val.property⟩
  rw [← he, mem_removePartitionBox] at hb
  exact hb.1 rfl

theorem sup_two_corner_removals (μ : YoungDiagram) (b c : YoungCorner μ) (hbc : b ≠ c) :
    removePartitionBox μ b ⊔ removePartitionBox μ c = μ := by
  apply le_antisymm
  · exact sup_le (removePartitionBox_le μ b) (removePartitionBox_le μ c)
  · intro a ha
    rw [YoungDiagram.mem_sup, mem_removePartitionBox, mem_removePartitionBox]
    by_cases hab : a = b.val.val
    · right
      refine ⟨?_, ha⟩
      intro hac
      exact hbc (Subtype.ext (Subtype.ext (hab.symm.trans hac)))
    · exact Or.inl ⟨hab, ha⟩

def youngPredecessors (μ : YoungDiagram) : Set YoungDiagram := Set.range (removePartitionBox μ)

theorem partition_eq_of_same_predecessors_two_corners (μ ν : YoungDiagram)
    (hs : partitionSize μ = partitionSize ν) (hpred : youngPredecessors μ = youngPredecessors ν)
    (b c : YoungCorner μ) (hbc : b ≠ c) : μ = ν := by
  apply partition_eq_of_le_of_size_le ?_ hs.ge
  rw [← sup_two_corner_removals μ b c hbc]
  apply sup_le
  · have hb : removePartitionBox μ b ∈ youngPredecessors ν := hpred ▸ Set.mem_range_self b
    obtain ⟨d, hd⟩ := hb
    rw [← hd]
    exact removePartitionBox_le ν d
  · have hc : removePartitionBox μ c ∈ youngPredecessors ν := hpred ▸ Set.mem_range_self c
    obtain ⟨d, hd⟩ := hc
    rw [← hd]
    exact removePartitionBox_le ν d

end
end ModifiedCartan


