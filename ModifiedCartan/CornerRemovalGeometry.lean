import ModifiedCartan.CornerPredecessors

open scoped Classical

namespace ModifiedCartan
noncomputable section

theorem partition_eq_of_same_corner_removal (μ ν : YoungDiagram)
    (b : YoungCorner μ) (c : YoungCorner ν)
    (hc : b.val.val = c.val.val) (he : removePartitionBox μ b = removePartitionBox ν c) : μ = ν := by
  apply YoungDiagram.ext
  ext a
  by_cases ha : a = b.val.val
  · subst a
    exact ⟨fun _ => hc ▸ c.val.property, fun _ => b.val.property⟩
  · have hca : a ≠ c.val.val := by rwa [← hc]
    constructor
    · intro hm
      have hh : a ∈ removePartitionBox μ b := (mem_removePartitionBox μ b a).mpr ⟨ha, hm⟩
      rw [he] at hh
      exact ((mem_removePartitionBox ν c a).mp hh).2
    · intro hm
      have hh : a ∈ removePartitionBox ν c := (mem_removePartitionBox ν c a).mpr ⟨hca, hm⟩
      rw [← he] at hh
      exact ((mem_removePartitionBox μ b a).mp hh).2

theorem corner_not_mem_of_same_removal (μ ν : YoungDiagram)
    (b : YoungCorner μ) (c : YoungCorner ν)
    (hbc : b.val.val ≠ c.val.val) (he : removePartitionBox μ b = removePartitionBox ν c) :
    b.val.val ∉ ν := by
  intro hb
  have hm : b.val.val ∈ removePartitionBox ν c :=
    (mem_removePartitionBox ν c b.val.val).mpr ⟨hbc, hb⟩
  rw [← he, mem_removePartitionBox] at hm
  exact hm.1 rfl

theorem corner_not_le_of_same_removal (μ ν : YoungDiagram)
    (b : YoungCorner μ) (c : YoungCorner ν)
    (hbc : b.val.val ≠ c.val.val) (he : removePartitionBox μ b = removePartitionBox ν c) :
    ¬ b.val.val ≤ c.val.val := by
  intro hle
  exact corner_not_mem_of_same_removal μ ν b c hbc he (ν.isLowerSet hle c.val.property)

/-- Two rectangles with the same deleted-corner diagram can differ only in the two-box case. -/
theorem unique_corners_ordered_coordinates (μ ν : YoungDiagram)
    (b : YoungCorner μ) (c : YoungCorner ν)
    (hb : ∀ d : YoungCorner μ, d = b) (hc : ∀ d : YoungCorner ν, d = c)
    (he : removePartitionBox μ b = removePartitionBox ν c)
    (hr : b.val.val.1 < c.val.val.1) :
    b.val.val = (0, 1) ∧ c.val.val = (1, 0) := by
  have hneq : b.val.val ≠ c.val.val := by intro h; have := congrArg Prod.fst h; omega
  have hnot := corner_not_le_of_same_removal μ ν b c hneq he
  have hcol : c.val.val.2 < b.val.val.2 := by
    by_contra h
    exact hnot ⟨hr.le, by omega⟩
  have htransfer (x : ℕ × ℕ) (hx : x ≤ b.val.val) (hne : x ≠ b.val.val) : x ≤ c.val.val := by
    have hm : x ∈ removePartitionBox μ b :=
      (mem_removePartitionBox μ b x).mpr ⟨hne, μ.isLowerSet hx b.val.property⟩
    rw [he] at hm
    exact (mem_iff_le_unique_corner ν c hc x).mp ((mem_removePartitionBox ν c x).mp hm).2
  have htransfer' (x : ℕ × ℕ) (hx : x ≤ c.val.val) (hne : x ≠ c.val.val) : x ≤ b.val.val := by
    have hm : x ∈ removePartitionBox ν c :=
      (mem_removePartitionBox ν c x).mpr ⟨hne, ν.isLowerSet hx c.val.property⟩
    rw [← he] at hm
    exact (mem_iff_le_unique_corner μ b hb x).mp ((mem_removePartitionBox μ b x).mp hm).2
  have hbrow : b.val.val.1 = 0 := by
    by_contra hn
    have hh := htransfer (b.val.val.1 - 1, b.val.val.2)
      ⟨Nat.sub_le _ _, le_rfl⟩ (by intro hh; have := congrArg Prod.fst hh; dsimp at this; omega)
    have hh' : b.val.val.2 ≤ c.val.val.2 := hh.2
    omega
  have hccol : c.val.val.2 = 0 := by
    by_contra hn
    have hh := htransfer' (c.val.val.1, c.val.val.2 - 1)
      ⟨le_rfl, Nat.sub_le _ _⟩ (by intro hh; have := congrArg Prod.snd hh; dsimp at this; omega)
    have hh' : c.val.val.1 ≤ b.val.val.1 := hh.1
    omega
  have hbcol : b.val.val.2 = 1 := by
    have hh := htransfer (b.val.val.1, b.val.val.2 - 1)
      ⟨le_rfl, Nat.sub_le _ _⟩ (by intro hh; have := congrArg Prod.snd hh; dsimp at this; omega)
    have hh' : b.val.val.2 - 1 ≤ c.val.val.2 := hh.2
    omega
  have hcrow : c.val.val.1 = 1 := by
    have hh := htransfer' (c.val.val.1 - 1, c.val.val.2)
      ⟨Nat.sub_le _ _, le_rfl⟩ (by intro hh; have := congrArg Prod.fst hh; dsimp at this; omega)
    have hh' : c.val.val.1 - 1 ≤ b.val.val.1 := hh.1
    omega
  exact ⟨Prod.ext hbrow hbcol, Prod.ext hcrow hccol⟩

end
end ModifiedCartan


