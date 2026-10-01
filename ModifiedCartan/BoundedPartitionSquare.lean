import ModifiedCartan.SizedYoungDiagrams
import ModifiedCartan.PartitionBoxes

namespace ModifiedCartan

theorem partition_le_square_of_size_le (μ : YoungDiagram) (n : ℕ) (h : partitionSize μ ≤ n) :
    μ ≤ partitionSquare n := by
  intro a ha
  exact Finset.mem_product.mpr
    ⟨Finset.mem_range.mpr ((YoungDiagram.mem_iff_lt_colLen.mp ha).trans_le
      ((partition_colLen_le_size μ a.2).trans h)),
      Finset.mem_range.mpr ((YoungDiagram.mem_iff_lt_rowLen.mp ha).trans_le
        ((partition_rowLen_le_size μ a.1).trans h))⟩

theorem partitionSquare_fits (n : ℕ) : PartitionFits n (partitionSquare n) := by
  unfold PartitionFits
  by_contra hn
  have hm : (n + 1, 0) ∈ partitionSquare n :=
    YoungDiagram.mem_iff_lt_rowLen.mpr (Nat.pos_of_ne_zero hn)
  have hx := Finset.mem_product.mp hm
  have hh := Finset.mem_range.mp hx.1
  omega

end ModifiedCartan


