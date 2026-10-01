import ModifiedCartan.RankedYoungCoverEquivs
import ModifiedCartan.FiniteCommonNeighborSums

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

theorem young_lattice_weighted_differential (n : ℕ) (f : YoungDiagram → ℕ) (μ : SizedYoungDiagram n) :
    (∑ ξ : SizedYoungDiagram (n + 1), if PartitionCovers ξ.val μ.val then
      ∑ ν : SizedYoungDiagram n, if PartitionCovers ξ.val ν.val then f ν.val else 0 else 0) =
    f μ.val + ∑ δ : SizedYoungDiagram (n - 1), if PartitionCovers μ.val δ.val then
      ∑ ν : SizedYoungDiagram n, if PartitionCovers ν.val δ.val then f ν.val else 0 else 0 := by
  have hcard (ν : SizedYoungDiagram n) :
      Fintype.card {ξ : SizedYoungDiagram (n + 1) //
        PartitionCovers ξ.val μ.val ∧ PartitionCovers ξ.val ν.val} =
      Fintype.card {δ : SizedYoungDiagram (n - 1) //
        PartitionCovers μ.val δ.val ∧ PartitionCovers ν.val δ.val} + if μ = ν then 1 else 0 := by
    rw [Fintype.card_congr (youngCommonSuccessorSizedEquiv μ.val ν.val n μ.property),
      Fintype.card_congr (youngCommonPredecessorSizedEquiv μ.val ν.val n μ.property)]
    have he : μ.val = ν.val ↔ μ = ν := ⟨Subtype.ext, fun h => congrArg Subtype.val h⟩
    simpa only [he] using young_lattice_differential_card μ.val ν.val
      (μ.property.trans ν.property.symm)
  calc
    _ = ∑ ν : SizedYoungDiagram n,
        Fintype.card {ξ : SizedYoungDiagram (n + 1) //
          PartitionCovers ξ.val μ.val ∧ PartitionCovers ξ.val ν.val} * f ν.val :=
      finite_weighted_common_neighbors
        (fun ν : SizedYoungDiagram n => fun ξ : SizedYoungDiagram (n + 1) =>
          PartitionCovers ξ.val ν.val) (fun ν => f ν.val) μ
    _ = ∑ ν : SizedYoungDiagram n,
        (Fintype.card {δ : SizedYoungDiagram (n - 1) //
          PartitionCovers μ.val δ.val ∧ PartitionCovers ν.val δ.val} + if μ = ν then 1 else 0) * f ν.val := by
      apply Finset.sum_congr rfl
      intro ν _
      rw [hcard ν]
    _ = f μ.val + ∑ ν : SizedYoungDiagram n,
        Fintype.card {δ : SizedYoungDiagram (n - 1) //
          PartitionCovers μ.val δ.val ∧ PartitionCovers ν.val δ.val} * f ν.val := by
      simp only [add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul]
      simp [add_comm]
    _ = _ := congrArg (fun k => f μ.val + k)
      (finite_weighted_common_neighbors
        (fun ν : SizedYoungDiagram n => fun δ : SizedYoungDiagram (n - 1) =>
          PartitionCovers ν.val δ.val) (fun ν => f ν.val) μ).symm

end
end ModifiedCartan


