import ModifiedCartan.BoundedPartitionSquare
import ModifiedCartan.FixedPointPermutationSums

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

def sizedPartitionsInSquareEquiv (n k : ℕ) (hk : k ≤ n) :
    SizedYoungDiagram k ≃ {μ : Subpartition (partitionSquare n) // partitionSize μ.val = k} where
  toFun μ := ⟨⟨μ.val, partition_le_square_of_size_le μ.val n (μ.property.le.trans hk)⟩, μ.property⟩
  invFun μ := ⟨μ.val.val, μ.property⟩
  left_inv μ := rfl
  right_inv μ := rfl

theorem sum_sizedYoungDiagram_in_square {M : Type*} [AddCommMonoid M]
    (n k : ℕ) (hk : k ≤ n) (f : YoungDiagram → M) :
    (∑ μ : SizedYoungDiagram k, f μ.val) =
      ∑ μ : Subpartition (partitionSquare n), if partitionSize μ.val = k then f μ.val else 0 := by
  calc
    _ = ∑ μ : {μ : Subpartition (partitionSquare n) // partitionSize μ.val = k}, f μ.val.val :=
      Equiv.sum_comp (sizedPartitionsInSquareEquiv n k hk) (fun μ => f μ.val.val)
    _ = _ := (sum_dite_eq_sum_subtype
      (fun μ : Subpartition (partitionSquare n) => partitionSize μ.val = k) (fun μ _ => f μ.val)).symm

end
end ModifiedCartan

