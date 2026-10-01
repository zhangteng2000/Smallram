import ModifiedCartan.YoungBoxFiberCounts
import ModifiedCartan.SymmetricPairDeletion
import ModifiedCartan.RemovedBoxes

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

theorem youngPairContent_removed_sum (μ : YoungDiagram) (b : YoungCorner μ) :
    (∑ x : {a : YoungBoxes μ // a ≠ b.val},
      ∑ y : {a : YoungBoxes μ // a ≠ b.val}, youngPairContent x.val y.val) =
      ∑ x : YoungBoxes (removePartitionBox μ b),
        ∑ y : YoungBoxes (removePartitionBox μ b), youngPairContent x y := by
  calc
    _ = ∑ x : YoungBoxes (removePartitionBox μ b),
        ∑ y : {a : YoungBoxes μ // a ≠ b.val},
          youngPairContent (youngRemovedBoxesEquiv μ b x).val y.val :=
      ((youngRemovedBoxesEquiv μ b).sum_comp (fun x =>
        ∑ y : {a : YoungBoxes μ // a ≠ b.val}, youngPairContent x.val y.val)).symm
    _ = ∑ x : YoungBoxes (removePartitionBox μ b),
        ∑ y : YoungBoxes (removePartitionBox μ b),
          youngPairContent (youngRemovedBoxesEquiv μ b x).val (youngRemovedBoxesEquiv μ b y).val := by
      apply Finset.sum_congr rfl
      intro x _
      exact ((youngRemovedBoxesEquiv μ b).sum_comp (fun y =>
        youngPairContent (youngRemovedBoxesEquiv μ b x).val y.val)).symm
    _ = _ := rfl

theorem youngTranspositionScalar_corner (μ : YoungDiagram) (b : YoungCorner μ) :
    youngTranspositionScalar μ = youngTranspositionScalar (removePartitionBox μ b) +
      ((b.val.val.2 : ℂ) - (b.val.val.1 : ℂ)) := by
  have he := half_sum_symmetric_delete (@youngPairContent μ)
    youngPairContent_symm b.val (youngPairContent_self b.val)
  rw [youngPairContent_removed_sum μ b, sum_youngPairContent,
    youngCorner_rowLen, youngCorner_colLen] at he
  change youngTranspositionScalar μ = youngTranspositionScalar (removePartitionBox μ b) +
    ((↑(b.val.val.2 + 1) : ℂ) - (↑(b.val.val.1 + 1) : ℂ)) at he
  simpa only [Nat.cast_add, Nat.cast_one, add_sub_add_right_eq_sub] using he

theorem youngCorner_content_injective (μ : YoungDiagram) :
    Function.Injective (fun b : YoungCorner μ => (b.val.val.2 : ℂ) - (b.val.val.1 : ℂ)) := by
  intro b c he
  have hh : (b.val.val.2 : ℂ) + (c.val.val.1 : ℂ) =
      (c.val.val.2 : ℂ) + (b.val.val.1 : ℂ) := by linear_combination he
  have hn : b.val.val.2 + c.val.val.1 = c.val.val.2 + b.val.val.1 := by exact_mod_cast hh
  rcases le_total b.val.val.1 c.val.val.1 with hr | hr
  · have hc : b.val.val.2 ≤ c.val.val.2 := by omega
    have hv := b.property c.val.val c.val.property ⟨hr, hc⟩
    exact Subtype.ext (Subtype.ext hv.symm)
  · have hc : c.val.val.2 ≤ b.val.val.2 := by omega
    have hv := c.property b.val.val b.val.property ⟨hr, hc⟩
    exact Subtype.ext (Subtype.ext hv)

end
end ModifiedCartan


