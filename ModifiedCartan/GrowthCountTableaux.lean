import ModifiedCartan.MinorGrowthCount
import ModifiedCartan.SkewGrowthRows
import ModifiedCartan.TableauCountRecurrence
import ModifiedCartan.FinitePartitions

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

theorem minorGrowthCount_succ_skew (n : ℕ) (μ ν : YoungDiagram) (k : ℕ) :
    minorGrowthCount n μ ν (k + 1) =
      ∑ r : SkewAddition n ν μ, minorGrowthCount n r.enlarged ν k := by
  rw [minorGrowthCount_succ]
  have hz : (∑ i : {i : LegalMinorRow n μ // ¬ growMinorPartition i ≤ ν},
      minorGrowthCount n (growMinorPartition i.val) ν k) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    exact minorGrowthCount_eq_zero_of_not_le k i.property
  have hs := Fintype.sum_subtype_add_sum_subtype
    (fun i : LegalMinorRow n μ => growMinorPartition i ≤ ν)
    (fun i => minorGrowthCount n (growMinorPartition i) ν k)
  rw [hz, add_zero] at hs
  rw [← hs]
  have he := (legalMinorRowSkewAdditionEquiv n ν μ).sum_comp
    (fun r => minorGrowthCount n r.enlarged ν k)
  rw [← he]
  apply Finset.sum_congr rfl
  intro i _
  change minorGrowthCount n (growMinorPartition i.val) ν k =
    minorGrowthCount n (addPartitionBox μ (i.val.val.rev : ℕ) _) ν k
  simp only [fin_rev_val_for_minor, growMinorPartition]

/-- Derivative paths have the actual standard skew-tableau multiplicity. -/
theorem minorGrowthCount_eq_standardSkewTableauCount {n : ℕ} {μ ν : YoungDiagram}
    (hμν : μ ≤ ν) (hν : PartitionFits n ν) (k : ℕ)
    (hsize : partitionSize ν = partitionSize μ + k) :
    minorGrowthCount n μ ν k = standardSkewTableauCount ν μ := by
  induction k generalizing μ with
  | zero =>
    have heq : μ = ν := partition_eq_of_le_of_size_le hμν (by omega)
    subst μ
    simp [minorGrowthCount_zero, standardSkewTableauCount_self]
  | succ k ih =>
    have hp : 0 < (ν.cells \ μ.cells).card := by
      rw [skewPartitionBoxes_card hμν]
      omega
    rw [minorGrowthCount_succ_skew, standardSkewTableauCount_rec hμν hν hp]
    apply Finset.sum_congr rfl
    intro r _
    apply ih r.inside
    change partitionSize ν = partitionSize r.enlarged + k
    have hr : partitionSize r.enlarged = partitionSize μ + 1 :=
      partitionSize_addPartitionBox μ r.row r.legal
    omega

end
end ModifiedCartan


