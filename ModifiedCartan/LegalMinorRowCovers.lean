import ModifiedCartan.MinorGrowthPaths
import ModifiedCartan.PartitionCoverAddition
import ModifiedCartan.SizedYoungDiagrams

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

theorem growMinorPartition_injective (n : ℕ) (μ : YoungDiagram) :
    Function.Injective (growMinorPartition (n := n) (μ := μ)) := by
  intro i j he
  have hr := addPartitionBox_row_injective μ (n - (i.val : ℕ)) (n - (j.val : ℕ))
    i.property j.property he
  apply Subtype.ext
  apply Fin.ext
  have hi := i.val.isLt
  have hj := j.val.isLt
  omega

theorem exists_legalMinorRow_of_cover {n : ℕ} {μ ν : YoungDiagram}
    (hn : μ.colLen 0 ≤ n) (hc : PartitionCovers ν μ) :
    ∃ i : LegalMinorRow n μ, growMinorPartition i = ν := by
  obtain ⟨r, hr, hrh, he⟩ := hc.exists_row_addition
  let i : Fin (n + 1) := ⟨n - r, by omega⟩
  have hi : n - (i : ℕ) = r := by dsimp [i]; omega
  let j : LegalMinorRow n μ := ⟨i, hi.symm ▸ hr⟩
  refine ⟨j, ?_⟩
  have hh : growMinorPartition j = addPartitionBox μ r hr := by
    dsimp [growMinorPartition, j]
    congr 1
  exact hh.trans he

theorem sum_legalMinorRows_eq_sum_covers {M : Type*} [AddCommMonoid M]
    (n : ℕ) (μ : YoungDiagram) (hn : μ.colLen 0 ≤ n) (f : YoungDiagram → M) :
    (∑ i : LegalMinorRow n μ, f (growMinorPartition i)) =
      ∑ ν : SizedYoungDiagram (partitionSize μ + 1),
        if PartitionCovers ν.val μ then f ν.val else 0 := by
  let e : LegalMinorRow n μ → SizedYoungDiagram (partitionSize μ + 1) :=
    fun i => ⟨growMinorPartition i, partitionSize_growMinorPartition i⟩
  apply Fintype.sum_of_injective e
  · intro i j he
    exact growMinorPartition_injective n μ (congrArg Subtype.val he)
  · intro ν hν
    have hncover : ¬ PartitionCovers ν.val μ := by
      intro hc
      obtain ⟨i, hi⟩ := exists_legalMinorRow_of_cover hn hc
      exact hν ⟨i, Subtype.ext hi⟩
    simp only [hncover, ite_false]
  · intro i
    have hc : PartitionCovers (growMinorPartition i) μ :=
      addPartitionBox_covers μ _ i.property
    exact (if_pos hc).symm

end
end ModifiedCartan


