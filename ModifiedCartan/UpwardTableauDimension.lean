import ModifiedCartan.WeightedYoungDifferential
import ModifiedCartan.RankedTableauDimension

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

/-- The sum of tableau dimensions over all one-box enlargements is (size + 1) times the original. -/
theorem youngTableauDimension_upward (μ : YoungDiagram) :
    (∑ ξ : YoungSuccessor μ, youngTableauDimension ξ.val) =
      (partitionSize μ + 1) * youngTableauDimension μ := by
  suffices hmain : ∀ n : ℕ, ∀ μ : YoungDiagram, partitionSize μ = n →
      (∑ ξ : YoungSuccessor μ, youngTableauDimension ξ.val) = (n + 1) * youngTableauDimension μ from
    hmain (partitionSize μ) μ rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro μ hμ
    let m : SizedYoungDiagram n := ⟨μ, hμ⟩
    calc
      _ = ∑ ξ : SizedYoungDiagram (n + 1),
          if PartitionCovers ξ.val μ then youngTableauDimension ξ.val else 0 :=
        youngTableauDimension_successors_rank μ n hμ
      _ = ∑ ξ : SizedYoungDiagram (n + 1), if PartitionCovers ξ.val μ then
          ∑ ν : SizedYoungDiagram n, if PartitionCovers ξ.val ν.val then youngTableauDimension ν.val else 0 else 0 := by
        apply Finset.sum_congr rfl
        intro ξ _
        rw [youngTableauDimension_rank_rec n ξ.val ξ.property]
      _ = youngTableauDimension μ + ∑ δ : SizedYoungDiagram (n - 1), if PartitionCovers μ δ.val then
          ∑ ν : SizedYoungDiagram n, if PartitionCovers ν.val δ.val then youngTableauDimension ν.val else 0 else 0 :=
        young_lattice_weighted_differential n youngTableauDimension m
      _ = youngTableauDimension μ + ∑ δ : SizedYoungDiagram (n - 1),
          if PartitionCovers μ δ.val then n * youngTableauDimension δ.val else 0 := by
        congr 1
        apply Finset.sum_congr rfl
        intro δ _
        split_ifs with hδ
        · have hs : partitionSize δ.val + 1 = n := hδ.2.symm.trans hμ
          have hlt : partitionSize δ.val < n := by omega
          have hi := ih (partitionSize δ.val) hlt δ.val rfl
          have hr := youngTableauDimension_successors_rank_of_size δ.val n hs
          simpa only [hs] using (hr.symm.trans hi)
        · rfl
      _ = youngTableauDimension μ + n * ∑ δ : SizedYoungDiagram (n - 1),
          if PartitionCovers μ δ.val then youngTableauDimension δ.val else 0 := by
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro δ _
        split_ifs <;> simp
      _ = (n + 1) * youngTableauDimension μ := by
        by_cases hn : n = 0
        · simp only [hn, zero_mul, add_zero, zero_add, one_mul]
        · have hr := youngTableauDimension_rank_rec (n - 1) μ (by omega)
          rw [← hr]
          ring

theorem specht_finrank_sum_successors (μ : YoungDiagram) :
    (∑ ξ : YoungSuccessor μ, Module.finrank ℂ (YoungSpechtModule ξ.val)) =
      (partitionSize μ + 1) * Module.finrank ℂ (YoungSpechtModule μ) := by
  simp only [← youngTableauDimension_eq_finrank]
  exact youngTableauDimension_upward μ

end
end ModifiedCartan


