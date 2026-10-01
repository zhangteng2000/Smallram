import ModifiedCartan.MinorDerivativeTableaux
import ModifiedCartan.PartitionMinorSupport

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

def subpartitionFinset (ω : YoungDiagram) : Finset YoungDiagram :=
  Finset.univ.image (fun ν : Subpartition ω => ν.val)

@[simp] theorem mem_subpartitionFinset {ν ω : YoungDiagram} :
    ν ∈ subpartitionFinset ω ↔ ν ≤ ω := by
  simp [subpartitionFinset]

theorem sum_subpartitionFinset (ω : YoungDiagram) (f : YoungDiagram → Polynomial ℂ) :
    (∑ ν ∈ subpartitionFinset ω, f ν) = ∑ ν : Subpartition ω, f ν.val := by
  apply Finset.sum_image
  intro ν _ η _ h
  exact Subtype.ext h

theorem PartitionFits.of_le {n : ℕ} {ν ω : YoungDiagram}
    (hω : PartitionFits n ω) (h : ν ≤ ω) : PartitionFits n ν := by
  have hr := partition_rowLen_mono h (n + 1)
  dsimp [PartitionFits] at hω ⊢
  omega

theorem minorGrowthCount_eq_tableaux_if_size {n : ℕ} {μ ν : YoungDiagram}
    (hν : PartitionFits n ν) (k : ℕ) :
    minorGrowthCount n μ ν k =
      if partitionSize ν = partitionSize μ + k then standardSkewTableauCount ν μ else 0 := by
  split_ifs with hs
  · by_cases hμν : μ ≤ ν
    · exact minorGrowthCount_eq_standardSkewTableauCount hμν hν k hs
    · rw [minorGrowthCount_eq_zero_of_not_le k hμν, standardSkewTableauCount_of_not_le hμν]
  · exact minorGrowthCount_eq_zero_of_size_ne k hs

theorem sum_minorGrowthPaths_eq_sum_subpartitions {n : ℕ} (μ ω : YoungDiagram)
    (p : Fin (n + 1) → Polynomial ℂ)
    (hp : ∀ j, (p j).natDegree ≤ partitionMinorOrders n ω j) (k : ℕ) :
    (∑ q : MinorGrowthPath n μ k, partitionPolynomialMinor (minorGrowthEndpoint k q) p) =
      ∑ ν : Subpartition ω,
        (minorGrowthCount n μ ν.val k : Polynomial ℂ) * partitionPolynomialMinor ν.val p := by
  rw [← sum_subpartitionFinset ω (fun ν =>
    (minorGrowthCount n μ ν k : Polynomial ℂ) * partitionPolynomialMinor ν p)]
  have hs := Finset.sum_fiberwise_eq_sum_filter'
    (Finset.univ : Finset (MinorGrowthPath n μ k)) (subpartitionFinset ω)
    (minorGrowthEndpoint k) (fun ν => partitionPolynomialMinor ν p)
  have hc : (∑ ν ∈ subpartitionFinset ω,
      (minorGrowthCount n μ ν k : Polynomial ℂ) * partitionPolynomialMinor ν p) =
      ∑ ν ∈ subpartitionFinset ω,
        ∑ q ∈ (Finset.univ : Finset (MinorGrowthPath n μ k)) with
          minorGrowthEndpoint k q = ν, partitionPolynomialMinor ν p := by
    apply Finset.sum_congr rfl
    intro ν _
    simp only [Finset.sum_const, nsmul_eq_mul, minorGrowthCount, Fintype.card_subtype]
  rw [hc, hs]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro q _ hq
  have hnot : ¬ minorGrowthEndpoint k q ≤ ω := by
    intro hle
    exact hq (Finset.mem_filter.mpr ⟨Finset.mem_univ q, mem_subpartitionFinset.mpr hle⟩)
  exact partitionPolynomialMinor_eq_zero_of_not_le _ ω p hp hnot

/-- All derivative coefficients are supported on the actual subpartitions of the degree shape. -/
theorem iterate_derivative_partitionPolynomialMinor_subpartitions {n : ℕ} {μ ω : YoungDiagram}
    (p : Fin (n + 1) → Polynomial ℂ) (hμ : PartitionFits n μ) (hω : PartitionFits n ω)
    (hp : ∀ j, (p j).natDegree ≤ partitionMinorOrders n ω j) (k : ℕ) :
    Polynomial.derivative^[k] (partitionPolynomialMinor μ p) =
      ∑ ν : Subpartition ω,
        if partitionSize ν.val = partitionSize μ + k then
          (standardSkewTableauCount ν.val μ : Polynomial ℂ) * partitionPolynomialMinor ν.val p
        else 0 := by
  rw [iterate_derivative_partitionPolynomialMinor p hμ k,
    sum_minorGrowthPaths_eq_sum_subpartitions μ ω p hp k]
  apply Finset.sum_congr rfl
  intro ν _
  rw [minorGrowthCount_eq_tableaux_if_size (hω.of_le ν.property) k]
  split_ifs <;> simp

end
end ModifiedCartan


