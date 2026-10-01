import ModifiedCartan.GrowthCountTableaux

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

def minorGrowthEndpoints (n : ℕ) (μ : YoungDiagram) (k : ℕ) : Finset YoungDiagram :=
  Finset.univ.image (minorGrowthEndpoint (n := n) (μ := μ) k)

theorem mem_minorGrowthEndpoints {n : ℕ} {μ ν : YoungDiagram} {k : ℕ} :
    ν ∈ minorGrowthEndpoints n μ k ↔
      ∃ p : MinorGrowthPath n μ k, minorGrowthEndpoint k p = ν := by
  simp [minorGrowthEndpoints]

theorem sum_minorGrowthEndpoints (n : ℕ) (μ : YoungDiagram) (k : ℕ)
    (f : YoungDiagram → Polynomial ℂ) :
    (∑ p : MinorGrowthPath n μ k, f (minorGrowthEndpoint k p)) =
      ∑ ν ∈ minorGrowthEndpoints n μ k, (minorGrowthCount n μ ν k : Polynomial ℂ) * f ν := by
  have hs := Finset.sum_fiberwise_of_maps_to'
    (s := (Finset.univ : Finset (MinorGrowthPath n μ k)))
    (t := minorGrowthEndpoints n μ k)
    (g := minorGrowthEndpoint k)
    (fun p _ => mem_minorGrowthEndpoints.mpr ⟨p, rfl⟩) f
  rw [← hs]
  apply Finset.sum_congr rfl
  intro ν _
  rw [Finset.sum_const, nsmul_eq_mul]
  congr 1
  exact congrArg (Nat.cast : ℕ → Polynomial ℂ) (Fintype.card_subtype _).symm

/-- Iterated minor differentiation, grouped with actual skew-tableau coefficients. -/
theorem iterate_derivative_partitionPolynomialMinor_tableaux {n : ℕ} {μ : YoungDiagram}
    (p : Fin (n + 1) → Polynomial ℂ) (hμ : PartitionFits n μ) (k : ℕ) :
    Polynomial.derivative^[k] (partitionPolynomialMinor μ p) =
      ∑ ν ∈ minorGrowthEndpoints n μ k,
        (standardSkewTableauCount ν μ : Polynomial ℂ) * partitionPolynomialMinor ν p := by
  rw [iterate_derivative_partitionPolynomialMinor p hμ k,
    sum_minorGrowthEndpoints n μ k (fun ν => partitionPolynomialMinor ν p)]
  apply Finset.sum_congr rfl
  intro ν hν
  obtain ⟨q, rfl⟩ := mem_minorGrowthEndpoints.mp hν
  rw [minorGrowthCount_eq_standardSkewTableauCount (le_minorGrowthEndpoint k q)
    (minorGrowthEndpoint_fits hμ k q) k (partitionSize_minorGrowthEndpoint k q)]

end
end ModifiedCartan


