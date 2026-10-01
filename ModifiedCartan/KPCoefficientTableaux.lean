import ModifiedCartan.KPCoefficientGrowthPaths
import ModifiedCartan.BoundedPartitionSquare
import ModifiedCartan.MinorDerivativeSubpartitions

open scoped BigOperators Classical MonoidAlgebra

namespace ModifiedCartan
noncomputable section

variable {A : Type*} [Fintype A] [DecidableEq A]

theorem kpBetaCoefficientPolynomial_of_not_le_square (μ : YoungDiagram)
    (z : A → ℂ) (g : Equiv.Perm A) (h : ¬ μ ≤ partitionSquare (Fintype.card A)) :
    kpBetaCoefficientPolynomial μ z g = 0 := by
  apply kpBetaCoefficientPolynomial_of_size_gt
  by_contra! hn
  exact h (partition_le_square_of_size_le μ _ hn)

theorem sum_minorGrowthPaths_kp_subpartitions (μ : YoungDiagram)
    (z : A → ℂ) (g : Equiv.Perm A) (k : ℕ) :
    (∑ p : MinorGrowthPath (Fintype.card A) μ k,
      kpBetaCoefficientPolynomial (minorGrowthEndpoint k p) z g) =
      ∑ ν : Subpartition (partitionSquare (Fintype.card A)),
        (minorGrowthCount (Fintype.card A) μ ν.val k : Polynomial ℂ) * kpBetaCoefficientPolynomial ν.val z g := by
  rw [← sum_subpartitionFinset (partitionSquare (Fintype.card A)) (fun ν =>
    (minorGrowthCount (Fintype.card A) μ ν k : Polynomial ℂ) * kpBetaCoefficientPolynomial ν z g)]
  have hs := Finset.sum_fiberwise_eq_sum_filter'
    (Finset.univ : Finset (MinorGrowthPath (Fintype.card A) μ k))
    (subpartitionFinset (partitionSquare (Fintype.card A))) (minorGrowthEndpoint k)
    (fun ν => kpBetaCoefficientPolynomial ν z g)
  have hc : (∑ ν ∈ subpartitionFinset (partitionSquare (Fintype.card A)),
      (minorGrowthCount (Fintype.card A) μ ν k : Polynomial ℂ) * kpBetaCoefficientPolynomial ν z g) =
      ∑ ν ∈ subpartitionFinset (partitionSquare (Fintype.card A)),
        ∑ p ∈ (Finset.univ : Finset (MinorGrowthPath (Fintype.card A) μ k)) with
          minorGrowthEndpoint k p = ν, kpBetaCoefficientPolynomial ν z g := by
    apply Finset.sum_congr rfl
    intro ν _
    simp only [Finset.sum_const, nsmul_eq_mul, minorGrowthCount, Fintype.card_subtype]
  rw [hc, hs]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro p _ hp
  have hn : ¬ minorGrowthEndpoint k p ≤ partitionSquare (Fintype.card A) := by
    intro hn
    exact hp (Finset.mem_filter.mpr ⟨Finset.mem_univ p, mem_subpartitionFinset.mpr hn⟩)
  exact kpBetaCoefficientPolynomial_of_not_le_square _ z g hn

theorem iterate_derivative_kpBetaCoefficientPolynomial_tableaux (μ : YoungDiagram)
    (z : A → ℂ) (g : Equiv.Perm A) (k : ℕ) :
    Polynomial.derivative^[k] (kpBetaCoefficientPolynomial μ z g) =
      ∑ ν : Subpartition (partitionSquare (Fintype.card A)),
        if partitionSize ν.val = partitionSize μ + k then
          (standardSkewTableauCount ν.val μ : Polynomial ℂ) * kpBetaCoefficientPolynomial ν.val z g else 0 := by
  rw [iterate_derivative_kpBetaCoefficientPolynomial, sum_minorGrowthPaths_kp_subpartitions]
  apply Finset.sum_congr rfl
  intro ν _
  rw [minorGrowthCount_eq_tableaux_if_size ((partitionSquare_fits (Fintype.card A)).of_le ν.property) k]
  split_ifs <;> simp

theorem iterate_derivative_kpBetaCoefficientPolynomial_eval (μ : YoungDiagram)
    (z : A → ℂ) (g : Equiv.Perm A) (k : ℕ) (a : ℂ) :
    (Polynomial.derivative^[k] (kpBetaCoefficientPolynomial μ z g)).eval a =
      ∑ ν : Subpartition (partitionSquare (Fintype.card A)),
        if partitionSize ν.val = partitionSize μ + k then
          (standardSkewTableauCount ν.val μ : ℂ) * (kpBetaCoefficientPolynomial ν.val z g).eval a else 0 := by
  rw [iterate_derivative_kpBetaCoefficientPolynomial_tableaux, Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro ν _
  split_ifs <;> simp

end
end ModifiedCartan


