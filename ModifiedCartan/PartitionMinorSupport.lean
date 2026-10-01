import ModifiedCartan.SortedMinorOrders
import ModifiedCartan.PartitionMinorDerivative

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

theorem partition_le_iff_minorOrders_le {n : ℕ} {μ ω : YoungDiagram}
    (hμ : PartitionFits n μ) :
    μ ≤ ω ↔ ∀ i : Fin (n + 1), partitionMinorOrders n μ i ≤ partitionMinorOrders n ω i := by
  constructor
  · intro h i
    have hr := partition_rowLen_mono h (n - (i : ℕ))
    dsimp [partitionMinorOrders]
    omega
  · intro h
    rw [partition_le_iff_rowLen_le]
    intro r
    by_cases hr : r < n + 1
    · let i : Fin (n + 1) := ⟨n - r, by omega⟩
      have hi := h i
      have heq : n - (n - r) = r := by omega
      dsimp [partitionMinorOrders, i] at hi
      rw [heq] at hi
      omega
    · rw [hμ.rowLen_eq_zero (by omega)]
      exact Nat.zero_le _

theorem polynomialDerivativeMinor_eq_zero_of_order_bound {N : ℕ}
    (a b : Fin N → ℕ) (p : Fin N → Polynomial ℂ)
    (ha : StrictMono a) (hb : Monotone b) (hp : ∀ j, (p j).natDegree ≤ b j)
    (hi : ∃ i, b i < a i) : polynomialDerivativeMinor a p = 0 := by
  rw [polynomialDerivativeMinor, Matrix.det_apply]
  apply Finset.sum_eq_zero
  intro σ _
  obtain ⟨j, hj⟩ := exists_order_above_permuted_bound ha hb hi σ
  have hz : (∏ i : Fin N, (Matrix.of fun i j => Polynomial.derivative^[a i] (p j)) (σ i) i) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    exact Polynomial.iterate_derivative_eq_zero ((hp j).trans_lt hj)
  rw [hz, smul_zero]

/-- Coordinates outside the degree shape vanish, as in the Schubert-cell convention. -/
theorem partitionPolynomialMinor_eq_zero_of_not_le {n : ℕ}
    (μ ω : YoungDiagram) (p : Fin (n + 1) → Polynomial ℂ)
    (hp : ∀ j, (p j).natDegree ≤ partitionMinorOrders n ω j) (h : ¬ μ ≤ ω) :
    partitionPolynomialMinor μ p = 0 := by
  by_cases hμ : PartitionFits n μ
  · rw [partitionPolynomialMinor_of_fits hμ]
    have hi : ∃ i, partitionMinorOrders n ω i < partitionMinorOrders n μ i := by
      by_contra! hi
      exact h ((partition_le_iff_minorOrders_le hμ).mpr hi)
    exact polynomialDerivativeMinor_eq_zero_of_order_bound _ _ p
      (partitionMinorOrders_strictMono n μ) (partitionMinorOrders_strictMono n ω).monotone hp hi
  · exact partitionPolynomialMinor_of_not_fits hμ p

end
end ModifiedCartan


