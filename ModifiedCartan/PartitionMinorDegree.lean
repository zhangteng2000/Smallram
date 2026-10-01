import ModifiedCartan.PartitionMinorSupport
import ModifiedCartan.MinorGrowthPaths

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

theorem polynomial_natDegree_le_of_iterate_derivative_eq_zero
    (p : Polynomial ℂ) (d : ℕ) (h : Polynomial.derivative^[d + 1] p = 0) :
    p.natDegree ≤ d := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro N hN
  have hc := congrArg (fun q : Polynomial ℂ => q.coeff (N - (d + 1))) h
  rw [Polynomial.coeff_iterate_derivative, Polynomial.coeff_zero,
    Nat.sub_add_cancel (by omega : d + 1 ≤ N), nsmul_eq_mul] at hc
  have hn : (N.descFactorial (d + 1) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.descFactorial_pos.mpr (by omega : d + 1 ≤ N)).ne'
  exact (mul_eq_zero.mp hc).resolve_left hn

theorem iterate_derivative_partitionPolynomialMinor_eq_zero_of_size {n : ℕ}
    (μ ω : YoungDiagram) (p : Fin (n + 1) → Polynomial ℂ)
    (hp : ∀ j, (p j).natDegree ≤ partitionMinorOrders n ω j)
    (k : ℕ) (hk : partitionSize ω < partitionSize μ + k) :
    Polynomial.derivative^[k] (partitionPolynomialMinor μ p) = 0 := by
  by_cases hμ : PartitionFits n μ
  · rw [iterate_derivative_partitionPolynomialMinor p hμ k]
    apply Finset.sum_eq_zero
    intro q _
    apply partitionPolynomialMinor_eq_zero_of_not_le _ ω p hp
    intro hle
    have hs := partitionSize_mono hle
    rw [partitionSize_minorGrowthEndpoint k q] at hs
    omega
  · rw [partitionPolynomialMinor_of_not_fits hμ p]
    exact Polynomial.iterate_derivative_zero

/-- The degree loss equals the number of derivative-order boxes. -/
theorem partitionPolynomialMinor_natDegree_le {n : ℕ}
    (μ ω : YoungDiagram) (p : Fin (n + 1) → Polynomial ℂ)
    (hp : ∀ j, (p j).natDegree ≤ partitionMinorOrders n ω j) :
    (partitionPolynomialMinor μ p).natDegree ≤ partitionSize ω - partitionSize μ := by
  apply polynomial_natDegree_le_of_iterate_derivative_eq_zero
  exact iterate_derivative_partitionPolynomialMinor_eq_zero_of_size μ ω p hp _ (by omega)

end
end ModifiedCartan


