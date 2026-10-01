import ModifiedCartan.KPCoefficientDerivative
import ModifiedCartan.LegalMinorRowCovers

open scoped BigOperators Classical MonoidAlgebra

namespace ModifiedCartan
noncomputable section

variable {A : Type*} [Fintype A] [DecidableEq A]

theorem kpBetaCoefficientPolynomial_derivative_legal (μ : YoungDiagram)
    (z : A → ℂ) (g : Equiv.Perm A) :
    (kpBetaCoefficientPolynomial μ z g).derivative =
      ∑ i : LegalMinorRow (Fintype.card A) μ, kpBetaCoefficientPolynomial (growMinorPartition i) z g := by
  by_cases hs : partitionSize μ ≤ Fintype.card A
  · rw [kpBetaCoefficientPolynomial_derivative]
    exact (sum_legalMinorRows_eq_sum_covers (Fintype.card A) μ
      ((partition_colLen_le_size μ 0).trans hs) (fun ν => kpBetaCoefficientPolynomial ν z g)).symm
  · have hgμ : Fintype.card A < partitionSize μ := by omega
    rw [kpBetaCoefficientPolynomial_of_size_gt μ z g hgμ, Polynomial.derivative_zero]
    symm
    apply Finset.sum_eq_zero
    intro i _
    apply kpBetaCoefficientPolynomial_of_size_gt
    rw [partitionSize_growMinorPartition]
    omega

theorem iterate_derivative_kpBetaCoefficientPolynomial (μ : YoungDiagram)
    (z : A → ℂ) (g : Equiv.Perm A) (k : ℕ) :
    Polynomial.derivative^[k] (kpBetaCoefficientPolynomial μ z g) =
      ∑ p : MinorGrowthPath (Fintype.card A) μ k,
        kpBetaCoefficientPolynomial (minorGrowthEndpoint k p) z g := by
  induction k generalizing μ with
  | zero =>
    haveI : Unique (MinorGrowthPath (Fintype.card A) μ 0) := inferInstanceAs (Unique PUnit)
    simp [minorGrowthEndpoint]
  | succ k ih =>
    rw [Function.iterate_succ_apply, kpBetaCoefficientPolynomial_derivative_legal,
      Polynomial.iterate_derivative_sum]
    change (∑ i : LegalMinorRow (Fintype.card A) μ,
        Polynomial.derivative^[k] (kpBetaCoefficientPolynomial (growMinorPartition i) z g)) =
      ∑ p : (Σ i : LegalMinorRow (Fintype.card A) μ,
        MinorGrowthPath (Fintype.card A) (growMinorPartition i) k),
          kpBetaCoefficientPolynomial (minorGrowthEndpoint k p.2) z g
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro i _
    exact ih (growMinorPartition i)

end
end ModifiedCartan


