import ModifiedCartan.SupportedPowerSumEvaluation
import ModifiedCartan.KPAlphaBoundedFrobenius
import ModifiedCartan.KPSubsetWeights

open scoped BigOperators Classical MonoidAlgebra

namespace ModifiedCartan
noncomputable section

/-- The literal second factor of KP equation (4.3), after substituting the
parameters, is precisely the generating polynomial of the actual KP beta
operators in the normalized finite character transforms. LaTeX `eq:KP-operators`.
The character transforms have not yet been identified with Schur determinants. -/
theorem evaluatedPowerSumSeries_frobenius {A B : Type*} [Fintype A] [Fintype B]
    (z : A → ℂ) (θ : Equiv.Perm A) :
    evaluateSupportedMarkers z ((supportedPowerSumSeries A B).coeff θ) =
      LaurentPolynomial.C
        (∑ μ : Subpartition (partitionSquare (Fintype.card A)),
          MvPolynomial.C ((kpBeta μ.val z 0).coeff θ) * finiteFrobeniusPolynomial B μ.val) := by
  rw [evaluateSupportedPowerSumSeries]
  apply congrArg LaurentPolynomial.C
  simp_rw [supportedCycleSum_bounded_frobenius_coeff, kpBeta_eq_sum_all_subsets]
  simp only [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, MonoidAlgebra.coeff_smul_apply,
    smul_eq_mul, map_sum, Finset.mul_sum, Finset.sum_mul, kpWeight, zero_add, map_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro μ hμ
  apply Finset.sum_congr rfl
  intro X hX
  ring

end
end ModifiedCartan

