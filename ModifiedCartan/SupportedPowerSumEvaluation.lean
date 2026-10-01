import ModifiedCartan.KPAlphaFrobeniusCoefficients
import ModifiedCartan.SupportedMarkerEvaluation

open scoped BigOperators Classical MonoidAlgebra

namespace ModifiedCartan
noncomputable section

theorem evaluateSupportedPowerSumSeries {A B : Type*} [Fintype A] [Fintype B]
    (z : A → ℂ) (θ : Equiv.Perm A) :
    evaluateSupportedMarkers z ((supportedPowerSumSeries A B).coeff θ) =
      LaurentPolynomial.C (∑ X : Finset A,
        MvPolynomial.C (∏ l ∈ Finset.univ \ X, z l) * (supportedCycleSum B X).coeff θ) := by
  rw [supportedPowerSumSeries, Fintype.sum_sigma]
  simp only [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, map_sum,
    supportedCycleSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro X hX
  apply Finset.sum_congr rfl
  intro π hπ
  by_cases hg : π.val = θ <;>
    simp only [MonoidAlgebra.coeff_single, Finsupp.single_apply, hg, ite_true, ite_false,
      map_zero, mul_zero, zero_mul, evaluateSupportedMarkers_monomial, finiteCyclePolynomial,
      map_mul] <;> ring

end
end ModifiedCartan

