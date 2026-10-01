import ModifiedCartan.ZSupportLaurentNormalization
import ModifiedCartan.ZComplementLaurentProduct
import ModifiedCartan.BernsteinCompositionSeries

open scoped BigOperators Classical LaurentPolynomial

namespace ModifiedCartan
noncomputable section

/-- Exact factorization of the actual right-factor sum from KP Section 4.1.
This theorem still precedes the Schur/character and coefficient bridges. -/
theorem rightZFactorLaurentSeries_factorized {A B : Type*} [Fintype A] [Fintype B]
    (θ : Equiv.Perm A) (Z : Finset A) :
    rightZFactorLaurentSeries B θ Z =
      LaurentPolynomial.C (MvPolynomial.C ((-1 : ℂ) ^ Fintype.card A)) *
      ((LaurentPolynomial.T (-(∑ c ∈ permutationCycleImage θ (zStripComplement θ Z),
          (permutationCycleWeight θ (fun _ => 1) c : ℤ))) *
        finiteCompositionSeries B (zStripLength θ Z)) *
       ∏ c ∈ permutationCycleImage θ (zStripComplement θ Z),
        (1 - LaurentPolynomial.T (permutationCycleWeight θ (fun _ => 1) c : ℤ) *
          LaurentPolynomial.C (finitePowerSumPolynomial B (permutationCycleWeight θ (fun _ => 1) c)))) := by
  rw [rightZFactorLaurentSeries_parameters, ← zComplementLaurentProduct θ Z,
    finiteCompositionSeries]
  simp_rw [zSupportLaurentTerm_normalized]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]

end
end ModifiedCartan

