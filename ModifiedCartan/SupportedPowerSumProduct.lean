import ModifiedCartan.SupportedPowerSumQuadratic

open scoped BigOperators Classical MonoidAlgebra

namespace ModifiedCartan
noncomputable section

def supportedColumnLaurentSeries (A B : Type*) [Fintype A] :
    MonoidAlgebra (MvPolynomial A (LaurentPolynomial (MvPolynomial B ℂ))) (Equiv.Perm A) :=
  ∑ p : SupportedPermutationData A,
    MonoidAlgebra.single p.2.val
      (MvPolynomial.monomial (markerSquarefreeDegree (Finset.univ \ p.1))
        (LaurentPolynomial.T (-(p.1.card : ℤ)) *
          LaurentPolynomial.C (MvPolynomial.C
            (((Equiv.Perm.sign p.2.val : ℤ) : ℂ) * (-1 : ℂ) ^ p.1.card))))

def supportedPowerSumSeries (A B : Type*) [Fintype A] [Fintype B] :
    MonoidAlgebra (MvPolynomial A (LaurentPolynomial (MvPolynomial B ℂ))) (Equiv.Perm A) :=
  ∑ p : SupportedPermutationData A,
    MonoidAlgebra.single p.2.val
      (MvPolynomial.monomial (markerSquarefreeDegree (Finset.univ \ p.1))
        (LaurentPolynomial.C (permutationFixedColoringSum
          (supportedPermutationRestriction p.1 p.2.val p.2.property)
          (fun b : B => (MvPolynomial.X b : MvPolynomial B ℂ)))))

/-- Literal multiplication of the two supported-permutation generating series
gives KP equation (4.3), auxiliary to LaTeX `lem:KP-correspondence`. -/
theorem supportedPowerSumQuadratic_eq_product (A B : Type*) [Fintype A] [Fintype B] :
    supportedPowerSumQuadratic A B =
      supportedColumnLaurentSeries A B * supportedPowerSumSeries A B := by
  rw [supportedPowerSumQuadratic, Fintype.sum_prod_type,
    supportedColumnLaurentSeries, supportedPowerSumSeries, Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  rw [MonoidAlgebra.single_mul_single, MvPolynomial.monomial_mul]
  simp only [complementMarkerDegree, supportedPowerSumLaurentWeight, map_mul, mul_assoc]

end
end ModifiedCartan

