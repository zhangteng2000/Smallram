import ModifiedCartan.KPPolynomialCoefficients

open scoped BigOperators Classical MonoidAlgebra

namespace ModifiedCartan
noncomputable section

variable {A : Type*} [Fintype A] [DecidableEq A]

theorem kpBetaCoefficientPolynomial_derivative_subsets (μ : YoungDiagram)
    (z : A → ℂ) (g : Equiv.Perm A) :
    (kpBetaCoefficientPolynomial μ z g).derivative =
      ∑ J : SizedLetterSubset A (partitionSize μ + 1),
        Polynomial.C ((∑ a : J.val, kpAlpha μ (J.val.erase a.val)).coeff g) * kpWeightPolynomial z J.val := by
  simp only [kpBetaCoefficientPolynomial, Polynomial.derivative_sum, Polynomial.derivative_mul,
    Polynomial.derivative_C, zero_mul, zero_add, kpWeightPolynomial_derivative, Finset.mul_sum]
  rw [sum_sizedSubset_insert (partitionSize μ)
    (fun I a => Polynomial.C ((kpAlpha μ I).coeff g) * kpWeightPolynomial z (insert a I))]
  apply Finset.sum_congr rfl
  intro J _
  simp only [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, map_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.insert_erase a.property]

theorem kpBetaCoefficientPolynomial_derivative (μ : YoungDiagram) (z : A → ℂ) (g : Equiv.Perm A) :
    (kpBetaCoefficientPolynomial μ z g).derivative =
      ∑ ν : SizedYoungDiagram (partitionSize μ + 1),
        if PartitionCovers ν.val μ then kpBetaCoefficientPolynomial ν.val z g else 0 := by
  rw [kpBetaCoefficientPolynomial_derivative_subsets]
  have hα (J : SizedLetterSubset A (partitionSize μ + 1)) :
      (∑ a : J.val, kpAlpha μ (J.val.erase a.val)) =
        ∑ ν : SizedYoungDiagram (partitionSize μ + 1),
          if PartitionCovers ν.val μ then kpAlpha ν.val J.val else 0 :=
    (kpAlpha_sum_erase_subset J.val μ J.property).trans
      (sum_sizedYoungDiagram_congr J.property (fun ν => if PartitionCovers ν μ then kpAlpha ν J.val else 0))
  simp_rw [hα]
  simp only [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, map_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ν _
  by_cases hc : PartitionCovers ν.val μ
  · simp only [hc, ite_true]
    exact sum_sizedLetterSubset_congr ν.property.symm
      (fun I => Polynomial.C ((kpAlpha ν.val I).coeff g) * kpWeightPolynomial z I)
  · simp only [hc, ite_false, MonoidAlgebra.coeff_zero, Finsupp.zero_apply, map_zero,
      zero_mul, Finset.sum_const_zero]

end
end ModifiedCartan


