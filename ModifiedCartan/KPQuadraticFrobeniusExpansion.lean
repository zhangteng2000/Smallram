import ModifiedCartan.KPColumnLaurentExpansion
import ModifiedCartan.KPBetaFrobeniusIdentification
import ModifiedCartan.EvaluatedQuadraticResidue

open scoped BigOperators Classical MonoidAlgebra

namespace ModifiedCartan
noncomputable section

theorem finiteGroupAlgebra_coeff_mul {G R : Type*} [Group G] [Fintype G] [Semiring R]
    (x y : MonoidAlgebra R G) (g : G) :
    (x * y).coeff g = ∑ h : G, x.coeff h * y.coeff (h⁻¹ * g) := by
  rw [MonoidAlgebra.coeff_mul_apply_left]
  exact Finsupp.sum_fintype _ _ (fun _ => zero_mul _)

/-- KP (4.3) with both factors replaced by their proved actual character
    expansions. Auxiliary to paper `lem:KP-correspondence`. -/
theorem evaluatedSupportedProduct_frobenius {A B : Type*} [Fintype A] [Fintype B]
    (z : A → ℂ) (θ : Equiv.Perm A) :
    (((MonoidAlgebra.mapRingHom (Equiv.Perm A) (evaluateSupportedMarkers z))
        (supportedColumnLaurentSeries A B) *
      (MonoidAlgebra.mapRingHom (Equiv.Perm A) (evaluateSupportedMarkers z))
        (supportedPowerSumSeries A B)).coeff θ) =
      ∑ k ∈ Finset.range (Fintype.card A + 1),
        ∑ μ : Subpartition (partitionSquare (Fintype.card A)),
          LaurentPolynomial.T (-(k : ℤ)) * LaurentPolynomial.C
            (MvPolynomial.C ((-1 : ℂ) ^ k *
              (kpBeta (columnPartition k) z 0 * kpBeta μ.val z 0).coeff θ) *
                finiteFrobeniusPolynomial B μ.val) := by
  rw [finiteGroupAlgebra_coeff_mul]
  simp only [MonoidAlgebra.coeff_mapRingHom, evaluatedColumnLaurentSeries_eq_sum,
    evaluatedPowerSumSeries_frobenius, finiteGroupAlgebra_coeff_mul,
    map_sum, Finset.mul_sum, Finset.sum_mul]
  conv_lhs =>
    arg 2
    ext σ
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro μ hμ
  apply Finset.sum_congr rfl
  intro σ hσ
  simp only [map_mul]
  ring

end
end ModifiedCartan

#print axioms ModifiedCartan.evaluatedSupportedProduct_frobenius
