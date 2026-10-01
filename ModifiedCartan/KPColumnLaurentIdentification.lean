import ModifiedCartan.KPColumnSupportedExpansion
import ModifiedCartan.LaurentColumnCoefficient

open scoped BigOperators Classical MonoidAlgebra

namespace ModifiedCartan
noncomputable section

/-- After substituting the actual parameters, the Laurent coefficient of the
literal first factor in KP equation (4.3) is the previously defined single-column
KP operator, with the exact sign and Laurent exponent. LaTeX `eq:KP-operators`. -/
theorem supportedColumnLaurentSeries_coeff {A B : Type*} [Fintype A]
    (z : A → ℂ) (θ : Equiv.Perm A) (k : ℕ) :
    (evaluateSupportedMarkers (B := B) z ((supportedColumnLaurentSeries A B).coeff θ)).coeff (-(k : ℤ)) =
      MvPolynomial.C ((-1 : ℂ) ^ k * (kpBeta (columnPartition k) z 0).coeff θ) := by
  rw [supportedColumnLaurentSeries, kpBeta_column_supported]
  simp only [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, map_sum,
    AddMonoidAlgebra.coeff_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hg : p.2.val = θ <;> by_cases hk : p.1.card = k <;>
    simp only [MonoidAlgebra.coeff_single, MonoidAlgebra.coeff_smul_apply,
      Finsupp.single_apply, evaluateSupportedMarkers_monomial, laurentColumnWeight_coeff,
      hg, hk, ite_true, ite_false, map_zero, MonoidAlgebra.coeff_zero,
      AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply, smul_eq_mul, zero_add, mul_zero]

end
end ModifiedCartan

