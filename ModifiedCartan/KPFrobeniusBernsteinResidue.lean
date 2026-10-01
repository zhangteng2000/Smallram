import ModifiedCartan.KPQuadraticFrobeniusExpansion
import ModifiedCartan.FrobeniusBernsteinCoefficients

open scoped BigOperators Classical LaurentPolynomial

namespace ModifiedCartan
noncomputable section

theorem finiteBernsteinLaurent_scalar_T_coeff {B : Type*} [Fintype B]
    (f : MvPolynomial (Option B) ℂ) (c : ℂ) (j n : ℤ) :
    (finiteBernsteinLaurent B
      (LaurentPolynomial.T j * LaurentPolynomial.C (MvPolynomial.C c * f))).coeff n =
      MvPolynomial.C c * (LaurentPolynomial.T j * finiteBernstein B f).coeff n := by
  rw [map_mul, finiteBernsteinLaurent_T_mul, finiteBernsteinLaurent_scalar_mul,
    finiteBernsteinLaurent_C, mul_left_comm, laurent_coeff_C_mul]

/-- The actual KP beta operators satisfy the finite Frobenius Bernstein
    residue identity for every parameter tuple, including repeated parameters.
    Auxiliary to manuscript `lem:KP-correspondence`. -/
theorem kpFrobeniusBernstein_residue {A B : Type*} [Fintype A] [Fintype B]
    (z : A → ℂ) (θ : Equiv.Perm A) :
    (∑ k ∈ Finset.range (Fintype.card A + 1),
      ∑ μ : Subpartition (partitionSquare (Fintype.card A)),
        MvPolynomial.C ((-1 : ℂ) ^ k *
          (kpBeta (columnPartition k) z 0 * kpBeta μ.val z 0).coeff θ) *
            finiteFrobeniusBernsteinResidue B μ.val k) = 0 := by
  have h := supportedPowerSumProduct_evaluated_residue (B := B) z θ
  rw [evaluatedSupportedProduct_frobenius, finiteBernsteinLaurent_sum] at h
  simp only [finiteBernsteinLaurent_sum, AddMonoidAlgebra.coeff_sum,
    Finsupp.finsetSum_apply, finiteBernsteinLaurent_scalar_T_coeff] at h
  exact h

end
end ModifiedCartan

#print axioms ModifiedCartan.kpFrobeniusBernstein_residue
