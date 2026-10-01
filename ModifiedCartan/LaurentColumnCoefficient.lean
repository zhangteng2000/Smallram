import ModifiedCartan.SupportedMarkerEvaluation

open scoped Classical

namespace ModifiedCartan
noncomputable section

theorem laurentColumnWeight_coeff {B : Type*} (m k : ℕ) (c w : ℂ) :
    (LaurentPolynomial.T (-(m : ℤ)) *
      LaurentPolynomial.C (MvPolynomial.C (c * (-1 : ℂ) ^ m)) *
      LaurentPolynomial.C (MvPolynomial.C w) : LaurentPolynomial (MvPolynomial B ℂ)).coeff (-(k : ℤ)) =
      if m = k then MvPolynomial.C ((-1 : ℂ) ^ k * (w * c)) else 0 := by
  have he : LaurentPolynomial.T (-(m : ℤ)) *
      LaurentPolynomial.C (MvPolynomial.C (c * (-1 : ℂ) ^ m)) *
      LaurentPolynomial.C (MvPolynomial.C w) =
      (LaurentPolynomial.C (MvPolynomial.C ((-1 : ℂ) ^ m * (w * c))) *
        LaurentPolynomial.T (-(m : ℤ)) : LaurentPolynomial (MvPolynomial B ℂ)) := by
    rw [show (-1 : ℂ) ^ m * (w * c) = (c * (-1 : ℂ) ^ m) * w by ring]
    simp only [map_mul]
    ring
  rw [he, ← LaurentPolynomial.single_eq_C_mul_T]
  simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, neg_inj, Nat.cast_inj]
  by_cases h : m = k
  · subst m
    simp
  · simp [h]

end
end ModifiedCartan

