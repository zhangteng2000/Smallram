import ModifiedCartan.BernsteinLaurentFactors

open scoped Classical LaurentPolynomial

namespace ModifiedCartan
noncomputable section

theorem finiteAlphabetShiftLaurent_scalar (B : Type*) (c : ℂ) :
    finiteAlphabetShiftLaurent B (LaurentPolynomial.C (MvPolynomial.C c)) =
      LaurentPolynomial.C (MvPolynomial.C c) := by
  rw [finiteAlphabetShiftLaurent_C]
  simp [finiteAlphabetShift]

theorem finiteBernsteinLaurent_scalar_mul (B : Type*) [Fintype B] (c : ℂ)
    (f : LaurentPolynomial (MvPolynomial (Option B) ℂ)) :
    finiteBernsteinLaurent B (LaurentPolynomial.C (MvPolynomial.C c) * f) =
      LaurentPolynomial.C (MvPolynomial.C c) * finiteBernsteinLaurent B f := by
  rw [finiteBernsteinLaurent_mul, finiteAlphabetShiftLaurent_scalar]

theorem finiteBernsteinLaurent_scalar_residue (B : Type*) [Fintype B] (c : ℂ)
    (f : LaurentPolynomial (MvPolynomial (Option B) ℂ))
    (hf : (finiteBernsteinLaurent B f).coeff (-1) = 0) :
    (finiteBernsteinLaurent B (LaurentPolynomial.C (MvPolynomial.C c) * f)).coeff (-1) = 0 := by
  rw [finiteBernsteinLaurent_scalar_mul, ← LaurentPolynomial.single_eq_C,
    AddMonoidAlgebra.coeff_single_zero_mul, hf, mul_zero]

end
end ModifiedCartan

