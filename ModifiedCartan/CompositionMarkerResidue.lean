import ModifiedCartan.CompositionMarkerSubstitution

open scoped BigOperators LaurentPolynomial

namespace ModifiedCartan
noncomputable section

/-- Exact finite formal change-of-variable identity used for the composition
residue in KP source Lemma 2.25. The marker coefficient identification is separate. -/
theorem compositionMarkerResidue {A B R : Type*} [Fintype A] [Fintype B]
    [CommRing R] [IsDomain R] [CharZero R] (ℓ : A → ℕ) (y : A → R) (x : B → R) :
    ((1 + ∑ a : A, LaurentPolynomial.C ((ℓ a : R) * y a) *
        LaurentPolynomial.T (-(ℓ a : ℤ) - 1)) *
      ∏ b : B, ((1 - LaurentPolynomial.C (x b) * LaurentPolynomial.T 1) +
        ∑ a : A, LaurentPolynomial.C (y a) *
          (LaurentPolynomial.T (-(ℓ a : ℤ)) * LaurentPolynomial.C (x b) -
            LaurentPolynomial.C (x b ^ (ℓ a + 1))))).coeff (-1) = 0 := by
  rw [← compositionMarkerSubstitution_derivative]
  simp_rw [← compositionMarkerSubstitution_affine]
  exact laurent_residue_derivative_mul_affine_product
    (compositionMarkerSubstitution ℓ y) x (fun b => 1 - ∑ a : A, y a * x b ^ (ℓ a + 1))

end
end ModifiedCartan

