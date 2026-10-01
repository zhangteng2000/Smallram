import ModifiedCartan.LaurentChangeVariableResidue

open scoped BigOperators LaurentPolynomial

namespace ModifiedCartan
noncomputable section

def compositionMarkerSubstitution {A R : Type*} [Fintype A] [CommRing R]
    (ℓ : A → ℕ) (y : A → R) : LaurentPolynomial R :=
  LaurentPolynomial.T 1 - ∑ a : A,
    LaurentPolynomial.C (y a) * LaurentPolynomial.T (-(ℓ a : ℤ))

theorem compositionMarkerSubstitution_derivative {A R : Type*} [Fintype A] [CommRing R]
    (ℓ : A → ℕ) (y : A → R) :
    laurentDerivative (compositionMarkerSubstitution ℓ y) =
      1 + ∑ a : A, LaurentPolynomial.C ((ℓ a : R) * y a) *
        LaurentPolynomial.T (-(ℓ a : ℤ) - 1) := by
  change laurentDerivation R (LaurentPolynomial.T 1 - ∑ a : A,
    LaurentPolynomial.C (y a) * LaurentPolynomial.T (-(ℓ a : ℤ))) = _
  simp only [map_sub, map_sum, laurentDerivation_apply, laurentDerivative_T,
    laurentDerivative_C_mul_T, Int.cast_one, sub_self, LaurentPolynomial.T_zero,
    map_one, mul_one, Int.cast_neg, Int.cast_natCast, mul_neg, map_neg, neg_mul,
    Finset.sum_neg_distrib, sub_neg_eq_add]
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  rw [mul_comm (y a)]

theorem compositionMarkerSubstitution_affine {A R : Type*} [Fintype A] [CommRing R]
    (ℓ : A → ℕ) (y : A → R) (x : R) :
    LaurentPolynomial.C (1 - ∑ a : A, y a * x ^ (ℓ a + 1)) -
        LaurentPolynomial.C x * compositionMarkerSubstitution ℓ y =
      (1 - LaurentPolynomial.C x * LaurentPolynomial.T 1) +
        ∑ a : A, LaurentPolynomial.C (y a) *
          (LaurentPolynomial.T (-(ℓ a : ℤ)) * LaurentPolynomial.C x -
            LaurentPolynomial.C (x ^ (ℓ a + 1))) := by
  rw [compositionMarkerSubstitution, map_sub, map_one, map_sum]
  simp only [map_mul]
  rw [mul_sub, Finset.mul_sum]
  simp only [mul_sub, Finset.sum_sub_distrib]
  have h : (∑ a : A, LaurentPolynomial.C x *
      (LaurentPolynomial.C (y a) * LaurentPolynomial.T (-(ℓ a : ℤ)))) =
      ∑ a : A, LaurentPolynomial.C (y a) *
        (LaurentPolynomial.T (-(ℓ a : ℤ)) * LaurentPolynomial.C x) := by
    exact Finset.sum_congr rfl (fun a ha => by ring)
  rw [h]
  ring

end
end ModifiedCartan

