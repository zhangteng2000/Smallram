import ModifiedCartan.CompositionLaurentWeights
import ModifiedCartan.PositiveGeometricSum

open scoped BigOperators LaurentPolynomial

namespace ModifiedCartan
noncomputable section

def normalizedGeometricLaurent {R : Type*} [CommRing R] (n : ℕ)
    (z : LaurentPolynomial R) : LaurentPolynomial R :=
  LaurentPolynomial.T (-(n : ℤ) - 1) * positiveGeometricSum n z

def normalizedGeometricColor {R : Type*} [CommRing R] (n : ℕ) (x : R) : LaurentPolynomial R :=
  normalizedGeometricLaurent n (LaurentPolynomial.C x * LaurentPolynomial.T 1)

theorem normalizedGeometricLaurent_one {R : Type*} [CommRing R] (n : ℕ) :
    normalizedGeometricLaurent (R := R) n 1 = compositionJacobianWeight n := by
  simp only [normalizedGeometricLaurent, positiveGeometricSum, one_pow,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
    compositionJacobianWeight, map_natCast]
  exact mul_comm _ _

theorem normalizedGeometricColor_boundary {R : Type*} [CommRing R] (n : ℕ) (x : R) :
    compositionUnusedWeight x * normalizedGeometricColor n x = compositionBoundaryWeight n x := by
  have h₁ : (LaurentPolynomial.T (-(n : ℤ) - 1) : LaurentPolynomial R) *
      LaurentPolynomial.T 1 = LaurentPolynomial.T (-(n : ℤ)) := by
    rw [← LaurentPolynomial.T_add]
    congr 1
    omega
  have h₂ : (LaurentPolynomial.T (-(n : ℤ) - 1) : LaurentPolynomial R) *
      LaurentPolynomial.T ((n + 1 : ℕ) : ℤ) = 1 := by
    rw [← LaurentPolynomial.T_add]
    convert LaurentPolynomial.T_zero (R := R) using 1 <;> congr 1 <;> omega
  calc
    _ = LaurentPolynomial.T (-(n : ℤ) - 1) *
        ((1 - LaurentPolynomial.C x * LaurentPolynomial.T 1) *
          positiveGeometricSum n (LaurentPolynomial.C x * LaurentPolynomial.T 1)) := by
      unfold compositionUnusedWeight normalizedGeometricColor normalizedGeometricLaurent
      ring
    _ = LaurentPolynomial.T (-(n : ℤ) - 1) *
        (LaurentPolynomial.C x * LaurentPolynomial.T 1 -
          (LaurentPolynomial.C x * LaurentPolynomial.T 1) ^ (n + 1)) := by
      rw [one_sub_mul_positiveGeometricSum]
    _ = (LaurentPolynomial.T (-(n : ℤ) - 1) * LaurentPolynomial.T 1) * LaurentPolynomial.C x -
        (LaurentPolynomial.T (-(n : ℤ) - 1) * LaurentPolynomial.T ((n + 1 : ℕ) : ℤ)) *
          LaurentPolynomial.C (x ^ (n + 1)) := by
      rw [mul_pow, LaurentPolynomial.T_pow]
      simp only [mul_one, map_pow]
      ring
    _ = _ := by rw [h₁, h₂, one_mul]; rfl

end
end ModifiedCartan

