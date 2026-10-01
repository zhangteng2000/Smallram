import ModifiedCartan.LaurentMarkerEquiv
import ModifiedCartan.CompositionMarkerResidue

open scoped BigOperators LaurentPolynomial

namespace ModifiedCartan
noncomputable section

def compositionUnusedWeight {R : Type*} [CommRing R] (x : R) : LaurentPolynomial R :=
  1 - LaurentPolynomial.C x * LaurentPolynomial.T 1

def compositionBoundaryWeight {R : Type*} [CommRing R] (n : ℕ) (x : R) : LaurentPolynomial R :=
  LaurentPolynomial.T (-(n : ℤ)) * LaurentPolynomial.C x - LaurentPolynomial.C (x ^ (n + 1))

def compositionJacobianWeight {R : Type*} [CommRing R] (n : ℕ) : LaurentPolynomial R :=
  LaurentPolynomial.C (n : R) * LaurentPolynomial.T (-(n : ℤ) - 1)

theorem laurentMarkerEquiv_unused {A R : Type*} [CommRing R] (x : R) :
    laurentMarkerEquiv A R (MvPolynomial.C (compositionUnusedWeight x)) =
      1 - LaurentPolynomial.C (MvPolynomial.C x) * LaurentPolynomial.T 1 := by
  simp only [compositionUnusedWeight, map_sub, map_one, map_mul,
    laurentMarkerEquiv_C_C, laurentMarkerEquiv_C_T]

theorem laurentMarkerEquiv_boundary {A R : Type*} [CommRing R] (n : ℕ) (x : R) :
    laurentMarkerEquiv A R (MvPolynomial.C (compositionBoundaryWeight n x)) =
      LaurentPolynomial.T (-(n : ℤ)) * LaurentPolynomial.C (MvPolynomial.C x) -
        LaurentPolynomial.C ((MvPolynomial.C x) ^ (n + 1)) := by
  simp only [compositionBoundaryWeight, map_sub, map_mul, laurentMarkerEquiv_C_C,
    laurentMarkerEquiv_C_T, map_pow]

theorem laurentMarkerEquiv_jacobian {A R : Type*} [CommRing R] (n : ℕ) (a : A) :
    laurentMarkerEquiv A R (MvPolynomial.X a * MvPolynomial.C (compositionJacobianWeight n)) =
      LaurentPolynomial.C ((n : MvPolynomial A R) * MvPolynomial.X a) *
        LaurentPolynomial.T (-(n : ℤ) - 1) := by
  simp only [compositionJacobianWeight, map_mul, laurentMarkerEquiv_X,
    laurentMarkerEquiv_C_C, laurentMarkerEquiv_C_T, map_natCast]
  ring

end
end ModifiedCartan

