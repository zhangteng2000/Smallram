import ModifiedCartan.MonoidAlgebraCoefficientSwap
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Algebra.MvPolynomial.Basic

namespace ModifiedCartan
noncomputable section

def laurentMarkerEquiv (A R : Type*) [CommSemiring R] :
    MvPolynomial A (LaurentPolynomial R) ≃+* LaurentPolynomial (MvPolynomial A R) :=
  AddMonoidAlgebra.commRingEquiv

theorem laurentMarkerEquiv_coeff {A R : Type*} [CommSemiring R]
    (p : MvPolynomial A (LaurentPolynomial R)) (d : A →₀ ℕ) (n : ℤ) :
    MvPolynomial.coeff d ((laurentMarkerEquiv A R p).coeff n) =
      (MvPolynomial.coeff d p).coeff n :=
  addMonoidAlgebra_comm_coeff p n d

theorem laurentMarkerEquiv_C_C {A R : Type*} [CommSemiring R] (x : R) :
    laurentMarkerEquiv A R (MvPolynomial.C (LaurentPolynomial.C x)) =
      LaurentPolynomial.C (MvPolynomial.C x) := by
  exact AddMonoidAlgebra.commRingEquiv_single_single 0 0 x

theorem laurentMarkerEquiv_C_T {A R : Type*} [CommSemiring R] (n : ℤ) :
    laurentMarkerEquiv A R (MvPolynomial.C (LaurentPolynomial.T n)) =
      LaurentPolynomial.T n := by
  exact AddMonoidAlgebra.commRingEquiv_single_zero_single n

theorem laurentMarkerEquiv_X {A R : Type*} [CommSemiring R] (a : A) :
    laurentMarkerEquiv A R (MvPolynomial.X a) =
      LaurentPolynomial.C (MvPolynomial.X a) := by
  exact AddMonoidAlgebra.commRingEquiv_single_single (Finsupp.single a 1) 0 1

end
end ModifiedCartan

