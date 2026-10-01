import ModifiedCartan.LaurentDerivative
import Mathlib.RingTheory.Derivation.Basic

open scoped BigOperators LaurentPolynomial

namespace ModifiedCartan
noncomputable section

theorem laurentDerivative_mul_single_single {R : Type*} [CommRing R]
    (m n : ℤ) (a b : R) :
    laurentDerivative (AddMonoidAlgebra.single m a * AddMonoidAlgebra.single n b) =
      AddMonoidAlgebra.single m a * laurentDerivative (AddMonoidAlgebra.single n b) +
        AddMonoidAlgebra.single n b * laurentDerivative (AddMonoidAlgebra.single m a) := by
  simp only [AddMonoidAlgebra.single_mul_single, laurentDerivative_single]
  rw [show m + (n - 1) = m + n - 1 by omega,
    show n + (m - 1) = m + n - 1 by omega, ← AddMonoidAlgebra.single_add]
  apply congrArg (AddMonoidAlgebra.single (m + n - 1))
  push_cast
  ring

theorem laurentDerivative_mul {R : Type*} [CommRing R] (p q : LaurentPolynomial R) :
    laurentDerivative (p * q) = p * laurentDerivative q + q * laurentDerivative p := by
  induction p using LaurentPolynomial.induction_on' with
  | add p r hp hr =>
    simp only [add_mul, laurentDerivative_add, hp, hr, mul_add]
    ring
  | C_mul_T n a =>
    induction q using LaurentPolynomial.induction_on' with
    | add q r hq hr =>
      simp only [mul_add, laurentDerivative_add, hq, hr, add_mul]
      ring
    | C_mul_T m b =>
      simpa only [← LaurentPolynomial.single_eq_C_mul_T] using
        laurentDerivative_mul_single_single n m a b

def laurentDerivation (R : Type*) [CommRing R] :
    Derivation R (LaurentPolynomial R) (LaurentPolynomial R) where
  toFun := laurentDerivative
  map_add' := laurentDerivative_add
  map_smul' r p := laurentDerivative_smul r p
  map_one_eq_zero' := by
    change laurentDerivative (LaurentPolynomial.C (1 : R)) = 0
    exact laurentDerivative_C 1
  leibniz' p q := laurentDerivative_mul p q

theorem laurentDerivation_apply {R : Type*} [CommRing R] (p : LaurentPolynomial R) :
    laurentDerivation R p = laurentDerivative p := rfl

theorem laurentDerivative_T {R : Type*} [CommRing R] (n : ℤ) :
    laurentDerivative (LaurentPolynomial.T n : LaurentPolynomial R) =
      LaurentPolynomial.C (n : R) * LaurentPolynomial.T (n - 1) := by
  rw [LaurentPolynomial.T, laurentDerivative_single, one_mul,
    LaurentPolynomial.single_eq_C_mul_T]

end
end ModifiedCartan

