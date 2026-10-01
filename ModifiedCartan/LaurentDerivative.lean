import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Tactic.Ring

open scoped BigOperators LaurentPolynomial

namespace ModifiedCartan
noncomputable section

def laurentDerivative {R : Type*} [CommRing R] (p : LaurentPolynomial R) :
    LaurentPolynomial R :=
  p.coeff.sum (fun n a => AddMonoidAlgebra.single (n - 1) (a * (n : R)))

theorem laurentDerivative_add {R : Type*} [CommRing R] (p q : LaurentPolynomial R) :
    laurentDerivative (p + q) = laurentDerivative p + laurentDerivative q := by
  simp only [laurentDerivative, AddMonoidAlgebra.coeff_add]
  exact Finsupp.sum_add_index' (fun n => by simp) (fun n a b => by
    rw [add_mul, AddMonoidAlgebra.single_add])

theorem laurentDerivative_single {R : Type*} [CommRing R] (n : ℤ) (a : R) :
    laurentDerivative (AddMonoidAlgebra.single n a) =
      AddMonoidAlgebra.single (n - 1) (a * (n : R)) := by
  simp only [laurentDerivative, AddMonoidAlgebra.coeff_single]
  exact Finsupp.sum_single_index (by simp)

theorem laurentDerivative_coeff {R : Type*} [CommRing R] (p : LaurentPolynomial R) (n : ℤ) :
    (laurentDerivative p).coeff n = p.coeff (n + 1) * ((n + 1 : ℤ) : R) := by
  classical
  simp only [laurentDerivative, Finsupp.sum, AddMonoidAlgebra.coeff_sum,
    Finset.sum_apply', AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  rw [Finset.sum_eq_single (n + 1)]
  · simp
  · intro m hm hmn
    have he : m - 1 ≠ n := by omega
    simp only [ite_eq_right he]
  · intro hn
    simp [Finsupp.notMem_support_iff.mp hn]

theorem laurentDerivative_residue {R : Type*} [CommRing R] (p : LaurentPolynomial R) :
    (laurentDerivative p).coeff (-1) = 0 := by
  rw [laurentDerivative_coeff]
  simp

theorem laurentDerivative_smul {R : Type*} [CommRing R] (r : R) (p : LaurentPolynomial R) :
    laurentDerivative (r • p) = r • laurentDerivative p := by
  apply LaurentPolynomial.ext
  intro n
  simp only [laurentDerivative_coeff, AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul, mul_assoc]

theorem laurentDerivative_C {R : Type*} [CommRing R] (r : R) :
    laurentDerivative (LaurentPolynomial.C r) = 0 := by
  rw [← LaurentPolynomial.single_eq_C, laurentDerivative_single]
  simp

theorem laurentDerivative_C_mul_T {R : Type*} [CommRing R] (n : ℤ) (a : R) :
    laurentDerivative (LaurentPolynomial.C a * LaurentPolynomial.T n) =
      LaurentPolynomial.C (a * (n : R)) * LaurentPolynomial.T (n - 1) := by
  rw [← LaurentPolynomial.single_eq_C_mul_T, laurentDerivative_single,
    LaurentPolynomial.single_eq_C_mul_T]

end
end ModifiedCartan

