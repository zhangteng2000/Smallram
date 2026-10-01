import Mathlib.Algebra.Polynomial.Laurent

open scoped LaurentPolynomial

namespace ModifiedCartan
noncomputable section

def laurentVariableUnit (R : Type*) [CommSemiring R] : (LaurentPolynomial R)ˣ where
  val := LaurentPolynomial.T 1
  inv := LaurentPolynomial.T (-1)
  val_inv := by rw [← LaurentPolynomial.T_add, add_neg_cancel, LaurentPolynomial.T_zero]
  inv_val := by rw [← LaurentPolynomial.T_add, neg_add_cancel, LaurentPolynomial.T_zero]

theorem laurent_eval₂_variable_T {R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* LaurentPolynomial S) (n : ℤ) :
    LaurentPolynomial.eval₂ f (laurentVariableUnit S) (LaurentPolynomial.T n) =
      LaurentPolynomial.T n := by
  cases n with
  | ofNat n =>
    change LaurentPolynomial.eval₂ f (laurentVariableUnit S)
      (LaurentPolynomial.T (n : ℤ)) = LaurentPolynomial.T (n : ℤ)
    rw [LaurentPolynomial.eval₂_T_n f (laurentVariableUnit S) n]
    change (LaurentPolynomial.T 1 : LaurentPolynomial S) ^ n = _
    rw [LaurentPolynomial.T_pow, mul_one]
  | negSucc n =>
    change LaurentPolynomial.eval₂ f (laurentVariableUnit S)
      (LaurentPolynomial.T (-((n + 1 : ℕ) : ℤ))) = _
    rw [LaurentPolynomial.eval₂_T_neg_n]
    change (LaurentPolynomial.T (-1) : LaurentPolynomial S) ^ (n + 1) = _
    rw [LaurentPolynomial.T_pow]
    congr 1
    omega

end
end ModifiedCartan

