import Mathlib.Algebra.Polynomial.Laurent

open scoped Classical LaurentPolynomial

namespace ModifiedCartan
noncomputable section

theorem laurent_coeff_C_mul {R : Type*} [Semiring R]
    (c : R) (p : LaurentPolynomial R) (j : ℤ) :
    (LaurentPolynomial.C c * p).coeff j = c * p.coeff j := by
  rw [← LaurentPolynomial.single_eq_C, AddMonoidAlgebra.coeff_single_zero_mul]

theorem laurent_coeff_T_mul {R : Type*} [Semiring R]
    (k : ℤ) (p : LaurentPolynomial R) (j : ℤ) :
    (LaurentPolynomial.T k * p).coeff j = p.coeff (j - k) := by
  simp only [LaurentPolynomial.T, AddMonoidAlgebra.coeff_single_mul_apply, one_mul,
    sub_eq_add_neg, add_comm]

theorem toLaurent_coeff_nat {R : Type*} [Semiring R] (p : Polynomial R) (j : ℕ) :
    p.toLaurent.coeff (j : ℤ) = p.coeff j := by
  rw [LaurentPolynomial.coeff_toLaurent]
  change (Finsupp.mapDomain (Nat.castEmbedding : ℕ ↪ ℤ) p.toFinsupp.coeff)
    ((Nat.castEmbedding : ℕ ↪ ℤ) j) = _
  rw [Finsupp.mapDomain_apply (Nat.castEmbedding : ℕ ↪ ℤ).injective,
    Polynomial.toFinsupp_apply]

theorem invert_toLaurent_coeff_neg_nat {R : Type*} [CommSemiring R]
    (p : Polynomial R) (j : ℕ) :
    (LaurentPolynomial.invert p.toLaurent).coeff (-(j : ℤ)) = p.coeff j := by
  rw [LaurentPolynomial.invert_apply, neg_neg, toLaurent_coeff_nat]

end
end ModifiedCartan
