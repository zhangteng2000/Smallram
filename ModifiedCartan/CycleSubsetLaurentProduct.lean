import ModifiedCartan.LaurentCompositionExpansion
import Mathlib.Algebra.BigOperators.Ring.Finset

open scoped BigOperators Classical LaurentPolynomial

namespace ModifiedCartan
noncomputable section

theorem laurent_signed_product {I R : Type*} [CommRing R] (s : Finset I) (j : I → ℤ) (p : I → R) :
    (∏ i ∈ s, -(LaurentPolynomial.T (j i) * LaurentPolynomial.C (p i))) =
      LaurentPolynomial.C ((-1 : R) ^ s.card * ∏ i ∈ s, p i) *
        LaurentPolynomial.T (∑ i ∈ s, j i) := by
  have he (i : I) : -(LaurentPolynomial.T (j i) * LaurentPolynomial.C (p i)) =
      LaurentPolynomial.C (-p i) * LaurentPolynomial.T (j i) := by
    rw [map_neg]
    ring
  simp_rw [he]
  rw [Finset.prod_mul_distrib, ← map_prod, laurent_prod_T, Finset.prod_neg]

/-- Actual powerset expansion of the finite complement-cycle product. -/
theorem sum_signed_laurent_subsets {I R : Type*} [CommRing R]
    (s : Finset I) (j : I → ℤ) (p : I → R) :
    (∑ c ∈ s.powerset, LaurentPolynomial.C ((-1 : R) ^ c.card * ∏ i ∈ c, p i) *
      LaurentPolynomial.T (∑ i ∈ c, j i)) =
    ∏ i ∈ s, (1 - LaurentPolynomial.T (j i) * LaurentPolynomial.C (p i)) := by
  calc
    _ = ∑ c ∈ s.powerset, ∏ i ∈ c, -(LaurentPolynomial.T (j i) * LaurentPolynomial.C (p i)) := by
      apply Finset.sum_congr rfl
      intro c hc
      exact (laurent_signed_product c j p).symm
    _ = ∏ i ∈ s, (1 + -(LaurentPolynomial.T (j i) * LaurentPolynomial.C (p i))) :=
      (Finset.prod_one_add s).symm
    _ = _ := by simp only [sub_eq_add_neg]

end
end ModifiedCartan

