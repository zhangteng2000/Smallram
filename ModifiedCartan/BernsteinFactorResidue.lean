import ModifiedCartan.BernsteinLaurentFactors
import ModifiedCartan.LaurentCompositionExpansion

open scoped BigOperators Classical LaurentPolynomial

namespace ModifiedCartan
noncomputable section

theorem laurent_powerSumFactor_product {I B : Type*} [Fintype B] (s : Finset I) (j : I → ℕ) :
    (∏ i ∈ s, -(LaurentPolynomial.T (j i : ℤ) *
      LaurentPolynomial.C (finitePowerSumPolynomial B (j i)))) =
      LaurentPolynomial.C (∏ i ∈ s, -finitePowerSumPolynomial B (j i)) *
        LaurentPolynomial.T (∑ i ∈ s, (j i : ℤ)) := by
  have he (i : I) : -(LaurentPolynomial.T (j i : ℤ) *
      LaurentPolynomial.C (finitePowerSumPolynomial B (j i))) =
      LaurentPolynomial.C (-finitePowerSumPolynomial B (j i)) * LaurentPolynomial.T (j i : ℤ) := by
    rw [map_neg]
    ring
  simp_rw [he]
  rw [Finset.prod_mul_distrib, ← map_prod, laurent_prod_T]

theorem finiteBernsteinLaurent_strip_factors {I B : Type*} [Fintype B] (s : Finset I)
    (j : I → ℕ) (f : LaurentPolynomial (MvPolynomial (Option B) ℂ)) :
    finiteBernsteinLaurent B ((∏ i ∈ s, (1 - LaurentPolynomial.T (j i : ℤ) *
      LaurentPolynomial.C (finitePowerSumPolynomial (Option B) (j i)))) * f) =
      LaurentPolynomial.C (∏ i ∈ s, -finitePowerSumPolynomial B (j i)) *
        finiteBernsteinLaurent B (LaurentPolynomial.T (∑ i ∈ s, (j i : ℤ)) * f) := by
  rw [finiteBernsteinLaurent_powerSumFactors, laurent_powerSumFactor_product,
    finiteBernsteinLaurent_T_mul, mul_assoc]

theorem finiteBernsteinLaurent_strip_factors_residue {I B : Type*} [Fintype B] (s : Finset I)
    (j : I → ℕ) (f : LaurentPolynomial (MvPolynomial (Option B) ℂ))
    (hf : (finiteBernsteinLaurent B (LaurentPolynomial.T (∑ i ∈ s, (j i : ℤ)) * f)).coeff (-1) = 0) :
    (finiteBernsteinLaurent B ((∏ i ∈ s, (1 - LaurentPolynomial.T (j i : ℤ) *
      LaurentPolynomial.C (finitePowerSumPolynomial (Option B) (j i)))) * f)).coeff (-1) = 0 := by
  rw [finiteBernsteinLaurent_strip_factors, ← LaurentPolynomial.single_eq_C,
    AddMonoidAlgebra.coeff_single_zero_mul, hf, mul_zero]

end
end ModifiedCartan

