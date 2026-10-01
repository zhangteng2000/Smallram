import ModifiedCartan.FiniteBernsteinLaurent

open scoped BigOperators Classical LaurentPolynomial

namespace ModifiedCartan
noncomputable section

theorem finiteAlphabetShiftLaurent_powerSumFactor (B : Type*) [Fintype B] (j : ℕ) :
    finiteAlphabetShiftLaurent B (1 - LaurentPolynomial.T (j : ℤ) *
      LaurentPolynomial.C (finitePowerSumPolynomial (Option B) j)) =
      -(LaurentPolynomial.T (j : ℤ) * LaurentPolynomial.C (finitePowerSumPolynomial B j)) := by
  rw [map_sub, map_one, map_mul, finiteAlphabetShiftLaurent_T,
    finiteAlphabetShiftLaurent_C, finiteAlphabetShift_powerSum, mul_add,
    ← LaurentPolynomial.T_add, add_neg_cancel, LaurentPolynomial.T_zero]
  ring

theorem finiteBernsteinLaurent_mul (B : Type*) [Fintype B]
    (g f : LaurentPolynomial (MvPolynomial (Option B) ℂ)) :
    finiteBernsteinLaurent B (g * f) = finiteAlphabetShiftLaurent B g * finiteBernsteinLaurent B f := by
  rw [finiteBernsteinLaurent, map_mul]
  exact mul_left_comm _ _ _

theorem finiteBernsteinLaurent_powerSumFactor (B : Type*) [Fintype B] (j : ℕ)
    (f : LaurentPolynomial (MvPolynomial (Option B) ℂ)) :
    finiteBernsteinLaurent B ((1 - LaurentPolynomial.T (j : ℤ) *
      LaurentPolynomial.C (finitePowerSumPolynomial (Option B) j)) * f) =
      -(LaurentPolynomial.T (j : ℤ) * LaurentPolynomial.C (finitePowerSumPolynomial B j)) *
        finiteBernsteinLaurent B f := by
  rw [finiteBernsteinLaurent_mul, finiteAlphabetShiftLaurent_powerSumFactor]

theorem finiteBernsteinLaurent_powerSumFactors {I B : Type*} [Fintype B] (s : Finset I)
    (j : I → ℕ) (f : LaurentPolynomial (MvPolynomial (Option B) ℂ)) :
    finiteBernsteinLaurent B ((∏ i ∈ s, (1 - LaurentPolynomial.T (j i : ℤ) *
      LaurentPolynomial.C (finitePowerSumPolynomial (Option B) (j i)))) * f) =
      (∏ i ∈ s, -(LaurentPolynomial.T (j i : ℤ) *
        LaurentPolynomial.C (finitePowerSumPolynomial B (j i)))) * finiteBernsteinLaurent B f := by
  rw [finiteBernsteinLaurent_mul, map_prod]
  simp only [finiteAlphabetShiftLaurent_powerSumFactor]

end
end ModifiedCartan

