import ModifiedCartan.FiniteAlphabetShift
import Mathlib.Tactic.Ring

open scoped BigOperators Classical LaurentPolynomial

namespace ModifiedCartan
noncomputable section

def finiteElementaryLaurent (B : Type*) [Fintype B] : LaurentPolynomial (MvPolynomial B ℂ) :=
  ∏ b : B, (1 - LaurentPolynomial.C (MvPolynomial.X b) * LaurentPolynomial.T 1)

/-- Finite-alphabet realization of multiplication by E(-t) after adding t⁻¹
as one extra variable. -/
def finiteBernstein (B : Type*) [Fintype B] (f : MvPolynomial (Option B) ℂ) :
    LaurentPolynomial (MvPolynomial B ℂ) :=
  finiteElementaryLaurent B * finiteAlphabetShift B f

theorem finiteAlphabetShift_powerSum_factor (B : Type*) [Fintype B] (j : ℕ)
    (f : MvPolynomial (Option B) ℂ) :
    finiteAlphabetShift B f - LaurentPolynomial.T (j : ℤ) *
      finiteAlphabetShift B (finitePowerSumPolynomial (Option B) j * f) =
        -(LaurentPolynomial.T (j : ℤ) * LaurentPolynomial.C (finitePowerSumPolynomial B j)) *
          finiteAlphabetShift B f := by
  have ht : (LaurentPolynomial.T (j : ℤ) : LaurentPolynomial (MvPolynomial B ℂ)) *
      LaurentPolynomial.T (-(j : ℤ)) = 1 := by
    rw [← LaurentPolynomial.T_add, add_neg_cancel, LaurentPolynomial.T_zero]
  rw [map_mul, finiteAlphabetShift_powerSum]
  calc
    _ = finiteAlphabetShift B f -
        (LaurentPolynomial.T (j : ℤ) * LaurentPolynomial.T (-(j : ℤ))) * finiteAlphabetShift B f -
        LaurentPolynomial.T (j : ℤ) * LaurentPolynomial.C (finitePowerSumPolynomial B j) *
          finiteAlphabetShift B f := by ring
    _ = _ := by rw [ht]; ring

/-- Exact finite-alphabet power-sum factor identity used in KP source Lemma 2.24. -/
theorem finiteBernstein_powerSum_factor (B : Type*) [Fintype B] (j : ℕ)
    (f : MvPolynomial (Option B) ℂ) :
    finiteBernstein B f - LaurentPolynomial.T (j : ℤ) *
      finiteBernstein B (finitePowerSumPolynomial (Option B) j * f) =
        -(LaurentPolynomial.T (j : ℤ) * LaurentPolynomial.C (finitePowerSumPolynomial B j)) *
          finiteBernstein B f := by
  unfold finiteBernstein
  calc
    _ = finiteElementaryLaurent B * (finiteAlphabetShift B f - LaurentPolynomial.T (j : ℤ) *
        finiteAlphabetShift B (finitePowerSumPolynomial (Option B) j * f)) := by ring
    _ = _ := by rw [finiteAlphabetShift_powerSum_factor]; ring

end
end ModifiedCartan

