import ModifiedCartan.FiniteBernstein
import ModifiedCartan.ScaledMonomialExtraVariable

open scoped BigOperators Classical LaurentPolynomial

namespace ModifiedCartan
noncomputable section

theorem finiteAlphabetShift_scaledMonomial {A B : Type*}
    [Fintype A] [DecidableEq A] [Fintype B] (κ : A → ℕ) :
    finiteAlphabetShift B (scaledMonomialPolynomial (Option B) κ) =
      LaurentPolynomial.C (scaledMonomialPolynomial B κ) +
        ∑ a : A, LaurentPolynomial.T (-(κ a : ℤ)) * LaurentPolynomial.C
          (scaledMonomialPolynomial B (fun i : {i : A // i ≠ a} => κ i.val)) := by
  rw [scaledMonomialPolynomial_add_variable, map_add, map_sum]
  simp only [map_mul, map_pow, finiteAlphabetShift_none, finiteAlphabetShift_rename,
    LaurentPolynomial.T_pow, mul_neg, mul_one]

theorem finiteBernstein_scaledMonomial {A B : Type*}
    [Fintype A] [DecidableEq A] [Fintype B] (κ : A → ℕ) :
    finiteBernstein B (scaledMonomialPolynomial (Option B) κ) =
      finiteElementaryLaurent B * LaurentPolynomial.C (scaledMonomialPolynomial B κ) +
        ∑ a : A, LaurentPolynomial.T (-(κ a : ℤ)) * (finiteElementaryLaurent B * LaurentPolynomial.C
          (scaledMonomialPolynomial B (fun i : {i : A // i ≠ a} => κ i.val))) := by
  rw [finiteBernstein, finiteAlphabetShift_scaledMonomial, mul_add, Finset.mul_sum]
  apply congrArg (fun q => finiteElementaryLaurent B *
    LaurentPolynomial.C (scaledMonomialPolynomial B κ) + q)
  apply Finset.sum_congr rfl
  intro a ha
  exact mul_left_comm _ _ _

end
end ModifiedCartan


