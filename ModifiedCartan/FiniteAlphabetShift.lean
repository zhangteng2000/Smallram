import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Data.Complex.Basic

open scoped BigOperators Classical LaurentPolynomial

namespace ModifiedCartan
noncomputable section

def finiteAlphabetShift (B : Type*) :
    MvPolynomial (Option B) ℂ →+* LaurentPolynomial (MvPolynomial B ℂ) :=
  MvPolynomial.eval₂Hom (LaurentPolynomial.C.comp MvPolynomial.C)
    (fun b => match b with
      | none => LaurentPolynomial.T (-1)
      | some b => LaurentPolynomial.C (MvPolynomial.X b))

theorem finiteAlphabetShift_none (B : Type*) :
    finiteAlphabetShift B (MvPolynomial.X none) = LaurentPolynomial.T (-1) := by
  simp [finiteAlphabetShift]

theorem finiteAlphabetShift_some (B : Type*) (b : B) :
    finiteAlphabetShift B (MvPolynomial.X (some b)) = LaurentPolynomial.C (MvPolynomial.X b) := by
  simp [finiteAlphabetShift]

theorem finiteAlphabetShift_rename (B : Type*) (f : MvPolynomial B ℂ) :
    finiteAlphabetShift B (MvPolynomial.rename some f) = LaurentPolynomial.C f := by
  induction f using MvPolynomial.induction_on with
  | C c => simp [finiteAlphabetShift]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p b hp => simp only [map_mul, MvPolynomial.rename_X, finiteAlphabetShift_some, hp]

def finitePowerSumPolynomial (B : Type*) [Fintype B] (j : ℕ) : MvPolynomial B ℂ :=
  ∑ b : B, MvPolynomial.X b ^ j

theorem finiteAlphabetShift_powerSum (B : Type*) [Fintype B] (j : ℕ) :
    finiteAlphabetShift B (finitePowerSumPolynomial (Option B) j) =
      LaurentPolynomial.T (-(j : ℤ)) + LaurentPolynomial.C (finitePowerSumPolynomial B j) := by
  simp only [finitePowerSumPolynomial, Fintype.sum_option, map_add, map_sum, map_pow,
    finiteAlphabetShift_none, finiteAlphabetShift_some, LaurentPolynomial.T_pow,
    mul_neg, mul_one]

end
end ModifiedCartan

