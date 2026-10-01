import ModifiedCartan.LaurentVariableUnit
import ModifiedCartan.FiniteBernstein

open scoped BigOperators Classical LaurentPolynomial

namespace ModifiedCartan
noncomputable section

def finiteAlphabetShiftLaurent (B : Type*) :
    LaurentPolynomial (MvPolynomial (Option B) ℂ) →+* LaurentPolynomial (MvPolynomial B ℂ) :=
  LaurentPolynomial.eval₂ (finiteAlphabetShift B) (laurentVariableUnit (MvPolynomial B ℂ))

theorem finiteAlphabetShiftLaurent_T (B : Type*) (n : ℤ) :
    finiteAlphabetShiftLaurent B (LaurentPolynomial.T n) = LaurentPolynomial.T n :=
  laurent_eval₂_variable_T (finiteAlphabetShift B) n

theorem finiteAlphabetShiftLaurent_C (B : Type*) (f : MvPolynomial (Option B) ℂ) :
    finiteAlphabetShiftLaurent B (LaurentPolynomial.C f) = finiteAlphabetShift B f :=
  LaurentPolynomial.eval₂_C _ _ f

def finiteBernsteinLaurent (B : Type*) [Fintype B]
    (f : LaurentPolynomial (MvPolynomial (Option B) ℂ)) : LaurentPolynomial (MvPolynomial B ℂ) :=
  finiteElementaryLaurent B * finiteAlphabetShiftLaurent B f

theorem finiteBernsteinLaurent_add (B : Type*) [Fintype B]
    (f g : LaurentPolynomial (MvPolynomial (Option B) ℂ)) :
    finiteBernsteinLaurent B (f + g) = finiteBernsteinLaurent B f + finiteBernsteinLaurent B g := by
  rw [finiteBernsteinLaurent, map_add, mul_add]
  rfl

theorem finiteBernsteinLaurent_sum {I B : Type*} [Fintype B]
    (s : Finset I) (f : I → LaurentPolynomial (MvPolynomial (Option B) ℂ)) :
    finiteBernsteinLaurent B (∑ i ∈ s, f i) = ∑ i ∈ s, finiteBernsteinLaurent B (f i) := by
  rw [finiteBernsteinLaurent, map_sum, Finset.mul_sum]
  rfl

theorem finiteBernsteinLaurent_T_mul (B : Type*) [Fintype B] (n : ℤ)
    (f : LaurentPolynomial (MvPolynomial (Option B) ℂ)) :
    finiteBernsteinLaurent B (LaurentPolynomial.T n * f) =
      LaurentPolynomial.T n * finiteBernsteinLaurent B f := by
  rw [finiteBernsteinLaurent, map_mul, finiteAlphabetShiftLaurent_T]
  exact mul_left_comm _ _ _

theorem finiteBernsteinLaurent_C (B : Type*) [Fintype B] (f : MvPolynomial (Option B) ℂ) :
    finiteBernsteinLaurent B (LaurentPolynomial.C f) = finiteBernstein B f := by
  rw [finiteBernsteinLaurent, finiteAlphabetShiftLaurent_C]
  rfl

end
end ModifiedCartan

