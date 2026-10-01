import ModifiedCartan.DescendingVandermonde
import ModifiedCartan.FiniteBernstein
import Mathlib.Algebra.MvPolynomial.Equiv

open scoped BigOperators Classical LaurentPolynomial

namespace ModifiedCartan
noncomputable section

def finiteFinAlphabetShift (m : ℕ) :
    MvPolynomial (Fin (m + 1)) ℂ →+* LaurentPolynomial (MvPolynomial (Fin m) ℂ) :=
  (finiteAlphabetShift (Fin m)).comp (MvPolynomial.rename (_root_.finSuccEquiv m)).toRingHom

theorem finiteFinAlphabetShift_X_zero (m : ℕ) :
    finiteFinAlphabetShift m (MvPolynomial.X 0) = LaurentPolynomial.T (-1) := by
  simp [finiteFinAlphabetShift, finiteAlphabetShift_none]

theorem finiteFinAlphabetShift_X_succ {m : ℕ} (i : Fin m) :
    finiteFinAlphabetShift m (MvPolynomial.X i.succ) = LaurentPolynomial.C (MvPolynomial.X i) := by
  simp [finiteFinAlphabetShift, finiteAlphabetShift_some]

theorem finiteFinAlphabetShift_C (m : ℕ) (c : ℂ) :
    finiteFinAlphabetShift m (MvPolynomial.C c) = LaurentPolynomial.C (MvPolynomial.C c) := by
  simp [finiteFinAlphabetShift, finiteAlphabetShift]

theorem finiteFinAlphabetShift_rename_succ (m : ℕ) (f : MvPolynomial (Fin m) ℂ) :
    finiteFinAlphabetShift m (MvPolynomial.rename Fin.succ f) = LaurentPolynomial.C f := by
  induction f using MvPolynomial.induction_on with
  | C c => simp only [MvPolynomial.rename_C, finiteFinAlphabetShift_C]
  | add f g hf hg => simp only [map_add, hf, hg]
  | mul_X f i hf => simp only [map_mul, MvPolynomial.rename_X, finiteFinAlphabetShift_X_succ, hf]

theorem laurent_T_neg_one_sub {R : Type*} [CommRing R] (c : R) :
    LaurentPolynomial.T (-1) - LaurentPolynomial.C c =
      LaurentPolynomial.T (-1) * (1 - LaurentPolynomial.C c * LaurentPolynomial.T 1) := by
  have h : (LaurentPolynomial.T (-1) : LaurentPolynomial R) * LaurentPolynomial.T 1 = 1 := by
    rw [← LaurentPolynomial.T_add]
    norm_num
  calc
    _ = LaurentPolynomial.T (-1) - LaurentPolynomial.C c *
        (LaurentPolynomial.T (-1) * LaurentPolynomial.T 1) := by rw [h, mul_one]
    _ = _ := by ring

theorem finiteFinAlphabetShift_vandermonde (m : ℕ) :
    finiteFinAlphabetShift m (finiteVandermondeAlternant (m + 1)) =
      LaurentPolynomial.T (-(m : ℤ)) * LaurentPolynomial.C (finiteVandermondeAlternant m) *
        finiteElementaryLaurent (Fin m) := by
  rw [finiteVandermondeAlternant_map_succ]
  change (∏ i : Fin m, (finiteFinAlphabetShift m (MvPolynomial.X 0) -
    finiteFinAlphabetShift m (MvPolynomial.X i.succ))) *
      finiteFinAlphabetShift m (MvPolynomial.rename Fin.succ (finiteVandermondeAlternant m)) = _
  simp only [finiteFinAlphabetShift_X_zero, finiteFinAlphabetShift_X_succ,
    finiteFinAlphabetShift_rename_succ, laurent_T_neg_one_sub, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, LaurentPolynomial.T_pow,
    mul_neg, mul_one]
  unfold finiteElementaryLaurent
  ring

/-- Clearing the finite Vandermonde denominator converts the literal Bernstein
    operator into a shifted alternating polynomial. Auxiliary to `lem:KP-correspondence`. -/
theorem finiteBernstein_mul_vandermonde {m : ℕ} (f : MvPolynomial (Fin (m + 1)) ℂ) :
    LaurentPolynomial.C (finiteVandermondeAlternant m) *
      finiteBernstein (Fin m) (MvPolynomial.rename (_root_.finSuccEquiv m) f) =
        LaurentPolynomial.T (m : ℤ) *
          finiteFinAlphabetShift m (finiteVandermondeAlternant (m + 1) * f) := by
  rw [map_mul, finiteFinAlphabetShift_vandermonde]
  have h : (LaurentPolynomial.T (m : ℤ) : LaurentPolynomial (MvPolynomial (Fin m) ℂ)) *
      LaurentPolynomial.T (-(m : ℤ)) = 1 := by
    rw [← LaurentPolynomial.T_add, add_neg_cancel, LaurentPolynomial.T_zero]
  change _ = LaurentPolynomial.T (m : ℤ) *
    (LaurentPolynomial.T (-(m : ℤ)) * LaurentPolynomial.C (finiteVandermondeAlternant m) *
      finiteElementaryLaurent (Fin m) * _)
  rw [← mul_assoc, ← mul_assoc, ← mul_assoc, h, one_mul]
  simp only [finiteBernstein, finiteFinAlphabetShift, RingHom.comp_apply, mul_assoc]
  rfl

end
end ModifiedCartan

#print axioms ModifiedCartan.finiteBernstein_mul_vandermonde
