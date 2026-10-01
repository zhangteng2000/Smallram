import ModifiedCartan.FiniteFinAlphabetShift
import ModifiedCartan.LaurentPolynomialCoefficients

open scoped BigOperators Classical LaurentPolynomial

namespace ModifiedCartan
noncomputable section

theorem finiteFinAlphabetShift_eq_invert {m : ℕ} (f : MvPolynomial (Fin (m + 1)) ℂ) :
    finiteFinAlphabetShift m f =
      LaurentPolynomial.invert (MvPolynomial.finSuccEquiv ℂ m f).toLaurent := by
  have hx (i : Fin (m + 1)) : finiteFinAlphabetShift m (MvPolynomial.X i) =
      LaurentPolynomial.invert (MvPolynomial.finSuccEquiv ℂ m (MvPolynomial.X i)).toLaurent := by
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [finiteFinAlphabetShift_X_zero, MvPolynomial.finSuccEquiv_X_zero]
    · simp [finiteFinAlphabetShift_X_succ, MvPolynomial.finSuccEquiv_X_succ]
  induction f using MvPolynomial.induction_on with
  | C c => simp [finiteFinAlphabetShift_C, MvPolynomial.finSuccEquiv_apply]
  | add f g hf hg => simp only [map_add, hf, hg]
  | mul_X f i hf =>
    simpa only [map_mul] using congrArg₂
      (fun p q : LaurentPolynomial (MvPolynomial (Fin m) ℂ) => p * q) hf (hx i)

theorem finiteFinAlphabetShift_coeff_neg_nat {m : ℕ}
    (f : MvPolynomial (Fin (m + 1)) ℂ) (j : ℕ) :
    (finiteFinAlphabetShift m f).coeff (-(j : ℤ)) =
      (MvPolynomial.finSuccEquiv ℂ m f).coeff j := by
  rw [finiteFinAlphabetShift_eq_invert, invert_toLaurent_coeff_neg_nat]

/-- The literal finite Bernstein residue is the required first-variable
    coefficient of the alternating polynomial, with the exact index and sign.
    Auxiliary to KP Lemma 2.20 in manuscript `lem:KP-correspondence`. -/
theorem finiteBernstein_residue_mul_vandermonde {m k : ℕ}
    (f : MvPolynomial (Fin (m + 1)) ℂ) (hk : k ≤ m + 1) :
    finiteVandermondeAlternant m *
      (LaurentPolynomial.T (-(k : ℤ)) *
        finiteBernstein (Fin m) (MvPolynomial.rename (_root_.finSuccEquiv m) f)).coeff (-1) =
      (MvPolynomial.finSuccEquiv ℂ m (finiteVandermondeAlternant (m + 1) * f)).coeff
        (m + 1 - k) := by
  have h := congrArg (fun p : LaurentPolynomial (MvPolynomial (Fin m) ℂ) =>
    (LaurentPolynomial.T (-(k : ℤ)) * p).coeff (-1)) (finiteBernstein_mul_vandermonde f)
  have hl : LaurentPolynomial.T (-(k : ℤ)) *
      (LaurentPolynomial.C (finiteVandermondeAlternant m) *
        finiteBernstein (Fin m) (MvPolynomial.rename (_root_.finSuccEquiv m) f)) =
      LaurentPolynomial.C (finiteVandermondeAlternant m) *
        (LaurentPolynomial.T (-(k : ℤ)) *
          finiteBernstein (Fin m) (MvPolynomial.rename (_root_.finSuccEquiv m) f)) := by ring
  rw [hl, laurent_coeff_C_mul] at h
  simp only [laurent_coeff_T_mul] at h
  have he : ((-1 : ℤ) - -(k : ℤ)) - (m : ℤ) = -((m + 1 - k : ℕ) : ℤ) := by
    omega
  rw [he, finiteFinAlphabetShift_coeff_neg_nat] at h
  simpa only [laurent_coeff_T_mul] using h

end
end ModifiedCartan

#print axioms ModifiedCartan.finiteBernstein_residue_mul_vandermonde
