import ModifiedCartan.FiniteBernsteinCoefficients
import ModifiedCartan.FiniteFrobeniusSchur
import ModifiedCartan.FrobeniusAlphabetEquiv

open scoped BigOperators Classical LaurentPolynomial

namespace ModifiedCartan
noncomputable section

def finiteFrobeniusBernsteinResidue (B : Type*) [Fintype B] (μ : YoungDiagram) (k : ℕ) :
    MvPolynomial B ℂ :=
  (LaurentPolynomial.T (-(k : ℤ)) *
    finiteBernstein B (finiteFrobeniusPolynomial (Option B) μ)).coeff (-1)

/-- The exact alternant coefficient of a finite Frobenius Bernstein residue.
    This supplies the finite character-to-single-column bridge for
    manuscript `lem:KP-correspondence`, without invoking a symmetric-function result. -/
theorem finiteFrobeniusBernsteinResidue_mul_vandermonde {m k : ℕ}
    (μ : YoungDiagram) (hμ : μ.colLen 0 ≤ m + 1) (hk : k ≤ m + 1) :
    finiteVandermondeAlternant m * finiteFrobeniusBernsteinResidue (Fin m) μ k =
      (MvPolynomial.finSuccEquiv ℂ m
        (finiteAlternant (partitionAlternantExponent (m + 1) μ))).coeff (m + 1 - k) := by
  have h := finiteBernstein_residue_mul_vandermonde
    (finiteFrobeniusPolynomial (Fin (m + 1)) μ) hk
  rw [finiteFrobeniusPolynomial_rename_equiv,
    finiteFrobeniusPolynomial_mul_alternant μ hμ] at h
  exact h

end
end ModifiedCartan

#print axioms ModifiedCartan.finiteFrobeniusBernsteinResidue_mul_vandermonde
