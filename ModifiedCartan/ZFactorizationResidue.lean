import ModifiedCartan.ZFactorizationLaurentSeries
import ModifiedCartan.RightZFactorResidue

open scoped Classical

namespace ModifiedCartan
noncomputable section

/-- The finite Bernstein residue of the literal supported-factorization sum
vanishes. KP Section 4.1.4, auxiliary to LaTeX `lem:KP-correspondence`. -/
theorem zFactorizationLaurentSeries_residue {A B : Type*} [Fintype A] [Fintype B]
    (θ : Equiv.Perm A) (Z : Finset A) :
    (finiteBernsteinLaurent B (zFactorizationLaurentSeries (Option B) θ Z)).coeff (-1) = 0 := by
  rw [zFactorizationLaurentSeries_eq]
  exact finiteBernsteinLaurent_scalar_residue B _ _ (rightZFactorLaurentSeries_residue θ Z)

end
end ModifiedCartan

