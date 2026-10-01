import ModifiedCartan.SupportedPowerSumQuadratic
import ModifiedCartan.ZFactorizationResidue

open scoped Classical

namespace ModifiedCartan
noncomputable section

/-- Every squarefree marker coefficient of the actual supported-permutation
quadratic expression has zero finite Bernstein residue. KP Section 4.1.4;
auxiliary to LaTeX `lem:KP-correspondence`. Non-squarefree coefficients and the
Schur/Plucker bridge remain separate statements. -/
theorem supportedPowerSumQuadratic_squarefree_residue {A B : Type*}
    [Fintype A] [Fintype B] (θ : Equiv.Perm A) (Z : Finset A) :
    (finiteBernsteinLaurent B
      (MvPolynomial.coeff (markerSquarefreeDegree (Finset.univ \ Z))
        ((supportedPowerSumQuadratic A (Option B)).coeff θ))).coeff (-1) = 0 := by
  rw [supportedPowerSumQuadratic_squarefree_coeff]
  exact zFactorizationLaurentSeries_residue θ Z

end
end ModifiedCartan

