import ModifiedCartan.RightZFactorLaurentProduct
import ModifiedCartan.BernsteinScalarResidue
import ModifiedCartan.FactoredCompositionResidue

open scoped BigOperators Classical LaurentPolynomial

namespace ModifiedCartan
noncomputable section

/-- The exact actual-permutation right-factor Laurent sum lies in the finite
Bernstein residue kernel. KP Section 4.1; auxiliary to `lem:KP-correspondence`.
No character-to-Schur or Plucker assertion is included in this theorem. -/
theorem rightZFactorLaurentSeries_residue {A B : Type*} [Fintype A] [Fintype B]
    (θ : Equiv.Perm A) (Z : Finset A) :
    (finiteBernsteinLaurent B (rightZFactorLaurentSeries (Option B) θ Z)).coeff (-1) = 0 := by
  rw [rightZFactorLaurentSeries_factorized]
  apply finiteBernsteinLaurent_scalar_residue
  rw [mul_comm]
  exact finiteBernstein_factored_composition_residue (zStripLength θ Z)
    (permutationCycleImage θ (zStripComplement θ Z))
    (permutationCycleWeight θ (fun _ => 1))

end
end ModifiedCartan

